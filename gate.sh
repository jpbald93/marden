#!/bin/bash
# Gate for the Lean formalisation. It passes only if all of these hold:
#  * the sources contain no `sorry`, `admit`, `native_decide`, `axiom` keyword (anywhere,
#    including one on a line of its own), `#eval`, `run_cmd`, `initialize`, `IO`, `set_option`,
#    or syntax-extension commands (`macro`, `elab`, `syntax`, `notation`, `import Lean`, ...),
#    which could redefine `#print axioms`;
#  * the library builds without errors;
#  * the gate itself (not a file in the repo) generates the `#print axioms` report for each
#    REQUIRED declaration, and each report is present exactly once;
#  * each REQUIRED declaration (with its transitive dependencies) uses only Lean's standard axioms
#    (propext, Classical.choice, Quot.sound).
# REQUIRED lists every declaration cited in the accompanying paper, plus the declarations queried
# during development; names are fully qualified. Definitions may use a subset of the three axioms.
# Trust boundary: the token filter is a heuristic over the project's .lean sources. The gate assumes
# the pinned toolchain, Mathlib and lake configuration are unmodified. It is not a sandbox, and it
# does not audit declarations other than the REQUIRED ones.
# Lean wraps long axiom lists across several lines, so the output is flattened before parsing.
export PATH="$HOME/.elan/bin:$PATH"
cd "$(dirname "$0")" || exit 1
LIB="Marden"
REQUIRED="Marden.exists_critical_points Marden.focalSum Marden.focalSum_midpoint_sq Marden.focalSum_midpoints_eq Marden.focal_le_of_mul Marden.focal_lt_of_mul Marden.foci_of_reflection Marden.focus_off_side Marden.lam_eq_core Marden.lam_twelfth_core Marden.marden Marden.midpoint_mul Marden.nondeg_of_midpoints Marden.reflection_of_min Marden.steiner_inellipse_iff Marden.steiner_inellipse_unique Marden.steiner_unique Marden.vieta Marden.l14_collinear_iff Marden.l14_marden Marden.l14_steiner_unique Marden.l14w_not_collinear Marden.l14w_derivative Marden.l14w_marden Marden.l15_collinear_iff Marden.l15_of_not_collinear Marden.l15_midpoint_eq Marden.l15_centroid_eq Marden.l15_dist_add_dist Marden.l15_strict_on_line Marden.l15_strict_of_on_line Marden.l15_marden Marden.l15_steiner_unique Marden.Classical.l15_focal_line_cont Marden.Classical.l15_focal_line_ge Marden.Classical.l15_ivt_pos Marden.Classical.l15_strict_of_unique Marden.Classical.l15_strict_of_inter Marden.Classical.l15_steiner_foci Marden.Classical.l15_cross Marden.Classical.l15_mem_line_of_cross Marden.Classical.l15_dist_convex Marden.Classical.l15_halfplane Marden.Classical.l15_cross_centroid Marden.Classical.l15_mem_hull Marden.Classical.l15_cross_ne Marden.Classical.l15_midpoint_mem Marden.Classical.l15_cross_swap Marden.Classical.l15_marden_steiner Marden.Classical.l15_roots Marden.Classical.l15_crit Marden.Classical.cov_Conics4_a Marden.Classical.cov_Conics4_b_part Marden.Classical.cov_Conics5 Marden.Classical.l15_equilateral_iff Marden.Classical.cov_Conics5_double_root"
SOURCES="$(find $LIB -name '*.lean' | sort | tr '\n' ' ') $LIB.lean"
[ -e .lake/packages/mathlib ] || lake exe cache get || { echo "FAIL: could not fetch Mathlib cache"; exit 1; }
if grep -nE "\bsorry\b|\badmit\b|native_decide|\baxiom\b|#eval|\brun_cmd\b|\binitialize\b|\bIO\b|\bdebug\.|\bmacro|\belab|\bsyntax\b|\bnotation\b|\binfix|\bprefix\b|\bpostfix\b|import Lean|open Lean|\bset_option\b" $SOURCES; then
  echo "FAIL: forbidden token"; exit 1; fi
build=$(lake build $LIB 2>&1); bstatus=$?
printf '%s\n' "$build" | tail -3
[ "$bstatus" -eq 0 ] || { printf '%s\n' "$build"; echo "FAIL: build"; exit 1; }
chk=".gatecheck_$$.lean"
trap 'rm -f "$chk"' EXIT
{ echo "import $LIB"; for t in $REQUIRED; do echo "#print axioms $t"; done; } > "$chk"
out=$(lake env lean "$chk" 2>&1); status=$?
printf '%s\n' "$out"
[ "$status" -eq 0 ] || { echo "FAIL: axiom report"; exit 1; }
echo "$out" | grep -qE "(^|:)[[:space:]]*error" && { echo "FAIL: Lean reported an error"; exit 1; }
flat=$(printf '%s\n' "$out" | awk '/^'"'"'/{if(buf!="")print buf; buf=$0; next} {buf=buf" "$0} END{if(buf!="")print buf}')
reports=$(printf '%s\n' "$flat" | grep -E "depends on axioms|does not depend on any axioms")
n=0
for t in $REQUIRED; do
  te=$(printf '%s' "$t" | sed 's/[.]/\\./g')
  c=$(printf '%s\n' "$reports" | grep -cE "^'$te' (depends on axioms|does not depend)")
  [ "$c" -eq 1 ] || { echo "FAIL: expected one axiom report for $t, found $c"; exit 1; }
  n=$((n+1))
done
[ "$(printf '%s\n' "$reports" | grep -c .)" -eq "$n" ] || { echo "FAIL: unexpected extra reports"; exit 1; }
printf '%s\n' "$reports" | grep "depends on axioms" | grep -qv '\]' && { echo "FAIL: unterminated axiom list"; exit 1; }
bad=$(printf '%s\n' "$reports" | grep "depends on axioms" | sed 's/.*depends on axioms: *\[//; s/\].*//' \
      | tr ',' '\n' | sed 's/^ *//; s/ *$//' | grep -v '^$' | sort -u \
      | grep -vE '^(propext|Classical\.choice|Quot\.sound)$')
[ -n "$bad" ] && { echo "FAIL: nonstandard axioms: $bad"; exit 1; }
echo "PASS ($n declarations, standard axioms only)"
