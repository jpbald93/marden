import Marden.Basic
import Marden.Tangent
import Marden.Main
import Marden.Unique

/-!
# Layer 15: classical-statement comparison

Layer 15. These definitions and statements were written independently, from textbook statements,
by an AI model that did not see this code; they are reproduced verbatim. Each cov_* theorem proves
(or proves part of) one of them from this development.

Each writer statement `classical_X` is packaged as `def classical_X : Prop := ∀ binders, statement`,
with the binders and body unchanged. The `Marden.l15_*` bridge lemmas restate the Layer-14 bridges
(collinearity, midpoint, centroid, focal sum, side-line parametrisation); the other `l15_*`
declarations are the new proofs needed for the comparison. `cov_Conics4_b_part` proves only the
centre-of-symmetry clause of `classical_Conics4_b`; its area clauses are not proved here. No writer
statement was found to be false.
-/

open Complex Polynomial

namespace Marden
/-- Bridge: collinearity of `a b c` in `ℂ` is the vanishing of `Im ((c - a) / (b - a))`. -/
theorem l15_collinear_iff (a b c : ℂ) :
    Collinear ℝ ({a, b, c} : Set ℂ) ↔ ((c - a) / (b - a)).im = 0 := by
  constructor
  · intro h
    obtain ⟨v, hv⟩ := (collinear_iff_of_mem (p₀ := a) (by simp)).1 h
    obtain ⟨r₁, hr₁⟩ := hv b (by simp)
    obtain ⟨r₂, hr₂⟩ := hv c (by simp)
    rw [vadd_eq_add, Complex.real_smul] at hr₁ hr₂
    have e1 : b - a = (r₁ : ℂ) * v := by rw [hr₁]; ring
    have e2 : c - a = (r₂ : ℂ) * v := by rw [hr₂]; ring
    rcases eq_or_ne ((r₁ : ℂ) * v) 0 with h0 | h0
    · rw [e1, h0, div_zero, Complex.zero_im]
    · have hv0 : v ≠ 0 := right_ne_zero_of_mul h0
      have hr0 : (r₁ : ℂ) ≠ 0 := left_ne_zero_of_mul h0
      rw [e1, e2, mul_div_mul_right _ _ hv0, ← Complex.ofReal_div, Complex.ofReal_im]
  · intro h
    rcases eq_or_ne a b with rfl | hab
    · rw [Set.insert_eq_of_mem (by simp)]; exact collinear_pair ℝ _ _
    · have hba : b - a ≠ 0 := sub_ne_zero.2 hab.symm
      have hc : c ∈ line[ℝ, a, b] := by
        rw [mem_affineSpan_pair_iff_exists_lineMap_eq]
        refine ⟨((c - a) / (b - a)).re, ?_⟩
        rw [AffineMap.lineMap_apply_module']
        have : (((c - a) / (b - a)).re : ℂ) = (c - a) / (b - a) := by
          apply Complex.ext <;> simp [h]
        rw [Complex.real_smul, this, div_mul_cancel₀ _ hba]; ring
      have := collinear_insert_of_mem_affineSpan_pair hc
      rwa [Set.insert_comm c a, Set.pair_comm c b] at this

/-- Bridge: a non-collinear triple has pairwise distinct vertices and satisfies the repository's
non-collinearity condition. -/
theorem l15_of_not_collinear {a b c : ℂ} (h : ¬ Collinear ℝ ({a, b, c} : Set ℂ)) :
    a ≠ b ∧ b ≠ c ∧ c ≠ a ∧ ((c - a) / (b - a)).im ≠ 0 := by
  rw [l15_collinear_iff] at h
  refine ⟨?_, ?_, ?_, h⟩
  · rintro rfl; simp at h
  · rintro rfl
    have hab : b - a ≠ 0 := by rintro h0; rw [h0, div_zero] at h; simp at h
    rw [div_self hab] at h; simp at h
  · rintro rfl; simp at h

theorem l15_midpoint_eq (a b : ℂ) : midpoint ℝ a b = (a + b) / 2 := by
  rw [midpoint_eq_smul_add, Complex.real_smul, invOf_eq_inv]
  push_cast
  ring

theorem l15_centroid_eq (a b c : ℂ) :
    Finset.univ.centroid ℝ ![a, b, c] = (a + b + c) / 3 := by
  rw [Finset.centroid_def,
    Finset.affineCombination_eq_linear_combination _ _ _
      (Finset.sum_centroidWeights_eq_one_of_card_eq_add_one (n := 2) ℝ _ (by simp))]
  simp [Fin.sum_univ_three, Finset.centroidWeights_apply, Complex.real_smul]
  ring

theorem l15_dist_add_dist (f₁ f₂ z : ℂ) : dist z f₁ + dist z f₂ = focalSum f₁ f₂ z := by
  rw [Complex.dist_eq, Complex.dist_eq]; rfl

/-- Bridge: points of the side line `line[ℝ, x, y]` other than the midpoint are exactly
`(x + y)/2 + t (y - x)` with real `t ≠ 0`. -/
theorem l15_strict_on_line {x y f₁ f₂ : ℂ} {S : ℝ}
    (h : ∀ t : ℝ, t ≠ 0 → S < focalSum f₁ f₂ ((x + y) / 2 + t * (y - x))) :
    ∀ p ∈ line[ℝ, x, y], p ≠ midpoint ℝ x y → S < dist p f₁ + dist p f₂ := by
  intro p hp hpm
  obtain ⟨r, rfl⟩ := (mem_affineSpan_pair_iff_exists_lineMap_eq).1 hp
  rw [l15_dist_add_dist]
  have e : AffineMap.lineMap x y r = (x + y) / 2 + ((r - 1 / 2 : ℝ) : ℂ) * (y - x) := by
    rw [AffineMap.lineMap_apply_module', Complex.real_smul]; push_cast; ring
  rw [e]
  refine h _ fun h0 => hpm ?_
  rw [e, h0, l15_midpoint_eq]; simp

theorem l15_strict_of_on_line {x y f₁ f₂ : ℂ} {S : ℝ} (hxy : x ≠ y)
    (h : ∀ p ∈ line[ℝ, x, y], p ≠ midpoint ℝ x y → S < dist p f₁ + dist p f₂) :
    ∀ t : ℝ, t ≠ 0 → S < focalSum f₁ f₂ ((x + y) / 2 + t * (y - x)) := by
  intro t ht
  have hmem : (x + y) / 2 + t * (y - x) ∈ line[ℝ, x, y] := by
    rw [mem_affineSpan_pair_iff_exists_lineMap_eq]
    refine ⟨t + 1 / 2, ?_⟩
    rw [AffineMap.lineMap_apply_module', Complex.real_smul]; push_cast; ring
  rw [← l15_dist_add_dist]
  refine h _ hmem fun he => ?_
  rw [l15_midpoint_eq] at he
  have : (t : ℂ) * (y - x) = 0 := by linear_combination he
  rcases mul_eq_zero.1 this with h1 | h1
  · exact ht (by exact_mod_cast h1)
  · exact hxy (sub_eq_zero.1 h1).symm

/-- **Marden's theorem, Mathlib-only form.** Let `a b c : ℂ` be non-collinear and let `z₁ z₂`
be the roots of `p'` for `p = (X - a)(X - b)(X - c)`. Put `S = dist m z₁ + dist m z₂` for the
midpoint `m` of `ab`. Then the three side midpoints lie on the ellipse
`{z | dist z z₁ + dist z z₂ = S}`; every other point of each side line lies strictly outside the
closed elliptical region (metric tangency at the midpoint); the ellipse is non-degenerate
(`dist z₁ z₂ < S`); and its centre `midpoint z₁ z₂` is the centroid of the triangle. -/
theorem l15_marden {a b c z₁ z₂ : ℂ} (hnc : ¬ Collinear ℝ ({a, b, c} : Set ℂ))
    (hder : derivative ((X - C a) * (X - C b) * (X - C c)) = C 3 * (X - C z₁) * (X - C z₂)) :
    dist (midpoint ℝ b c) z₁ + dist (midpoint ℝ b c) z₂ =
        dist (midpoint ℝ a b) z₁ + dist (midpoint ℝ a b) z₂ ∧
      dist (midpoint ℝ c a) z₁ + dist (midpoint ℝ c a) z₂ =
        dist (midpoint ℝ a b) z₁ + dist (midpoint ℝ a b) z₂ ∧
      (∀ p ∈ line[ℝ, a, b], p ≠ midpoint ℝ a b →
        dist (midpoint ℝ a b) z₁ + dist (midpoint ℝ a b) z₂ < dist p z₁ + dist p z₂) ∧
      (∀ p ∈ line[ℝ, b, c], p ≠ midpoint ℝ b c →
        dist (midpoint ℝ a b) z₁ + dist (midpoint ℝ a b) z₂ < dist p z₁ + dist p z₂) ∧
      (∀ p ∈ line[ℝ, c, a], p ≠ midpoint ℝ c a →
        dist (midpoint ℝ a b) z₁ + dist (midpoint ℝ a b) z₂ < dist p z₁ + dist p z₂) ∧
      dist z₁ z₂ < dist (midpoint ℝ a b) z₁ + dist (midpoint ℝ a b) z₂ ∧
      midpoint ℝ z₁ z₂ = Finset.univ.centroid ℝ ![a, b, c] := by
  obtain ⟨hab, hbc, hca, hnc'⟩ := l15_of_not_collinear hnc
  obtain ⟨⟨h1, h2, h3⟩, t1, t2, t3, hcen⟩ := marden (z₁ := z₁) (z₂ := z₂) hder hab hbc hca hnc'
  have hnd := nondeg_of_midpoints hab hnc' h1 h2 h3
  have hS : dist (midpoint ℝ a b) z₁ + dist (midpoint ℝ a b) z₂ = focalSum z₁ z₂ ((a + b) / 2) := by
    rw [l15_dist_add_dist, l15_midpoint_eq]
  have e2 : ∀ q : ℝ, 2 * (q / 2) = q := fun q => by ring
  simp only [e2] at h2 h3 t1 t2 t3 hnd
  rw [hS]
  refine ⟨by rw [l15_dist_add_dist, l15_midpoint_eq, h2],
    by rw [l15_dist_add_dist, l15_midpoint_eq, h3],
    l15_strict_on_line t1, l15_strict_on_line t2, l15_strict_on_line t3,
    by rw [Complex.dist_eq]; exact hnd, by rw [l15_midpoint_eq, l15_centroid_eq, hcen]⟩

/-- **Uniqueness of the Steiner inellipse, Mathlib-only form.** If an ellipse
`{z | dist z f₁ + dist z f₂ = S}` passes through the three side midpoints of a non-collinear
triangle and each side line meets the closed region `dist · f₁ + dist · f₂ ≤ S` only at its
midpoint, then `{f₁, f₂}` are the roots of `p'` and `S` is the Marden focal sum. -/
theorem l15_steiner_unique {a b c z₁ z₂ f₁ f₂ : ℂ} {S : ℝ}
    (hnc : ¬ Collinear ℝ ({a, b, c} : Set ℂ))
    (hder : derivative ((X - C a) * (X - C b) * (X - C c)) = C 3 * (X - C z₁) * (X - C z₂))
    (hm₁ : dist (midpoint ℝ a b) f₁ + dist (midpoint ℝ a b) f₂ = S)
    (hm₂ : dist (midpoint ℝ b c) f₁ + dist (midpoint ℝ b c) f₂ = S)
    (hm₃ : dist (midpoint ℝ c a) f₁ + dist (midpoint ℝ c a) f₂ = S)
    (ht₁ : ∀ p ∈ line[ℝ, a, b], p ≠ midpoint ℝ a b → S < dist p f₁ + dist p f₂)
    (ht₂ : ∀ p ∈ line[ℝ, b, c], p ≠ midpoint ℝ b c → S < dist p f₁ + dist p f₂)
    (ht₃ : ∀ p ∈ line[ℝ, c, a], p ≠ midpoint ℝ c a → S < dist p f₁ + dist p f₂) :
    ((f₁ = z₁ ∧ f₂ = z₂) ∨ (f₁ = z₂ ∧ f₂ = z₁)) ∧
      S = dist (midpoint ℝ a b) z₁ + dist (midpoint ℝ a b) z₂ := by
  obtain ⟨hab, hbc, hca, hnc'⟩ := l15_of_not_collinear hnc
  rw [l15_dist_add_dist, l15_midpoint_eq] at hm₁ hm₂ hm₃
  have e2 : S = 2 * (S / 2) := by ring
  rw [e2] at hm₁ hm₂ hm₃
  have k₁ := l15_strict_of_on_line hab ht₁
  have k₂ := l15_strict_of_on_line hbc ht₂
  have k₃ := l15_strict_of_on_line hca ht₃
  rw [e2] at k₁ k₂ k₃
  obtain ⟨hf, hA⟩ := steiner_unique hder hab hbc hca hnc' hm₁ hm₂ hm₃ k₁ k₂ k₃
  refine ⟨hf, ?_⟩
  rw [l15_dist_add_dist, l15_midpoint_eq]
  linarith

end Marden

open EuclideanGeometry InnerProductGeometry Real Polynomial

noncomputable section

namespace Marden.Classical

/-! ### Writer definitions (verbatim) -/

def IsEllipseWithFoci (E : Set ℂ) (f₁ f₂ : ℂ) : Prop :=
  ∃ r : ℝ, dist f₁ f₂ < r ∧ E = {z | dist z f₁ + dist z f₂ = r}

def IsEllipse (E : Set ℂ) : Prop := ∃ f₁ f₂, IsEllipseWithFoci E f₁ f₂

def IsInscribedEllipse (a b c : ℂ) (E : Set ℂ) : Prop :=
  IsEllipse E ∧ E ⊆ convexHull ℝ {a, b, c} ∧
  (∃ t, E ∩ (line[ℝ, a, b] : Set ℂ) = {t}) ∧
  (∃ t, E ∩ (line[ℝ, b, c] : Set ℂ) = {t}) ∧
  (∃ t, E ∩ (line[ℝ, c, a] : Set ℂ) = {t})

def IsSteinerInellipse (a b c : ℂ) (E : Set ℂ) : Prop :=
  IsEllipse E ∧ E ⊆ convexHull ℝ {a, b, c} ∧
  E ∩ (line[ℝ, a, b] : Set ℂ) = {midpoint ℝ a b} ∧
  E ∩ (line[ℝ, b, c] : Set ℂ) = {midpoint ℝ b c} ∧
  E ∩ (line[ℝ, c, a] : Set ℂ) = {midpoint ℝ c a}

/-! ### Writer statements (verbatim, packaged as `Prop`s) -/

def classical_Conics4_a : Prop := ∀ (a b c : ℂ) (habc : ¬ Collinear ℝ ({a, b, c} : Set ℂ)),
    ∃! E : Set ℂ, IsSteinerInellipse a b c E

def classical_Conics4_b : Prop := ∀ (a b c : ℂ) (habc : ¬ Collinear ℝ ({a, b, c} : Set ℂ))
    (E : Set ℂ) (hE : IsSteinerInellipse a b c E),
    (∀ z ∈ E, 2 * ((a + b + c) / 3) - z ∈ E) ∧
    MeasureTheory.volume (convexHull ℝ E) =
      ENNReal.ofReal (π / (3 * √3)) * MeasureTheory.volume (convexHull ℝ {a, b, c}) ∧
    (∀ E', IsInscribedEllipse a b c E' → E' ≠ E →
      MeasureTheory.volume (convexHull ℝ E') < MeasureTheory.volume (convexHull ℝ E))

def classical_Conics5 : Prop := ∀ (a b c : ℂ) (habc : ¬ Collinear ℝ ({a, b, c} : Set ℂ))
    (E : Set ℂ) (hE : IsSteinerInellipse a b c E) (f₁ f₂ : ℂ)
    (hf : IsEllipseWithFoci E f₁ f₂),
    (derivative ((X - C a) * (X - C b) * (X - C c))).roots = {f₁, f₂} ∧
    f₁ + f₂ = 2 * (a + b + c) / 3 ∧ f₁ * f₂ = (a * b + b * c + c * a) / 3

def classical_Conics5_double_root : Prop := ∀ (a b c : ℂ)
    (habc : ¬ Collinear ℝ ({a, b, c} : Set ℂ)) (E : Set ℂ) (hE : IsSteinerInellipse a b c E),
    (∀ z, (derivative ((X - C a) * (X - C b) * (X - C c))).roots = {z, z} →
      ∃ ρ > 0, E = Metric.sphere z ρ) ∧
    ((∃ z, (derivative ((X - C a) * (X - C b) * (X - C c))).roots = {z, z}) ↔
      (dist a b = dist b c ∧ dist b c = dist c a))

/-! ### Comparer lemmas (NEW) -/

open Marden

/-- Focal sum along a line through `m` in direction `d ≠ 0`. -/
lemma l15_focal_line_cont (m d f₁ f₂ : ℂ) :
    Continuous (fun t : ℝ => dist (m + t * d) f₁ + dist (m + t * d) f₂) := by
  fun_prop

lemma l15_focal_line_ge (m d f₁ f₂ : ℂ) (t : ℝ) :
    2 * |t| * ‖d‖ - (dist m f₁ + dist m f₂) ≤ dist (m + t * d) f₁ + dist (m + t * d) f₂ := by
  have h1 : ‖(t : ℂ) * d‖ ≤ dist (m + t * d) f₁ + dist m f₁ := by
    rw [Complex.dist_eq, Complex.dist_eq]
    calc ‖(t : ℂ) * d‖ = ‖(m + t * d - f₁) - (m - f₁)‖ := by ring_nf
      _ ≤ _ := norm_sub_le _ _
  have h2 : ‖(t : ℂ) * d‖ ≤ dist (m + t * d) f₂ + dist m f₂ := by
    rw [Complex.dist_eq, Complex.dist_eq]
    calc ‖(t : ℂ) * d‖ = ‖(m + t * d - f₂) - (m - f₂)‖ := by ring_nf
      _ ≤ _ := norm_sub_le _ _
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs] at h1 h2
  linarith

/-- IVT: if the focal sum is `r` at `t = 0` and `< r` at some `t₀ > 0`, it equals `r` at some
`t₁ > 0`. -/
lemma l15_ivt_pos (m d f₁ f₂ : ℂ) (hd : d ≠ 0) (r t₀ : ℝ) (ht₀ : 0 < t₀)
    (hlt : dist (m + t₀ * d) f₁ + dist (m + t₀ * d) f₂ < r) :
    ∃ t₁ : ℝ, 0 < t₁ ∧ dist (m + t₁ * d) f₁ + dist (m + t₁ * d) f₂ = r := by
  set g := fun t : ℝ => dist (m + t * d) f₁ + dist (m + t * d) f₂ with hg
  have hdn : 0 < ‖d‖ := norm_pos_iff.2 hd
  set A := dist m f₁ + dist m f₂
  have hA : 0 ≤ A := by positivity
  set T := t₀ + (|r| + A) / (2 * ‖d‖) + 1
  have hT : t₀ ≤ T := by
    have : 0 ≤ (|r| + A) / (2 * ‖d‖) := by positivity
    simp only [T]; linarith
  have hgT : r ≤ g T := by
    have h := l15_focal_line_ge m d f₁ f₂ T
    have hT0 : 0 < T := by linarith
    rw [abs_of_pos hT0] at h
    have : 2 * T * ‖d‖ ≥ |r| + A + 2 * ‖d‖ := by
      have e : 2 * T * ‖d‖ = 2 * t₀ * ‖d‖ + (|r| + A) + 2 * ‖d‖ := by
        simp only [T]; field_simp
      rw [e]; nlinarith
    have := le_abs_self r
    show r ≤ dist (m + T * d) f₁ + dist (m + T * d) f₂
    linarith
  obtain ⟨t₁, ht₁, he⟩ := intermediate_value_Icc hT (l15_focal_line_cont m d f₁ f₂).continuousOn
    ⟨hlt.le, hgT⟩
  exact ⟨t₁, lt_of_lt_of_le ht₀ ht₁.1, he⟩

/-- If a line through `m` meets the ellipse `{sum = r}` only at `m`, every other point of the
line has focal sum `> r`. -/
lemma l15_strict_of_unique (m d f₁ f₂ : ℂ) (hd : d ≠ 0) (r : ℝ)
    (hm : dist m f₁ + dist m f₂ = r)
    (huniq : ∀ t : ℝ, dist (m + t * d) f₁ + dist (m + t * d) f₂ = r → t = 0) :
    ∀ t : ℝ, t ≠ 0 → r < dist (m + t * d) f₁ + dist (m + t * d) f₂ := by
  intro t ht
  by_contra hle
  push_neg at hle
  rcases hle.lt_or_eq with hlt | heq
  · rcases lt_or_gt_of_ne ht with hneg | hpos
    · obtain ⟨t₁, ht₁, he⟩ := l15_ivt_pos m (-d) f₁ f₂ (neg_ne_zero.2 hd) r (-t) (by linarith)
        (by rw [show ((-t : ℝ) : ℂ) * -d = (t : ℂ) * d by push_cast; ring]; exact hlt)
      have e1 : ((-t₁ : ℝ) : ℂ) * d = (t₁ : ℂ) * -d := by push_cast; ring
      have := huniq (-t₁) (by rw [e1]; exact he)
      linarith
    · obtain ⟨t₁, ht₁, he⟩ := l15_ivt_pos m d f₁ f₂ hd r t hpos hlt
      have := huniq t₁ he; linarith
  · exact ht (huniq t heq)

/-- From the writer's "`E ∩ line[x,y] = {midpoint}`" for the focal ellipse, the repository's strict
tangency hypothesis. -/
lemma l15_strict_of_inter {x y f₁ f₂ : ℂ} {r : ℝ} (hxy : x ≠ y)
    (h : {z | dist z f₁ + dist z f₂ = r} ∩ (line[ℝ, x, y] : Set ℂ) = {midpoint ℝ x y}) :
    ∀ p ∈ line[ℝ, x, y], p ≠ midpoint ℝ x y → r < dist p f₁ + dist p f₂ := by
  have hd : y - x ≠ 0 := sub_ne_zero.2 hxy.symm
  have hmem : ∀ t : ℝ, (x + y) / 2 + t * (y - x) ∈ line[ℝ, x, y] := by
    intro t
    rw [mem_affineSpan_pair_iff_exists_lineMap_eq]
    refine ⟨t + 1 / 2, ?_⟩
    rw [AffineMap.lineMap_apply_module', Complex.real_smul]; push_cast; ring
  have hmid : midpoint ℝ x y ∈ ({midpoint ℝ x y} : Set ℂ) := rfl
  rw [← h] at hmid
  have hm : dist ((x + y) / 2) f₁ + dist ((x + y) / 2) f₂ = r := by
    have := hmid.1; rwa [l15_midpoint_eq] at this
  have huniq : ∀ t : ℝ, dist ((x + y) / 2 + t * (y - x)) f₁ + dist ((x + y) / 2 + t * (y - x)) f₂
      = r → t = 0 := by
    intro t ht
    have h2 : (x + y) / 2 + t * (y - x) ∈ ({midpoint ℝ x y} : Set ℂ) := by
      rw [← h]; exact ⟨ht, hmem t⟩
    rw [Set.mem_singleton_iff, l15_midpoint_eq] at h2
    have : (t : ℂ) * (y - x) = 0 := by linear_combination h2
    rcases mul_eq_zero.1 this with h1 | h1
    · exact_mod_cast h1
    · exact absurd h1 hd
  have key := l15_strict_of_unique ((x + y) / 2) (y - x) f₁ f₂ hd r hm huniq
  have key' : ∀ t : ℝ, t ≠ 0 → r < focalSum f₁ f₂ ((x + y) / 2 + t * (y - x)) := by
    intro t ht; rw [← l15_dist_add_dist]; exact key t ht
  exact l15_strict_on_line key'

/-- **Classification**: a writer-Steiner inellipse in focal form has the Marden foci and the
Marden focal sum. -/
lemma l15_steiner_foci {a b c z₁ z₂ f₁ f₂ : ℂ} {r : ℝ}
    (hnc : ¬ Collinear ℝ ({a, b, c} : Set ℂ))
    (hder : derivative ((X - C a) * (X - C b) * (X - C c)) = C 3 * (X - C z₁) * (X - C z₂))
    (E : Set ℂ) (hE : E = {z | dist z f₁ + dist z f₂ = r})
    (hS : IsSteinerInellipse a b c E) :
    ((f₁ = z₁ ∧ f₂ = z₂) ∨ (f₁ = z₂ ∧ f₂ = z₁)) ∧
      r = dist (midpoint ℝ a b) z₁ + dist (midpoint ℝ a b) z₂ := by
  obtain ⟨hab, hbc, hca, -⟩ := l15_of_not_collinear hnc
  obtain ⟨-, -, h1, h2, h3⟩ := hS
  subst hE
  have m1 : midpoint ℝ a b ∈ ({midpoint ℝ a b} : Set ℂ) := rfl
  have m2 : midpoint ℝ b c ∈ ({midpoint ℝ b c} : Set ℂ) := rfl
  have m3 : midpoint ℝ c a ∈ ({midpoint ℝ c a} : Set ℂ) := rfl
  rw [← h1] at m1; rw [← h2] at m2; rw [← h3] at m3
  exact l15_steiner_unique hnc hder m1.1 m2.1 m3.1 (l15_strict_of_inter hab h1)
    (l15_strict_of_inter hbc h2) (l15_strict_of_inter hca h3)

/-! #### The Marden ellipse lies in the closed triangle -/

/-- Signed area form. -/
def l15_cross (p q z : ℂ) : ℝ := (q - p).re * (z - p).im - (q - p).im * (z - p).re

lemma l15_mem_line_of_cross {x y p : ℂ} (hxy : x ≠ y) (h : l15_cross x y p = 0) :
    p ∈ line[ℝ, x, y] := by
  have hd : y - x ≠ 0 := sub_ne_zero.2 hxy.symm
  have hn : Complex.normSq (y - x) ≠ 0 := (Complex.normSq_pos.2 hd).ne'
  rw [mem_affineSpan_pair_iff_exists_lineMap_eq]
  refine ⟨((p - x) / (y - x)).re, ?_⟩
  rw [AffineMap.lineMap_apply_module', Complex.real_smul]
  have him : ((p - x) / (y - x)).im = 0 := by
    rw [Complex.div_im]
    unfold l15_cross at h
    rw [div_sub_div_same, div_eq_zero_iff]; left
    simp only [Complex.sub_re, Complex.sub_im] at h ⊢
    linarith
  have : (((p - x) / (y - x)).re : ℂ) = (p - x) / (y - x) := by
    apply Complex.ext <;> simp [him]
  rw [this, div_mul_cancel₀ _ hd]; ring

lemma l15_dist_convex (g z f : ℂ) (θ : ℝ) (h0 : 0 ≤ θ) (h1 : θ ≤ 1) :
    dist (g + θ * (z - g)) f ≤ (1 - θ) * dist g f + θ * dist z f := by
  rw [Complex.dist_eq, Complex.dist_eq, Complex.dist_eq]
  have e : g + θ * (z - g) - f = ((1 - θ : ℝ) : ℂ) * (g - f) + (θ : ℂ) * (z - f) := by
    push_cast; ring
  rw [e]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_of_nonneg (by linarith), abs_of_nonneg h0]

/-- Half-plane lemma: a convex focal region `sum ≤ S` that contains `g` strictly inside, and meets
the line `xy` only in points with `sum ≥ S`, lies in the closed half-plane of `g`. -/
lemma l15_halfplane {x y g f₁ f₂ : ℂ} {S : ℝ} (hxy : x ≠ y)
    (hg : dist g f₁ + dist g f₂ < S) (hgs : l15_cross x y g ≠ 0)
    (hline : ∀ p ∈ line[ℝ, x, y], S ≤ dist p f₁ + dist p f₂)
    (z : ℂ) (hz : dist z f₁ + dist z f₂ ≤ S) : 0 ≤ l15_cross x y z * l15_cross x y g := by
  by_contra hneg
  push_neg at hneg
  set cg := l15_cross x y g
  set cz := l15_cross x y z
  have hcg2 : 0 < cg ^ 2 := by positivity
  set θ := cg ^ 2 / (cg ^ 2 - cz * cg)
  have hden : 0 < cg ^ 2 - cz * cg := by linarith
  have hθ0 : 0 ≤ θ := div_nonneg hcg2.le hden.le
  have hθ1 : θ < 1 := by rw [div_lt_one hden]; linarith
  set p := g + θ * (z - g)
  have hcp : l15_cross x y p = 0 := by
    have e : l15_cross x y p = (1 - θ) * l15_cross x y g + θ * l15_cross x y z := by
      simp only [p, l15_cross, Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
        Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
      ring
    have hθe : θ * (cg ^ 2 - cz * cg) = cg ^ 2 := div_mul_cancel₀ _ hden.ne'
    rw [e]
    show (1 - θ) * cg + θ * cz = 0
    have hc : cg * ((1 - θ) * cg + θ * cz) = 0 := by linear_combination -hθe
    rcases mul_eq_zero.1 hc with h | h
    · exact absurd h hgs
    · exact h
  have hp := hline p (l15_mem_line_of_cross hxy hcp)
  have c1 := l15_dist_convex g z f₁ θ hθ0 hθ1.le
  have c2 := l15_dist_convex g z f₂ θ hθ0 hθ1.le
  have : dist p f₁ + dist p f₂ < S := by
    have h3 : (1 - θ) * (dist g f₁ + dist g f₂) + θ * (dist z f₁ + dist z f₂) < S := by
      have : (1 - θ) * (dist g f₁ + dist g f₂) < (1 - θ) * S :=
        mul_lt_mul_of_pos_left hg (by linarith)
      nlinarith
    linarith
  linarith

lemma l15_cross_centroid (x y w : ℂ) :
    l15_cross x y ((x + y + w) / 3) = l15_cross x y w / 3 := by
  simp only [l15_cross, Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
    Complex.div_re, Complex.div_im]
  norm_num; ring

lemma l15_mem_hull {a b c z : ℂ} (hD : l15_cross a b c ≠ 0)
    (h1 : 0 ≤ l15_cross a b z * l15_cross a b c)
    (h2 : 0 ≤ l15_cross b c z * l15_cross b c a)
    (h3 : 0 ≤ l15_cross c a z * l15_cross c a b) : z ∈ convexHull ℝ ({a, b, c} : Set ℂ) := by
  set D := l15_cross a b c
  have eb : l15_cross b c a = D := by simp only [D, l15_cross, Complex.sub_re, Complex.sub_im]; ring
  have ec : l15_cross c a b = D := by simp only [D, l15_cross, Complex.sub_re, Complex.sub_im]; ring
  rw [eb] at h2; rw [ec] at h3
  set wa := l15_cross b c z / D
  set wb := l15_cross c a z / D
  set wc := l15_cross a b z / D
  have hD2 : 0 < D * D := mul_self_pos.2 hD
  have pos : ∀ q : ℝ, 0 ≤ q * D → 0 ≤ q / D := by
    intro q hq
    have : q / D = q * D / (D * D) := by field_simp
    rw [this]; exact div_nonneg hq hD2.le
  have hsum : wa + wb + wc = 1 := by
    simp only [wa, wb, wc]
    rw [← add_div, ← add_div, div_eq_one_iff_eq hD]
    simp only [D, l15_cross, Complex.sub_re, Complex.sub_im]; ring
  have hz : z = wa • a + wb • b + wc • c := by
    apply Complex.ext <;>
    · simp only [wa, wb, wc, Complex.add_re, Complex.add_im, Complex.real_smul,
        Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
      field_simp
      simp only [D, l15_cross, Complex.sub_re, Complex.sub_im]; ring
  have hcv := convex_convexHull ℝ ({a, b, c} : Set ℂ)
  have ha : a ∈ convexHull ℝ ({a, b, c} : Set ℂ) := subset_convexHull ℝ _ (by simp)
  have hb : b ∈ convexHull ℝ ({a, b, c} : Set ℂ) := subset_convexHull ℝ _ (by simp)
  have hc : c ∈ convexHull ℝ ({a, b, c} : Set ℂ) := subset_convexHull ℝ _ (by simp)
  have := hcv.sum_mem (t := Finset.univ) (w := ![wa, wb, wc]) (z := ![a, b, c])
    (by intro i _; fin_cases i
        · exact pos _ h2
        · exact pos _ h3
        · exact pos _ h1)
    (by simp [Fin.sum_univ_three, hsum])
    (by intro i _; fin_cases i <;> simp [ha, hb, hc])
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at this
  rw [hz]; exact this

lemma l15_cross_ne {a b c : ℂ} (hnc : ¬ Collinear ℝ ({a, b, c} : Set ℂ)) : l15_cross a b c ≠ 0 := by
  intro h
  obtain ⟨hab, -, -, -⟩ := l15_of_not_collinear hnc
  apply hnc
  have hc := l15_mem_line_of_cross hab h
  have := collinear_insert_of_mem_affineSpan_pair hc
  rwa [Set.insert_comm c a, Set.pair_comm c b] at this

lemma l15_midpoint_mem (x y : ℂ) : midpoint ℝ x y ∈ line[ℝ, x, y] :=
  AffineMap.lineMap_mem_affineSpan_pair _ _ _

lemma l15_cross_swap (x y z : ℂ) : l15_cross y x z = -l15_cross x y z := by
  simp only [l15_cross, Complex.sub_re, Complex.sub_im]; ring

/-- The Marden ellipse is a Steiner inellipse in the writer's sense (incl. lying in the closed
triangle — NEW: the repository does not state containment). -/
lemma l15_marden_steiner {a b c z₁ z₂ : ℂ} (hnc : ¬ Collinear ℝ ({a, b, c} : Set ℂ))
    (hder : derivative ((X - C a) * (X - C b) * (X - C c)) = C 3 * (X - C z₁) * (X - C z₂)) :
    IsSteinerInellipse a b c
      {z | dist z z₁ + dist z z₂ = dist (midpoint ℝ a b) z₁ + dist (midpoint ℝ a b) z₂} := by
  obtain ⟨hab, hbc, hca, -⟩ := l15_of_not_collinear hnc
  obtain ⟨e2, e3, t1, t2, t3, hnd, hcen⟩ := l15_marden hnc hder
  set S := dist (midpoint ℝ a b) z₁ + dist (midpoint ℝ a b) z₂ with hSdef
  have inter : ∀ x y : ℂ, (∀ p ∈ line[ℝ, x, y], p ≠ midpoint ℝ x y → S < dist p z₁ + dist p z₂) →
      dist (midpoint ℝ x y) z₁ + dist (midpoint ℝ x y) z₂ = S →
      {z | dist z z₁ + dist z z₂ = S} ∩ (line[ℝ, x, y] : Set ℂ) = {midpoint ℝ x y} := by
    intro x y ht hm
    ext p
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_singleton_iff, SetLike.mem_coe]
    constructor
    · rintro ⟨hp, hl⟩
      by_contra hne
      have := ht p hl hne; linarith
    · rintro rfl
      exact ⟨hm, l15_midpoint_mem x y⟩
  have le_on : ∀ x y : ℂ, (∀ p ∈ line[ℝ, x, y], p ≠ midpoint ℝ x y → S < dist p z₁ + dist p z₂) →
      dist (midpoint ℝ x y) z₁ + dist (midpoint ℝ x y) z₂ = S →
      ∀ p ∈ line[ℝ, x, y], S ≤ dist p z₁ + dist p z₂ := by
    intro x y ht hm p hp
    by_cases h : p = midpoint ℝ x y
    · rw [h, hm]
    · exact (ht p hp h).le
  set g := (a + b + c) / 3
  have hg : dist g z₁ + dist g z₂ < S := by
    have hgm : g = midpoint ℝ z₁ z₂ := by rw [hcen, l15_centroid_eq]
    rw [hgm, dist_midpoint_left (𝕜 := ℝ), dist_midpoint_right (𝕜 := ℝ)]
    have : ‖(2 : ℝ)‖⁻¹ * dist z₁ z₂ + ‖(2 : ℝ)‖⁻¹ * dist z₁ z₂ = dist z₁ z₂ := by
      rw [Real.norm_two]; ring
    linarith
  have hD := l15_cross_ne hnc
  have g1 : l15_cross a b g = l15_cross a b c / 3 := l15_cross_centroid a b c
  have g2 : l15_cross b c g = l15_cross b c a / 3 := by
    rw [show g = (b + c + a) / 3 by simp only [g]; ring]; exact l15_cross_centroid b c a
  have g3 : l15_cross c a g = l15_cross c a b / 3 := by
    rw [show g = (c + a + b) / 3 by simp only [g]; ring]; exact l15_cross_centroid c a b
  have eb : l15_cross b c a = l15_cross a b c := by
    simp only [l15_cross, Complex.sub_re, Complex.sub_im]; ring
  have ec : l15_cross c a b = l15_cross a b c := by
    simp only [l15_cross, Complex.sub_re, Complex.sub_im]; ring
  refine ⟨⟨z₁, z₂, S, hnd, rfl⟩, ?_, inter a b t1 rfl, inter b c t2 e2, inter c a t3 e3⟩
  intro z hz
  have hz' : dist z z₁ + dist z z₂ ≤ S := le_of_eq hz
  have k1 := l15_halfplane hab hg (by rw [g1]; exact div_ne_zero hD three_ne_zero)
    (le_on a b t1 rfl) z hz'
  have k2 := l15_halfplane hbc hg (by rw [g2, eb]; exact div_ne_zero hD three_ne_zero)
    (le_on b c t2 e2) z hz'
  have k3 := l15_halfplane hca hg (by rw [g3, ec]; exact div_ne_zero hD three_ne_zero)
    (le_on c a t3 e3) z hz'
  rw [g1] at k1; rw [g2] at k2; rw [g3] at k3
  apply l15_mem_hull hD <;> nlinarith

lemma l15_roots {a b c z₁ z₂ : ℂ}
    (hder : derivative ((X - C a) * (X - C b) * (X - C c)) = C 3 * (X - C z₁) * (X - C z₂)) :
    (derivative ((X - C a) * (X - C b) * (X - C c))).roots = {z₁, z₂} := by
  rw [hder, mul_assoc, roots_C_mul _ (by norm_num), roots_mul (mul_ne_zero (X_sub_C_ne_zero _)
    (X_sub_C_ne_zero _)), roots_X_sub_C, roots_X_sub_C]
  rfl

lemma l15_crit (a b c : ℂ) : ∃ z₁ z₂ : ℂ,
    derivative ((X - C a) * (X - C b) * (X - C c)) = C 3 * (X - C z₁) * (X - C z₂) :=
  exists_critical_points a b c

/-! ### Comparison theorems -/

theorem cov_Conics4_a : classical_Conics4_a := by
  intro a b c hnc
  obtain ⟨z₁, z₂, hder⟩ := l15_crit a b c
  refine ⟨_, l15_marden_steiner hnc hder, fun E hE => ?_⟩
  obtain ⟨f₁, f₂, r, -, hEr⟩ := hE.1
  obtain ⟨hf, hr⟩ := l15_steiner_foci hnc hder E hEr hE
  rw [hEr, hr]
  rcases hf with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rfl
  · ext z; simp only [Set.mem_setOf_eq]; constructor <;> intro h <;> linarith

/-- Strongest part of Conics4(b): the centre-of-symmetry clause. -/
theorem cov_Conics4_b_part (a b c : ℂ) (habc : ¬ Collinear ℝ ({a, b, c} : Set ℂ))
    (E : Set ℂ) (hE : IsSteinerInellipse a b c E) :
    ∀ z ∈ E, 2 * ((a + b + c) / 3) - z ∈ E := by
  obtain ⟨z₁, z₂, hder⟩ := l15_crit a b c
  obtain ⟨f₁, f₂, r, -, hEr⟩ := hE.1
  obtain ⟨hf, -⟩ := l15_steiner_foci habc hder E hEr hE
  obtain ⟨hs, -⟩ := vieta (a := a) (b := b) (c := c) hder
  have hsum : f₁ + f₂ = 2 * ((a + b + c) / 3) := by
    rcases hf with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [hs]; ring
    · rw [add_comm, hs]; ring
  intro z hz
  rw [hEr] at hz ⊢
  simp only [Set.mem_setOf_eq] at hz ⊢
  rw [← hsum, Complex.dist_eq, Complex.dist_eq, show f₁ + f₂ - z - f₁ = -(z - f₂) by ring,
    show f₁ + f₂ - z - f₂ = -(z - f₁) by ring, norm_neg, norm_neg, ← Complex.dist_eq,
    ← Complex.dist_eq]
  linarith

theorem cov_Conics5 : classical_Conics5 := by
  intro a b c hnc E hE f₁ f₂ hf
  obtain ⟨z₁, z₂, hder⟩ := l15_crit a b c
  obtain ⟨r, -, hEr⟩ := hf
  obtain ⟨hff, -⟩ := l15_steiner_foci hnc hder E hEr hE
  obtain ⟨hs, hp⟩ := vieta (a := a) (b := b) (c := c) hder
  rw [l15_roots hder]
  rcases hff with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨rfl, hs, hp⟩
  · exact ⟨Multiset.pair_comm _ _, by rw [add_comm]; exact hs, by rw [mul_comm]; exact hp⟩

/-- Algebra: equilateral ⇔ `u² - u v + v² = 0` (u = b - a, v = c - a), for `u ≠ 0`. -/
lemma l15_equilateral_iff (u v : ℂ) (hu : u ≠ 0) :
    u ^ 2 - u * v + v ^ 2 = 0 ↔ (‖u‖ = ‖v - u‖ ∧ ‖v - u‖ = ‖v‖) := by
  constructor
  · intro h
    obtain ⟨w, hv⟩ : ∃ w, v = w * u := ⟨v / u, by field_simp⟩
    rw [hv] at h
    have hw : w ^ 2 - w + 1 = 0 := by
      have : u ^ 2 * (w ^ 2 - w + 1) = 0 := by linear_combination h
      rcases mul_eq_zero.1 this with h' | h'
      · exact absurd (pow_eq_zero_iff two_ne_zero |>.1 h') hu
      · exact h'
    have hw3 : w ^ 3 = -1 := by linear_combination (w + 1) * hw
    have hn3 : ‖w‖ ^ 3 = 1 := by rw [← norm_pow, hw3, norm_neg, norm_one]
    have hn : ‖w‖ = 1 := (pow_eq_one_iff_of_nonneg (norm_nonneg _) three_ne_zero).1 hn3
    have h1w : ‖w - 1‖ = 1 := by
      rw [show w - 1 = w ^ 2 by linear_combination (-1 : ℂ) * hw, norm_pow, hn, one_pow]
    rw [hv, show w * u - u = (w - 1) * u by ring, norm_mul, norm_mul, hn, h1w]
    simp
  · rintro ⟨h1, h2⟩
    have n1 : u * (starRingEnd ℂ) u = v * (starRingEnd ℂ) v := by
      rw [Complex.mul_conj, Complex.mul_conj, Complex.normSq_eq_norm_sq,
        Complex.normSq_eq_norm_sq, h1, h2]
    have n2 : (u - v) * ((starRingEnd ℂ) u - (starRingEnd ℂ) v) = u * (starRingEnd ℂ) u := by
      rw [← map_sub, Complex.mul_conj, Complex.mul_conj, Complex.normSq_eq_norm_sq,
        Complex.normSq_eq_norm_sq, norm_sub_rev, h1]
    have hcu : (starRingEnd ℂ) u ≠ 0 := by simpa using hu
    have : (starRingEnd ℂ) u * (u ^ 2 - u * v + v ^ 2) = 0 := by
      linear_combination (-v) * n2 + (u - v) * n1
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h hcu
    · exact h

theorem cov_Conics5_double_root : classical_Conics5_double_root := by
  intro a b c hnc E hE
  obtain ⟨hab, -, -, -⟩ := l15_of_not_collinear hnc
  obtain ⟨z₁, z₂, hder⟩ := l15_crit a b c
  have hroots := l15_roots hder
  obtain ⟨hs, hp⟩ := vieta (a := a) (b := b) (c := c) hder
  have pair : ∀ z, (derivative ((X - C a) * (X - C b) * (X - C c))).roots = {z, z} ↔
      (z₁ = z ∧ z₂ = z) := by
    intro z
    rw [hroots]
    constructor
    · intro h
      have m1 : z₁ ∈ ({z₁, z₂} : Multiset ℂ) := Multiset.mem_cons_self _ _
      have m2 : z₂ ∈ ({z₁, z₂} : Multiset ℂ) := by simp
      rw [h] at m1 m2
      simp at m1 m2
      exact ⟨m1, m2⟩
    · rintro ⟨rfl, rfl⟩; rfl
  refine ⟨fun z hz => ?_, ?_⟩
  · obtain ⟨h1, h2⟩ := (pair z).1 hz
    obtain ⟨f₁, f₂, r, hr, hEr⟩ := hE.1
    obtain ⟨hf, -⟩ := l15_steiner_foci hnc hder E hEr hE
    rw [h1, h2] at hf
    have hf' : f₁ = z ∧ f₂ = z := by rcases hf with h | h <;> exact h
    obtain ⟨rfl, rfl⟩ := hf'
    refine ⟨r / 2, by rw [dist_self] at hr; linarith, ?_⟩
    rw [hEr]; ext w
    simp only [Set.mem_setOf_eq, Metric.mem_sphere]
    constructor <;> intro h <;> linarith
  · have disc : (z₁ - z₂) ^ 2 = 4 / 9 * ((b - a) ^ 2 - (b - a) * (c - a) + (c - a) ^ 2) := by
      linear_combination (z₁ + z₂ + 2 * (a + b + c) / 3) * hs - 4 * hp
    have hu : b - a ≠ 0 := sub_ne_zero.2 hab.symm
    rw [show (∃ z, (derivative ((X - C a) * (X - C b) * (X - C c))).roots = {z, z}) ↔ z₁ = z₂ by
      constructor
      · rintro ⟨z, hz⟩; obtain ⟨h1, h2⟩ := (pair z).1 hz; rw [h1, h2]
      · intro h; exact ⟨z₁, (pair z₁).2 ⟨rfl, h.symm⟩⟩]
    have e : z₁ = z₂ ↔ (b - a) ^ 2 - (b - a) * (c - a) + (c - a) ^ 2 = 0 := by
      rw [← sub_eq_zero, ← pow_eq_zero_iff two_ne_zero, disc]
      constructor
      · intro h; linear_combination (9 / 4 : ℂ) * h
      · intro h; rw [h, mul_zero]
    rw [e, l15_equilateral_iff _ _ hu, Complex.dist_eq, Complex.dist_eq, Complex.dist_eq,
      show c - a - (b - a) = c - b by ring, norm_sub_rev a b, norm_sub_rev b c]

end Marden.Classical
