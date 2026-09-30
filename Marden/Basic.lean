import Mathlib

/-!
# Marden's theorem: focal/midpoint property

Let `p(z) = (z-a)(z-b)(z-c)`. The critical points `z₁, z₂` of `p` are characterised
by Vieta: `z₁ + z₂ = 2(a+b+c)/3`, `z₁ z₂ = (ab+bc+ca)/3`
(since `p' = 3z² - 2(a+b+c)z + (ab+bc+ca)`).

We show the three side midpoints have the same focal sum
`‖m - z₁‖ + ‖m - z₂‖`, so they lie on one ellipse with foci `z₁, z₂`.
-/

open Complex

namespace Marden

/-- Sum of distances from `z` to the two foci `f₁ f₂`. -/
noncomputable def focalSum (f₁ f₂ z : ℂ) : ℝ := ‖z - f₁‖ + ‖z - f₂‖

variable {a b c z₁ z₂ : ℂ}

/-- Key identity: `(m - z₁)(m - z₂) = p'(m)/3 = -(b-a)²/12` for `m = (a+b)/2`. -/
theorem midpoint_mul (hs : z₁ + z₂ = 2 * (a + b + c) / 3)
    (hp : z₁ * z₂ = (a * b + b * c + c * a) / 3) :
    ((a + b) / 2 - z₁) * ((a + b) / 2 - z₂) = -(b - a) ^ 2 / 12 := by
  linear_combination (-(a + b) / 2) * hs + hp

lemma sym_norms (a b c : ℂ) :
    ‖(a + b - 2 * c) / 3‖ ^ 2 + ‖b - a‖ ^ 2 / 3
      = 2 * (‖a - b‖ ^ 2 + ‖b - c‖ ^ 2 + ‖c - a‖ ^ 2) / 9 := by
  simp only [Complex.sq_norm, Complex.normSq_apply]
  simp
  ring

/-- The squared focal sum at the midpoint of `ab` is a symmetric expression. -/
theorem focalSum_midpoint_sq (hs : z₁ + z₂ = 2 * (a + b + c) / 3)
    (hp : z₁ * z₂ = (a * b + b * c + c * a) / 3) :
    focalSum z₁ z₂ ((a + b) / 2) ^ 2
      = ‖z₁ - z₂‖ ^ 2 / 2 + (‖a - b‖ ^ 2 + ‖b - c‖ ^ 2 + ‖c - a‖ ^ 2) / 9 := by
  have hm := midpoint_mul hs hp
  have hprod : ‖(a + b) / 2 - z₁‖ * ‖(a + b) / 2 - z₂‖ = ‖b - a‖ ^ 2 / 12 := by
    rw [← norm_mul, hm, norm_div, norm_neg, norm_pow]
    norm_num
  have hpar := parallelogram_law_with_norm ℝ ((a + b) / 2 - z₁) ((a + b) / 2 - z₂)
  have h1 : (a + b) / 2 - z₁ + ((a + b) / 2 - z₂) = (a + b - 2 * c) / 3 := by
    linear_combination (-1 : ℂ) * hs
  have h2 : (a + b) / 2 - z₁ - ((a + b) / 2 - z₂) = -(z₁ - z₂) := by ring
  rw [h1, h2, norm_neg] at hpar
  have hsym := sym_norms a b c
  unfold focalSum
  nlinarith [hpar, hprod, hsym]

theorem focalSum_nonneg (f₁ f₂ z : ℂ) : 0 ≤ focalSum f₁ f₂ z := by
  unfold focalSum; positivity

/-- **Marden, focal part.** The three side midpoints have the same focal sum
with respect to the critical points `z₁, z₂`. -/
theorem focalSum_midpoints_eq (hs : z₁ + z₂ = 2 * (a + b + c) / 3)
    (hp : z₁ * z₂ = (a * b + b * c + c * a) / 3) :
    focalSum z₁ z₂ ((a + b) / 2) = focalSum z₁ z₂ ((b + c) / 2) ∧
    focalSum z₁ z₂ ((b + c) / 2) = focalSum z₁ z₂ ((c + a) / 2) := by
  have hab := focalSum_midpoint_sq hs hp
  have hbc := focalSum_midpoint_sq (a := b) (b := c) (c := a)
    (by rw [hs]; ring) (by rw [hp]; ring)
  have hca := focalSum_midpoint_sq (a := c) (b := a) (c := b)
    (by rw [hs]; ring) (by rw [hp]; ring)
  refine ⟨?_, ?_⟩
  · refine (pow_left_inj₀ (focalSum_nonneg _ _ _) (focalSum_nonneg _ _ _) two_ne_zero).1 ?_
    rw [hab, hbc]; ring
  · refine (pow_left_inj₀ (focalSum_nonneg _ _ _) (focalSum_nonneg _ _ _) two_ne_zero).1 ?_
    rw [hbc, hca]; ring

end Marden
