import Marden.Tangent

/-!
# Marden's theorem

`p = (X - a)(X - b)(X - c)` over `ℂ`. Take `z₁, z₂` with
`p' = 3 (X - z₁)(X - z₂)` (the critical points, counted with multiplicity). If
`a, b, c` are not collinear, then the ellipse `{z | ‖z - z₁‖ + ‖z - z₂‖ = 2A}`,
with `2A` the common focal sum of the midpoints, goes through the three side
midpoints. At each midpoint `m` of a side `xy`, every other point of the line `xy`
lies strictly outside the ellipse (`focalSum > 2A`), so the line is tangent at `m`.
The centre `(z₁+z₂)/2` is the centroid.
-/

open Complex Polynomial

namespace Marden

/-- The cubic with roots `a b c`. -/
noncomputable def cubic (a b c : ℂ) : ℂ[X] := (X - C a) * (X - C b) * (X - C c)

theorem derivative_cubic (a b c : ℂ) :
    derivative (cubic a b c)
      = C 3 * X ^ 2 - C (2 * (a + b + c)) * X + C (a * b + b * c + c * a) := by
  unfold cubic
  simp only [derivative_mul, derivative_sub, derivative_X, derivative_C, sub_zero, one_mul,
    mul_one, map_mul, map_add, map_ofNat]
  ring

/-- Vieta for the critical points. -/
theorem vieta {a b c z₁ z₂ : ℂ}
    (h : derivative (cubic a b c) = C 3 * (X - C z₁) * (X - C z₂)) :
    z₁ + z₂ = 2 * (a + b + c) / 3 ∧ z₁ * z₂ = (a * b + b * c + c * a) / 3 := by
  rw [derivative_cubic] at h
  have h0 := congrArg (eval 0) h
  have h1 := congrArg (eval 1) h
  simp at h0 h1
  constructor
  · linear_combination (1 / 3 : ℂ) * h1 - (1 / 3 : ℂ) * h0
  · linear_combination (-1 / 3 : ℂ) * h0

/-- The critical points exist (explicit quadratic formula over the algebraically
closed field `ℂ`), so the hypothesis of `marden` is always satisfiable. -/
theorem exists_critical_points (a b c : ℂ) :
    ∃ z₁ z₂ : ℂ, derivative (cubic a b c) = C 3 * (X - C z₁) * (X - C z₂) := by
  obtain ⟨r, hr⟩ := IsAlgClosed.exists_eq_mul_self
    ((a + b + c) ^ 2 - 3 * (a * b + b * c + c * a))
  refine ⟨(a + b + c + r) / 3, (a + b + c - r) / 3, ?_⟩
  rw [derivative_cubic]
  have h1 : 2 * (a + b + c) = 3 * ((a + b + c + r) / 3 + (a + b + c - r) / 3) := by ring
  have h2 : a * b + b * c + c * a = 3 * ((a + b + c + r) / 3 * ((a + b + c - r) / 3)) := by
    linear_combination (-1 / 3 : ℂ) * hr
  rw [h1, h2]
  simp only [map_mul, map_add]
  ring

/-- If `u v = -d²/12` and `u/d` is real then `(u+v)/d` is real. -/
lemma sum_real_of_real (u v d : ℂ) (hd : d ≠ 0) (huv : u * v = -d ^ 2 / 12)
    (him : (u / d).im = 0) : ((u + v) / d).im = 0 := by
  obtain ⟨w, rfl⟩ : ∃ w, u = w * d := ⟨u / d, by field_simp⟩
  rw [mul_div_cancel_right₀ w hd] at him
  have hw0 : w ≠ 0 := by
    rintro rfl
    have : d ^ 2 = 0 := by linear_combination (12 : ℂ) * huv
    exact hd (pow_eq_zero_iff two_ne_zero |>.1 this)
  have hv := v_eq w v d hd hw0 huv
  rw [hv, show w * d + -((1 / (12 * ‖w‖ ^ 2) : ℝ) : ℂ) * (starRingEnd ℂ) w * d
      = (w + -((1 / (12 * ‖w‖ ^ 2) : ℝ) : ℂ) * (starRingEnd ℂ) w) * d by ring,
    mul_div_cancel_right₀ _ hd]
  have h2 : (-((1 / (12 * ‖w‖ ^ 2) : ℝ) : ℂ) * (starRingEnd ℂ) w).im = 0 := by
    rw [neg_mul, Complex.neg_im, Complex.im_ofReal_mul, Complex.conj_im, him]; simp
  rw [Complex.add_im, him, h2, add_zero]

/-- Non-collinearity keeps the focus `z₁` off the side line `ab`. -/
theorem focus_off_side {a b c z₁ z₂ : ℂ} (hs : z₁ + z₂ = 2 * (a + b + c) / 3)
    (hp : z₁ * z₂ = (a * b + b * c + c * a) / 3) (hab : a ≠ b)
    (hnc : ((c - a) / (b - a)).im ≠ 0) :
    (((a + b) / 2 - z₁) / (b - a)).im ≠ 0 := by
  have hd : b - a ≠ 0 := sub_ne_zero.2 hab.symm
  intro him
  have h := sum_real_of_real _ _ _ hd (midpoint_mul hs hp) him
  rw [show ((a + b) / 2 - z₁ + ((a + b) / 2 - z₂)) / (b - a)
      = ((1 / 3 : ℝ) : ℂ) + ((-2 / 3 : ℝ) : ℂ) * ((c - a) / (b - a)) by
    rw [show (a + b) / 2 - z₁ + ((a + b) / 2 - z₂) = (a + b - 2 * c) / 3 by
      linear_combination (-1 : ℂ) * hs]
    push_cast
    field_simp
    ring] at h
  rw [Complex.add_im, Complex.ofReal_im, Complex.im_ofReal_mul, zero_add] at h
  rcases mul_eq_zero.1 h with h | h
  · norm_num at h
  · exact hnc h

/-- **Tangency at the midpoint of side `ab`.** -/
theorem tangent_at_midpoint {a b c z₁ z₂ : ℂ} (hs : z₁ + z₂ = 2 * (a + b + c) / 3)
    (hp : z₁ * z₂ = (a * b + b * c + c * a) / 3) (hab : a ≠ b)
    (hnc : ((c - a) / (b - a)).im ≠ 0) (t : ℝ) (ht : t ≠ 0) :
    focalSum z₁ z₂ ((a + b) / 2) < focalSum z₁ z₂ ((a + b) / 2 + t * (b - a)) := by
  have hd : b - a ≠ 0 := sub_ne_zero.2 hab.symm
  have h := focal_lt_of_mul ((a + b) / 2 - z₁) ((a + b) / 2 - z₂) (b - a) hd
    (midpoint_mul hs hp) (focus_off_side hs hp hab hnc) t ht
  unfold focalSum
  rw [show (a + b) / 2 + t * (b - a) - z₁ = (a + b) / 2 - z₁ + t * (b - a) by ring,
    show (a + b) / 2 + t * (b - a) - z₂ = (a + b) / 2 - z₂ + t * (b - a) by ring]
  exact h

lemma im_div_mul_normSq (x y : ℂ) (hy : y ≠ 0) :
    (x / y).im * Complex.normSq y = x.im * y.re - x.re * y.im := by
  have hn : Complex.normSq y ≠ 0 := (Complex.normSq_pos.2 hy).ne'
  rw [Complex.div_im]
  field_simp

/-- Non-collinearity is invariant under the cyclic shift `a → b → c → a`. -/
lemma noncollinear_cycle {a b c : ℂ} (hab : a ≠ b) (hbc : b ≠ c)
    (hnc : ((c - a) / (b - a)).im ≠ 0) : ((a - b) / (c - b)).im ≠ 0 := by
  have hba : b - a ≠ 0 := sub_ne_zero.2 hab.symm
  have hcb : c - b ≠ 0 := sub_ne_zero.2 hbc.symm
  have e1 := im_div_mul_normSq (c - a) (b - a) hba
  have e2 := im_div_mul_normSq (a - b) (c - b) hcb
  have hn : 0 < Complex.normSq (b - a) := Complex.normSq_pos.2 hba
  intro h
  rw [h, zero_mul] at e2
  simp only [Complex.sub_re, Complex.sub_im] at e1 e2
  have : ((c - a) / (b - a)).im * Complex.normSq (b - a) = 0 := by rw [e1]; linarith
  rcases mul_eq_zero.1 this with h' | h'
  · exact hnc h'
  · exact hn.ne' h'

/-- **Marden's theorem.** Let `a b c` be non-collinear and let `z₁ z₂` be the
critical points of `(X-a)(X-b)(X-c)`, i.e. `p' = 3 (X - z₁)(X - z₂)`. Put
`A := focalSum z₁ z₂ ((a+b)/2) / 2`. Then
1. the three side midpoints lie on the ellipse `‖z - z₁‖ + ‖z - z₂‖ = 2A`;
2. each side line meets the closed region `‖z - z₁‖ + ‖z - z₂‖ ≤ 2A` only at its
   midpoint (tangency);
3. the centre `(z₁ + z₂)/2` is the centroid. -/
theorem marden {a b c z₁ z₂ : ℂ}
    (hder : derivative (cubic a b c) = C 3 * (X - C z₁) * (X - C z₂))
    (hab : a ≠ b) (hbc : b ≠ c) (hca : c ≠ a)
    (hnc : ((c - a) / (b - a)).im ≠ 0) :
    let A := focalSum z₁ z₂ ((a + b) / 2) / 2
    (focalSum z₁ z₂ ((a + b) / 2) = 2 * A ∧
      focalSum z₁ z₂ ((b + c) / 2) = 2 * A ∧
      focalSum z₁ z₂ ((c + a) / 2) = 2 * A) ∧
    (∀ t : ℝ, t ≠ 0 → 2 * A < focalSum z₁ z₂ ((a + b) / 2 + t * (b - a))) ∧
    (∀ t : ℝ, t ≠ 0 → 2 * A < focalSum z₁ z₂ ((b + c) / 2 + t * (c - b))) ∧
    (∀ t : ℝ, t ≠ 0 → 2 * A < focalSum z₁ z₂ ((c + a) / 2 + t * (a - c))) ∧
    (z₁ + z₂) / 2 = (a + b + c) / 3 := by
  intro A
  obtain ⟨hs, hp⟩ := vieta hder
  have hs' : z₁ + z₂ = 2 * (b + c + a) / 3 := by rw [hs]; ring
  have hp' : z₁ * z₂ = (b * c + c * a + a * b) / 3 := by rw [hp]; ring
  have hs'' : z₁ + z₂ = 2 * (c + a + b) / 3 := by rw [hs]; ring
  have hp'' : z₁ * z₂ = (c * a + a * b + b * c) / 3 := by rw [hp]; ring
  have hnc' := noncollinear_cycle hab hbc hnc
  have hnc'' := noncollinear_cycle hbc hca hnc'
  obtain ⟨e1, e2⟩ := focalSum_midpoints_eq hs hp
  have hA : 2 * A = focalSum z₁ z₂ ((a + b) / 2) := by simp only [A]; ring
  refine ⟨⟨hA.symm, by rw [hA, e1], by rw [hA, e1, e2]⟩, ?_, ?_, ?_, ?_⟩
  · intro t ht; rw [hA]; exact tangent_at_midpoint hs hp hab hnc t ht
  · intro t ht; rw [hA, e1]; exact tangent_at_midpoint hs' hp' hbc hnc' t ht
  · intro t ht; rw [hA, e1, e2]; exact tangent_at_midpoint hs'' hp'' hca hnc'' t ht
  · rw [hs]; ring

end Marden
