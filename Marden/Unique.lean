import Marden.Main

/-!
# Uniqueness of the Steiner inellipse

Algebraic core: the reflection law `(mₖ - f₁)(mₖ - f₂) = -λₖ dₖ²` at the three side
midpoints, together with equal focal sums, forces `λ₁ = λ₂ = λ₃ = 1/12` and hence
`f₁ + f₂ = 2(a+b+c)/3`, `f₁ f₂ = (ab+bc+ca)/3`.
-/

open Complex Polynomial

namespace Marden

/-- Polynomial identity behind `λ₁ = λ₂`. The capital letters play the role of the
complex conjugates, but the identity holds for independent variables. -/
lemma lam_eq_core (a b c f₁ f₂ A B C F₁ F₂ l₁ l₂ : ℂ)
    (P1 : ((a + b) / 2 - f₁) * ((a + b) / 2 - f₂) = -l₁ * (b - a) ^ 2)
    (P2 : ((b + c) / 2 - f₁) * ((b + c) / 2 - f₂) = -l₂ * (c - b) ^ 2)
    (P1c : ((A + B) / 2 - F₁) * ((A + B) / 2 - F₂) = -l₁ * (B - A) ^ 2)
    (P2c : ((B + C) / 2 - F₁) * ((B + C) / 2 - F₂) = -l₂ * (C - B) ^ 2)
    (Fq : ((a + b) / 2 - f₁) * ((A + B) / 2 - F₁) + ((a + b) / 2 - f₂) * ((A + B) / 2 - F₂)
          + 2 * l₁ * (b - a) * (B - A)
        = ((b + c) / 2 - f₁) * ((B + C) / 2 - F₁) + ((b + c) / 2 - f₂) * ((B + C) / 2 - F₂)
          + 2 * l₂ * (c - b) * (C - B)) :
    (l₁ - l₂) * ((B - A) * (c - b) - (b - a) * (C - B)) ^ 2 = 0 := by
  linear_combination (-(c - a) * (C - A)) * Fq + (C - A) ^ 2 * P1 - (C - A) ^ 2 * P2
    + (c - a) ^ 2 * P1c - (c - a) ^ 2 * P2c

/-- Polynomial identity behind `λ = 1/12`. -/
lemma lam_twelfth_core (a b c f₁ f₂ l : ℂ)
    (P1 : ((a + b) / 2 - f₁) * ((a + b) / 2 - f₂) = -l * (b - a) ^ 2)
    (P2 : ((b + c) / 2 - f₁) * ((b + c) / 2 - f₂) = -l * (c - b) ^ 2)
    (P3 : ((c + a) / 2 - f₁) * ((c + a) / 2 - f₂) = -l * (a - c) ^ 2) :
    (a - b) * (a - c) * (b - c) * (12 * l - 1) = 0 := by
  linear_combination (8 : ℂ) * (((b + c) / 2 - (c + a) / 2) * P1
    + ((c + a) / 2 - (a + b) / 2) * P2 + ((a + b) / 2 - (b + c) / 2) * P3)

/-! ## Converse tangency: a minimum along the line forces the reflection law -/

lemma hasDerivAt_norm_line (u d : ℂ) (hu : u ≠ 0) :
    HasDerivAt (fun t : ℝ => ‖u + t * d‖) ((u.re * d.re + u.im * d.im) / ‖u‖) 0 := by
  have e : (fun t : ℝ => ‖u + t * d‖)
      = fun t : ℝ => √((u.re + t * d.re) ^ 2 + (u.im + t * d.im) ^ 2) := by
    funext t; rw [Complex.norm_eq_sqrt_sq_add_sq]; simp
  rw [e]
  have l1 : HasDerivAt (fun t : ℝ => u.re + t * d.re) d.re 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const d.re).const_add u.re
  have l2 : HasDerivAt (fun t : ℝ => u.im + t * d.im) d.im 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const d.im).const_add u.im
  have h1 : HasDerivAt (fun t : ℝ => (u.re + t * d.re) ^ 2 + (u.im + t * d.im) ^ 2)
      (2 * (u.re * d.re + u.im * d.im)) 0 :=
    ((l1.fun_pow 2).add (l2.fun_pow 2)).congr_deriv (by simp; ring)
  have hpos : 0 < u.re ^ 2 + u.im ^ 2 := by
    have := Complex.normSq_pos.2 hu
    rw [Complex.normSq_apply] at this; nlinarith
  have hne : (u.re + 0 * d.re) ^ 2 + (u.im + 0 * d.im) ^ 2 ≠ 0 := by
    simp only [zero_mul, add_zero]; exact hpos.ne'
  convert h1.sqrt hne using 1
  rw [Complex.norm_eq_sqrt_sq_add_sq]
  simp only [zero_mul, add_zero]
  rw [mul_div_mul_left _ _ two_ne_zero]

/-- First-order condition at a minimum of the focal sum along a line. -/
theorem firstOrder_of_localMin (u v d : ℂ) (hu : u ≠ 0) (hv : v ≠ 0)
    (hmin : IsLocalMin (fun t : ℝ => ‖u + t * d‖ + ‖v + t * d‖) 0) :
    (u.re * d.re + u.im * d.im) / ‖u‖ + (v.re * d.re + v.im * d.im) / ‖v‖ = 0 :=
  hmin.hasDerivAt_eq_zero ((hasDerivAt_norm_line u d hu).add (hasDerivAt_norm_line v d hv))

/-- **Converse tangency.** If `t ↦ ‖u + t d‖ + ‖v + t d‖` is minimised at `t = 0` and the
ellipse is non-degenerate (`‖u - v‖ < ‖u‖ + ‖v‖`, i.e. the point is not on the focal
segment), then `u v / d²` is a negative real: `u v = -λ d²` with `λ = ‖u‖‖v‖/‖d‖²`.
Here `u = m - f₁`, `v = m - f₂`; this is the reflection law. -/
theorem reflection_of_min (u v d : ℂ) (hd : d ≠ 0) (hnd : ‖u - v‖ < ‖u‖ + ‖v‖)
    (hmin : ∀ t : ℝ, ‖u‖ + ‖v‖ ≤ ‖u + t * d‖ + ‖v + t * d‖) :
    u * v = -((‖u‖ * ‖v‖ / ‖d‖ ^ 2 : ℝ) : ℂ) * d ^ 2 := by
  have hu : u ≠ 0 := by rintro rfl; simp at hnd
  have hv : v ≠ 0 := by rintro rfl; simp at hnd
  obtain ⟨U, rfl⟩ : ∃ U, u = U * d := ⟨u / d, by field_simp⟩
  obtain ⟨V, rfl⟩ : ∃ V, v = V * d := ⟨v / d, by field_simp⟩
  have hU : U ≠ 0 := by rintro rfl; simp at hu
  have hV : V ≠ 0 := by rintro rfl; simp at hv
  have hdn : 0 < ‖d‖ := norm_pos_iff.2 hd
  have hnU : 0 < ‖U‖ := norm_pos_iff.2 hU
  have hnV : 0 < ‖V‖ := norm_pos_iff.2 hV
  have hmin' : IsLocalMin (fun t : ℝ => ‖U + t * 1‖ + ‖V + t * 1‖) 0 := by
    refine Filter.Eventually.of_forall (fun t => ?_)
    show ‖U + ((0 : ℝ) : ℂ) * 1‖ + ‖V + ((0 : ℝ) : ℂ) * 1‖ ≤ ‖U + (t : ℂ) * 1‖ + ‖V + (t : ℂ) * 1‖
    have h := hmin t
    rw [show U * d + t * d = (U + t * 1) * d by ring, show V * d + t * d = (V + t * 1) * d by ring,
      norm_mul, norm_mul, norm_mul, norm_mul] at h
    simp only [Complex.ofReal_zero, zero_mul, add_zero]
    nlinarith
  have hfo := firstOrder_of_localMin U V 1 hU hV hmin'
  simp only [Complex.one_re, Complex.one_im, mul_one, mul_zero, add_zero] at hfo
  rw [div_add_div _ _ hnU.ne' hnV.ne', div_eq_zero_iff] at hfo
  have h : U.re * ‖V‖ + ‖U‖ * V.re = 0 := by
    rcases hfo with h | h
    · exact h
    · exact absurd h (by positivity)
  have sU : ‖U‖ ^ 2 = U.re ^ 2 + U.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have sV : ‖V‖ ^ 2 = V.re ^ 2 + V.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have key : (U.im * ‖V‖ - V.im * ‖U‖) * (U.im * ‖V‖ + V.im * ‖U‖) = 0 := by
    linear_combination (-‖V‖ ^ 2) * sU + ‖U‖ ^ 2 * sV + (V.re * ‖U‖ - U.re * ‖V‖) * h
  rcases mul_eq_zero.1 key with hA | hB
  · have hc : ((‖V‖ : ℝ) : ℂ) * U = -((‖U‖ : ℝ) : ℂ) * (starRingEnd ℂ) V := by
      apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> linarith
    have hUV : U * V = -((‖U‖ * ‖V‖ : ℝ) : ℂ) := by
      have hVc : ((‖V‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hnV.ne'
      apply mul_left_cancel₀ hVc
      push_cast
      linear_combination V * hc - ((‖U‖ : ℝ) : ℂ) * Complex.conj_mul' V
    have hr : ‖U * d‖ * ‖V * d‖ / ‖d‖ ^ 2 = ‖U‖ * ‖V‖ := by
      rw [div_eq_iff (by positivity), norm_mul, norm_mul]; ring
    rw [hr, show U * d * (V * d) = (U * V) * d ^ 2 by ring, hUV]
  · exfalso
    have hc : ((‖V‖ : ℝ) : ℂ) * U = -((‖U‖ : ℝ) : ℂ) * V := by
      apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> linarith
    have h2 : ((‖U‖ : ℝ) : ℂ) * (U * d - V * d) = ((‖U‖ + ‖V‖ : ℝ) : ℂ) * (U * d) := by
      push_cast; linear_combination (-d) * hc
    have h3 := congrArg norm h2
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
      Real.norm_of_nonneg (norm_nonneg _), Real.norm_of_nonneg (by positivity)] at h3
    have h4 : ‖U * d - V * d‖ = ‖U * d‖ + ‖V * d‖ := by
      rw [norm_mul U d, norm_mul V d]
      rw [norm_mul U d] at h3
      apply mul_left_cancel₀ hnU.ne'
      rw [h3]; ring
    linarith

/-! ## Algebraic uniqueness under the reflection law -/

/-- Non-collinearity in the form needed below. -/
lemma cross_ne_zero {a b c : ℂ} (hab : a ≠ b) (hnc : ((c - a) / (b - a)).im ≠ 0) :
    (starRingEnd ℂ) (b - a) * (c - b) - (b - a) * (starRingEnd ℂ) (c - b) ≠ 0 := by
  have hba : b - a ≠ 0 := sub_ne_zero.2 hab.symm
  have e1 := im_div_mul_normSq (c - a) (b - a) hba
  have hn : 0 < Complex.normSq (b - a) := Complex.normSq_pos.2 hba
  intro h
  have him := congrArg Complex.im h
  simp only [Complex.sub_im, Complex.mul_im, Complex.conj_re, Complex.conj_im,
    Complex.sub_re, Complex.zero_im] at him e1
  apply hnc
  have : ((c - a) / (b - a)).im * Complex.normSq (b - a) = 0 := by rw [e1]; linarith
  rcases mul_eq_zero.1 this with h' | h'
  · exact h'
  · exact absurd h' hn.ne'

/-- One side pair: the reflection law at the midpoints of `ab` and `bc` plus equal focal
sums forces equal `λ`. -/
lemma lam_eq {a b c f₁ f₂ : ℂ} {l₁ l₂ : ℝ} (hab : a ≠ b)
    (hnc : ((c - a) / (b - a)).im ≠ 0)
    (h1 : ((a + b) / 2 - f₁) * ((a + b) / 2 - f₂) = -(l₁ : ℂ) * (b - a) ^ 2)
    (h2 : ((b + c) / 2 - f₁) * ((b + c) / 2 - f₂) = -(l₂ : ℂ) * (c - b) ^ 2)
    (hl₁ : 0 ≤ l₁) (hl₂ : 0 ≤ l₂)
    (hF : focalSum f₁ f₂ ((a + b) / 2) = focalSum f₁ f₂ ((b + c) / 2)) : l₁ = l₂ := by
  have n1 : ‖(a + b) / 2 - f₁‖ * ‖(a + b) / 2 - f₂‖ = l₁ * ‖b - a‖ ^ 2 := by
    rw [← norm_mul, h1, norm_mul, norm_neg, Complex.norm_real, Real.norm_of_nonneg hl₁,
      norm_pow]
  have n2 : ‖(b + c) / 2 - f₁‖ * ‖(b + c) / 2 - f₂‖ = l₂ * ‖c - b‖ ^ 2 := by
    rw [← norm_mul, h2, norm_mul, norm_neg, Complex.norm_real, Real.norm_of_nonneg hl₂,
      norm_pow]
  unfold focalSum at hF
  have R : ‖(a + b) / 2 - f₁‖ ^ 2 + ‖(a + b) / 2 - f₂‖ ^ 2 + 2 * l₁ * ‖b - a‖ ^ 2
      = ‖(b + c) / 2 - f₁‖ ^ 2 + ‖(b + c) / 2 - f₂‖ ^ 2 + 2 * l₂ * ‖c - b‖ ^ 2 := by
    linear_combination (‖(a + b) / 2 - f₁‖ + ‖(a + b) / 2 - f₂‖ + ‖(b + c) / 2 - f₁‖
      + ‖(b + c) / 2 - f₂‖) * hF - 2 * n1 + 2 * n2
  have RC : (((‖(a + b) / 2 - f₁‖ ^ 2 + ‖(a + b) / 2 - f₂‖ ^ 2 + 2 * l₁ * ‖b - a‖ ^ 2 : ℝ)) : ℂ)
      = (((‖(b + c) / 2 - f₁‖ ^ 2 + ‖(b + c) / 2 - f₂‖ ^ 2 + 2 * l₂ * ‖c - b‖ ^ 2 : ℝ)) : ℂ) := by
    rw [R]
  push_cast at RC
  simp only [← Complex.mul_conj', map_sub, map_add, map_div₀, map_ofNat] at RC
  have c1 := congrArg (starRingEnd ℂ) h1
  have c2 := congrArg (starRingEnd ℂ) h2
  simp only [map_mul, map_sub, map_add, map_div₀, map_ofNat, map_neg, map_pow,
    Complex.conj_ofReal] at c1 c2
  have core := lam_eq_core a b c f₁ f₂ ((starRingEnd ℂ) a) ((starRingEnd ℂ) b)
    ((starRingEnd ℂ) c) ((starRingEnd ℂ) f₁) ((starRingEnd ℂ) f₂) l₁ l₂ h1 h2 c1 c2
    (by linear_combination RC)
  have hx := cross_ne_zero hab hnc
  simp only [map_sub] at hx
  have hx' : ((starRingEnd ℂ) b - (starRingEnd ℂ) a) * (c - b)
      - (b - a) * ((starRingEnd ℂ) c - (starRingEnd ℂ) b) ≠ 0 := hx
  rcases mul_eq_zero.1 core with h | h
  · exact_mod_cast sub_eq_zero.1 h
  · exact absurd (pow_eq_zero_iff two_ne_zero |>.1 h) hx'

/-- **Algebraic uniqueness.** If at each side midpoint `m` (side direction `d`) the
reflection law `(m - f₁)(m - f₂) = -λ d²` holds with `λ ≥ 0` real, and the three
midpoints have equal focal sums, then `f₁, f₂` satisfy Vieta for the critical points:
`f₁ + f₂ = 2(a+b+c)/3`, `f₁ f₂ = (ab+bc+ca)/3`. Moreover every `λ` equals `1/12`. -/
theorem foci_of_reflection {a b c f₁ f₂ : ℂ} {l₁ l₂ l₃ : ℝ}
    (hab : a ≠ b) (hbc : b ≠ c) (hca : c ≠ a) (hnc : ((c - a) / (b - a)).im ≠ 0)
    (h1 : ((a + b) / 2 - f₁) * ((a + b) / 2 - f₂) = -(l₁ : ℂ) * (b - a) ^ 2)
    (h2 : ((b + c) / 2 - f₁) * ((b + c) / 2 - f₂) = -(l₂ : ℂ) * (c - b) ^ 2)
    (h3 : ((c + a) / 2 - f₁) * ((c + a) / 2 - f₂) = -(l₃ : ℂ) * (a - c) ^ 2)
    (hl₁ : 0 ≤ l₁) (hl₂ : 0 ≤ l₂) (hl₃ : 0 ≤ l₃)
    (hF₁ : focalSum f₁ f₂ ((a + b) / 2) = focalSum f₁ f₂ ((b + c) / 2))
    (hF₂ : focalSum f₁ f₂ ((b + c) / 2) = focalSum f₁ f₂ ((c + a) / 2)) :
    f₁ + f₂ = 2 * (a + b + c) / 3 ∧ f₁ * f₂ = (a * b + b * c + c * a) / 3 ∧
      l₁ = 1 / 12 ∧ l₂ = 1 / 12 ∧ l₃ = 1 / 12 := by
  have e12 := lam_eq hab hnc h1 h2 hl₁ hl₂ hF₁
  have hnc' := noncollinear_cycle hab hbc hnc
  have e23 := lam_eq (a := b) (b := c) (c := a) hbc hnc' h2 h3 hl₂ hl₃ hF₂
  subst e12 e23
  have t := lam_twelfth_core a b c f₁ f₂ (l₁ : ℂ) h1 h2 h3
  have hd : (a - b) * (a - c) * (b - c) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (sub_ne_zero.2 hab) (sub_ne_zero.2 hca.symm)) (sub_ne_zero.2 hbc)
  have hl : (12 : ℂ) * l₁ - 1 = 0 := (mul_eq_zero.1 t).resolve_left hd
  have hlr : l₁ = 1 / 12 := by
    have : ((12 * l₁ - 1 : ℝ) : ℂ) = 0 := by push_cast; exact hl
    have := Complex.ofReal_eq_zero.1 this
    linarith
  have hac : a - c ≠ 0 := sub_ne_zero.2 hca.symm
  have hs : f₁ + f₂ = 2 * (a + b + c) / 3 := by
    have : (a - c) * (f₁ + f₂ - 2 * (a + b + c) / 3) = 0 := by
      linear_combination (-2 : ℂ) * h1 + 2 * h2 + (1 / 6 : ℂ) * ((b - a) ^ 2 - (c - b) ^ 2) * hl
    have := (mul_eq_zero.1 this).resolve_left hac
    linear_combination this
  refine ⟨hs, ?_, hlr, hlr, hlr⟩
  linear_combination h1 + (a + b) / 2 * hs - (1 / 12 : ℂ) * (b - a) ^ 2 * hl

/-! ## Uniqueness of the Steiner inellipse -/

/-- **Uniqueness of the Steiner inellipse.** Let `a b c` be non-collinear, with critical
points `z₁ z₂`. Suppose `f₁ f₂ : ℂ` and `A' : ℝ` give a genuine (non-degenerate,
`‖f₁ - f₂‖ < 2A'`) ellipse `‖z - f₁‖ + ‖z - f₂‖ = 2A'` that passes through the three side
midpoints, and each side line stays outside the open elliptical region
(`2A' ≤ focalSum` along the line, i.e. the line is a supporting/tangent line at the
midpoint). Then `{f₁, f₂} = {z₁, z₂}` and `A'` equals the `A` of `marden`. -/
theorem steiner_inellipse_unique {a b c z₁ z₂ f₁ f₂ : ℂ} {A' : ℝ}
    (hder : derivative (cubic a b c) = C 3 * (X - C z₁) * (X - C z₂))
    (hab : a ≠ b) (hbc : b ≠ c) (hca : c ≠ a)
    (hnc : ((c - a) / (b - a)).im ≠ 0)
    (hnd : ‖f₁ - f₂‖ < 2 * A')
    (hm₁ : focalSum f₁ f₂ ((a + b) / 2) = 2 * A')
    (hm₂ : focalSum f₁ f₂ ((b + c) / 2) = 2 * A')
    (hm₃ : focalSum f₁ f₂ ((c + a) / 2) = 2 * A')
    (ht₁ : ∀ t : ℝ, 2 * A' ≤ focalSum f₁ f₂ ((a + b) / 2 + t * (b - a)))
    (ht₂ : ∀ t : ℝ, 2 * A' ≤ focalSum f₁ f₂ ((b + c) / 2 + t * (c - b)))
    (ht₃ : ∀ t : ℝ, 2 * A' ≤ focalSum f₁ f₂ ((c + a) / 2 + t * (a - c))) :
    ((f₁ = z₁ ∧ f₂ = z₂) ∨ (f₁ = z₂ ∧ f₂ = z₁)) ∧
      A' = focalSum z₁ z₂ ((a + b) / 2) / 2 := by
  -- reflection law at each midpoint
  have refl : ∀ x y : ℂ, x ≠ y → focalSum f₁ f₂ ((x + y) / 2) = 2 * A' →
      (∀ t : ℝ, 2 * A' ≤ focalSum f₁ f₂ ((x + y) / 2 + t * (y - x))) →
      ((x + y) / 2 - f₁) * ((x + y) / 2 - f₂)
        = -((‖(x + y) / 2 - f₁‖ * ‖(x + y) / 2 - f₂‖ / ‖y - x‖ ^ 2 : ℝ) : ℂ) * (y - x) ^ 2 := by
    intro x y hxy hm ht
    apply reflection_of_min _ _ _ (sub_ne_zero.2 hxy.symm)
    · rw [show (x + y) / 2 - f₁ - ((x + y) / 2 - f₂) = -(f₁ - f₂) by ring, norm_neg]
      unfold focalSum at hm; linarith
    · intro t
      have h := ht t
      unfold focalSum at hm h
      rw [show (x + y) / 2 + t * (y - x) - f₁ = (x + y) / 2 - f₁ + t * (y - x) by ring,
        show (x + y) / 2 + t * (y - x) - f₂ = (x + y) / 2 - f₂ + t * (y - x) by ring] at h
      linarith
  obtain ⟨hs, hp, -, -, -⟩ := foci_of_reflection hab hbc hca hnc
    (refl a b hab hm₁ ht₁) (refl b c hbc hm₂ ht₂) (refl c a hca hm₃ ht₃)
    (by positivity) (by positivity) (by positivity)
    (by rw [hm₁, hm₂]) (by rw [hm₂, hm₃])
  obtain ⟨hs', hp'⟩ := vieta hder
  have hsum : f₁ + f₂ = z₁ + z₂ := by rw [hs, hs']
  have hprod : f₁ * f₂ = z₁ * z₂ := by rw [hp, hp']
  have hfoci : (f₁ = z₁ ∧ f₂ = z₂) ∨ (f₁ = z₂ ∧ f₂ = z₁) := by
    have : (f₁ - z₁) * (f₁ - z₂) = 0 := by linear_combination f₁ * hsum - hprod
    rcases mul_eq_zero.1 this with h | h
    · left; refine ⟨sub_eq_zero.1 h, ?_⟩
      linear_combination hsum - h
    · right; refine ⟨sub_eq_zero.1 h, ?_⟩
      linear_combination hsum - h
  refine ⟨hfoci, ?_⟩
  have hsymm : focalSum z₁ z₂ ((a + b) / 2) = focalSum f₁ f₂ ((a + b) / 2) := by
    rcases hfoci with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rfl
    · unfold focalSum; ring
  rw [hsymm, hm₁]; ring

/-- Variant with the strict tangency condition exactly as produced by `marden`. -/
theorem steiner_inellipse_unique' {a b c z₁ z₂ f₁ f₂ : ℂ} {A' : ℝ}
    (hder : derivative (cubic a b c) = C 3 * (X - C z₁) * (X - C z₂))
    (hab : a ≠ b) (hbc : b ≠ c) (hca : c ≠ a)
    (hnc : ((c - a) / (b - a)).im ≠ 0)
    (hnd : ‖f₁ - f₂‖ < 2 * A')
    (hm₁ : focalSum f₁ f₂ ((a + b) / 2) = 2 * A')
    (hm₂ : focalSum f₁ f₂ ((b + c) / 2) = 2 * A')
    (hm₃ : focalSum f₁ f₂ ((c + a) / 2) = 2 * A')
    (ht₁ : ∀ t : ℝ, t ≠ 0 → 2 * A' < focalSum f₁ f₂ ((a + b) / 2 + t * (b - a)))
    (ht₂ : ∀ t : ℝ, t ≠ 0 → 2 * A' < focalSum f₁ f₂ ((b + c) / 2 + t * (c - b)))
    (ht₃ : ∀ t : ℝ, t ≠ 0 → 2 * A' < focalSum f₁ f₂ ((c + a) / 2 + t * (a - c))) :
    ((f₁ = z₁ ∧ f₂ = z₂) ∨ (f₁ = z₂ ∧ f₂ = z₁)) ∧
      A' = focalSum z₁ z₂ ((a + b) / 2) / 2 := by
  have weak : ∀ m d : ℂ, focalSum f₁ f₂ m = 2 * A' →
      (∀ t : ℝ, t ≠ 0 → 2 * A' < focalSum f₁ f₂ (m + t * d)) →
      ∀ t : ℝ, 2 * A' ≤ focalSum f₁ f₂ (m + t * d) := by
    intro m d hm ht t
    rcases eq_or_ne t 0 with rfl | h
    · simp [hm]
    · exact (ht t h).le
  exact steiner_inellipse_unique hder hab hbc hca hnc hnd hm₁ hm₂ hm₃
    (weak _ _ hm₁ ht₁) (weak _ _ hm₂ ht₂) (weak _ _ hm₃ ht₃)

/-! ## Removing the non-degeneracy hypothesis -/

/-- Equality in the triangle inequality: `m` lies on the line through `f₁, f₂`. -/
lemma on_focal_line (f₁ f₂ m : ℂ) (h : ‖m - f₁‖ + ‖m - f₂‖ = ‖f₁ - f₂‖) :
    ∃ r : ℝ, m - f₁ = r * (f₂ - f₁) := by
  have hs : SameRay ℝ (m - f₁) (f₂ - m) := by
    rw [sameRay_iff_norm_add, show m - f₁ + (f₂ - m) = f₂ - f₁ by ring, norm_sub_rev f₂ f₁,
      norm_sub_rev f₂ m]
    exact h.symm
  obtain ⟨r, -, -, -, -, h1, -⟩ := hs.exists_eq_smul_add
  refine ⟨r, ?_⟩
  rw [h1, Complex.real_smul]
  ring

/-- For a non-degenerate triangle, an "ellipse" through the three side midpoints is
automatically non-degenerate (it is not the focal segment, nor a point). -/
theorem nondeg_of_midpoints {a b c f₁ f₂ : ℂ} {A' : ℝ} (hab : a ≠ b)
    (hnc : ((c - a) / (b - a)).im ≠ 0)
    (hm₁ : focalSum f₁ f₂ ((a + b) / 2) = 2 * A')
    (hm₂ : focalSum f₁ f₂ ((b + c) / 2) = 2 * A')
    (hm₃ : focalSum f₁ f₂ ((c + a) / 2) = 2 * A') : ‖f₁ - f₂‖ < 2 * A' := by
  by_contra hlt
  have hle : 2 * A' ≤ ‖f₁ - f₂‖ := not_lt.1 hlt
  have seg : ∀ m, focalSum f₁ f₂ m = 2 * A' → ‖m - f₁‖ + ‖m - f₂‖ = ‖f₁ - f₂‖ := by
    intro m hm
    have tri : ‖f₁ - f₂‖ ≤ ‖m - f₂‖ + ‖m - f₁‖ := by
      rw [show f₁ - f₂ = (m - f₂) - (m - f₁) by ring]; exact norm_sub_le _ _
    unfold focalSum at hm
    linarith
  obtain ⟨r₁, h1⟩ := on_focal_line _ _ _ (seg _ hm₁)
  obtain ⟨r₂, h2⟩ := on_focal_line _ _ _ (seg _ hm₂)
  obtain ⟨r₃, h3⟩ := on_focal_line _ _ _ (seg _ hm₃)
  have hba : b - a = ((2 * (r₂ - r₃) : ℝ) : ℂ) * (f₂ - f₁) := by
    push_cast; linear_combination 2 * h2 - 2 * h3
  have hca' : c - a = ((2 * (r₂ - r₁) : ℝ) : ℂ) * (f₂ - f₁) := by
    push_cast; linear_combination 2 * h2 - 2 * h1
  have he : f₂ - f₁ ≠ 0 := by
    intro h0; apply hab
    rw [h0, mul_zero] at hba
    exact (sub_eq_zero.1 hba).symm
  apply hnc
  rw [hca', hba, mul_div_mul_right _ _ he, ← Complex.ofReal_div, Complex.ofReal_im]

/-- **Uniqueness of the Steiner inellipse (final form).** Hypotheses exactly mirror the
conclusion of `Marden.marden`: if an ellipse `{z | ‖z - f₁‖ + ‖z - f₂‖ = 2A'}` passes
through the three side midpoints of a non-degenerate triangle and each side line meets
it only at the midpoint (all other points of the line strictly outside), then its foci
are the critical points `z₁, z₂` of `(X-a)(X-b)(X-c)` and `A'` is the `A` of `marden`. -/
theorem steiner_unique {a b c z₁ z₂ f₁ f₂ : ℂ} {A' : ℝ}
    (hder : derivative (cubic a b c) = C 3 * (X - C z₁) * (X - C z₂))
    (hab : a ≠ b) (hbc : b ≠ c) (hca : c ≠ a)
    (hnc : ((c - a) / (b - a)).im ≠ 0)
    (hm₁ : focalSum f₁ f₂ ((a + b) / 2) = 2 * A')
    (hm₂ : focalSum f₁ f₂ ((b + c) / 2) = 2 * A')
    (hm₃ : focalSum f₁ f₂ ((c + a) / 2) = 2 * A')
    (ht₁ : ∀ t : ℝ, t ≠ 0 → 2 * A' < focalSum f₁ f₂ ((a + b) / 2 + t * (b - a)))
    (ht₂ : ∀ t : ℝ, t ≠ 0 → 2 * A' < focalSum f₁ f₂ ((b + c) / 2 + t * (c - b)))
    (ht₃ : ∀ t : ℝ, t ≠ 0 → 2 * A' < focalSum f₁ f₂ ((c + a) / 2 + t * (a - c))) :
    ((f₁ = z₁ ∧ f₂ = z₂) ∨ (f₁ = z₂ ∧ f₂ = z₁)) ∧
      A' = focalSum z₁ z₂ ((a + b) / 2) / 2 :=
  steiner_inellipse_unique' hder hab hbc hca hnc (nondeg_of_midpoints hab hnc hm₁ hm₂ hm₃)
    hm₁ hm₂ hm₃ ht₁ ht₂ ht₃

/-- **Marden + uniqueness, as an `iff`.** For a non-degenerate triangle with critical points
`z₁ z₂`, an ellipse `{z | ‖z - f₁‖ + ‖z - f₂‖ = 2A'}` passes through the three side
midpoints with each side line touching it only there **iff** its foci are `{z₁, z₂}` and
`A'` is the Marden value. So "the foci of *the* Steiner inellipse" is well defined. -/
theorem steiner_inellipse_iff {a b c z₁ z₂ f₁ f₂ : ℂ} {A' : ℝ}
    (hder : derivative (cubic a b c) = C 3 * (X - C z₁) * (X - C z₂))
    (hab : a ≠ b) (hbc : b ≠ c) (hca : c ≠ a)
    (hnc : ((c - a) / (b - a)).im ≠ 0) :
    ((focalSum f₁ f₂ ((a + b) / 2) = 2 * A' ∧
      focalSum f₁ f₂ ((b + c) / 2) = 2 * A' ∧
      focalSum f₁ f₂ ((c + a) / 2) = 2 * A') ∧
    (∀ t : ℝ, t ≠ 0 → 2 * A' < focalSum f₁ f₂ ((a + b) / 2 + t * (b - a))) ∧
    (∀ t : ℝ, t ≠ 0 → 2 * A' < focalSum f₁ f₂ ((b + c) / 2 + t * (c - b))) ∧
    (∀ t : ℝ, t ≠ 0 → 2 * A' < focalSum f₁ f₂ ((c + a) / 2 + t * (a - c))))
    ↔ (((f₁ = z₁ ∧ f₂ = z₂) ∨ (f₁ = z₂ ∧ f₂ = z₁)) ∧
      A' = focalSum z₁ z₂ ((a + b) / 2) / 2) := by
  constructor
  · rintro ⟨⟨h1, h2, h3⟩, t1, t2, t3⟩
    exact steiner_unique hder hab hbc hca hnc h1 h2 h3 t1 t2 t3
  · rintro ⟨hf, rfl⟩
    have key : ∀ z, focalSum f₁ f₂ z = focalSum z₁ z₂ z := by
      intro z
      rcases hf with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rfl
      · unfold focalSum; ring
    simp only [key]
    obtain ⟨h1, h2, h3, h4, -⟩ := marden hder hab hbc hca hnc
    exact ⟨h1, h2, h3, h4⟩

end Marden
