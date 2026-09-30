import Marden.Basic

/-!
# Tangency at the midpoints

For a side `x y` with midpoint `m = (x+y)/2` and direction `d = y - x`, write
`u = m - z₁`, `v = m - z₂`.  The algebraic identity `u * v = -d²/12`
(`Marden.midpoint_mul`) says `u v / d²` is a negative real, which is the
reflection property of the tangent line.  We prove the *metric* consequence:
every point `m + t d` of the side line has focal sum `≥` that of `m`, strictly
for `t ≠ 0` when the foci are off the line.  So the line meets the closed
elliptical region `{focalSum ≤ 2A}` in exactly the point `m`: it is tangent there.
-/

open Complex

namespace Marden

lemma triangle_aux (w : ℂ) (μ t : ℝ) (hμ : 0 ≤ μ) :
    (1 + μ) * ‖w‖ ≤ ‖w + t‖ + ‖μ * w - t‖ := by
  have h : (w + t) + (μ * w - t) = ((1 + μ : ℝ) : ℂ) * w := by push_cast; ring
  calc (1 + μ) * ‖w‖ = ‖(w + t) + (μ * w - t)‖ := by
        rw [h, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
    _ ≤ _ := norm_add_le _ _

lemma triangle_aux_strict (w : ℂ) (μ t : ℝ) (hμ : 0 < μ) (hw : w.im ≠ 0) (ht : t ≠ 0) :
    (1 + μ) * ‖w‖ < ‖w + t‖ + ‖μ * w - t‖ := by
  have h : (w + t) + (μ * w - t) = ((1 + μ : ℝ) : ℂ) * w := by push_cast; ring
  have hne : ¬ SameRay ℝ (w + t) (μ * w - t) := by
    intro hr
    have h1 : w + t ≠ 0 := by
      intro h0; apply hw; have := congrArg Complex.im h0; simpa using this
    have h2 : (μ : ℂ) * w - t ≠ 0 := by
      intro h0; apply hw; have := congrArg Complex.im h0
      simp at this
      rcases this with h | h
      · exact absurd h hμ.ne'
      · exact h
    obtain ⟨r₁, r₂, hr₁, hr₂, hr⟩ := hr.exists_pos h1 h2
    have him := congrArg Complex.im hr
    have hre := congrArg Complex.re hr
    simp at him hre
    have e1 : r₁ = r₂ * μ := by
      have := mul_right_cancel₀ hw (show r₁ * w.im = (r₂ * μ) * w.im by linarith)
      exact this
    rw [e1] at hre
    have : t * (r₂ * (μ + 1)) = 0 := by linarith
    rcases mul_eq_zero.1 this with h | h
    · exact ht h
    · have : 0 < r₂ * (μ + 1) := by positivity
      linarith
  calc (1 + μ) * ‖w‖ = ‖(w + t) + (μ * w - t)‖ := by
        rw [h, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
    _ < _ := norm_add_lt_of_not_sameRay hne

/-- From `(w d) v = -d²/12` we get `v = -μ · conj w · d` with `μ = 1/(12‖w‖²) > 0`. -/
lemma v_eq (w v d : ℂ) (hd : d ≠ 0) (hw : w ≠ 0) (h : (w * d) * v = -d ^ 2 / 12) :
    v = -((1 / (12 * ‖w‖ ^ 2) : ℝ) : ℂ) * (starRingEnd ℂ) w * d := by
  have hn : (‖w‖ ^ 2 : ℝ) ≠ 0 := by positivity
  have hn' : ((‖w‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hn
  have hmc : w * (starRingEnd ℂ) w = ((‖w‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hwd : w * d ≠ 0 := mul_ne_zero hw hd
  apply mul_left_cancel₀ hwd
  rw [h, show w * d * (-((1 / (12 * ‖w‖ ^ 2) : ℝ) : ℂ) * (starRingEnd ℂ) w * d)
      = -((1 / (12 * ‖w‖ ^ 2) : ℝ) : ℂ) * (w * (starRingEnd ℂ) w) * d ^ 2 by ring, hmc]
  have hn'' : ((‖w‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 hw
  push_cast
  field_simp

/-- Metric tangency lemma: if `u v = -d²/12` then `t ↦ ‖u + t d‖ + ‖v + t d‖`
is minimised at `t = 0`. -/
theorem focal_le_of_mul (u v d : ℂ) (hd : d ≠ 0) (huv : u * v = -d ^ 2 / 12) (t : ℝ) :
    ‖u‖ + ‖v‖ ≤ ‖u + t * d‖ + ‖v + t * d‖ := by
  obtain ⟨w, rfl⟩ : ∃ w, u = w * d := ⟨u / d, by field_simp⟩
  have hw0 : w ≠ 0 := by
    rintro rfl
    have : d ^ 2 = 0 := by linear_combination (12 : ℂ) * huv
    exact hd (pow_eq_zero_iff two_ne_zero |>.1 this)
  set μ : ℝ := 1 / (12 * ‖w‖ ^ 2) with hμdef
  have hv := v_eq w v d hd hw0 huv
  rw [← hμdef] at hv
  have hμ : 0 ≤ μ := by positivity
  have e1 : ‖w * d + t * d‖ = ‖w + t‖ * ‖d‖ := by
    rw [show w * d + t * d = (w + t) * d by ring, norm_mul]
  have e2 : ‖v + t * d‖ = ‖μ * w - t‖ * ‖d‖ := by
    rw [hv, show -(μ : ℂ) * (starRingEnd ℂ) w * d + t * d
        = -((starRingEnd ℂ) (μ * w - t)) * d by simp; ring, norm_mul, norm_neg,
      Complex.norm_conj]
  have e3 : ‖w * d‖ = ‖w‖ * ‖d‖ := norm_mul _ _
  have e4 : ‖v‖ = μ * ‖w‖ * ‖d‖ := by
    rw [hv, norm_mul, norm_mul, norm_neg, Complex.norm_conj, Complex.norm_real,
      Real.norm_of_nonneg hμ]
  rw [e1, e2, e3, e4]
  have := triangle_aux w μ t hμ
  have hdn : 0 ≤ ‖d‖ := norm_nonneg _
  nlinarith

/-- Strict version, when `u/d` is not real (the focus `z₁` is off the line). -/
theorem focal_lt_of_mul (u v d : ℂ) (hd : d ≠ 0) (huv : u * v = -d ^ 2 / 12)
    (hw : (u / d).im ≠ 0) (t : ℝ) (ht : t ≠ 0) :
    ‖u‖ + ‖v‖ < ‖u + t * d‖ + ‖v + t * d‖ := by
  obtain ⟨w, rfl⟩ : ∃ w, u = w * d := ⟨u / d, by field_simp⟩
  rw [mul_div_cancel_right₀ w hd] at hw
  have hw0 : w ≠ 0 := by rintro rfl; simp at hw
  set μ : ℝ := 1 / (12 * ‖w‖ ^ 2) with hμdef
  have hv := v_eq w v d hd hw0 huv
  rw [← hμdef] at hv
  have hμ : 0 < μ := by
    have : 0 < ‖w‖ := norm_pos_iff.2 hw0
    positivity
  have e1 : ‖w * d + t * d‖ = ‖w + t‖ * ‖d‖ := by
    rw [show w * d + t * d = (w + t) * d by ring, norm_mul]
  have e2 : ‖v + t * d‖ = ‖μ * w - t‖ * ‖d‖ := by
    rw [hv, show -(μ : ℂ) * (starRingEnd ℂ) w * d + t * d
        = -((starRingEnd ℂ) (μ * w - t)) * d by simp; ring, norm_mul, norm_neg,
      Complex.norm_conj]
  have e3 : ‖w * d‖ = ‖w‖ * ‖d‖ := norm_mul _ _
  have e4 : ‖v‖ = μ * ‖w‖ * ‖d‖ := by
    rw [hv, norm_mul, norm_mul, norm_neg, Complex.norm_conj, Complex.norm_real,
      Real.norm_of_nonneg hμ.le]
  rw [e1, e2, e3, e4]
  have := triangle_aux_strict w μ t hμ hw ht
  have hdn : 0 < ‖d‖ := norm_pos_iff.2 hd
  nlinarith

end Marden
