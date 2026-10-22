import Marden.Unique

/-!
# Layer 14: Mathlib-only restatement and witness

`l14_marden` and `l14_steiner_unique` restate Marden's theorem and the uniqueness of the Steiner
inellipse with types that mention only Mathlib notions: `Collinear`, `line[ℝ, a, b]`, `midpoint`,
`dist`, `Finset.centroid` and the polynomial `(X - C a) * (X - C b) * (X - C c)` with
`Polynomial.derivative`. Tangency is stated metrically: the side line meets the closed region
`dist · z₁ + dist · z₂ ≤ 2A` only at its midpoint. `l14w_marden` instantiates the hypotheses at
the triangle `0, 5, 1 + 4i`, whose critical points are `1 + 2i` and `3 + (2/3)i`.
-/

open Complex Polynomial

namespace Marden

/-- Bridge: collinearity of `a b c` in `ℂ` is the vanishing of `Im ((c - a) / (b - a))`. -/
theorem l14_collinear_iff (a b c : ℂ) :
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
theorem l14_of_not_collinear {a b c : ℂ} (h : ¬ Collinear ℝ ({a, b, c} : Set ℂ)) :
    a ≠ b ∧ b ≠ c ∧ c ≠ a ∧ ((c - a) / (b - a)).im ≠ 0 := by
  rw [l14_collinear_iff] at h
  refine ⟨?_, ?_, ?_, h⟩
  · rintro rfl; simp at h
  · rintro rfl
    have hab : b - a ≠ 0 := by rintro h0; rw [h0, div_zero] at h; simp at h
    rw [div_self hab] at h; simp at h
  · rintro rfl; simp at h

theorem l14_midpoint_eq (a b : ℂ) : midpoint ℝ a b = (a + b) / 2 := by
  rw [midpoint_eq_smul_add, Complex.real_smul, invOf_eq_inv]
  push_cast
  ring

theorem l14_centroid_eq (a b c : ℂ) :
    Finset.univ.centroid ℝ ![a, b, c] = (a + b + c) / 3 := by
  rw [Finset.centroid_def,
    Finset.affineCombination_eq_linear_combination _ _ _
      (Finset.sum_centroidWeights_eq_one_of_card_eq_add_one (n := 2) ℝ _ (by simp))]
  simp [Fin.sum_univ_three, Finset.centroidWeights_apply, Complex.real_smul]
  ring

theorem l14_dist_add_dist (f₁ f₂ z : ℂ) : dist z f₁ + dist z f₂ = focalSum f₁ f₂ z := by
  rw [Complex.dist_eq, Complex.dist_eq]; rfl

/-- Bridge: points of the side line `line[ℝ, x, y]` other than the midpoint are exactly
`(x + y)/2 + t (y - x)` with real `t ≠ 0`. -/
theorem l14_strict_on_line {x y f₁ f₂ : ℂ} {S : ℝ}
    (h : ∀ t : ℝ, t ≠ 0 → S < focalSum f₁ f₂ ((x + y) / 2 + t * (y - x))) :
    ∀ p ∈ line[ℝ, x, y], p ≠ midpoint ℝ x y → S < dist p f₁ + dist p f₂ := by
  intro p hp hpm
  obtain ⟨r, rfl⟩ := (mem_affineSpan_pair_iff_exists_lineMap_eq).1 hp
  rw [l14_dist_add_dist]
  have e : AffineMap.lineMap x y r = (x + y) / 2 + ((r - 1 / 2 : ℝ) : ℂ) * (y - x) := by
    rw [AffineMap.lineMap_apply_module', Complex.real_smul]; push_cast; ring
  rw [e]
  refine h _ fun h0 => hpm ?_
  rw [e, h0, l14_midpoint_eq]; simp

theorem l14_strict_of_on_line {x y f₁ f₂ : ℂ} {S : ℝ} (hxy : x ≠ y)
    (h : ∀ p ∈ line[ℝ, x, y], p ≠ midpoint ℝ x y → S < dist p f₁ + dist p f₂) :
    ∀ t : ℝ, t ≠ 0 → S < focalSum f₁ f₂ ((x + y) / 2 + t * (y - x)) := by
  intro t ht
  have hmem : (x + y) / 2 + t * (y - x) ∈ line[ℝ, x, y] := by
    rw [mem_affineSpan_pair_iff_exists_lineMap_eq]
    refine ⟨t + 1 / 2, ?_⟩
    rw [AffineMap.lineMap_apply_module', Complex.real_smul]; push_cast; ring
  rw [← l14_dist_add_dist]
  refine h _ hmem fun he => ?_
  rw [l14_midpoint_eq] at he
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
theorem l14_marden {a b c z₁ z₂ : ℂ} (hnc : ¬ Collinear ℝ ({a, b, c} : Set ℂ))
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
  obtain ⟨hab, hbc, hca, hnc'⟩ := l14_of_not_collinear hnc
  obtain ⟨⟨h1, h2, h3⟩, t1, t2, t3, hcen⟩ := marden (z₁ := z₁) (z₂ := z₂) hder hab hbc hca hnc'
  have hnd := nondeg_of_midpoints hab hnc' h1 h2 h3
  have hS : dist (midpoint ℝ a b) z₁ + dist (midpoint ℝ a b) z₂ = focalSum z₁ z₂ ((a + b) / 2) := by
    rw [l14_dist_add_dist, l14_midpoint_eq]
  have e2 : ∀ q : ℝ, 2 * (q / 2) = q := fun q => by ring
  simp only [e2] at h2 h3 t1 t2 t3 hnd
  rw [hS]
  refine ⟨by rw [l14_dist_add_dist, l14_midpoint_eq, h2],
    by rw [l14_dist_add_dist, l14_midpoint_eq, h3],
    l14_strict_on_line t1, l14_strict_on_line t2, l14_strict_on_line t3,
    by rw [Complex.dist_eq]; exact hnd, by rw [l14_midpoint_eq, l14_centroid_eq, hcen]⟩

/-- **Uniqueness of the Steiner inellipse, Mathlib-only form.** If an ellipse
`{z | dist z f₁ + dist z f₂ = S}` passes through the three side midpoints of a non-collinear
triangle and each side line meets the closed region `dist · f₁ + dist · f₂ ≤ S` only at its
midpoint, then `{f₁, f₂}` are the roots of `p'` and `S` is the Marden focal sum. -/
theorem l14_steiner_unique {a b c z₁ z₂ f₁ f₂ : ℂ} {S : ℝ}
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
  obtain ⟨hab, hbc, hca, hnc'⟩ := l14_of_not_collinear hnc
  rw [l14_dist_add_dist, l14_midpoint_eq] at hm₁ hm₂ hm₃
  have e2 : S = 2 * (S / 2) := by ring
  rw [e2] at hm₁ hm₂ hm₃
  have k₁ := l14_strict_of_on_line hab ht₁
  have k₂ := l14_strict_of_on_line hbc ht₂
  have k₃ := l14_strict_of_on_line hca ht₃
  rw [e2] at k₁ k₂ k₃
  obtain ⟨hf, hA⟩ := steiner_unique hder hab hbc hca hnc' hm₁ hm₂ hm₃ k₁ k₂ k₃
  refine ⟨hf, ?_⟩
  rw [l14_dist_add_dist, l14_midpoint_eq]
  linarith

/-- The witness triangle `0, 5, 1 + 4i` is not collinear. -/
theorem l14w_not_collinear :
    ¬ Collinear ℝ ({0, 5, 1 + 4 * I} : Set ℂ) := by
  rw [l14_collinear_iff]
  have : ((1 + 4 * I - 0) / (5 - 0) : ℂ) = (1 / 5 : ℝ) + ((4 / 5 : ℝ) : ℂ) * I := by
    push_cast; ring
  rw [this]; simp

/-- The roots of `p'` for the witness triangle are `1 + 2i` and `3 + (2/3)i`. -/
theorem l14w_derivative :
    derivative ((X - C (0 : ℂ)) * (X - C 5) * (X - C (1 + 4 * I))) =
      C 3 * (X - C (1 + 2 * I)) * (X - C (3 + 2 / 3 * I)) := by
  have h := derivative_cubic (0 : ℂ) 5 (1 + 4 * I)
  unfold cubic at h
  rw [h]
  have h1 : (2 * (0 + 5 + (1 + 4 * I)) : ℂ) = 3 * ((1 + 2 * I) + (3 + 2 / 3 * I)) := by ring
  have h2 : (0 * 5 + 5 * (1 + 4 * I) + (1 + 4 * I) * 0 : ℂ)
      = 3 * ((1 + 2 * I) * (3 + 2 / 3 * I)) := by
    ring_nf; rw [I_sq]; ring
  rw [h1, h2]
  simp only [map_mul, map_add]
  ring

/-- **Witness for `l14_marden` / `l14_steiner_unique`.** The triangle `0, 5, 1 + 4i` with
`z₁ = 1 + 2i`, `z₂ = 3 + (2/3)i` satisfies both hypotheses (non-collinear, `p' = 3(X-z₁)(X-z₂)`).
The vertices are pairwise distinct, the foci are distinct (so the ellipse is not a circle), the
three side midpoints are pairwise distinct, and the full conclusion of `l14_marden` holds; in
particular the ellipse is non-degenerate (`dist z₁ z₂ < S`). -/
theorem l14w_marden :
    ¬ Collinear ℝ ({0, 5, 1 + 4 * I} : Set ℂ) ∧
    derivative ((X - C (0 : ℂ)) * (X - C 5) * (X - C (1 + 4 * I))) =
      C 3 * (X - C (1 + 2 * I)) * (X - C (3 + 2 / 3 * I)) ∧
    (0 : ℂ) ≠ 5 ∧ (5 : ℂ) ≠ 1 + 4 * I ∧ (1 + 4 * I : ℂ) ≠ 0 ∧
    (1 + 2 * I : ℂ) ≠ 3 + 2 / 3 * I ∧
    midpoint ℝ (0 : ℂ) 5 ≠ midpoint ℝ (5 : ℂ) (1 + 4 * I) ∧
    midpoint ℝ (5 : ℂ) (1 + 4 * I) ≠ midpoint ℝ (1 + 4 * I : ℂ) 0 ∧
    midpoint ℝ (1 + 4 * I : ℂ) 0 ≠ midpoint ℝ (0 : ℂ) 5 ∧
    dist (1 + 2 * I : ℂ) (3 + 2 / 3 * I) <
      dist (midpoint ℝ (0 : ℂ) 5) (1 + 2 * I) + dist (midpoint ℝ (0 : ℂ) 5) (3 + 2 / 3 * I) ∧
    midpoint ℝ (1 + 2 * I : ℂ) (3 + 2 / 3 * I) = Finset.univ.centroid ℝ ![0, 5, 1 + 4 * I] := by
  have hM := l14_marden l14w_not_collinear l14w_derivative
  refine ⟨l14w_not_collinear, l14w_derivative, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    hM.2.2.2.2.2.1, hM.2.2.2.2.2.2⟩ <;>
    (try simp only [l14_midpoint_eq]) <;> intro h <;> have h1 := congrArg Complex.re h <;>
    have h2 := congrArg Complex.im h <;> revert h1 h2 <;> norm_num

end Marden
