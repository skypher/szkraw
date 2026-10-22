import Szkraw.RectCauchy

/-!
# Contour sums over unions of grid squares

For a finite set `S` of grid squares (mesh `h`, origin `c`), the sum of the boundary integrals over
the squares of `S` only involves the edges between a square of `S` and a square outside `S`:
interior edges cancel. This gives the bound used in the Nörlund–Rice estimate (Lemma 9.5).
-/

namespace Szkraw

open Complex MeasureTheory intervalIntegral Set Finset
open scoped Interval

variable (c : ℂ) (h : ℝ)

/-- The lower-left corner of the grid square `(i, j)`. -/
noncomputable def sqLo (p : ℤ × ℤ) : ℂ := c + ((p.1 : ℝ) * h : ℝ) + ((p.2 : ℝ) * h : ℝ) * I

/-- The horizontal edge `H(i,j)`: row `j`, from column `i` to `i + 1`. -/
noncomputable def hEdge (f : ℂ → ℂ) (p : ℤ × ℤ) : ℂ :=
  ∫ x : ℝ in (c.re + p.1 * h)..(c.re + (p.1 + 1) * h), f (x + (c.im + p.2 * h) * I)

/-- The vertical edge `V(i,j)`: column `i`, from row `j` to `j + 1`. -/
noncomputable def vEdge (f : ℂ → ℂ) (p : ℤ × ℤ) : ℂ :=
  ∫ y : ℝ in (c.im + p.2 * h)..(c.im + (p.2 + 1) * h), f ((c.re + p.1 * h : ℝ) + y * I)

/-- The boundary integral of the square `p`. -/
noncomputable def sqInt (f : ℂ → ℂ) (p : ℤ × ℤ) : ℂ := rectInt f (sqLo c h p) (sqLo c h (p.1 + 1, p.2 + 1))

theorem sqInt_eq (f : ℂ → ℂ) (p : ℤ × ℤ) :
    sqInt c h f p = hEdge c h f p - hEdge c h f (p.1, p.2 + 1) + I * vEdge c h f (p.1 + 1, p.2) -
      I * vEdge c h f p := by
  simp only [sqInt, rectInt, sqLo, hEdge, vEdge, smul_eq_mul, add_re, add_im, ofReal_re, ofReal_im, mul_re,
    mul_im, I_re, I_im, mul_zero, mul_one, sub_zero, zero_add, add_zero, Int.cast_add, Int.cast_one]
  push_cast
  rfl

theorem sum_sub_sum_sdiff {α : Type*} [DecidableEq α] (s t : Finset α) (f : α → ℂ) :
    ∑ x ∈ s, f x - ∑ x ∈ t, f x = ∑ x ∈ s \ t, f x - ∑ x ∈ t \ s, f x := by
  have h1 := sum_sdiff (s₁ := s ∩ t) (s₂ := s) (f := f) inter_subset_left
  have h2 := sum_sdiff (s₁ := s ∩ t) (s₂ := t) (f := f) inter_subset_right
  rw [sdiff_inter_self_left] at h1
  rw [show t \ (s ∩ t) = t \ s by ext x; simp] at h2
  rw [← h1, ← h2]; ring

/-- The shift of a set of squares by `(di, dj)`. -/
def shiftSet (S : Finset (ℤ × ℤ)) (d : ℤ × ℤ) : Finset (ℤ × ℤ) := S.image (· + d)

/-- **Edge cancellation**: the sum of the boundary integrals over the squares of `S` is bounded by
the edge integrals over the edges between `S` and its complement. -/
theorem gridSum_bound (f : ℂ → ℂ) (S : Finset (ℤ × ℤ)) :
    ‖∑ p ∈ S, sqInt c h f p‖ ≤
      (∑ q ∈ S \ shiftSet S (0, 1), ‖hEdge c h f q‖) + (∑ q ∈ shiftSet S (0, 1) \ S, ‖hEdge c h f q‖) +
      (∑ q ∈ shiftSet S (1, 0) \ S, ‖vEdge c h f q‖) + (∑ q ∈ S \ shiftSet S (1, 0), ‖vEdge c h f q‖) := by
  have hinj : ∀ d : ℤ × ℤ, Set.InjOn (· + d) (S : Set (ℤ × ℤ)) := fun d x _ y _ hxy => by simpa using hxy
  have e1 : ∑ p ∈ S, hEdge c h f (p.1, p.2 + 1) = ∑ q ∈ shiftSet S (0, 1), hEdge c h f q := by
    rw [shiftSet, sum_image (hinj _)]
    exact sum_congr rfl fun p _ => by congr 1; ext <;> simp
  have e2 : ∑ p ∈ S, vEdge c h f (p.1 + 1, p.2) = ∑ q ∈ shiftSet S (1, 0), vEdge c h f q := by
    rw [shiftSet, sum_image (hinj _)]
    exact sum_congr rfl fun p _ => by congr 1; ext <;> simp
  have hsum : ∑ p ∈ S, sqInt c h f p =
      ((∑ q ∈ S \ shiftSet S (0, 1), hEdge c h f q) - ∑ q ∈ shiftSet S (0, 1) \ S, hEdge c h f q) +
        I * ((∑ q ∈ shiftSet S (1, 0) \ S, vEdge c h f q) - ∑ q ∈ S \ shiftSet S (1, 0), vEdge c h f q) := by
    simp_rw [sqInt_eq]
    rw [sum_sub_distrib, sum_add_distrib, sum_sub_distrib, ← mul_sum, ← mul_sum, e1, e2,
      ← sum_sub_sum_sdiff, ← sum_sub_sum_sdiff]
    ring
  rw [hsum]
  calc _ ≤ ‖(∑ q ∈ S \ shiftSet S (0, 1), hEdge c h f q) - ∑ q ∈ shiftSet S (0, 1) \ S, hEdge c h f q‖ +
        ‖I * ((∑ q ∈ shiftSet S (1, 0) \ S, vEdge c h f q) - ∑ q ∈ S \ shiftSet S (1, 0), vEdge c h f q)‖ :=
        norm_add_le _ _
    _ ≤ _ := by
      rw [norm_mul, Complex.norm_I, one_mul]
      have a1 := norm_sub_le (∑ q ∈ S \ shiftSet S (0, 1), hEdge c h f q) (∑ q ∈ shiftSet S (0, 1) \ S, hEdge c h f q)
      have a2 := norm_sub_le (∑ q ∈ shiftSet S (1, 0) \ S, vEdge c h f q) (∑ q ∈ S \ shiftSet S (1, 0), vEdge c h f q)
      have b1 := norm_sum_le (S \ shiftSet S (0, 1)) (hEdge c h f)
      have b2 := norm_sum_le (shiftSet S (0, 1) \ S) (hEdge c h f)
      have b3 := norm_sum_le (shiftSet S (1, 0) \ S) (vEdge c h f)
      have b4 := norm_sum_le (S \ shiftSet S (1, 0)) (vEdge c h f)
      linarith

end Szkraw
