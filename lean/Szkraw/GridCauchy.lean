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

/-- The closed square `p`. -/
def sqSet (p : ℤ × ℤ) : Set ℂ :=
  [[(sqLo c h p).re, (sqLo c h (p.1 + 1, p.2 + 1)).re]] ×ℂ [[(sqLo c h p).im, (sqLo c h (p.1 + 1, p.2 + 1)).im]]

/-- The square containing `a`. -/
noncomputable def sqIdx (a : ℂ) : ℤ × ℤ := (⌊(a.re - c.re) / h⌋, ⌊(a.im - c.im) / h⌋)

/-- `a` lies on no grid line. -/
def OffGrid (a : ℂ) : Prop :=
  (∀ i : ℤ, (a.re - c.re) / h ≠ i) ∧ ∀ j : ℤ, (a.im - c.im) / h ≠ j

variable {c h}

theorem sqLo_re (p : ℤ × ℤ) : (sqLo c h p).re = c.re + p.1 * h := by simp [sqLo]
theorem sqLo_im (p : ℤ × ℤ) : (sqLo c h p).im = c.im + p.2 * h := by simp [sqLo]

/-- An off-grid point lies strictly inside its square. -/
theorem inside_sqIdx (hh : 0 < h) {a : ℂ} (ha : OffGrid c h a) :
    (sqLo c h (sqIdx c h a)).re < a.re ∧ a.re < (sqLo c h ((sqIdx c h a).1 + 1, (sqIdx c h a).2 + 1)).re ∧
      (sqLo c h (sqIdx c h a)).im < a.im ∧ a.im < (sqLo c h ((sqIdx c h a).1 + 1, (sqIdx c h a).2 + 1)).im := by
  simp only [sqLo_re, sqLo_im, sqIdx, Int.cast_add, Int.cast_one]
  have f1 := Int.floor_le ((a.re - c.re) / h)
  have f2 := Int.lt_floor_add_one ((a.re - c.re) / h)
  have f3 := Int.floor_le ((a.im - c.im) / h)
  have f4 := Int.lt_floor_add_one ((a.im - c.im) / h)
  have g1 : (⌊(a.re - c.re) / h⌋ : ℝ) < (a.re - c.re) / h := lt_of_le_of_ne f1 (Ne.symm (ha.1 _))
  have g3 : (⌊(a.im - c.im) / h⌋ : ℝ) < (a.im - c.im) / h := lt_of_le_of_ne f3 (Ne.symm (ha.2 _))
  rw [lt_div_iff₀ hh] at g1 g3
  rw [div_lt_iff₀ hh] at f2 f4
  refine ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- An off-grid point lies outside every other closed square. -/
theorem not_mem_sqSet (hh : 0 < h) {a : ℂ} (ha : OffGrid c h a) {p : ℤ × ℤ} (hp : p ≠ sqIdx c h a) :
    a ∉ sqSet c h p := by
  rintro ⟨hre, him⟩
  simp only [Set.mem_preimage, sqLo_re, sqLo_im, Int.cast_add, Int.cast_one] at hre him
  rw [Set.uIcc_of_le (by nlinarith)] at hre him
  apply hp
  refine Prod.ext ?_ ?_
  · show p.1 = ⌊(a.re - c.re) / h⌋
    rw [eq_comm, Int.floor_eq_iff]
    constructor
    · rw [le_div_iff₀ hh]; linarith [hre.1]
    · rw [div_lt_iff₀ hh]
      rcases eq_or_lt_of_le hre.2 with h' | h'
      · exact absurd (by rw [h']; push_cast; field_simp; ring : (a.re - c.re) / h = ((p.1 + 1 : ℤ) : ℝ)) (ha.1 _)
      · linarith
  · show p.2 = ⌊(a.im - c.im) / h⌋
    rw [eq_comm, Int.floor_eq_iff]
    constructor
    · rw [le_div_iff₀ hh]; linarith [him.1]
    · rw [div_lt_iff₀ hh]
      rcases eq_or_lt_of_le him.2 with h' | h'
      · exact absurd (by rw [h']; push_cast; field_simp; ring : (a.im - c.im) / h = ((p.2 + 1 : ℤ) : ℝ)) (ha.2 _)
      · linarith

/-- **Grid Cauchy formula**: for `f` holomorphic on an open set containing the squares of `S`
and `a` off the grid, `Σ_{p ∈ S} ∮_{∂p} f(x)/(x - a) dx = 2πi f(a)` if `a`'s square is in `S`,
and `0` otherwise. -/
theorem gridSum_cauchy (hh : 0 < h) (f : ℂ → ℂ) (D : Set ℂ) (hD : IsOpen D) (hf : DifferentiableOn ℂ f D)
    (S : Finset (ℤ × ℤ)) (hS : ∀ p ∈ S, sqSet c h p ⊆ D) {a : ℂ} (ha : OffGrid c h a) :
    ∑ p ∈ S, sqInt c h (fun x => f x * (x - a)⁻¹) p =
      if sqIdx c h a ∈ S then 2 * Real.pi * I * f a else 0 := by
  have hzero : ∀ p ∈ S, p ≠ sqIdx c h a → sqInt c h (fun x => f x * (x - a)⁻¹) p = 0 := by
    intro p hp hne
    apply rectInt_eq_zero
    exact (hf.mono (hS p hp)).mul (inv_sub_diffOn a _ (not_mem_sqSet hh ha hne))
  split_ifs with hin
  · rw [sum_eq_single (sqIdx c h a) (fun p hp hne => hzero p hp hne) (fun h' => absurd hin h')]
    obtain ⟨h1, h2, h3, h4⟩ := inside_sqIdx hh ha
    exact rectInt_cauchy f D hD hf a _ _ h1 h2 h3 h4 (hS _ hin)
  · exact sum_eq_zero fun p hp => hzero p hp (fun h' => hin (h' ▸ hp))

end Szkraw
