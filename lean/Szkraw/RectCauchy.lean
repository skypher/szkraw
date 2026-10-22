import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Complex.RemovableSingularity

/-!
# Cauchy's integral formula for rectangles

`rectInt f z w` is the integral of `f` over the boundary of the rectangle with opposite corners
`z`, `w`, in the form used by Mathlib's Cauchy–Goursat theorem. This file proves additivity under
splitting, `rectInt (z - a)⁻¹ = 2πi` for `a` inside, and Cauchy's formula for rectangles.
-/

namespace Szkraw

open Complex MeasureTheory intervalIntegral Set
open scoped Interval

/-- The integral over the boundary of the rectangle with corners `z`, `w`. -/
noncomputable def rectInt (f : ℂ → ℂ) (z w : ℂ) : ℂ :=
  (∫ x : ℝ in z.re..w.re, f (x + z.im * I)) - (∫ x : ℝ in z.re..w.re, f (x + w.im * I)) +
    I • (∫ y : ℝ in z.im..w.im, f (re w + y * I)) - I • (∫ y : ℝ in z.im..w.im, f (re z + y * I))

theorem rectInt_eq_zero (f : ℂ → ℂ) (z w : ℂ) (H : DifferentiableOn ℂ f ([[z.re, w.re]] ×ℂ [[z.im, w.im]])) :
    rectInt f z w = 0 := integral_boundary_rect_eq_zero_of_differentiableOn f z w H

theorem rectInt_eq_zero_off_countable (f : ℂ → ℂ) (z w : ℂ) (s : Set ℂ) (hs : s.Countable)
    (Hc : ContinuousOn f ([[z.re, w.re]] ×ℂ [[z.im, w.im]]))
    (Hd : ∀ x ∈ Ioo (min z.re w.re) (max z.re w.re) ×ℂ Ioo (min z.im w.im) (max z.im w.im) \ s,
      DifferentiableAt ℂ f x) :
    rectInt f z w = 0 := integral_boundary_rect_eq_zero_of_differentiable_on_off_countable f z w s hs Hc Hd

/-- Splitting along a vertical line `re = m`. -/
theorem rectInt_split_re (f : ℂ → ℂ) (z w : ℂ) (m : ℝ)
    (h1 : IntervalIntegrable (fun x : ℝ => f (x + z.im * I)) volume z.re m)
    (h2 : IntervalIntegrable (fun x : ℝ => f (x + z.im * I)) volume m w.re)
    (h3 : IntervalIntegrable (fun x : ℝ => f (x + w.im * I)) volume z.re m)
    (h4 : IntervalIntegrable (fun x : ℝ => f (x + w.im * I)) volume m w.re) :
    rectInt f z w = rectInt f z (m + w.im * I) + rectInt f (m + z.im * I) w := by
  simp only [rectInt, add_re, ofReal_re, mul_re, I_re, I_im, ofReal_im, mul_zero, sub_zero, mul_one,
    add_im, mul_im, zero_add, add_zero]
  rw [← integral_add_adjacent_intervals h1 h2, ← integral_add_adjacent_intervals h3 h4]
  ring

/-- Splitting along a horizontal line `im = m`. -/
theorem rectInt_split_im (f : ℂ → ℂ) (z w : ℂ) (m : ℝ)
    (h1 : IntervalIntegrable (fun y : ℝ => f (re z + y * I)) volume z.im m)
    (h2 : IntervalIntegrable (fun y : ℝ => f (re z + y * I)) volume m w.im)
    (h3 : IntervalIntegrable (fun y : ℝ => f (re w + y * I)) volume z.im m)
    (h4 : IntervalIntegrable (fun y : ℝ => f (re w + y * I)) volume m w.im) :
    rectInt f z w = rectInt f z (w.re + m * I) + rectInt f (z.re + m * I) w := by
  simp only [rectInt, add_re, ofReal_re, mul_re, I_re, I_im, ofReal_im, mul_zero, sub_zero, mul_one,
    add_im, mul_im, zero_add, add_zero]
  rw [← integral_add_adjacent_intervals h1 h2, ← integral_add_adjacent_intervals h3 h4]
  simp only [smul_eq_mul]
  ring

theorem integral_two_rho_div (ρ : ℝ) (hρ : 0 < ρ) : ∫ t : ℝ in -ρ..ρ, 2 * ρ / (t ^ 2 + ρ ^ 2) = Real.pi := by
  have e : ∀ t : ℝ, 2 * ρ / (t ^ 2 + ρ ^ 2) = (2 / ρ) * (1 / (1 + (t / ρ) ^ 2)) := by
    intro t; field_simp; ring
  simp_rw [e]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_comp_div (fun u => 1 / (1 + u ^ 2)) hρ.ne',
    integral_one_div_one_add_sq, neg_div, div_self hρ.ne', Real.arctan_neg, Real.arctan_one, smul_eq_mul]
  field_simp
  ring

theorem inv_sub_inv_horiz (t ρ : ℝ) (hρ : 0 < ρ) :
    ((t : ℂ) - ρ * I)⁻¹ - ((t : ℂ) + ρ * I)⁻¹ = ((2 * ρ / (t ^ 2 + ρ ^ 2) : ℝ) : ℂ) * I := by
  have h1 : ((t : ℂ) - ρ * I) ≠ 0 := by
    intro h; have := congrArg im h; simp at this; linarith
  have h2 : ((t : ℂ) + ρ * I) ≠ 0 := by
    intro h; have := congrArg im h; simp at this; linarith
  have h3 : (t ^ 2 + ρ ^ 2 : ℝ) ≠ 0 := by positivity
  rw [inv_sub_inv h1 h2]
  have hd : ((t : ℂ) - ρ * I) * ((t : ℂ) + ρ * I) = ((t ^ 2 + ρ ^ 2 : ℝ) : ℂ) := by
    push_cast; ring_nf; rw [I_sq]; ring
  rw [hd]
  push_cast
  field_simp
  ring

theorem inv_sub_inv_vert (s ρ : ℝ) (hρ : 0 < ρ) :
    I * (((ρ : ℂ) + s * I)⁻¹ - (-(ρ : ℂ) + s * I)⁻¹) = ((2 * ρ / (s ^ 2 + ρ ^ 2) : ℝ) : ℂ) * I := by
  have h1 : ((ρ : ℂ) + s * I) ≠ 0 := by
    intro h; have := congrArg re h; simp at this; linarith
  have h2 : (-(ρ : ℂ) + s * I) ≠ 0 := by
    intro h; have := congrArg re h; simp at this; linarith
  have h3 : (s ^ 2 + ρ ^ 2 : ℝ) ≠ 0 := by positivity
  rw [inv_sub_inv h1 h2]
  have hd : ((ρ : ℂ) + s * I) * (-(ρ : ℂ) + s * I) = -((s ^ 2 + ρ ^ 2 : ℝ) : ℂ) := by
    push_cast; ring_nf; rw [I_sq]; ring
  rw [hd]
  push_cast
  field_simp
  ring_nf

theorem cont_inv_h (σ : ℝ) (hσ : σ ≠ 0) : Continuous fun t : ℝ => ((t : ℂ) + σ * I)⁻¹ := by
  refine Continuous.inv₀ (by fun_prop) fun t h => hσ ?_
  have := congrArg im h; simpa using this

theorem cont_inv_v (σ : ℝ) (hσ : σ ≠ 0) : Continuous fun s : ℝ => ((σ : ℂ) + (s : ℂ) * I)⁻¹ := by
  refine Continuous.inv₀ (by fun_prop) fun s h => hσ ?_
  have := congrArg re h; simpa using this

/-- `∮ (z - a)⁻¹ dz = 2πi` around the square of half-side `ρ` centred at `a`. -/
theorem rectInt_inv_square (a : ℂ) (ρ : ℝ) (hρ : 0 < ρ) :
    rectInt (fun z => (z - a)⁻¹) (a - ρ - ρ * I) (a + ρ + ρ * I) = 2 * Real.pi * I := by
  have hz : (a - ρ - ρ * I).re = a.re - ρ ∧ (a - ρ - ρ * I).im = a.im - ρ := by simp
  have hw : (a + ρ + ρ * I).re = a.re + ρ ∧ (a + ρ + ρ * I).im = a.im + ρ := by simp
  simp only [rectInt, hz.1, hz.2, hw.1, hw.2, smul_eq_mul]
  have hb : ∀ x : ℝ, ((x : ℂ) + ((a.im - ρ : ℝ) : ℂ) * I - a)⁻¹ = (((x - a.re : ℝ) : ℂ) + (-ρ : ℝ) * I)⁻¹ := by
    intro x; congr 1; apply Complex.ext <;> simp
  have ht : ∀ x : ℝ, ((x : ℂ) + ((a.im + ρ : ℝ) : ℂ) * I - a)⁻¹ = (((x - a.re : ℝ) : ℂ) + ρ * I)⁻¹ := by
    intro x; congr 1; apply Complex.ext <;> simp
  have hr : ∀ y : ℝ, (((a.re + ρ : ℝ) : ℂ) + y * I - a)⁻¹ = ((ρ : ℂ) + ((y - a.im : ℝ) : ℂ) * I)⁻¹ := by
    intro y; congr 1; apply Complex.ext <;> simp
  have hl : ∀ y : ℝ, (((a.re - ρ : ℝ) : ℂ) + y * I - a)⁻¹ = (((-ρ : ℝ) : ℂ) + ((y - a.im : ℝ) : ℂ) * I)⁻¹ := by
    intro y; congr 1; apply Complex.ext <;> simp
  simp_rw [hb, ht, hr, hl]
  have e1 := intervalIntegral.integral_comp_sub_right (fun t : ℝ => ((t : ℂ) + (-ρ : ℝ) * I)⁻¹) a.re
    (a := a.re - ρ) (b := a.re + ρ)
  have e2 := intervalIntegral.integral_comp_sub_right (fun t : ℝ => ((t : ℂ) + ρ * I)⁻¹) a.re
    (a := a.re - ρ) (b := a.re + ρ)
  have e3 := intervalIntegral.integral_comp_sub_right (fun s : ℝ => ((ρ : ℂ) + (s : ℂ) * I)⁻¹) a.im
    (a := a.im - ρ) (b := a.im + ρ)
  have e4 := intervalIntegral.integral_comp_sub_right (fun s : ℝ => (((-ρ : ℝ) : ℂ) + (s : ℂ) * I)⁻¹) a.im
    (a := a.im - ρ) (b := a.im + ρ)
  simp only [sub_sub_cancel_left, add_sub_cancel_left] at e1 e2 e3 e4
  rw [e1, e2, e3, e4]
  have i1 := (cont_inv_h (-ρ) (by linarith)).intervalIntegrable (μ := volume) (-ρ) ρ
  have i2 := (cont_inv_h ρ hρ.ne').intervalIntegrable (μ := volume) (-ρ) ρ
  have i3 := (cont_inv_v ρ hρ.ne').intervalIntegrable (μ := volume) (-ρ) ρ
  have i4 := (cont_inv_v (-ρ) (by linarith)).intervalIntegrable (μ := volume) (-ρ) ρ
  rw [← intervalIntegral.integral_sub i1 i2, add_sub_assoc, ← mul_sub, ← intervalIntegral.integral_sub i3 i4,
    ← intervalIntegral.integral_const_mul]
  have h1 : ∀ t : ℝ, ((t : ℂ) + ((-ρ : ℝ) : ℂ) * I)⁻¹ - ((t : ℂ) + ρ * I)⁻¹ = ((2 * ρ / (t ^ 2 + ρ ^ 2) : ℝ) : ℂ) * I := by
    intro t; rw [← inv_sub_inv_horiz t ρ hρ]; push_cast; ring_nf
  have h2 : ∀ s : ℝ, I * (((ρ : ℂ) + (s : ℂ) * I)⁻¹ - (((-ρ : ℝ) : ℂ) + (s : ℂ) * I)⁻¹) =
      ((2 * ρ / (s ^ 2 + ρ ^ 2) : ℝ) : ℂ) * I := by
    intro s; rw [← inv_sub_inv_vert s ρ hρ]; push_cast; ring_nf
  simp_rw [h1, h2]
  rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_ofReal, integral_two_rho_div ρ hρ]
  ring

theorem inv_sub_diffOn (a : ℂ) (S : Set ℂ) (ha : a ∉ S) : DifferentiableOn ℂ (fun z => (z - a)⁻¹) S :=
  fun _ hz => ((differentiableAt_id.sub_const a).inv (sub_ne_zero.mpr fun h => ha (h ▸ hz))).differentiableWithinAt

theorem inv_sub_cont_h (a : ℂ) (c : ℝ) (hc : c ≠ a.im) : Continuous fun x : ℝ => ((x : ℂ) + c * I - a)⁻¹ := by
  refine Continuous.inv₀ (by fun_prop) fun x h => hc ?_
  have := congrArg im h; simp at this; linarith

theorem inv_sub_cont_v (a : ℂ) (c : ℝ) (hc : c ≠ a.re) : Continuous fun y : ℝ => ((c : ℂ) + y * I - a)⁻¹ := by
  refine Continuous.inv₀ (by fun_prop) fun y h => hc ?_
  have := congrArg re h; simp at this; linarith

theorem shrink_left (a z w : ℂ) (m : ℝ) (hz : z.re < m) (hm : m < a.re) (h3 : z.im ≠ a.im) (h4 : w.im ≠ a.im) :
    rectInt (fun z => (z - a)⁻¹) z w = rectInt (fun z => (z - a)⁻¹) (m + z.im * I) w := by
  rw [rectInt_split_re _ z w m
    ((inv_sub_cont_h a z.im h3).intervalIntegrable _ _) ((inv_sub_cont_h a z.im h3).intervalIntegrable _ _)
    ((inv_sub_cont_h a w.im h4).intervalIntegrable _ _) ((inv_sub_cont_h a w.im h4).intervalIntegrable _ _)]
  rw [rectInt_eq_zero _ _ _ (inv_sub_diffOn a _ ?_), zero_add]
  rintro ⟨hre, -⟩
  simp only [Set.mem_preimage, add_re, ofReal_re, mul_re, I_re, I_im, ofReal_im, mul_zero, sub_zero, mul_one,
    add_zero, Set.mem_uIcc] at hre
  rcases hre with h | h <;> linarith [h.1, h.2]

theorem shrink_right (a z w : ℂ) (m : ℝ) (hm : a.re < m) (hw : m < w.re) (h3 : z.im ≠ a.im) (h4 : w.im ≠ a.im) :
    rectInt (fun z => (z - a)⁻¹) z w = rectInt (fun z => (z - a)⁻¹) z (m + w.im * I) := by
  rw [rectInt_split_re _ z w m
    ((inv_sub_cont_h a z.im h3).intervalIntegrable _ _) ((inv_sub_cont_h a z.im h3).intervalIntegrable _ _)
    ((inv_sub_cont_h a w.im h4).intervalIntegrable _ _) ((inv_sub_cont_h a w.im h4).intervalIntegrable _ _)]
  rw [rectInt_eq_zero _ (m + z.im * I) w (inv_sub_diffOn a _ ?_), add_zero]
  rintro ⟨hre, -⟩
  simp only [Set.mem_preimage, add_re, ofReal_re, mul_re, I_re, I_im, ofReal_im, mul_zero, sub_zero, mul_one,
    add_zero, Set.mem_uIcc] at hre
  rcases hre with h | h <;> linarith [h.1, h.2]

theorem shrink_bottom (a z w : ℂ) (m : ℝ) (hz : z.im < m) (hm : m < a.im) (h3 : z.re ≠ a.re) (h4 : w.re ≠ a.re) :
    rectInt (fun z => (z - a)⁻¹) z w = rectInt (fun z => (z - a)⁻¹) (z.re + m * I) w := by
  rw [rectInt_split_im _ z w m
    ((inv_sub_cont_v a z.re h3).intervalIntegrable _ _) ((inv_sub_cont_v a z.re h3).intervalIntegrable _ _)
    ((inv_sub_cont_v a w.re h4).intervalIntegrable _ _) ((inv_sub_cont_v a w.re h4).intervalIntegrable _ _)]
  rw [rectInt_eq_zero _ z (w.re + m * I) (inv_sub_diffOn a _ ?_), zero_add]
  rintro ⟨-, him⟩
  simp only [Set.mem_preimage, add_im, ofReal_im, mul_im, I_re, I_im, ofReal_re, mul_zero, mul_one,
    zero_add, Set.mem_uIcc] at him
  rcases him with h | h <;> linarith [h.1, h.2]

theorem shrink_top (a z w : ℂ) (m : ℝ) (hm : a.im < m) (hw : m < w.im) (h3 : z.re ≠ a.re) (h4 : w.re ≠ a.re) :
    rectInt (fun z => (z - a)⁻¹) z w = rectInt (fun z => (z - a)⁻¹) z (w.re + m * I) := by
  rw [rectInt_split_im _ z w m
    ((inv_sub_cont_v a z.re h3).intervalIntegrable _ _) ((inv_sub_cont_v a z.re h3).intervalIntegrable _ _)
    ((inv_sub_cont_v a w.re h4).intervalIntegrable _ _) ((inv_sub_cont_v a w.re h4).intervalIntegrable _ _)]
  rw [rectInt_eq_zero _ (z.re + m * I) w (inv_sub_diffOn a _ ?_), add_zero]
  rintro ⟨-, him⟩
  simp only [Set.mem_preimage, add_im, ofReal_im, mul_im, I_re, I_im, ofReal_re, mul_zero, mul_one,
    zero_add, Set.mem_uIcc] at him
  rcases him with h | h <;> linarith [h.1, h.2]

/-- `∮ (z - a)⁻¹ dz = 2πi` around every rectangle with `a` strictly inside. -/
theorem rectInt_inv (a z w : ℂ) (h1 : z.re < a.re) (h2 : a.re < w.re) (h3 : z.im < a.im) (h4 : a.im < w.im) :
    rectInt (fun z => (z - a)⁻¹) z w = 2 * Real.pi * I := by
  set ρ := min (min (a.re - z.re) (w.re - a.re)) (min (a.im - z.im) (w.im - a.im)) / 2
  have hρ : 0 < ρ := by
    simp only [ρ]; apply div_pos _ two_pos
    exact lt_min (lt_min (by linarith) (by linarith)) (lt_min (by linarith) (by linarith))
  have hm1 := min_le_left (min (a.re - z.re) (w.re - a.re)) (min (a.im - z.im) (w.im - a.im))
  have hm2 := min_le_right (min (a.re - z.re) (w.re - a.re)) (min (a.im - z.im) (w.im - a.im))
  have hm3 := min_le_left (a.re - z.re) (w.re - a.re)
  have hm4 := min_le_right (a.re - z.re) (w.re - a.re)
  have hm5 := min_le_left (a.im - z.im) (w.im - a.im)
  have hm6 := min_le_right (a.im - z.im) (w.im - a.im)
  have hρ1 : ρ < a.re - z.re := by simp only [ρ]; linarith
  have hρ2 : ρ < w.re - a.re := by simp only [ρ]; linarith
  have hρ3 : ρ < a.im - z.im := by simp only [ρ]; linarith
  have hρ4 : ρ < w.im - a.im := by simp only [ρ]; linarith
  rw [shrink_left a z w (a.re - ρ) (by linarith) (by linarith) (by linarith) (by linarith)]
  rw [shrink_right a _ w (a.re + ρ) (by linarith) (by linarith) (by simp; linarith) (by linarith)]
  rw [shrink_bottom a _ _ (a.im - ρ) (by simp; linarith) (by linarith) (by simp; linarith) (by simp; linarith)]
  rw [shrink_top a _ _ (a.im + ρ) (by linarith) (by simp; linarith) (by simp; linarith) (by simp; linarith)]
  have ez : ((((a.re - ρ : ℝ) : ℂ) + z.im * I).re : ℂ) + ((a.im - ρ : ℝ) : ℂ) * I = a - ρ - ρ * I := by
    apply Complex.ext <;> simp
  have ew : ((((a.re + ρ : ℝ) : ℂ) + w.im * I).re : ℂ) + ((a.im + ρ : ℝ) : ℂ) * I = a + ρ + ρ * I := by
    apply Complex.ext <;> simp
  rw [ez, ew]
  exact rectInt_inv_square a ρ hρ

/-- Edge congruence. -/
theorem rectInt_congr (f g : ℂ → ℂ) (z w : ℂ)
    (hb : ∀ x ∈ [[z.re, w.re]], f (x + z.im * I) = g (x + z.im * I))
    (ht : ∀ x ∈ [[z.re, w.re]], f (x + w.im * I) = g (x + w.im * I))
    (hr : ∀ y ∈ [[z.im, w.im]], f (re w + y * I) = g (re w + y * I))
    (hl : ∀ y ∈ [[z.im, w.im]], f (re z + y * I) = g (re z + y * I)) :
    rectInt f z w = rectInt g z w := by
  simp only [rectInt]
  rw [intervalIntegral.integral_congr hb, intervalIntegral.integral_congr ht, intervalIntegral.integral_congr hr,
    intervalIntegral.integral_congr hl]

theorem edge_integrable (g : ℂ → ℂ) (z w : ℂ) (hg : ContinuousOn g ([[z.re, w.re]] ×ℂ [[z.im, w.im]])) :
    IntervalIntegrable (fun x : ℝ => g (x + z.im * I)) volume z.re w.re ∧
      IntervalIntegrable (fun x : ℝ => g (x + w.im * I)) volume z.re w.re ∧
      IntervalIntegrable (fun y : ℝ => g (re w + y * I)) volume z.im w.im ∧
      IntervalIntegrable (fun y : ℝ => g (re z + y * I)) volume z.im w.im := by
  have hmaps : ∀ (c : ℝ), c ∈ [[z.im, w.im]] → Set.MapsTo (fun x : ℝ => (x : ℂ) + c * I) [[z.re, w.re]]
      ([[z.re, w.re]] ×ℂ [[z.im, w.im]]) := by
    intro c hc x hx; exact ⟨by simpa using hx, by simpa using hc⟩
  have hmaps' : ∀ (c : ℝ), c ∈ [[z.re, w.re]] → Set.MapsTo (fun y : ℝ => (c : ℂ) + y * I) [[z.im, w.im]]
      ([[z.re, w.re]] ×ℂ [[z.im, w.im]]) := by
    intro c hc y hy; exact ⟨by simpa using hc, by simpa using hy⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (hg.comp (by fun_prop) (hmaps z.im Set.left_mem_uIcc)).intervalIntegrable
  · exact (hg.comp (by fun_prop) (hmaps w.im Set.right_mem_uIcc)).intervalIntegrable
  · exact (hg.comp (by fun_prop) (hmaps' w.re Set.right_mem_uIcc)).intervalIntegrable
  · exact (hg.comp (by fun_prop) (hmaps' z.re Set.left_mem_uIcc)).intervalIntegrable

/-- Linearity. -/
theorem rectInt_add_mul (g h : ℂ → ℂ) (c : ℂ) (z w : ℂ)
    (hg : ContinuousOn g ([[z.re, w.re]] ×ℂ [[z.im, w.im]]))
    (hh : IntervalIntegrable (fun x : ℝ => h (x + z.im * I)) volume z.re w.re ∧
      IntervalIntegrable (fun x : ℝ => h (x + w.im * I)) volume z.re w.re ∧
      IntervalIntegrable (fun y : ℝ => h (re w + y * I)) volume z.im w.im ∧
      IntervalIntegrable (fun y : ℝ => h (re z + y * I)) volume z.im w.im) :
    rectInt (fun x => g x + c * h x) z w = rectInt g z w + c * rectInt h z w := by
  obtain ⟨g1, g2, g3, g4⟩ := edge_integrable g z w hg
  obtain ⟨h1, h2, h3, h4⟩ := hh
  simp only [rectInt, smul_eq_mul]
  rw [intervalIntegral.integral_add g1 (h1.const_mul c), intervalIntegral.integral_add g2 (h2.const_mul c),
    intervalIntegral.integral_add g3 (h3.const_mul c), intervalIntegral.integral_add g4 (h4.const_mul c),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul]
  ring

/-- **Cauchy's integral formula for rectangles.** -/
theorem rectInt_cauchy (f : ℂ → ℂ) (D : Set ℂ) (hD : IsOpen D) (hf : DifferentiableOn ℂ f D) (a z w : ℂ)
    (h1 : z.re < a.re) (h2 : a.re < w.re) (h3 : z.im < a.im) (h4 : a.im < w.im)
    (hsub : [[z.re, w.re]] ×ℂ [[z.im, w.im]] ⊆ D) :
    rectInt (fun x => f x * (x - a)⁻¹) z w = 2 * Real.pi * I * f a := by
  have haD : a ∈ D := hsub ⟨by simp [Set.mem_uIcc]; left; constructor <;> linarith,
    by simp [Set.mem_uIcc]; left; constructor <;> linarith⟩
  have hg : DifferentiableOn ℂ (dslope f a) D := (Complex.differentiableOn_dslope (hD.mem_nhds haD)).mpr hf
  have hg0 : rectInt (dslope f a) z w = 0 := rectInt_eq_zero _ z w (hg.mono hsub)
  -- on the edges, `f x (x - a)⁻¹ = dslope f a x + f a (x - a)⁻¹`
  have hpt : ∀ x : ℂ, x ≠ a → f x * (x - a)⁻¹ = dslope f a x + f a * (x - a)⁻¹ := by
    intro x hx
    rw [dslope_of_ne _ hx, slope_def_field]
    have : x - a ≠ 0 := sub_ne_zero.mpr hx
    field_simp
    ring
  have hcong : rectInt (fun x => f x * (x - a)⁻¹) z w = rectInt (fun x => dslope f a x + f a * (x - a)⁻¹) z w := by
    apply rectInt_congr
    · intro x _; apply hpt; intro h; have := congrArg im h; simp at this; linarith
    · intro x _; apply hpt; intro h; have := congrArg im h; simp at this; linarith
    · intro y _; apply hpt; intro h; have := congrArg re h; simp at this; linarith
    · intro y _; apply hpt; intro h; have := congrArg re h; simp at this; linarith
  rw [hcong, rectInt_add_mul _ _ _ z w (hg.continuousOn.mono hsub)
    ⟨(inv_sub_cont_h a z.im (by linarith)).intervalIntegrable _ _,
      (inv_sub_cont_h a w.im (by linarith)).intervalIntegrable _ _,
      (inv_sub_cont_v a w.re (by linarith)).intervalIntegrable _ _,
      (inv_sub_cont_v a z.re (by linarith)).intervalIntegrable _ _⟩,
    hg0, rectInt_inv a z w h1 h2 h3 h4]
  ring

end Szkraw
