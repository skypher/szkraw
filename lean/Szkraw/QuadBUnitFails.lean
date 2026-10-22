import Szkraw.VRQuadMain

/-!
# The unit-constant form of eq. `quad-B` fails

For `N = 20`, `d_i = (2^i - 1)/(2^20 - 1)`, `r = 1/2`, `t = 0`, `τ = 10⁻³`, the array satisfies the
hypotheses of Theorem 8.11, and `φ₂(16) φ₂(17) < c₁₇ φ₄(16)` with `φ_n(ℓ) = Δ^n c(ℓ)`.
-/

namespace Szkraw

open Finset

/-- The profile `d_i = (2^i - 1)/(2^20 - 1)`. -/
noncomputable def dPow (i : ℕ) : ℝ := ((2 : ℝ) ^ i - 1) / (2 ^ 20 - 1)

/-- The ratio `ρ(i) = 1/2 + C(i,2)/1000`. -/
noncomputable def rhoPow (i : ℕ) : ℝ := 1 / 2 + (i.choose 2 : ℝ) / 1000

noncomputable def quadBEx : Coefficients 20 where
  a i := 1 - dPow i
  b i := (1 - rhoPow i) * dPow i
  c i := rhoPow i * dPow i

theorem fwdDiff_two (f : ℕ → ℝ) (x : ℕ) : (fwdDiff 1)^[2] f x = f (x + 2) - 2 * f (x + 1) + f x := by
  simp only [Function.iterate_succ, Function.iterate_zero, Function.comp, id, fwdDiff]
  ring_nf

theorem fwdDiff_four (f : ℕ → ℝ) (x : ℕ) :
    (fwdDiff 1)^[4] f x = f (x + 4) - 4 * f (x + 3) + 6 * f (x + 2) - 4 * f (x + 1) + f x := by
  simp only [Function.iterate_succ, Function.iterate_zero, Function.comp, id, fwdDiff]
  ring_nf

theorem quadBEx_ineq :
    (fwdDiff 1)^[2] quadBEx.c 16 * (fwdDiff 1)^[2] quadBEx.c 17 < quadBEx.c 17 * (fwdDiff 1)^[4] quadBEx.c 16 := by
  rw [fwdDiff_two, fwdDiff_two, fwdDiff_four]
  norm_num [quadBEx, rhoPow, dPow, Nat.choose]

theorem dPow_newton (k : ℕ) (hk : 1 ≤ k) : newtonCoeff dPow k = 1 / (2 ^ 20 - 1) := by
  have h2 : ((2 : ℝ) + -1) ^ k = ∑ m ∈ range (k + 1), (2 : ℝ) ^ m * (-1) ^ (k - m) * (k.choose m : ℝ) := add_pow _ _ _
  have h1 : ((1 : ℝ) + -1) ^ k = ∑ m ∈ range (k + 1), (1 : ℝ) ^ m * (-1) ^ (k - m) * (k.choose m : ℝ) := add_pow _ _ _
  norm_num at h2
  rw [show (1 : ℝ) + -1 = 0 by norm_num, zero_pow (by omega)] at h1
  simp only [one_pow, one_mul] at h1
  unfold newtonCoeff dPow
  have hden : (2 : ℝ) ^ 20 - 1 ≠ 0 := by norm_num
  rw [eq_div_iff hden, sum_mul]
  have e : ∀ m ∈ range (k + 1), (-1 : ℝ) ^ (k - m) * (k.choose m : ℝ) * (((2 : ℝ) ^ m - 1) / (2 ^ 20 - 1)) *
      (2 ^ 20 - 1) = (2 : ℝ) ^ m * (-1) ^ (k - m) * (k.choose m : ℝ) - (-1) ^ (k - m) * (k.choose m : ℝ) := by
    intro m _; field_simp
  rw [sum_congr rfl e, sum_sub_distrib, ← h2, ← h1]; ring

theorem quadBEx_admissible : Admissible quadBEx := by
  have hd : ∀ i, i < 20 → dPow i < 1 := fun i hi => by
    unfold dPow
    rw [div_lt_one (by norm_num)]
    have : (2 : ℝ) ^ i < 2 ^ 20 := pow_lt_pow_right₀ (by norm_num) hi
    linarith
  have hd0 : ∀ i, 1 ≤ i → 0 < dPow i := fun i hi => by
    unfold dPow
    have : (2 : ℝ) ^ 1 ≤ 2 ^ i := pow_le_pow_right₀ (by norm_num) hi
    apply div_pos <;> norm_num at this ⊢ <;> linarith
  refine ⟨by norm_num, by norm_num [quadBEx, dPow], by norm_num [quadBEx, dPow], by norm_num [quadBEx, dPow],
    by norm_num [quadBEx, dPow], fun i _ => by simp only [quadBEx]; ring, fun i hi => ?_, fun i hi hi20 => ?_⟩
  · simp only [quadBEx]; linarith [hd i hi]
  · simp only [quadBEx]
    have hρ : 0 < rhoPow i := by unfold rhoPow; positivity
    exact mul_pos hρ (hd0 i hi)

theorem quadBEx_hyp : QuadRatioHyp quadBEx := by
  refine ⟨1 / 2, 0, 1 / 1000, by norm_num, le_rfl, by norm_num, fun i hi => ?_, fun i hi => ?_, ?_⟩
  · simp only [quadBEx, rhoPow, dPow]
    interval_cases i <;> norm_num [Nat.choose]
  · simp only [quadBEx, profile, rhoPow]; ring
  · have hp : profile quadBEx = dPow := by funext i; simp only [quadBEx, profile]; ring
    rw [hp]
    have hc : (0 : ℝ) < 1 / (2 ^ 20 - 1) := by norm_num
    refine ⟨by rw [dPow_newton 1 le_rfl]; exact hc, fun k hk _ => by rw [dPow_newton k hk]; exact hc.le,
      fun k hk _ => by rw [dPow_newton (k - 1) (by omega), dPow_newton k (by omega), dPow_newton (k + 1) (by omega)]; ring_nf; rfl,
      fun k hk _ h0 => by rw [dPow_newton k hk] at h0; exact absurd h0 hc.ne'⟩

/-- **The unit-constant form of eq. `quad-B` fails** for an array satisfying Theorem 8.11:
`φ₂(16) φ₂(17) < c₁₇ φ₄(16)`. -/
theorem quadB_unit_fails :
    Admissible quadBEx ∧ QuadRatioHyp quadBEx ∧
      (fwdDiff 1)^[2] quadBEx.c 16 * (fwdDiff 1)^[2] quadBEx.c 17 < quadBEx.c 17 * (fwdDiff 1)^[4] quadBEx.c 16 :=
  ⟨quadBEx_admissible, quadBEx_hyp, quadBEx_ineq⟩

end Szkraw
