import Szkraw.OpenExamples

/-!
# A cubic ratio that fails

Theorem 8.11 admits every convex quadratic ratio `ρ(x) = r + t x + τ C(x,2)` with nondecreasing `b`.
A cubic Newton term cannot be added: for `N = 4`, `d_i = i/4` and `ρ(x) = 19/20 + C(x,3)/320` the
array has `b = (0, 1/80, 1/40, 9/256, 3/80)`, nondecreasing, but `g(4,4;4) = -14011/30720000`.
-/

namespace Szkraw

open Finset Matrix

/-- `d_i = i/4`, `ρ = (19/20, 19/20, 19/20, 61/64, 77/80)`, i.e. `ρ(x) = 19/20 + C(x,3)/320`. -/
noncomputable def cubicEx : Coefficients 4 where
  a i := 1 - (i : ℝ) / 4
  b i := if i = 0 then 0 else if i = 1 then 1 / 80 else if i = 2 then 1 / 40 else if i = 3 then 9 / 256
    else 3 / 80
  c i := if i = 0 then 0 else if i = 1 then 19 / 80 else if i = 2 then 19 / 40 else if i = 3 then 183 / 256
    else 77 / 80

theorem cubicEx_admissible : Admissible cubicEx := by
  refine ⟨by norm_num, by simp [cubicEx], by simp [cubicEx], by simp [cubicEx], by norm_num [cubicEx],
    fun i hi => ?_, fun i hi => ?_, fun i hi hi4 => ?_⟩
  · interval_cases i <;> norm_num [cubicEx]
  · interval_cases i <;> norm_num [cubicEx]
  · interval_cases i <;> norm_num [cubicEx]

theorem cubicEx_g444 : productMatrix cubicEx 4 4 4 = -14011 / 30720000 := by
  simp only [productMatrix, matrixPair, cubicEx]
  simp [Matrix.mul_apply, Fin.sum_univ_five, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
    recurrenceMatrix]
  norm_num

/-- **A cubic ratio fails.** The linear profile `d_i = i/4` (Newton coefficients `(1/4, 0, 0, 0)`,
log-concave without internal zeros) with the ratio `ρ(x) = 19/20 + C(x,3)/320`, whose Newton
coefficients `(19/20, 0, 0, 1/320)` are nonnegative, has nondecreasing `b` and `g(4,4;4) < 0`. -/
theorem cubic_ratio_fails :
    Admissible cubicEx ∧ (∀ i, i ≤ 4 → profile cubicEx i = (i : ℝ) / 4) ∧
      LogConcaveNoInternalZeros 4 (newtonCoeff (profile cubicEx)) ∧
      (∀ i, i ≤ 4 → cubicEx.c i = (19 / 20 + (i.choose 3 : ℝ) / 320) * profile cubicEx i) ∧
      (∀ i, i < 4 → cubicEx.b i ≤ cubicEx.b (i + 1)) ∧
      productMatrix cubicEx 4 4 4 = -14011 / 30720000 ∧ ¬ MatrixPositivity cubicEx := by
  have nd : newtonCoeff (profile cubicEx) 1 = 1 / 4 ∧ newtonCoeff (profile cubicEx) 2 = 0 ∧
      newtonCoeff (profile cubicEx) 3 = 0 ∧ newtonCoeff (profile cubicEx) 4 = 0 := by
    simp only [newtonCoeff, profile, cubicEx, sum_range_succ, sum_range_zero]; norm_num [Nat.choose]
  obtain ⟨d1, d2, d3, d4⟩ := nd
  refine ⟨cubicEx_admissible, fun i hi => ?_, ⟨by rw [d1]; norm_num, fun k hk hk4 => ?_, fun k hk hk4 => ?_,
    fun k hk hk4 _ => ?_⟩, fun i hi => ?_, fun i hi => ?_, cubicEx_g444, fun hP => ?_⟩
  · interval_cases i <;> norm_num [cubicEx, profile]
  · interval_cases k
    · rw [d1]; norm_num
    · rw [d2]
    · rw [d3]
    · rw [d4]
  · have hk3 : k ≤ 3 := by omega
    interval_cases k
    · rw [d1, d3, d2]; norm_num
    · rw [d2, d4, d3]; norm_num
  · interval_cases k
    · exact d2
    · exact d3
    · exact d4
  · interval_cases i <;> norm_num [cubicEx, profile, Nat.choose]
  · interval_cases i <;> norm_num [cubicEx]
  · have := hP 4 le_rfl 4 4
    rw [show ((4 : Fin 5) : Fin (4 + 1)) = 4 from rfl] at this
    have h := cubicEx_g444
    linarith

end Szkraw
