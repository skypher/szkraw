import Szkraw.VRQuadMain

/-!
# Counterexamples in the open problems

* `d = (0,25,55,91)/91`, `c = (0,24,54,90)/91`: the Newton coefficients of `d` and of `c` are
  log-concave without internal zeros and `b` is nondecreasing, but `g(3,3;3) = -3/2002`.
* `d_i = i/3` with the concave ratio `ρ = (1/2, 3/4, 5/6)`, so that `b_i = 1/6` for `i ≥ 1`:
  `g(3,3;3) = -1/24`.
-/

namespace Szkraw

open Finset Matrix

/-- `d = (0,25,55,91)/91`, `c = (0,24,54,90)/91`, `b = (0,1,1,1)/91`. -/
noncomputable def openEx1 : Coefficients 3 where
  a i := if i = 0 then 1 else if i = 1 then 66 / 91 else if i = 2 then 36 / 91 else 0
  b i := if i = 0 then 0 else 1 / 91
  c i := if i = 0 then 0 else if i = 1 then 24 / 91 else if i = 2 then 54 / 91 else 90 / 91

/-- `d_i = i/3`, `c_i = ρ_i d_i` with `ρ = (1/2, 3/4, 5/6)`, `b_i = 1/6` for `i ≥ 1`. -/
noncomputable def openEx2 : Coefficients 3 where
  a i := 1 - (i : ℝ) / 3
  b i := if i = 0 then 0 else 1 / 6
  c i := if i = 0 then 0 else if i = 1 then 1 / 6 else if i = 2 then 1 / 2 else 5 / 6

theorem openEx1_admissible : Admissible openEx1 := by
  refine ⟨by norm_num, by simp [openEx1], by simp [openEx1], by simp [openEx1], by simp [openEx1],
    fun i hi => ?_, fun i hi => ?_, fun i hi hi3 => ?_⟩
  · interval_cases i <;> norm_num [openEx1]
  · interval_cases i <;> norm_num [openEx1]
  · interval_cases i <;> norm_num [openEx1]

theorem openEx2_admissible : Admissible openEx2 := by
  refine ⟨by norm_num, by simp [openEx2], by simp [openEx2], by simp [openEx2], by norm_num [openEx2],
    fun i hi => ?_, fun i hi => ?_, fun i hi hi3 => ?_⟩
  · interval_cases i <;> norm_num [openEx2]
  · interval_cases i <;> norm_num [openEx2]
  · interval_cases i <;> norm_num [openEx2]

theorem openEx1_g333 : productMatrix openEx1 3 3 3 = -3 / 2002 := by
  simp only [productMatrix, matrixPair, openEx1]
  simp [Matrix.mul_apply, Fin.sum_univ_four, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
    recurrenceMatrix]
  norm_num

theorem openEx2_g333 : productMatrix openEx2 3 3 3 = -1 / 24 := by
  simp only [productMatrix, matrixPair, openEx2]
  simp [Matrix.mul_apply, Fin.sum_univ_four, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
    recurrenceMatrix]
  norm_num

theorem lcnz_three {ν : ℕ → ℝ} (h1 : 0 < ν 1) (h2 : 0 ≤ ν 2) (h3 : 0 ≤ ν 3) (hlc : ν 1 * ν 3 ≤ ν 2 ^ 2)
    (hz : ν 2 = 0 → ν 3 = 0) : LogConcaveNoInternalZeros 3 ν := by
  refine ⟨h1, fun k hk hk3 => ?_, fun k hk hk3 => ?_, fun k hk hk3 h0 => ?_⟩
  · interval_cases k
    · exact h1.le
    · exact h2
    · exact h3
  · have : k = 2 := by omega
    subst this; exact hlc
  · interval_cases k
    · exact absurd h0 h1.ne'
    · exact hz h0

/-- **First counterexample in the open problems**: log-concave Newton coefficients of `d` and of `c`
and nondecreasing `b` do not imply nonnegative linearization. -/
theorem openEx1_fails :
    Admissible openEx1 ∧ LogConcaveNoInternalZeros 3 (newtonCoeff (profile openEx1)) ∧
      LogConcaveNoInternalZeros 3 (newtonCoeff openEx1.c) ∧ (∀ i, i < 3 → openEx1.b i ≤ openEx1.b (i + 1)) ∧
      productMatrix openEx1 3 3 3 = -3 / 2002 ∧ ¬ MatrixPositivity openEx1 := by
  have nd : newtonCoeff (profile openEx1) 1 = 25 / 91 ∧ newtonCoeff (profile openEx1) 2 = 5 / 91 ∧
      newtonCoeff (profile openEx1) 3 = 1 / 91 := by
    simp only [newtonCoeff, profile, openEx1, sum_range_succ, sum_range_zero]; norm_num [Nat.choose]
  have nc : newtonCoeff openEx1.c 1 = 24 / 91 ∧ newtonCoeff openEx1.c 2 = 6 / 91 ∧
      newtonCoeff openEx1.c 3 = 0 := by
    simp only [newtonCoeff, openEx1, sum_range_succ, sum_range_zero]; norm_num [Nat.choose]
  obtain ⟨d1, d2, d3⟩ := nd
  obtain ⟨c1, c2, c3⟩ := nc
  refine ⟨openEx1_admissible, lcnz_three (by rw [d1]; norm_num) (by rw [d2]; norm_num) (by rw [d3]; norm_num)
      (by rw [d1, d2, d3]; norm_num) (fun h => by rw [d2] at h; norm_num at h),
    lcnz_three (by rw [c1]; norm_num) (by rw [c2]; norm_num) (by rw [c3])
      (by rw [c1, c2, c3]; norm_num) (fun _ => c3), fun i hi => ?_, openEx1_g333, fun hP => ?_⟩
  · interval_cases i <;> norm_num [openEx1]
  · have := hP 3 le_rfl 3 3
    rw [show ((3 : Fin 4) : Fin (3 + 1)) = 3 from rfl] at this
    have h := openEx1_g333
    linarith

/-- **Second counterexample in the open problems**: the linear profile `d_i = i/3` with the concave
increasing ratio `ρ = (1/2, 3/4, 5/6)` has `b_i = 1/6` for `i ≥ 1` and `g(3,3;3) = -1/24`. -/
theorem openEx2_fails :
    Admissible openEx2 ∧ (∀ i, i ≤ 3 → profile openEx2 i = (i : ℝ) / 3) ∧
      openEx2.c 1 = 1 / 2 * profile openEx2 1 ∧ openEx2.c 2 = 3 / 4 * profile openEx2 2 ∧
      openEx2.c 3 = 5 / 6 * profile openEx2 3 ∧ (∀ i, 1 ≤ i → i ≤ 3 → openEx2.b i = 1 / 6) ∧
      productMatrix openEx2 3 3 3 = -1 / 24 ∧ ¬ MatrixPositivity openEx2 := by
  refine ⟨openEx2_admissible, fun i hi => ?_, by norm_num [openEx2, profile], by norm_num [openEx2, profile],
    by norm_num [openEx2, profile], fun i hi hi3 => ?_, openEx2_g333, fun hP => ?_⟩
  · interval_cases i <;> norm_num [openEx2, profile]
  · simp [openEx2, show i ≠ 0 by omega]
  · have := hP 3 le_rfl 3 3
    have h := openEx2_g333
    linarith

end Szkraw
