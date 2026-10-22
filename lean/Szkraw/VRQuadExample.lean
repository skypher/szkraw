import Szkraw.VRQuadMain

/-!
# The example after Theorem 8.11

For `d_i = i/4` and `ρ(x) = 1/2 + C(x,2)/40` the array satisfies the hypotheses of Theorem 8.11, so it
has nonnegative linearization, while the Newton coefficients of `c` are `(1/8, 1/80, 3/160, 0)` and are
not log-concave.
-/

namespace Szkraw

open Finset

/-- The array of the remark after Theorem 8.11: `d_i = i/4`, `ρ(x) = 1/2 + C(x,2)/40`. -/
noncomputable def quadExample : Coefficients 4 where
  a i := 1 - (i : ℝ) / 4
  b i := (1 - (1 / 2 + (i.choose 2 : ℝ) / 40)) * ((i : ℝ) / 4)
  c i := (1 / 2 + (i.choose 2 : ℝ) / 40) * ((i : ℝ) / 4)

theorem quadExample_profile (i : ℕ) : profile quadExample i = (i : ℝ) / 4 := by
  simp only [profile, quadExample]; ring

theorem quadExample_admissible : Admissible quadExample := by
  refine ⟨by norm_num, by simp [quadExample], by simp [quadExample], by simp [quadExample],
    by norm_num [quadExample], fun i _ => by simp only [quadExample]; ring, fun i hi => ?_, fun i hi hi4 => ?_⟩
  · simp only [quadExample]
    have : (i : ℝ) < 4 := by exact_mod_cast hi
    linarith
  · simp only [quadExample]
    have : (0 : ℝ) < i := by exact_mod_cast hi
    positivity

theorem quadExample_newton_profile :
    newtonCoeff (profile quadExample) 1 = 1 / 4 ∧ newtonCoeff (profile quadExample) 2 = 0 ∧
      newtonCoeff (profile quadExample) 3 = 0 ∧ newtonCoeff (profile quadExample) 4 = 0 := by
  simp only [newtonCoeff, quadExample_profile, sum_range_succ, sum_range_zero]
  norm_num [Nat.choose]

theorem quadExample_hyp : QuadRatioHyp quadExample := by
  refine ⟨1 / 2, 0, 1 / 40, by norm_num, le_rfl, by norm_num, fun i hi => ?_, fun i hi => ?_, ?_⟩
  · simp only [quadExample]
    interval_cases i <;> norm_num [Nat.choose]
  · rw [quadExample_profile]; simp only [quadExample]; ring
  · obtain ⟨h1, h2, h3, h4⟩ := quadExample_newton_profile
    refine ⟨by rw [h1]; norm_num, fun k hk hk4 => ?_, fun k hk hk4 => ?_, fun k hk hk4 _ => ?_⟩
    · interval_cases k <;> simp [h1, h2, h3, h4]
    · have : k ≤ 3 := by omega
      interval_cases k <;> simp [h2, h3, h4]
    · interval_cases k <;> simp [h2, h3, h4]

/-- **The example after Theorem 8.11**: the array satisfies Theorem 8.11 and has nonnegative
linearization, while the Newton coefficients of `c` are `(1/8, 1/80, 3/160, 0)`, not log-concave. -/
theorem quadExample_remark :
    Admissible quadExample ∧ QuadRatioHyp quadExample ∧ MatrixPositivity quadExample ∧
      newtonCoeff quadExample.c 1 = 1 / 8 ∧ newtonCoeff quadExample.c 2 = 1 / 80 ∧
      newtonCoeff quadExample.c 3 = 3 / 160 ∧ newtonCoeff quadExample.c 4 = 0 ∧
      ¬ LogConcaveNoInternalZeros 4 (newtonCoeff quadExample.c) := by
  have e1 : newtonCoeff quadExample.c 1 = 1 / 8 := by
    simp only [newtonCoeff, quadExample, sum_range_succ, sum_range_zero]; norm_num [Nat.choose]
  have e2 : newtonCoeff quadExample.c 2 = 1 / 80 := by
    simp only [newtonCoeff, quadExample, sum_range_succ, sum_range_zero]; norm_num [Nat.choose]
  have e3 : newtonCoeff quadExample.c 3 = 3 / 160 := by
    simp only [newtonCoeff, quadExample, sum_range_succ, sum_range_zero]; norm_num [Nat.choose]
  have e4 : newtonCoeff quadExample.c 4 = 0 := by
    simp only [newtonCoeff, quadExample, sum_range_succ, sum_range_zero]; norm_num [Nat.choose]
  refine ⟨quadExample_admissible, quadExample_hyp,
    quadratic_ratio_matrix 4 quadExample quadExample_admissible quadExample_hyp, e1, e2, e3, e4, ?_⟩
  rintro ⟨_, _, hlc, _⟩
  have := hlc 2 le_rfl (by norm_num)
  rw [show 2 - 1 = 1 from rfl, e1, e2, show 2 + 1 = 3 from rfl, e3] at this
  norm_num at this

end Szkraw
