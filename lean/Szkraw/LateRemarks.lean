import Szkraw.CubicMain
import Szkraw.Krawtchouk

/-!
# Remaining remarks: linear-profile arrays of Theorem 8.9, and a log-concavity violation that breaks (P)

* After Theorem 8.9: on the linear profile `d_i = i/N`, the arrays of Theorem 8.9 are arrays of Proposition 8.8
  (`κ₂ = 2κ/N²`, `β₂ = -κ₂`).
* P1, remark after Theorem 3.1 ("log-concavity is not necessary"): for `D(i) = (1-μ) i + μ [i]_q` with `μ = 1/100`,
  `q = 11/10`, `N = 6` and `r = 1`, the Newton coefficients satisfy `ν₁ν₃ = 100 ν₂²` and `g(6,6;6) < 0`.
-/

set_option linter.unusedSectionVars false

namespace Szkraw

open Finset Matrix

/-- **Remark after Theorem 8.9.** Linear-profile arrays of Theorem 8.9 are arrays of Proposition 8.8. -/
theorem affine_linear_quadratic {N : ℕ} (vv : Coefficients N) (hN : 1 ≤ N) {r κ : ℝ} (hκ : 0 ≤ κ)
    (hlin : ∀ i, i ≤ N → profile vv i = (i : ℝ) / N)
    (hc : ∀ i, i ≤ N → vv.c i = (r + κ * i / N) * profile vv i)
    (hb : ∀ i, i < N → vv.b i ≤ vv.b (i + 1)) : QuadHyp vv := by
  have hN0 : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  refine ⟨1 / N - (r / N + κ / N ^ 2), -(2 * κ / N ^ 2), r / N + κ / N ^ 2, 2 * κ / N ^ 2,
    fun n hn => ⟨?_, ?_⟩, by positivity, le_of_eq (by ring), hb⟩
  · have hb' : vv.b n = profile vv n - vv.c n := by unfold profile; ring
    rw [hb', hc n hn, hlin n hn, choose2_real]
    field_simp; ring
  · rw [hc n hn, hlin n hn, choose2_real]
    field_simp; ring

/-- The profile `d_i = D(i)/D(6)`, `D(i) = (99/100) i + (1/100) [i]_{11/10}`, scaled by `D(6) = 60171561/10⁷`. -/
noncomputable def sharpD (i : ℕ) : ℝ :=
  (if i = 0 then 0 else if i = 1 then 10000000 else if i = 2 then 20010000 else if i = 3 then 30031000
    else if i = 4 then 40064100 else if i = 5 then 50110510 else 60171561) / 60171561

/-- The constant-ratio array with `r = 1` on this profile: `a = 1 - d`, `b = 0`, `c = d`. -/
noncomputable def sharpEx : Coefficients 6 where
  a i := 1 - sharpD i
  b _ := 0
  c i := sharpD i

theorem sharpEx_g666 : productMatrix sharpEx 6 6 6 < 0 := by
  simp only [productMatrix, matrixPair, sharpEx, sharpD]
  simp [Matrix.mul_apply, Fin.sum_univ_seven, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
    recurrenceMatrix]
  norm_num

theorem sharpEx_admissible : Admissible sharpEx := by
  refine ⟨by norm_num, by simp [sharpEx, sharpD], by simp [sharpEx], by simp [sharpEx, sharpD],
    by norm_num [sharpEx, sharpD], fun i hi => ?_, fun i hi => ?_, fun i hi hi6 => ?_⟩
  · simp [sharpEx]
  · interval_cases i <;> norm_num [sharpEx, sharpD]
  · interval_cases i <;> norm_num [sharpEx, sharpD]

/-- **P1, "log-concavity is not necessary either", the failing case.** For `D(i) = (1-μ) i + μ [i]_q` with
`μ = 1/100`, `q = 11/10`, the constant-ratio array with `r = 1` and profile `d_i = D(i)/D(6)` is admissible, its
Newton coefficients satisfy `ν₁ ν₃ = (1/μ) ν₂² = 100 ν₂²`, and `g(6,6;6) < 0`. -/
theorem lc_violation_fails :
    Admissible sharpEx ∧
      (∀ i, i ≤ 6 → profile sharpEx i = ((99 / 100) * (i : ℝ) + (1 / 100) * ∑ j ∈ range i, (11 / 10 : ℝ) ^ j) /
        ((99 / 100) * 6 + (1 / 100) * ∑ j ∈ range 6, (11 / 10 : ℝ) ^ j)) ∧
      (∀ i, i ≤ 6 → sharpEx.c i = 1 * profile sharpEx i) ∧
      newtonCoeff (profile sharpEx) 1 * newtonCoeff (profile sharpEx) 3 = 100 * newtonCoeff (profile sharpEx) 2 ^ 2 ∧
      productMatrix sharpEx 6 6 6 < 0 ∧ ¬ MatrixPositivity sharpEx := by
  refine ⟨sharpEx_admissible, fun i hi => ?_, fun i hi => ?_, ?_, sharpEx_g666, fun hP => ?_⟩
  · interval_cases i <;> norm_num [sharpEx, sharpD, profile, sum_range_succ]
  · simp [sharpEx, profile]
  · simp only [newtonCoeff, profile, sharpEx, sharpD, sum_range_succ, sum_range_zero]; norm_num [Nat.choose]
  · have := hP 6 le_rfl 6 6
    rw [show ((6 : Fin 7) : Fin (6 + 1)) = 6 from rfl] at this
    have h := sharpEx_g666
    linarith

/-- For `a₀ = 1`, `b₀ = 0` the first product matrix is the recurrence matrix, so `g(1,1;i) = b_i` on the diagonal. -/
theorem productMatrix_one {N : ℕ} (v : Coefficients N) (ha0 : v.a 0 = 1) (hb0 : v.b 0 = 0) :
    productMatrix v 1 = recurrenceMatrix v := by
  simp [productMatrix, matrixPair, ha0, hb0]

/-- **Sharpness in Corollary 6.1** (proof of P3 Corollary 6.1). For `1/2 < p₀ < 1`, i.e. `r = p₀/(1-p₀) > 1`, the
Krawtchouk array normalized at `j = 0` has `g(1,1;1) = b₁ = (1-r)/N < 0`. -/
theorem krawtchouk_range_sharp (N : ℕ) (hN : 1 ≤ N) (p₀ : ℝ) (h1 : 1 / 2 < p₀) (h2 : p₀ < 1) :
    productMatrix (geometricCoefficients N ((1 - p₀) / p₀) 1) 1 ⟨1, by omega⟩ ⟨1, by omega⟩ =
        (1 - p₀ / (1 - p₀)) / N ∧
      (1 - p₀ / (1 - p₀)) / N < 0 ∧ ¬ MatrixPositivity (geometricCoefficients N ((1 - p₀) / p₀) 1) := by
  have hN0 : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hp0 : p₀ ≠ 0 := by linarith
  have hq0 : 1 - p₀ ≠ 0 := by linarith
  have ha0 : (geometricCoefficients N ((1 - p₀) / p₀) 1).a 0 = 1 := by
    simp [geometricCoefficients, qInteger_at_one, hN0]
  have hb0 : (geometricCoefficients N ((1 - p₀) / p₀) 1).b 0 = 0 := by
    simp [geometricCoefficients, qInteger_at_one]
  have hval : productMatrix (geometricCoefficients N ((1 - p₀) / p₀) 1) 1 ⟨1, by omega⟩ ⟨1, by omega⟩ =
      (1 - p₀ / (1 - p₀)) / N := by
    rw [productMatrix_one _ ha0 hb0]
    simp [recurrenceMatrix, geometricCoefficients, qInteger_at_one]
    field_simp
  have hneg : (1 - p₀ / (1 - p₀)) / N < 0 := by
    apply div_neg_of_neg_of_pos _ hNpos
    have : 1 < p₀ / (1 - p₀) := by rw [lt_div_iff₀ (by linarith)]; linarith
    linarith
  refine ⟨hval, hneg, fun hP => ?_⟩
  have := hP 1 hN ⟨1, by omega⟩ ⟨1, by omega⟩
  linarith

end Szkraw
