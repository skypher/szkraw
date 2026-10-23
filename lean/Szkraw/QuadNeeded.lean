import Szkraw.VRCorollaries
import Szkraw.LateRemarks

/-!
# P2, after Proposition 3.3: each hypothesis is needed

For quadratic arrays `b_n = β₁ n + β₂ C(n,2)`, `c_n = κ₁ n + κ₂ C(n,2)`, `a = 1 - b - c`, Proposition 3.3 assumes
`κ₂ ≥ 0`, `κ₂ + β₂ ≥ 0` and `b` nondecreasing. Dropping any one of them, with the other two kept, gives an
admissible array with `N = 3` and `g(3,3;3) < 0` (witnesses found by `runs/varratio/quadratic.py`-style search).
-/

namespace Szkraw

/-- The quadratic array with parameters `β₁ β₂ κ₁ κ₂`. -/
noncomputable def quadArray (N : ℕ) (β₁ β₂ κ₁ κ₂ : ℝ) : Coefficients N where
  a n := 1 - (β₁ * n + β₂ * (n.choose 2 : ℝ)) - (κ₁ * n + κ₂ * (n.choose 2 : ℝ))
  b n := β₁ * n + β₂ * (n.choose 2 : ℝ)
  c n := κ₁ * n + κ₂ * (n.choose 2 : ℝ)

theorem quadArray_admissible3 (β₁ β₂ κ₁ κ₂ : ℝ) (hsum : 3 * β₁ + 3 * β₂ + 3 * κ₁ + 3 * κ₂ = 1)
    (ha1 : 0 < 1 - β₁ - κ₁) (ha2 : 0 < 1 - (2 * β₁ + β₂) - (2 * κ₁ + κ₂)) (hc1 : 0 < κ₁)
    (hc2 : 0 < 2 * κ₁ + κ₂) (hc3 : 0 < 3 * κ₁ + 3 * κ₂) : Admissible (quadArray 3 β₁ β₂ κ₁ κ₂) := by
  refine ⟨by norm_num, by simp [quadArray], by simp [quadArray], by simp [quadArray], ?_,
    fun i _ => by simp only [quadArray]; ring, fun i hi => ?_, fun i hi hi3 => ?_⟩
  · simp only [quadArray]; norm_num [Nat.choose]; linarith
  · interval_cases i <;> simp only [quadArray] <;> norm_num [Nat.choose] <;> linarith
  · interval_cases i <;> simp only [quadArray] <;> norm_num [Nat.choose] <;> linarith

theorem quad_g_ncconv : productMatrix (quadArray 3 (1 / 57) (2 / 19) (17 / 57) (-5 / 57)) 3 3 3 < 0 := by
  simp only [productMatrix, matrixPair, quadArray]
  simp [Matrix.mul_apply, Fin.sum_univ_four, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
    recurrenceMatrix, Nat.choose]
  norm_num

theorem quad_g_ndconv : productMatrix (quadArray 3 (1 / 3) (-2 / 13) (5 / 39) (1 / 39)) 3 3 3 < 0 := by
  simp only [productMatrix, matrixPair, quadArray]
  simp [Matrix.mul_apply, Fin.sum_univ_four, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
    recurrenceMatrix, Nat.choose]
  norm_num

theorem quad_g_nbmono : productMatrix (quadArray 3 (1 / 5) (-1 / 5) (2 / 15) (1 / 5)) 3 3 3 < 0 := by
  simp only [productMatrix, matrixPair, quadArray]
  simp [Matrix.mul_apply, Fin.sum_univ_four, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
    recurrenceMatrix, Nat.choose]
  norm_num

/-- **P2, after Proposition 3.3**: each hypothesis of Proposition 3.3 is needed. -/
theorem quadratic_hypotheses_needed :
    -- `κ₂ ≥ 0` dropped
    (Admissible (quadArray 3 (1 / 57) (2 / 19) (17 / 57) (-5 / 57)) ∧ (-5 / 57 : ℝ) < 0 ∧
      (0 : ℝ) ≤ -5 / 57 + 2 / 19 ∧
      (∀ n, n < 3 → (quadArray 3 (1 / 57) (2 / 19) (17 / 57) (-5 / 57)).b n ≤
        (quadArray 3 (1 / 57) (2 / 19) (17 / 57) (-5 / 57)).b (n + 1)) ∧
      productMatrix (quadArray 3 (1 / 57) (2 / 19) (17 / 57) (-5 / 57)) 3 3 3 < 0) ∧
    -- `κ₂ + β₂ ≥ 0` dropped
    (Admissible (quadArray 3 (1 / 3) (-2 / 13) (5 / 39) (1 / 39)) ∧ (0 : ℝ) ≤ 1 / 39 ∧
      (1 / 39 + -2 / 13 : ℝ) < 0 ∧
      (∀ n, n < 3 → (quadArray 3 (1 / 3) (-2 / 13) (5 / 39) (1 / 39)).b n ≤
        (quadArray 3 (1 / 3) (-2 / 13) (5 / 39) (1 / 39)).b (n + 1)) ∧
      productMatrix (quadArray 3 (1 / 3) (-2 / 13) (5 / 39) (1 / 39)) 3 3 3 < 0) ∧
    -- `b` nondecreasing dropped
    (Admissible (quadArray 3 (1 / 5) (-1 / 5) (2 / 15) (1 / 5)) ∧ (0 : ℝ) ≤ 1 / 5 ∧ (0 : ℝ) ≤ 1 / 5 + -1 / 5 ∧
      (quadArray 3 (1 / 5) (-1 / 5) (2 / 15) (1 / 5)).b 3 < (quadArray 3 (1 / 5) (-1 / 5) (2 / 15) (1 / 5)).b 2 ∧
      productMatrix (quadArray 3 (1 / 5) (-1 / 5) (2 / 15) (1 / 5)) 3 3 3 < 0) := by
  refine ⟨⟨quadArray_admissible3 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num), by norm_num, by norm_num, fun n hn => ?_, quad_g_ncconv⟩,
    ⟨quadArray_admissible3 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num), by norm_num, by norm_num, fun n hn => ?_, quad_g_ndconv⟩,
    ⟨quadArray_admissible3 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num), by norm_num, by norm_num, ?_, quad_g_nbmono⟩⟩
  · interval_cases n <;> simp only [quadArray] <;> norm_num [Nat.choose]
  · interval_cases n <;> simp only [quadArray] <;> norm_num [Nat.choose]
  · simp only [quadArray]; norm_num [Nat.choose]

end Szkraw
