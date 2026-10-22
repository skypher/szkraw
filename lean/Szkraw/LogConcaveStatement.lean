import Szkraw.Statements
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Choose.Basic

/-!
# Statement of the log-concave Newton criterion (paper, Theorem 8.1)

The profile of an array is `d i = b i + c i`. Its Newton coefficients are the forward
differences at zero, `ν k = Δ^k d 0`. The criterion assumes a constant ratio
`c i = r * d i` and Newton coefficients that are nonnegative and log-concave without
internal zeros.
-/

namespace Szkraw

open Finset

/-- The profile `d i = b i + c i` of an array. -/
def profile {N : ℕ} (v : Coefficients N) (i : ℕ) : ℝ := v.b i + v.c i

/-- Newton coefficients `ν k = Σ_{i ≤ k} (-1)^(k-i) C(k,i) d i`, i.e. `Δ^k d (0)`. -/
noncomputable def newtonCoeff (d : ℕ → ℝ) (k : ℕ) : ℝ :=
  ∑ i ∈ range (k + 1), (-1 : ℝ) ^ (k - i) * (k.choose i : ℝ) * d i

/-- `(ν k)_{1 ≤ k ≤ N}` is nonnegative and log-concave without internal zeros, with `ν 1 > 0`. -/
def LogConcaveNoInternalZeros (N : ℕ) (ν : ℕ → ℝ) : Prop :=
  0 < ν 1 ∧
  (∀ k, 1 ≤ k → k ≤ N → 0 ≤ ν k) ∧
  (∀ k, 2 ≤ k → k + 1 ≤ N → ν (k - 1) * ν (k + 1) ≤ ν k ^ 2) ∧
  (∀ k, 1 ≤ k → k < N → ν k = 0 → ν (k + 1) = 0)

/-- Hypotheses of Theorem 8.1: constant ratio `c i = r d i` with `0 < r ≤ 1`, and a profile
whose Newton coefficients are log-concave without internal zeros. -/
def ConstantRatioLogConcave {N : ℕ} (v : Coefficients N) : Prop :=
  ∃ r : ℝ, 0 < r ∧ r ≤ 1 ∧
    (∀ i, i ≤ N → v.c i = r * profile v i) ∧
    LogConcaveNoInternalZeros N (newtonCoeff (profile v))

/-- Theorem 8.1 (log-concave Newton criterion), matrix-positivity conclusion: every
linearization coefficient `g(m,n;k) = productMatrix v m n k` is nonnegative. -/
def Stmt_logconcave_matrix : Prop :=
  ∀ (N : ℕ) (v : Coefficients N), Admissible v → ConstantRatioLogConcave v →
    MatrixPositivity v

end Szkraw
