import Szkraw.Statements
import Szkraw.LCSequences
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

/-- Theorem 8.1 in the form of the geometric criterion: finite realization (orthogonality
measure, terminal relation, product identities) together with matrix positivity. -/
def Stmt_logconcave : Prop :=
  ∀ (N : ℕ) (v : Coefficients N), Admissible v → ConstantRatioLogConcave v →
    FiniteRealization v ∧ MatrixPositivity v

end Szkraw

namespace Szkraw

/-- The padded Newton sequence `(0, ν 1, …, ν N, 0, …)`. -/
noncomputable def padNewton (N : ℕ) (ν : ℕ → ℝ) (i : ℕ) : ℝ := if 1 ≤ i ∧ i ≤ N then ν i else 0

theorem padNewton_lcnz {N : ℕ} {ν : ℕ → ℝ} (h : LogConcaveNoInternalZeros N ν) :
    LCNZ (padNewton N ν) := by
  obtain ⟨h1, hnn, hlc, hz⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · intro i; unfold padNewton; split_ifs with hi
    · exact hnn i hi.1 hi.2
    · exact le_rfl
  · intro i
    unfold padNewton
    by_cases hi0 : i = 0
    · subst hi0; simp only [Nat.one_le_iff_ne_zero, ne_eq, not_true_eq_false, false_and, if_false,
        zero_mul]; positivity
    by_cases hiN : i + 2 ≤ N
    · rw [if_pos ⟨by omega, by omega⟩, if_pos ⟨by omega, by omega⟩, if_pos ⟨by omega, by omega⟩]
      have := hlc (i + 1) (by omega) (by omega)
      simpa using this
    · rw [if_neg (by omega : ¬(1 ≤ i + 2 ∧ i + 2 ≤ N)), mul_zero]; positivity
  · intro i j k hij hjk hi hk
    unfold padNewton at *
    split_ifs at hi with hi'
    swap; · exact absurd hi (lt_irrefl 0)
    split_ifs at hk with hk'
    swap; · exact absurd hk (lt_irrefl 0)
    rw [if_pos ⟨by omega, by omega⟩]
    -- ν j > 0: otherwise ν vanishes from j on, contradicting ν k > 0
    by_contra hj
    have hj0 : ν j = 0 := le_antisymm (not_lt.mp hj) (hnn j (by omega) (by omega))
    have : ∀ m, j ≤ m → m ≤ N → ν m = 0 := by
      intro m hjm hmN
      induction m with
      | zero => omega
      | succ m ih =>
        rcases Nat.eq_or_lt_of_le hjm with e | e
        · rw [← e]; exact hj0
        · exact hz m (by omega) (by omega) (ih (by omega) (by omega))
    rw [this k hjk hk'.2] at hk; exact lt_irrefl 0 hk

end Szkraw
