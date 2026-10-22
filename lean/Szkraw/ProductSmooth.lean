import Szkraw.Statements
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Smooth dependence of the product coefficients on the recurrence coefficients

If the coefficients of an array depend `C^n` on a parameter and the upward coefficients
`a_0, …, a_{m-1}` do not vanish at a point, then every entry of `productMatrix v m`, that is every
`g(m, n; k)`, is `C^n` at that point.
-/

namespace Szkraw

open Finset

variable {N : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : WithTop ℕ∞}
  (v : E → Coefficients N) (x : E)

theorem recurrenceMatrix_contDiffAt
    (ha : ∀ i, ContDiffAt ℝ n (fun p => (v p).a i) x) (hb : ∀ i, ContDiffAt ℝ n (fun p => (v p).b i) x)
    (hc : ∀ i, ContDiffAt ℝ n (fun p => (v p).c i) x) (i j : Fin (N + 1)) :
    ContDiffAt ℝ n (fun p => recurrenceMatrix (v p) i j) x := by
  simp only [recurrenceMatrix]
  split_ifs
  exacts [ha _, hb _, hc _, contDiffAt_const]

theorem matrixPair_contDiffAt
    (ha : ∀ i, ContDiffAt ℝ n (fun p => (v p).a i) x) (hb : ∀ i, ContDiffAt ℝ n (fun p => (v p).b i) x)
    (hc : ∀ i, ContDiffAt ℝ n (fun p => (v p).c i) x) :
    ∀ m, (∀ i, i < m → (v x).a i ≠ 0) → ∀ i j : Fin (N + 1),
      ContDiffAt ℝ n (fun p => (matrixPair (v p) m).1 i j) x ∧
        ContDiffAt ℝ n (fun p => (matrixPair (v p) m).2 i j) x
  | 0, _ => fun i j => by
    simp only [matrixPair, Matrix.zero_apply, Matrix.one_apply]
    exact ⟨contDiffAt_const, contDiffAt_const⟩
  | m + 1, hm => fun i j => by
    have ih := matrixPair_contDiffAt ha hb hc m (fun i hi => hm i (by omega))
    refine ⟨(ih i j).2, ?_⟩
    simp only [matrixPair, Matrix.smul_apply, Matrix.sub_apply, Matrix.mul_apply, smul_eq_mul,
      Matrix.one_apply]
    refine ((ha m).inv (hm m (by omega))).mul ((ContDiffAt.sum fun l _ => ?_).sub ((hc m).mul (ih i j).1))
    refine ((recurrenceMatrix_contDiffAt v x ha hb hc i l).sub ?_).mul (ih l j).2
    split_ifs
    · exact (hb m).mul contDiffAt_const
    · exact (hb m).mul contDiffAt_const

/-- Every `g(m, n; k)` depends `C^n` on the coefficients where `a_0, …, a_{m-1}` do not vanish. -/
theorem productMatrix_contDiffAt
    (ha : ∀ i, ContDiffAt ℝ n (fun p => (v p).a i) x) (hb : ∀ i, ContDiffAt ℝ n (fun p => (v p).b i) x)
    (hc : ∀ i, ContDiffAt ℝ n (fun p => (v p).c i) x) (m : ℕ) (hm : ∀ i, i < m → (v x).a i ≠ 0)
    (i j : Fin (N + 1)) :
    ContDiffAt ℝ n (fun p => productMatrix (v p) m i j) x :=
  (matrixPair_contDiffAt v x ha hb hc m hm i j).2

end Szkraw
