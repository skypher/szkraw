import Szkraw.FiniteRealization
import Mathlib.Analysis.Matrix.Normed

open scoped Matrix.Norms.Operator

namespace Szkraw

theorem row_norm_le {N : ℕ} (M : Matrix (Fin (N+1)) (Fin (N+1)) ℝ)
    (c : ℝ) (hc : 0 ≤ c) (h : ∀ i, ∑ j, |M i j| ≤ c) : ‖M‖ ≤ c := by
  rw [Matrix.linfty_opNorm_def]
  have hh : (Finset.univ.sup fun i : Fin (N+1) => ∑ j, ‖M i j‖₊) ≤ (⟨c,hc⟩ : NNReal) := by
    apply Finset.sup_le
    intro i _
    apply NNReal.coe_le_coe.mp
    change (∑ j, ‖M i j‖₊ : NNReal).val ≤ c
    calc
      _ = ∑ j, ‖M i j‖ := NNReal.coe_sum _ _
      _ ≤ c := by simpa only [Real.norm_eq_abs] using h i
  exact_mod_cast hh

theorem stochastic_norm_le {N : ℕ} (M : Matrix (Fin (N+1)) (Fin (N+1)) ℝ)
    (hpos : ∀ i j, 0 ≤ M i j) (hsum : ∀ i, ∑ j, M i j = 1) : ‖M‖ ≤ 1 := by
  apply row_norm_le M 1 (by norm_num)
  intro i
  simp_rw [abs_of_nonneg (hpos i _)]
  exact le_of_eq (hsum i)

theorem entry_le_row_norm {N : ℕ} (M : Matrix (Fin (N+1)) (Fin (N+1)) ℝ)
    (i j : Fin (N+1)) : |M i j| ≤ ‖M‖ := by
  rw [Matrix.linfty_opNorm_def]
  have h1 : ‖M i j‖₊ ≤ ∑ k : Fin (N+1), ‖M i k‖₊ :=
    Finset.single_le_sum (f := fun k : Fin (N+1) => ‖M i k‖₊) (fun _ _ => by positivity) (Finset.mem_univ j)
  have h2 : (∑ k : Fin (N+1), ‖M i k‖₊) ≤
      Finset.univ.sup (fun k : Fin (N+1) => ∑ j, ‖M k j‖₊) :=
    Finset.le_sup (f := fun k : Fin (N+1) => ∑ j, ‖M k j‖₊) (Finset.mem_univ i)
  have h := h1.trans h2
  exact_mod_cast h

end Szkraw
