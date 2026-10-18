import Szkraw.PerturbationRadius
import Szkraw.RecurrenceNorm

open scoped Matrix.Norms.Operator

namespace Szkraw

/-- The full paper error estimate under its original scalar coefficient hypotheses. -/
theorem perturbation_matrix_error {N : ℕ} (v : Coefficients N) (hv : Admissible v)
    (r : ℝ) (hr : 0 < r) (hr1 : r < 1) (hclose : CloseToKrawtchouk v r)
    (m : ℕ) (hm : 1 ≤ m) (hmN : m ≤ N) :
    ‖productMatrix v m-productMatrix (krawCoefficients N r) m‖ ≤
      perturbationRadius N r*(8*N)^m := by
  let u := krawCoefficients N r
  have hu : Admissible u := kraw_admissible N hv.1 r hr (le_of_lt hr1)
  have hη := perturbation_radius_nonneg N hv.1 r hr hr1
  have hc : ∀ i, i ≤ N → |v.a i-u.a i| ≤ perturbationRadius N r ∧
      |v.b i-u.b i| ≤ perturbationRadius N r ∧ |v.c i-u.c i| ≤ perturbationRadius N r :=
    hclose.2
  apply matrix_error_amplification u v hu hv _ hη
    (admissible_recurrence_norm v hv hclose.1)
    (recurrence_difference_norm u v _ hη hc)
    (fun i hi => ⟨hclose.1 i hi,(admissible_sign_bounds v hv hclose.1 i hi).2.2.1⟩)
    (fun i hi => (admissible_sign_bounds v hv hclose.1 i hi).2.2.2) hc
    (close_leading_lower v hv r hr hr1 hclose)
    (kraw_product_norm N hv.1 r hr (le_of_lt hr1)) m hm hmN

theorem perturbation_amplified_radius (N : ℕ) (hN : 1 ≤ N) (r : ℝ) :
    perturbationRadius N r*(8*N)^N = (1/2 : ℝ)*(min r (1-r)/4)^N := by
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  unfold perturbationRadius
  rw [mul_assoc,←mul_pow]
  congr 2
  field_simp
  ring

/-- Every actual finite product entry stays within half the reference margin. -/
theorem perturbation_entry_error {N : ℕ} (v : Coefficients N) (hv : Admissible v)
    (r : ℝ) (hr : 0 < r) (hr1 : r < 1) (hclose : CloseToKrawtchouk v r)
    (m : ℕ) (hmN : m ≤ N) (i j : Fin (N+1)) :
    |productMatrix v m i j-productMatrix (krawCoefficients N r) m i j| ≤
      (1/2 : ℝ)*(min r (1-r)/4)^N := by
  by_cases hm : m = 0
  · subst m
    simp only [productMatrix,matrixPair,sub_self,abs_zero]
    have hs : 0 ≤ min r (1-r) := le_min (le_of_lt hr) (by linarith)
    positivity
  · have he := perturbation_matrix_error v hv r hr hr1 hclose m (by omega) hmN
    have hentry := entry_le_row_norm
      (productMatrix v m-productMatrix (krawCoefficients N r) m) i j
    simp only [Matrix.sub_apply] at hentry
    have hn : 1 ≤ 8*(N : ℝ) := by
      have hh : 1 ≤ (N : ℝ) := by exact_mod_cast hv.1
      linarith
    have hp := pow_le_pow_right₀ hn hmN
    have hη := perturbation_radius_nonneg N hv.1 r hr hr1
    calc
      _ ≤ _ := hentry.trans he
      _ ≤ perturbationRadius N r*(8*N)^N := mul_le_mul_of_nonneg_left hp hη
      _ = _ := perturbation_amplified_radius N hv.1 r

end Szkraw
