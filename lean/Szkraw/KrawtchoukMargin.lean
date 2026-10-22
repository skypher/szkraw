import Szkraw.BooleanMargin
import Szkraw.BooleanMatrix
import Szkraw.PerturbationAssembly

namespace Szkraw

theorem kraw_triangle_margin : Stmt_kraw_triangle_margin := by
  intro N hN r hr hr1 m n k hm ht
  have hn : n.val ≤ N := by omega
  have hk : k.val ≤ N := by omega
  obtain ⟨b,hb,hpos⟩ := boolean_margin_exists r hr hr1 N m n.val k.val hm hn hk ht
  have hcoord := boolean_matrix_coefficient N hN r hr hr1.le m hm n k b hb
  have hB := kraw_matrix_positivity N hN r hr (le_of_lt hr1) m hm n k
  have hs : 0 ≤ min r (1-r) := le_min (le_of_lt hr) (by linarith)
  have hc0 : 0 ≤ booleanProduct r N m n.val b := (pow_nonneg hs N).trans hpos
  have hck : 1 ≤ (N.choose k.val : ℝ) := by exact_mod_cast (Nat.choose_pos hk)
  have hcm : (N.choose m : ℝ) ≤ (2 : ℝ)^N := by exact_mod_cast Nat.choose_le_two_pow N m
  have hcn : (N.choose n.val : ℝ) ≤ (2 : ℝ)^N := by exact_mod_cast Nat.choose_le_two_pow N n.val
  have hd : (N.choose m : ℝ)*(N.choose n.val : ℝ) ≤ (4 : ℝ)^N := by
    calc
      _ ≤ (2 : ℝ)^N*2^N := mul_le_mul hcm hcn (by positivity) (by positivity)
      _ = _ := by rw [←mul_pow]; norm_num
  have hbound : (min r (1-r))^N ≤ productMatrix (krawCoefficients N r) m n k*(4 : ℝ)^N := by
    calc
      _ ≤ booleanProduct r N m n.val b := hpos
      _ ≤ booleanProduct r N m n.val b*(N.choose k.val : ℝ) := le_mul_of_one_le_right hc0 hck
      _ = productMatrix (krawCoefficients N r) m n k*(N.choose m : ℝ)*(N.choose n.val : ℝ) := hcoord
      _ ≤ _ := by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hd hB
  rw [div_pow]
  exact (div_le_iff₀ (by positivity : (0 : ℝ) < 4^N)).mpr hbound

/-- The full quantitative perturbation theorem, including realization and exact support. -/
theorem perturbation_criterion : Stmt_perturbation :=
  perturbation_assembly kraw_triangle_margin

theorem perturbation_matrix_positivity : Stmt_perturbation_matrix := by
  intro N v r hv hr hr1 hc
  exact (perturbation_criterion N v r hv hr hr1 hc).2.1

end Szkraw
