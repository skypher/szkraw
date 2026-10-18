import Szkraw.Geometric
import Szkraw.ErrorNorm

open scoped Matrix.Norms.Operator

namespace Szkraw

noncomputable def krawCoefficients (N : ℕ) (r : ℝ) : Coefficients N where
  a i := ((N : ℝ)-i)/N
  b i := (1-r)*i/N
  c i := r*i/N

theorem qInteger_at_one (n : ℕ) : qInteger 1 n = (n : ℝ) := by
  induction n with
  | zero => simp [qInteger]
  | succ n ih => simp [qInteger,ih,Nat.cast_add,Nat.cast_one]

theorem kraw_geometric_prefix (N : ℕ) (r : ℝ) (hr : 0 < r) (i : ℕ) (hi : i ≤ N) :
    (krawCoefficients N r).a i = (geometricCoefficients N (1/r) 1).a i ∧
    (krawCoefficients N r).b i = (geometricCoefficients N (1/r) 1).b i ∧
    (krawCoefficients N r).c i = (geometricCoefficients N (1/r) 1).c i := by
  simp only [krawCoefficients,geometricCoefficients,qInteger_at_one,one_pow,one_mul,Nat.cast_sub hi]
  constructor
  · trivial
  constructor <;> field_simp [ne_of_gt hr] <;> ring

theorem kraw_admissible (N : ℕ) (hN : 1 ≤ N) (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1) :
    Admissible (krawCoefficients N r) := by
  have hn : 0 < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  refine ⟨hN,?_,?_,?_,?_,?_,?_,?_⟩
  · simp [krawCoefficients,ne_of_gt hn]
  · simp [krawCoefficients]
  · simp [krawCoefficients]
  · simp [krawCoefficients]
  · intro i hi
    dsimp [krawCoefficients]
    field_simp
    ring
  · intro i hi
    apply div_pos _ hn
    exact sub_pos.mpr (by exact_mod_cast hi)
  · intro i hi _
    exact div_pos (mul_pos hr (by exact_mod_cast hi)) hn

theorem kraw_matrix_positivity (N : ℕ) (hN : 1 ≤ N) (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1) :
    MatrixPositivity (krawCoefficients N r) := by
  have hp : 1 ≤ 1/r := (le_div_iff₀ hr).mpr (by linarith)
  have hpos := geometric_family_matrix_positivity N hN (1/r) 1 hp le_rfl
  intro m hm i j
  rw [product_matrix_congr _ _ (kraw_geometric_prefix N r hr) m (by omega)]
  exact hpos m hm i j

theorem kraw_product_norm (N : ℕ) (hN : 1 ≤ N) (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1)
    (m : ℕ) (hm : m ≤ N) : ‖productMatrix (krawCoefficients N r) m‖ ≤ 1 := by
  exact stochastic_norm_le _ (kraw_matrix_positivity N hN r hr hr1 m hm)
    (fun i => product_row_sum _ (kraw_admissible N hN r hr hr1) m hm i)

end Szkraw
