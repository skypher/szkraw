import Szkraw.RowAction
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Tactic.FieldSimp

namespace Szkraw

noncomputable def reversibleWeight {N : ℕ} (v : Coefficients N) : ℕ → ℝ
  | 0 => 1
  | i+1 => reversibleWeight v i * v.a i / v.c (i+1)

theorem reversible_weight_pos {N : ℕ} (v : Coefficients N) (hv : Admissible v)
    (i : ℕ) (hi : i ≤ N) : 0 < reversibleWeight v i := by
  rcases hv with ⟨hN,ha0,hb0,hc0,haN,hsum,hapos,hcpos⟩
  induction i with
  | zero => norm_num [reversibleWeight]
  | succ i ih =>
      rw [reversibleWeight]
      exact div_pos (mul_pos (ih (by omega)) (hapos i (by omega)))
        (hcpos (i+1) (by omega) hi)

theorem reversible_weight_step {N : ℕ} (v : Coefficients N) (hv : Admissible v)
    (i : ℕ) (hi : i < N) :
    reversibleWeight v i*v.a i = reversibleWeight v (i+1)*v.c (i+1) := by
  have hc := hv.2.2.2.2.2.2.2 (i+1) (by omega) (by omega)
  rw [reversibleWeight]
  field_simp [ne_of_gt hc]

theorem detailed_balance_forward {N : ℕ} (v : Coefficients N) (hv : Admissible v)
    (i j : Fin (N+1)) (hf : j.val = i.val+1) :
    reversibleWeight v i.val*recurrenceMatrix v i j =
      reversibleWeight v j.val*recurrenceMatrix v j i := by
  have hr : i.val ≠ j.val+1 := by omega
  have hn : i ≠ j := by intro h; have := congrArg Fin.val h; omega
  simp only [recurrenceMatrix,if_pos hf,if_neg hr,if_neg hn]
  rw [hf]
  exact reversible_weight_step v hv i.val (by have := j.isLt; omega)

theorem detailed_balance {N : ℕ} (v : Coefficients N) (hv : Admissible v)
    (i j : Fin (N+1)) :
    reversibleWeight v i.val*recurrenceMatrix v i j =
      reversibleWeight v j.val*recurrenceMatrix v j i := by
  by_cases hf : j.val = i.val+1
  · exact detailed_balance_forward v hv i j hf
  · by_cases he : j = i
    · subst j; rfl
    · by_cases hr : i.val = j.val+1
      · exact (detailed_balance_forward v hv j i hr).symm
      · have he' : i ≠ j := Ne.symm he
        simp only [recurrenceMatrix,if_neg hf,if_neg hr,if_neg he,if_neg he',mul_zero]

noncomputable def symmetrizedMatrix {N : ℕ} (v : Coefficients N) :
    Matrix (Fin (N+1)) (Fin (N+1)) ℝ := fun i j =>
  Real.sqrt (reversibleWeight v i.val) * recurrenceMatrix v i j /
    Real.sqrt (reversibleWeight v j.val)

theorem symmetrized_matrix_hermitian {N : ℕ} (v : Coefficients N) (hv : Admissible v) :
    (symmetrizedMatrix v).IsHermitian := by
  apply Matrix.isHermitian_iff_isSymm.mpr
  ext i j
  have hi : 0 < reversibleWeight v i.val := reversible_weight_pos v hv i.val (by omega)
  have hj : 0 < reversibleWeight v j.val := reversible_weight_pos v hv j.val (by omega)
  have hsi := Real.sqrt_pos.mpr hi
  have hsj := Real.sqrt_pos.mpr hj
  change Real.sqrt (reversibleWeight v j.val)*recurrenceMatrix v j i /
      Real.sqrt (reversibleWeight v i.val) =
    Real.sqrt (reversibleWeight v i.val)*recurrenceMatrix v i j /
      Real.sqrt (reversibleWeight v j.val)
  apply (div_eq_div_iff (ne_of_gt hsi) (ne_of_gt hsj)).2
  have hsq_i := Real.sq_sqrt (le_of_lt hi)
  have hsq_j := Real.sq_sqrt (le_of_lt hj)
  have hd := detailed_balance v hv i j
  calc
    _ = (Real.sqrt (reversibleWeight v j.val))^2*recurrenceMatrix v j i := by ring
    _ = reversibleWeight v j.val*recurrenceMatrix v j i := by rw [hsq_j]
    _ = reversibleWeight v i.val*recurrenceMatrix v i j := hd.symm
    _ = (Real.sqrt (reversibleWeight v i.val))^2*recurrenceMatrix v i j := by rw [hsq_i]
    _ = _ := by ring

end Szkraw
