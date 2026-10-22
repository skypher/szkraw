import Szkraw.BinomialNormalization

namespace Szkraw

/-- Identify the selected Boolean coordinate with the actual finite product coefficient. -/
theorem boolean_matrix_coefficient (N : ℕ) (hN : 1 ≤ N) (r : ℝ)
    (hr : 0 < r) (hr1 : r ≤ 1) (m : ℕ) (hm : m ≤ N)
    (n k : Fin (N+1)) (b : Fin N → Bool) (hb : bitsWeight N b = k.val) :
    booleanProduct r N m n.val b * (N.choose k.val : ℝ) =
      productMatrix (krawCoefficients N r) m n k * (N.choose m : ℝ) * (N.choose n.val : ℝ) := by
  let p := 1/r
  let v := geometricCoefficients N p 1
  let U := normalizedElementary p 1 N
  let X := U 1
  have hp : 1 ≤ p := (le_div_iff₀ hr).mpr (by linarith)
  have hv : Admissible v := geometric_coefficients_admissible N hN p 1 hp le_rfl
  have heval : Polynomial.aeval X (recurrencePolynomial v m) = U m :=
    recurrence_evaluation v hv U X (normalized_elementary_zero p 1 N) rfl
      (fun j hj => normalized_three_term p 1 hp le_rfl N j (by omega)) m hm
  have hrep := representation_product v (fun j : Fin (N+1) => U j.val) X
    (geometric_row_action p 1 hp le_rfl N hN) m n
  rw [heval] at hrep
  have hcoord := congrArg (fun z => coordinate p 1 N z b) hrep
  have hnN : n.val ≤ N := by omega
  have hkN : k.val ≤ N := by omega
  have hU (j : ℕ) : U j = (normalizer p 1 N j)⁻¹ • elementary p 1 N j := rfl
  simp only [hU,smul_mul_smul,coordinate_smul,coordinate_sum,coordinate_elementary,hb] at hcoord
  have hsum : (∑ j : Fin (N+1), productMatrix v m n j *
      ((normalizer p 1 N j.val)⁻¹ * if j.val = k.val then 1 else 0)) =
      productMatrix v m n k * (normalizer p 1 N k.val)⁻¹ := by
    simp [Fin.val_inj]
  rw [hsum] at hcoord
  have hcongr := product_matrix_congr (krawCoefficients N r) v
    (kraw_geometric_prefix N r hr) m (by omega)
  rw [←hcongr] at hcoord
  dsimp [p] at hcoord
  rw [inverse_kraw_normalizer r hr N m hm,inverse_kraw_normalizer r hr N n.val hnN,
    inverse_kraw_normalizer r hr N k.val hkN] at hcoord
  have hcm : (N.choose m : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hm).ne'
  have hcn : (N.choose n.val : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hnN).ne'
  have hck : (N.choose k.val : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hkN).ne'
  have hrk : r^k.val ≠ 0 := pow_ne_zero _ (ne_of_gt hr)
  unfold booleanProduct
  rw [hb,pow_add]
  field_simp at hcoord ⊢
  nlinarith [hcoord]

end Szkraw
