import Szkraw.Krawtchouk

namespace Szkraw

/-- Coefficients in the squarefree y-basis, where y=r z and y²=(1-r)y+r. -/
noncomputable def booleanProduct (r : ℝ) (N m n : ℕ) (b : Fin N → Bool) : ℝ :=
  r^(m+n) / r^(bitsWeight N b) *
    coordinate (1/r) 1 N (elementary (1/r) 1 N m * elementary (1/r) 1 N n) b

theorem boolean_product_nonneg (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1)
    (N m n : ℕ) (b : Fin N → Bool) : 0 ≤ booleanProduct r N m n b := by
  have hp : 1 ≤ 1/r := (le_div_iff₀ hr).mpr (by linarith)
  apply mul_nonneg (div_nonneg (pow_nonneg (le_of_lt hr) _) (pow_nonneg (le_of_lt hr) _))
  exact coordinate_nonneg (1/r) 1 N _
    (tower_mul_nonneg (1/r) 1 hp le_rfl N _ _
      (elementary_nonneg _ _ _ _) (elementary_nonneg _ _ _ _)) b

theorem boolean_product_zero_left (r : ℝ) (hr : 0 < r) (N n : ℕ) (b : Fin N → Bool) :
    booleanProduct r N 0 n b = if n = bitsWeight N b then 1 else 0 := by
  simp only [booleanProduct,zero_add,elementary_zero,one_mul,coordinate_elementary]
  split_ifs with h
  · rw [h]
    simp [ne_of_gt hr]
  · simp

theorem boolean_product_comm (r : ℝ) (N m n : ℕ) (b : Fin N → Bool) :
    booleanProduct r N m n b = booleanProduct r N n m b := by
  simp only [booleanProduct,Nat.add_comm,mul_comm]

theorem boolean_product_false (r : ℝ) (hr : 0 < r)
    (N m n : ℕ) (b : Fin N → Bool) :
    booleanProduct r (N+1) (m+1) (n+1) (Fin.cons false b) =
      booleanProduct r N (m+1) (n+1) b + r*booleanProduct r N m n b := by
  have hre : (elementary (1/r) 1 (N+1) (m+1)*elementary (1/r) 1 (N+1) (n+1)).re =
      elementary (1/r) 1 N (m+1)*elementary (1/r) 1 N (n+1) +
        (1/r) • (elementary (1/r) 1 N m*elementary (1/r) 1 N n) := by
    simp only [elementary,QuadraticAlgebra.re_mul]
    simp only [one_pow,mul_one,Algebra.algebraMap_eq_smul_one,smul_mul_assoc,one_mul]
  simp only [booleanProduct,bitsWeight,Fin.cons_zero,Bool.false_eq_true,ite_false,zero_add,
    coordinate,Fin.tail_cons,hre,coordinate_add,coordinate_smul]
  have hp : r^(bitsWeight N b) ≠ 0 := pow_ne_zero _ (ne_of_gt hr)
  simp only [pow_add,pow_succ]
  field_simp

theorem boolean_product_true (r : ℝ) (hr : 0 < r)
    (N m n : ℕ) (b : Fin N → Bool) :
    booleanProduct r (N+1) (m+1) (n+1) (Fin.cons true b) =
      booleanProduct r N (m+1) n b + booleanProduct r N m (n+1) b +
        (1-r)*booleanProduct r N m n b := by
  have him : (elementary (1/r) 1 (N+1) (m+1)*elementary (1/r) 1 (N+1) (n+1)).im =
      elementary (1/r) 1 N (m+1)*elementary (1/r) 1 N n +
      elementary (1/r) 1 N m*elementary (1/r) 1 N (n+1) +
        (1/r-1) • (elementary (1/r) 1 N m*elementary (1/r) 1 N n) := by
    simp only [elementary,QuadraticAlgebra.im_mul]
    simp only [sub_self,zero_smul,zero_add,Algebra.algebraMap_eq_smul_one,smul_mul_assoc,one_mul]
  simp only [booleanProduct,bitsWeight,Fin.cons_zero,ite_true,coordinate,Fin.tail_cons,
    him,coordinate_add,coordinate_smul]
  have hp : r^(bitsWeight N b) ≠ 0 := pow_ne_zero _ (ne_of_gt hr)
  rw [pow_add r 1 (bitsWeight N b)]
  simp only [pow_one,pow_succ]
  field_simp
  ring

end Szkraw
