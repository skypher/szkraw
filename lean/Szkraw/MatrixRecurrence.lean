import Szkraw.Representation

namespace Szkraw

theorem product_next {N : ℕ} (v : Coefficients N) (k : ℕ) :
    productMatrix v (k+2) = (v.a (k+1))⁻¹ •
      ((recurrenceMatrix v - v.b (k+1) • (1 : Matrix _ _ ℝ))*productMatrix v (k+1) -
        v.c (k+1) • productMatrix v k) := rfl

theorem product_recurrence {N : ℕ} (v : Coefficients N) (hv : Admissible v)
    (k : ℕ) (hk : k+1 < N) :
    v.a (k+1) • productMatrix v (k+2) =
      (recurrenceMatrix v - v.b (k+1) • (1 : Matrix _ _ ℝ))*productMatrix v (k+1) -
        v.c (k+1) • productMatrix v k := by
  rw [product_next,smul_smul,mul_inv_cancel₀ (ne_of_gt (hv.2.2.2.2.2.2.1 (k+1) hk)),one_smul]

/-- Exact subtraction identity used before taking the maximum row-sum norm. -/
theorem product_difference_recurrence {N : ℕ} (v w : Coefficients N)
    (hv : Admissible v) (hw : Admissible w) (k : ℕ) (hk : k+1 < N) :
    w.a (k+1) • (productMatrix w (k+2)-productMatrix v (k+2)) =
      (recurrenceMatrix w-w.b (k+1) • (1 : Matrix _ _ ℝ)) *
        (productMatrix w (k+1)-productMatrix v (k+1)) -
      w.c (k+1) • (productMatrix w k-productMatrix v k) +
      (recurrenceMatrix w-recurrenceMatrix v -
        (w.b (k+1)-v.b (k+1)) • (1 : Matrix _ _ ℝ))*productMatrix v (k+1) -
      (w.c (k+1)-v.c (k+1)) • productMatrix v k -
      (w.a (k+1)-v.a (k+1)) • productMatrix v (k+2) := by
  have h1 := product_recurrence v hv k hk
  have h2 := product_recurrence w hw k hk
  rw [smul_sub,h2]
  simp only [Matrix.mul_sub,Matrix.sub_mul,Matrix.smul_mul,Matrix.one_mul,sub_smul] at *
  have ha : w.a (k+1) • productMatrix v (k+2) =
      (w.a (k+1)-v.a (k+1)) • productMatrix v (k+2) +
      (recurrenceMatrix v*productMatrix v (k+1)-v.b (k+1) • productMatrix v (k+1)-
        v.c (k+1) • productMatrix v k) := by
    rw [←h1]
    module
  conv_lhs => rw [ha]
  module

end Szkraw
