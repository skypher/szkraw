import Szkraw.Statements
import Mathlib.Algebra.Polynomial.AlgebraMap

namespace Szkraw

theorem pair_matrix_aeval {N : ℕ} (v : Coefficients N) (m : ℕ) :
    matrixPair v m =
      (Polynomial.aeval (recurrenceMatrix v) (polynomialPair v m).1,
       Polynomial.aeval (recurrenceMatrix v) (polynomialPair v m).2) := by
  induction m with
  | zero => simp [matrixPair, polynomialPair]
  | succ m ih =>
    simp only [matrixPair, polynomialPair]
    rw [ih]
    simp only [map_mul, map_sub, Polynomial.aeval_C, Polynomial.aeval_X]
    simp only [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]

theorem product_matrix_aeval {N : ℕ} (v : Coefficients N) (m : ℕ) :
    productMatrix v m = Polynomial.aeval (recurrenceMatrix v) (recurrencePolynomial v m) := by
  exact congrArg Prod.snd (pair_matrix_aeval v m)

end Szkraw
