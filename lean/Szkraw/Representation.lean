import Szkraw.MatrixBridge
import Szkraw.NormalizedRecurrence
import Mathlib.Algebra.BigOperators.Module
import Mathlib.Tactic.Module

namespace Szkraw

theorem representation_power {ι A : Type*} [Fintype ι] [DecidableEq ι]
    [CommRing A] [Algebra ℝ A] (J : Matrix ι ι ℝ) (U : ι → A) (X : A)
    (hJ : ∀ i, X*U i = ∑ j, J i j • U j) (n : ℕ) (i : ι) :
    X^n*U i = ∑ j, (J^n) i j • U j := by
  induction n generalizing i with
  | zero => simp [Matrix.one_apply]
  | succ n ih =>
      calc
        X^(n+1)*U i = X^n*(X*U i) := by rw [pow_succ]; ring
        _ = X^n*(∑ j, J i j • U j) := by rw [hJ]
        _ = ∑ j, J i j • (X^n*U j) := by simp [Finset.mul_sum, Algebra.mul_smul_comm]
        _ = ∑ j, J i j • (∑ k, (J^n) j k • U k) := by simp_rw [ih]
        _ = ∑ j, (J^(n+1)) i j • U j := by
          simp only [Finset.smul_sum, smul_smul, pow_succ', Matrix.mul_apply, Finset.sum_smul]
          exact Finset.sum_comm

theorem representation_polynomial {ι A : Type*} [Fintype ι] [DecidableEq ι]
    [CommRing A] [Algebra ℝ A] (J : Matrix ι ι ℝ) (U : ι → A) (X : A)
    (hJ : ∀ i, X*U i = ∑ j, J i j • U j) (f : Polynomial ℝ) (i : ι) :
    Polynomial.aeval X f * U i = ∑ j, (Polynomial.aeval J f) i j • U j := by
  induction f using Polynomial.induction_on' with
  | add f g hf hg =>
      simp only [map_add, add_mul, Matrix.add_apply, add_smul, Finset.sum_add_distrib]
      rw [hf,hg]
  | monomial n r =>
      simp only [Polynomial.aeval_monomial, Algebra.algebraMap_eq_smul_one,
        smul_mul_assoc, one_mul, Matrix.smul_apply, smul_eq_mul]
      rw [representation_power J U X hJ]
      simp only [Finset.smul_sum, smul_smul, smul_eq_mul]

theorem representation_product {N : ℕ} {A : Type*} [CommRing A] [Algebra ℝ A]
    (v : Coefficients N) (U : Fin (N+1) → A) (X : A)
    (hJ : ∀ i, X*U i = ∑ j, recurrenceMatrix v i j • U j)
    (m : ℕ) (i : Fin (N+1)) :
    Polynomial.aeval X (recurrencePolynomial v m)*U i =
      ∑ j, productMatrix v m i j • U j := by
  rw [product_matrix_aeval]
  exact representation_polynomial (recurrenceMatrix v) U X hJ _ i

theorem recurrence_evaluation {N : ℕ} {A : Type*} [CommRing A] [Algebra ℝ A]
    (v : Coefficients N) (hv : Admissible v) (U : ℕ → A) (X : A)
    (h0 : U 0 = 1) (h1 : U 1 = X)
    (hrec : ∀ k, k+1 < N → X*U (k+1) =
      v.a (k+1) • U (k+2) + v.b (k+1) • U (k+1) + v.c (k+1) • U k)
    (m : ℕ) (hm : m ≤ N) : Polynomial.aeval X (recurrencePolynomial v m) = U m := by
  rcases hv with ⟨hN,ha0,hb0,hc0,haN,hsum,hapos,hcpos⟩
  have hfull : ∀ k, k ≤ N → Polynomial.aeval X (recurrencePolynomial v k) = U k := by
    intro k
    induction k using Nat.twoStepInduction with
    | zero => intro _; simpa [recurrencePolynomial,polynomialPair] using h0.symm
    | one =>
        intro _
        simpa [recurrencePolynomial,polynomialPair,ha0,hb0,hc0,Polynomial.aeval_X]
          using h1.symm
    | more k ih0 ih1 =>
        intro hk
        change Polynomial.aeval X
          (Polynomial.C (v.a (k+1))⁻¹ *
            ((Polynomial.X-Polynomial.C (v.b (k+1))) * recurrencePolynomial v (k+1) -
              Polynomial.C (v.c (k+1)) * recurrencePolynomial v k)) = _
        simp only [map_mul,map_sub,Polynomial.aeval_C,Polynomial.aeval_X,
          Algebra.algebraMap_eq_smul_one,smul_mul_assoc,one_mul]
        rw [ih0 (by omega),ih1 (by omega)]
        have hr := hrec k (by omega)
        have ht : X*U (k+1) - v.b (k+1) • U (k+1) - v.c (k+1) • U k =
            v.a (k+1) • U (k+2) := by rw [hr]; module
        simp only [sub_mul,smul_mul_assoc,one_mul]
        rw [ht,smul_smul]
        simp [ne_of_gt (hapos (k+1) (by omega))]
  exact hfull m hm

end Szkraw
