import Szkraw.RowNorm
import Szkraw.MatrixRecurrence
import Szkraw.Amplification

open scoped Matrix.Norms.Operator

namespace Szkraw

theorem norm_five_terms {N : ℕ}
    (A B C D E : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) :
    ‖A-B+C-D-E‖ ≤ ‖A‖+‖B‖+‖C‖+‖D‖+‖E‖ := by
  calc
    _ ≤ ‖A-B+C-D‖+‖E‖ := norm_sub_le _ _
    _ ≤ (‖A-B+C‖+‖D‖)+‖E‖ := by gcongr; exact norm_sub_le _ _
    _ ≤ ((‖A-B‖+‖C‖)+‖D‖)+‖E‖ := by gcongr; exact norm_add_le _ _
    _ ≤ _ := by gcongr; exact norm_sub_le _ _

/-- Taking norms of the actual subtraction identity, before amplification. -/
theorem product_difference_norm {N : ℕ} (v w : Coefficients N)
    (hv : Admissible v) (hw : Admissible w) (k : ℕ) (hk : k+1 < N)
    (η : ℝ) (hη : 0 ≤ η)
    (hJ : ‖recurrenceMatrix w‖ ≤ 1)
    (hJdiff : ‖recurrenceMatrix w-recurrenceMatrix v‖ ≤ 3*η)
    (hb : 0 ≤ w.b (k+1)) (hb1 : w.b (k+1) ≤ 1)
    (hc : w.c (k+1) ≤ 1)
    (hda : |w.a (k+1)-v.a (k+1)| ≤ η)
    (hdb : |w.b (k+1)-v.b (k+1)| ≤ η)
    (hdc : |w.c (k+1)-v.c (k+1)| ≤ η)
    (hB : ‖productMatrix v (k+1)‖ ≤ 1)
    (hBprev : ‖productMatrix v k‖ ≤ 1)
    (hBnext : ‖productMatrix v (k+2)‖ ≤ 1) :
    w.a (k+1)*‖productMatrix w (k+2)-productMatrix v (k+2)‖ ≤
      2*‖productMatrix w (k+1)-productMatrix v (k+1)‖ +
      ‖productMatrix w k-productMatrix v k‖ + 6*η := by
  have hc0 : 0 ≤ w.c (k+1) := le_of_lt (hw.2.2.2.2.2.2.2 (k+1) (by omega) (by omega))
  have ha0 : 0 ≤ w.a (k+1) := le_of_lt (hw.2.2.2.2.2.2.1 (k+1) hk)
  have hQ : ‖recurrenceMatrix w-w.b (k+1) • (1 : Matrix (Fin (N+1)) (Fin (N+1)) ℝ)‖ ≤ 2 := by
    calc
      _ ≤ ‖recurrenceMatrix w‖+‖w.b (k+1) • (1 : Matrix (Fin (N+1)) (Fin (N+1)) ℝ)‖ := norm_sub_le _ _
      _ ≤ 1+w.b (k+1) := by simpa [norm_smul,Real.norm_of_nonneg hb] using add_le_add_right hJ ‖w.b (k+1) • (1 : Matrix (Fin (N+1)) (Fin (N+1)) ℝ)‖
      _ ≤ 2 := by linarith
  have hK : ‖recurrenceMatrix w-recurrenceMatrix v-
      (w.b (k+1)-v.b (k+1)) • (1 : Matrix (Fin (N+1)) (Fin (N+1)) ℝ)‖ ≤ 4*η := by
    calc
      _ ≤ ‖recurrenceMatrix w-recurrenceMatrix v‖+
          ‖(w.b (k+1)-v.b (k+1)) • (1 : Matrix (Fin (N+1)) (Fin (N+1)) ℝ)‖ := norm_sub_le _ _
      _ ≤ 3*η+η := by simpa [norm_smul,Real.norm_eq_abs] using add_le_add hJdiff hdb
      _ = _ := by ring
  have hA := norm_mul_le
    (recurrenceMatrix w-w.b (k+1) • (1 : Matrix (Fin (N+1)) (Fin (N+1)) ℝ))
    (productMatrix w (k+1)-productMatrix v (k+1))
  have hC := norm_mul_le
    (recurrenceMatrix w-recurrenceMatrix v-(w.b (k+1)-v.b (k+1)) •
      (1 : Matrix (Fin (N+1)) (Fin (N+1)) ℝ)) (productMatrix v (k+1))
  have hA' : ‖(recurrenceMatrix w-w.b (k+1) • (1 : Matrix (Fin (N+1)) (Fin (N+1)) ℝ))*
      (productMatrix w (k+1)-productMatrix v (k+1))‖ ≤
      2*‖productMatrix w (k+1)-productMatrix v (k+1)‖ := by
    exact hA.trans (mul_le_mul_of_nonneg_right hQ (norm_nonneg _))
  have hB' : ‖w.c (k+1) • (productMatrix w k-productMatrix v k)‖ ≤
      ‖productMatrix w k-productMatrix v k‖ := by
    rw [norm_smul,Real.norm_of_nonneg hc0]
    exact (mul_le_mul_of_nonneg_right hc (norm_nonneg _)).trans_eq (one_mul _)
  have hC' : ‖(recurrenceMatrix w-recurrenceMatrix v-(w.b (k+1)-v.b (k+1)) •
      (1 : Matrix (Fin (N+1)) (Fin (N+1)) ℝ))*productMatrix v (k+1)‖ ≤ 4*η := by
    calc
      _ ≤ _ := hC
      _ ≤ (4*η)*1 := by gcongr
      _ = _ := mul_one _
  have hD' : ‖(w.c (k+1)-v.c (k+1)) • productMatrix v k‖ ≤ η := by
    rw [norm_smul,Real.norm_eq_abs]
    exact (mul_le_mul hdc hBprev (norm_nonneg _) hη).trans_eq (mul_one _)
  have hE' : ‖(w.a (k+1)-v.a (k+1)) • productMatrix v (k+2)‖ ≤ η := by
    rw [norm_smul,Real.norm_eq_abs]
    exact (mul_le_mul hda hBnext (norm_nonneg _) hη).trans_eq (mul_one _)
  rw [←Real.norm_of_nonneg ha0,←norm_smul,product_difference_recurrence v w hv hw k hk]
  exact (norm_five_terms _ _ _ _ _).trans (by linarith)

/-- The scalar amplification lemma applied to genuine recurrence-matrix errors. -/
theorem matrix_error_amplification {N : ℕ} (v w : Coefficients N)
    (hv : Admissible v) (hw : Admissible w) (η : ℝ) (hη : 0 ≤ η)
    (hJ : ‖recurrenceMatrix w‖ ≤ 1)
    (hJdiff : ‖recurrenceMatrix w-recurrenceMatrix v‖ ≤ 3*η)
    (hb : ∀ i, i ≤ N → 0 ≤ w.b i ∧ w.b i ≤ 1)
    (hc : ∀ i, i ≤ N → w.c i ≤ 1)
    (hcoeff : ∀ i, i ≤ N → |w.a i-v.a i| ≤ η ∧
      |w.b i-v.b i| ≤ η ∧ |w.c i-v.c i| ≤ η)
    (hmin : ∀ i, 1 ≤ i → i < N → 1/(2*(N : ℝ)) ≤ w.a i)
    (hB : ∀ i, i ≤ N → ‖productMatrix v i‖ ≤ 1)
    (m : ℕ) (hm : 1 ≤ m) (hmN : m ≤ N) :
    ‖productMatrix w m-productMatrix v m‖ ≤ η*(8*N)^m := by
  let e : ℕ → ℝ := fun i => ‖productMatrix w i-productMatrix v i‖
  have he0 : e 0 = 0 := by simp [e,productMatrix,matrixPair]
  have hprod1 (z : Coefficients N) (hz : Admissible z) : productMatrix z 1 = recurrenceMatrix z := by
    simp [productMatrix,matrixPair,hz.2.1,hz.2.2.1,hz.2.2.2.1]
  have he1 : e 1 ≤ 3*η := by simpa only [e,hprod1 v hv,hprod1 w hw] using hJdiff
  have hrec : ∀ i, 1 ≤ i → i < N → e (i+1) ≤ 4*N*e i+2*N*e (i-1)+12*N*η := by
    intro i hi hiN
    obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0)
    have hh := product_difference_norm v w hv hw k hiN η hη hJ hJdiff
      (hb (k+1) (by omega)).1 (hb (k+1) (by omega)).2 (hc (k+1) (by omega))
      (hcoeff (k+1) (by omega)).1 (hcoeff (k+1) (by omega)).2.1
      (hcoeff (k+1) (by omega)).2.2
      (hB (k+1) (by omega)) (hB k (by omega)) (hB (k+2) (by omega))
    have hn : 0 < (N : ℝ) := by exact_mod_cast (by have := hv.1; omega : 0 < N)
    have hamin := hmin (k+1) (by omega) hiN
    have ha1 : 1 ≤ 2*(N : ℝ)*w.a (k+1) := by
      have ht := (div_le_iff₀ (by positivity : 0 < 2*(N : ℝ))).mp hamin
      nlinarith
    change e (k+2) ≤ _
    calc
      _ ≤ (2*(N : ℝ)*w.a (k+1))*e (k+2) :=
        le_mul_of_one_le_left (norm_nonneg _) ha1
      _ ≤ 2*(N : ℝ)*(2*e (k+1)+e k+6*η) := by
        have ht := mul_le_mul_of_nonneg_left hh (by positivity : 0 ≤ 2*(N : ℝ))
        dsimp [e]
        nlinarith [ht]
      _ = _ := by simp only [Nat.succ_sub_one]; ring
  exact error_amplification N η e hv.1 hη he0 he1 hrec m hm hmN

end Szkraw
