import Szkraw.RowAction
import Szkraw.Representation

namespace Szkraw

theorem geometric_family_matrix_positivity (N : ℕ) (hN : 1 ≤ N)
    (p q : ℝ) (hp : 1 ≤ p) (hq : 1 ≤ q) :
    MatrixPositivity (geometricCoefficients N p q) := by
  let v := geometricCoefficients N p q
  let U := normalizedElementary p q N
  let X := U 1
  have hv : Admissible v := geometric_coefficients_admissible N hN p q hp hq
  have heval : ∀ m, m ≤ N → Polynomial.aeval X (recurrencePolynomial v m) = U m := by
    intro m hm
    apply recurrence_evaluation v hv U X (normalized_elementary_zero p q N) rfl
      (fun k hk => ?_) m hm
    exact normalized_three_term p q hp hq N k (by omega)
  intro m hm i j
  have hrep := representation_product v (fun k : Fin (N+1) => U k.val) X
    (geometric_row_action p q hp hq N hN) m i
  rw [heval m hm] at hrep
  have hpos := tower_mul_nonneg p q hp hq N (U m) (U i.val)
    (normalized_elementary_nonneg p q hp hq N m hm)
    (normalized_elementary_nonneg p q hp hq N i.val (by omega))
  rw [hrep] at hpos
  exact normalized_coefficients_nonneg p q hp hq N
    (fun k => productMatrix v m i k) hpos j

theorem recurrence_matrix_congr {N : ℕ} (v w : Coefficients N)
    (h : ∀ i, i ≤ N → v.a i = w.a i ∧ v.b i = w.b i ∧ v.c i = w.c i) :
    recurrenceMatrix v = recurrenceMatrix w := by
  ext i j
  have hi := h i.val (by omega)
  simp only [recurrenceMatrix]
  rw [hi.1,hi.2.1,hi.2.2]

theorem matrix_pair_congr {N : ℕ} (v w : Coefficients N)
    (h : ∀ i, i ≤ N → v.a i = w.a i ∧ v.b i = w.b i ∧ v.c i = w.c i)
    (m : ℕ) (hm : m ≤ N+1) : matrixPair v m = matrixPair w m := by
  induction m with
  | zero => rfl
  | succ m ih =>
      have hc := h m (by omega)
      simp only [matrixPair]
      rw [ih (by omega),recurrence_matrix_congr v w h,hc.1,hc.2.1,hc.2.2]

theorem product_matrix_congr {N : ℕ} (v w : Coefficients N)
    (h : ∀ i, i ≤ N → v.a i = w.a i ∧ v.b i = w.b i ∧ v.c i = w.c i)
    (m : ℕ) (hm : m ≤ N+1) : productMatrix v m = productMatrix w m :=
  congrArg Prod.snd (matrix_pair_congr v w h m hm)

theorem geometric_matrix_positivity : Stmt_geometric_matrix := by
  intro N v hv hg
  obtain ⟨p,q,hp,hq,hcoeff⟩ := geometric_parameters N v hv hg
  have h := geometric_family_matrix_positivity N hv.1 p q hp hq
  intro m hm i j
  rw [product_matrix_congr v (geometricCoefficients N p q) hcoeff m (by omega)]
  exact h m hm i j

example : Stmt_geometric_matrix := geometric_matrix_positivity

end Szkraw
