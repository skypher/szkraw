import Szkraw.MatrixBridge
import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic.FieldSimp

/-!
# Row zero of `p_m(J)` and symmetry of linearization coefficients (F2)

For any coefficient array with `a i ≠ 0` for `i < N`, row `0` of
`productMatrix v m = p_m(J)` is the unit row `e_m` (`m ≤ N`), and consequently
`productMatrix v m n k = productMatrix v n m k` for `m, n ≤ N`.
-/

namespace Szkraw

open Matrix

variable {N : ℕ} (v : Coefficients N)

theorem J_commute_product (m : ℕ) :
    recurrenceMatrix v * productMatrix v m = productMatrix v m * recurrenceMatrix v := by
  rw [product_matrix_aeval]
  have := congrArg (Polynomial.aeval (recurrenceMatrix v)) (mul_comm Polynomial.X (recurrencePolynomial v m))
  simpa only [map_mul, Polynomial.aeval_X] using this

theorem product_commute (m n : ℕ) :
    productMatrix v m * productMatrix v n = productMatrix v n * productMatrix v m := by
  rw [product_matrix_aeval, product_matrix_aeval]
  have := congrArg (Polynomial.aeval (recurrenceMatrix v))
    (mul_comm (recurrencePolynomial v m) (recurrencePolynomial v n))
  simpa only [map_mul] using this

/-- Row `i` of `M * J`: `(M J) i k = Σ_l M i l J l k`, and column `k` of `J` has at most three entries. -/
theorem mul_J_entry (M : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (i k : Fin (N + 1)) :
    (M * recurrenceMatrix v) i k =
      ∑ l : Fin (N + 1), M i l * recurrenceMatrix v l k := rfl

/-- Row `0` of `p_m(J)` is the unit row `e_m`, for `m ≤ N`. -/
theorem row_zero (ha : ∀ i, i < N → v.a i ≠ 0) :
    ∀ m, m ≤ N → ∀ k : Fin (N + 1), productMatrix v m 0 k = if k.val = m then 1 else 0 := by
  -- strong form: rows of p_m and p_(m+1) together
  have key : ∀ m, m + 1 ≤ N → (∀ k : Fin (N + 1), productMatrix v m 0 k = if k.val = m then 1 else 0) →
      (∀ k : Fin (N + 1), (matrixPair v m).1 0 k = if m = 0 then 0 else if k.val + 1 = m then 1 else 0) →
      ∀ k : Fin (N + 1), productMatrix v (m + 1) 0 k = if k.val = m + 1 then 1 else 0 := by
    intro m hm hcur hprev k
    -- p_{m+1} = a_m⁻¹ ((J - b_m) p_m - c_m p_{m-1}),  row 0 via commutation
    have hdef : productMatrix v (m + 1) = (v.a m)⁻¹ •
        ((recurrenceMatrix v - v.b m • (1 : Matrix _ _ ℝ)) * productMatrix v m - v.c m • (matrixPair v m).1) := rfl
    rw [hdef, Matrix.sub_mul, J_commute_product]
    simp only [Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul, Matrix.smul_mul, Matrix.one_mul]
    rw [mul_J_entry]
    -- Σ_l p_m 0 l * J l k = J m k
    have hsum : ∑ l : Fin (N + 1), productMatrix v m 0 l * recurrenceMatrix v l k =
        recurrenceMatrix v ⟨m, by omega⟩ k := by
      rw [Finset.sum_eq_single ⟨m, by omega⟩]
      · rw [hcur]; simp
      · intro l _ hl; rw [hcur]; rw [if_neg (fun h => hl (Fin.ext h))]; ring
      · intro h; exact absurd (Finset.mem_univ _) h
    have hJ : recurrenceMatrix v ⟨m, by omega⟩ k =
        if k.val = m + 1 then v.a m else if k.val = m then v.b m else if m = k.val + 1 then v.c m else 0 := by
      unfold recurrenceMatrix
      have e : (k = (⟨m, by omega⟩ : Fin (N + 1))) ↔ k.val = m := Fin.ext_iff
      simp only [e]
    rw [hsum, hcur, hprev, hJ]
    have ham := ha m (by omega)
    split_ifs <;> first | omega | ring1 | (field_simp; ring1)
  have claim : ∀ m, m ≤ N → ∀ k : Fin (N + 1),
      productMatrix v m 0 k = (if k.val = m then 1 else 0) ∧
      (matrixPair v m).1 0 k = (if m = 0 then 0 else if k.val + 1 = m then 1 else 0) := by
    intro m
    induction m with
    | zero =>
      intro _ k
      refine ⟨?_, ?_⟩
      · simp only [productMatrix, matrixPair, Matrix.one_apply]
        by_cases hk : k.val = 0
        · have : (0 : Fin (N + 1)) = k := Fin.ext hk.symm
          simp [this, hk]
        · have : (0 : Fin (N + 1)) ≠ k := fun h => hk (by rw [← h]; rfl)
          simp [this, hk]
      · simp [matrixPair]
    | succ m ih =>
      intro hm k
      refine ⟨key m hm (fun k' => (ih (by omega) k').1) (fun k' => (ih (by omega) k').2) k, ?_⟩
      have h1 : (matrixPair v (m + 1)).1 = productMatrix v m := rfl
      rw [h1, (ih (by omega) k).1]
      simp
  intro m hm k
  exact (claim m hm k).1

/-- Row `n` of `p_m(J)` is row `m` of `p_n(J)`: `g(m,n;k) = g(n,m;k)` for `m, n ≤ N`. -/
theorem product_symm (ha : ∀ i, i < N → v.a i ≠ 0) (m n : ℕ) (hm : m ≤ N) (hn : n ≤ N)
    (k : Fin (N + 1)) :
    productMatrix v m ⟨n, by omega⟩ k = productMatrix v n ⟨m, by omega⟩ k := by
  have row : ∀ p q : ℕ, (hp : p ≤ N) → (_hq : q ≤ N) →
      (productMatrix v p * productMatrix v q) 0 k = productMatrix v q ⟨p, by omega⟩ k := by
    intro p q hp _
    rw [Matrix.mul_apply, Finset.sum_eq_single ⟨p, by omega⟩]
    · rw [row_zero v ha p hp]; simp
    · intro l _ hl; rw [row_zero v ha p hp, if_neg (fun h => hl (Fin.ext h)), zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [← row n m hn hm, ← row m n hm hn, product_commute]

end Szkraw
