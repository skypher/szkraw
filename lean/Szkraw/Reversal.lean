import Szkraw.LowProducts
import Szkraw.Krawtchouk

/-!
# Reversal, deep reduction and palindromic systems (paper, Lemma 7.14 – Corollary 7.17)

Matrix forms. `p_m(J) = productMatrix v m`; the reversed array `a'_i = c_{N-i}`,
`b'_i = b_{N-i}`, `c'_i = a_{N-i}` has the matrix `Π J Π`, and its polynomials evaluated at `J`
are `Rp t = Π p'_t(J') Π`.
-/

namespace Szkraw

open Finset Matrix

variable {N : ℕ}

/-! ### Matrices commuting with `J` -/

section commute

variable (v : Coefficients N)

/-- A matrix commuting with `J` commutes with every `p_m(J)`. -/
theorem commute_product (X : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (hX : X * recurrenceMatrix v = recurrenceMatrix v * X) :
    ∀ m, X * productMatrix v m = productMatrix v m * X := by
  have pair : ∀ m, X * productMatrix v m = productMatrix v m * X ∧
      X * (matrixPair v m).1 = (matrixPair v m).1 * X := by
    intro m
    induction m with
    | zero =>
      refine ⟨?_, ?_⟩
      · show X * 1 = 1 * X; rw [Matrix.mul_one, Matrix.one_mul]
      · show X * 0 = 0 * X; rw [Matrix.mul_zero, Matrix.zero_mul]
    | succ m ih =>
      obtain ⟨hP, hQ⟩ := ih
      refine ⟨?_, hP⟩
      have hdef : productMatrix v (m + 1) = (v.a m)⁻¹ •
          ((recurrenceMatrix v - v.b m • (1 : Matrix _ _ ℝ)) * productMatrix v m -
            v.c m • (matrixPair v m).1) := rfl
      rw [hdef]
      simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.one_mul]
      rw [← Matrix.mul_assoc, hX, Matrix.mul_assoc, hP, ← Matrix.mul_assoc, hQ]
  exact fun m => (pair m).1

/-- Row `0` of `p_n(J) X` is row `n` of `X`. -/
theorem row0_mul (ha : ∀ i, i < N → v.a i ≠ 0) (n : ℕ) (hn : n ≤ N)
    (X : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (l : Fin (N + 1)) :
    (productMatrix v n * X) 0 l = X ⟨n, by omega⟩ l := by
  rw [Matrix.mul_apply, Finset.sum_eq_single ⟨n, by omega⟩]
  · rw [row_zero v ha n hn]; simp
  · intro j _ hj; rw [row_zero v ha n hn, if_neg (fun h => hj (Fin.ext h)), zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- Two matrices commuting with `J` with the same row `0` are equal (`e_0` is cyclic). -/
theorem eq_of_row_zero (ha : ∀ i, i < N → v.a i ≠ 0) (X Y : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (hX : X * recurrenceMatrix v = recurrenceMatrix v * X)
    (hY : Y * recurrenceMatrix v = recurrenceMatrix v * Y) (h0 : ∀ l, X 0 l = Y 0 l) : X = Y := by
  ext n l
  have e : n = ⟨n.val, by omega⟩ := Fin.ext rfl
  have hXn := commute_product v X hX n.val
  have hYn := commute_product v Y hY n.val
  rw [e, ← row0_mul v ha n.val (by omega) X l, ← row0_mul v ha n.val (by omega) Y l, ← hXn, ← hYn,
    Matrix.mul_apply, Matrix.mul_apply]
  simp only [h0]

/-- The matrix product identity `p_m(J) p_n(J) = Σ_k g(m,n;k) p_k(J)` for `m, n ≤ N`. -/
theorem product_identity (ha : ∀ i, i < N → v.a i ≠ 0) (m n : ℕ) (hm : m ≤ N) (hn : n ≤ N) :
    productMatrix v m * productMatrix v n =
      ∑ k : Fin (N + 1), productMatrix v m ⟨n, by omega⟩ k • productMatrix v k := by
  apply eq_of_row_zero v ha
  · rw [Matrix.mul_assoc, ← J_commute_product, ← Matrix.mul_assoc, ← J_commute_product,
      Matrix.mul_assoc]
  · rw [Matrix.sum_mul, Matrix.mul_sum]
    apply sum_congr rfl; intro k _
    rw [Matrix.smul_mul, Matrix.mul_smul, J_commute_product]
  · intro l
    rw [row0_mul v ha m hm, Matrix.sum_apply]
    simp only [Matrix.smul_apply, smul_eq_mul]
    rw [Finset.sum_eq_single l]
    · rw [row_zero v ha l.val (by omega), if_pos rfl, mul_one, product_symm v ha n m hn hm]
    · intro k _ hk
      rw [row_zero v ha k.val (by omega), if_neg (fun h => hk (Fin.ext h.symm)), mul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h

end commute

/-! ### The reversed array and Lemma 7.14 -/

/-- The reversed array `a'_i = c_{N-i}`, `b'_i = b_{N-i}`, `c'_i = a_{N-i}`. -/
def revCoeff (v : Coefficients N) : Coefficients N :=
  ⟨fun i => v.c (N - i), fun i => v.b (N - i), fun i => v.a (N - i)⟩

/-- The reversal permutation matrix `Π`. -/
def revPerm (N : ℕ) : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ :=
  fun i j => if i.val + j.val = N then 1 else 0

theorem revPerm_mul_apply (X : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (i j : Fin (N + 1)) :
    (revPerm N * X) i j = X (Fin.rev i) j := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (Fin.rev i)]
  · unfold revPerm; rw [if_pos (by simp; omega), one_mul]
  · intro l _ hl; unfold revPerm
    rw [if_neg (fun h => hl (Fin.ext (by simp; omega))), zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem mul_revPerm_apply (X : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (i j : Fin (N + 1)) :
    (X * revPerm N) i j = X i (Fin.rev j) := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (Fin.rev j)]
  · unfold revPerm; rw [if_pos (by simp; omega), mul_one]
  · intro l _ hl; unfold revPerm
    rw [if_neg (fun h => hl (Fin.ext (by simp; omega))), mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem revPerm_sq : revPerm N * revPerm N = 1 := by
  ext i j
  rw [revPerm_mul_apply, Matrix.one_apply]
  unfold revPerm
  by_cases h : i = j
  · subst h; rw [if_pos (by simp; omega), if_pos rfl]
  · rw [if_neg (fun h' => h (Fin.ext (by simp at h'; omega))), if_neg h]

theorem revPerm_conj_apply (X : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (i j : Fin (N + 1)) :
    (revPerm N * X * revPerm N) i j = X (Fin.rev i) (Fin.rev j) := by
  rw [mul_revPerm_apply, revPerm_mul_apply]

/-- The matrix of the reversed array is `Π J Π`. -/
theorem J_rev (v : Coefficients N) :
    recurrenceMatrix (revCoeff v) = revPerm N * recurrenceMatrix v * revPerm N := by
  ext i j
  rw [revPerm_conj_apply]
  unfold recurrenceMatrix revCoeff
  simp only [Fin.val_rev]
  have hi := i.isLt; have hj := j.isLt
  by_cases h1 : j.val = i.val + 1
  · rw [if_pos h1, if_neg (by omega), if_neg (fun h => by rw [Fin.ext_iff] at h; simp at h; omega),
      if_pos (by omega)]
    congr 1; omega
  by_cases h2 : j = i
  · subst h2
    rw [if_neg h1, if_pos rfl, if_neg (by omega), if_pos rfl]
    congr 1; omega
  by_cases h3 : i.val = j.val + 1
  · rw [if_neg h1, if_neg h2, if_pos h3, if_pos (by omega)]
    congr 1; omega
  · rw [if_neg h1, if_neg h2, if_neg h3, if_neg (by omega),
      if_neg (fun h => h2 (Fin.ext (by rw [Fin.ext_iff] at h; simp at h; omega))), if_neg (by omega)]

/-- `p'_t(J) = Π p'_t(J') Π`. -/
noncomputable def Rp (v : Coefficients N) (t : ℕ) : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ :=
  revPerm N * productMatrix (revCoeff v) t * revPerm N

theorem J_eq_conj (v : Coefficients N) :
    recurrenceMatrix v = revPerm N * recurrenceMatrix (revCoeff v) * revPerm N := by
  rw [J_rev, ← Matrix.mul_assoc, ← Matrix.mul_assoc, revPerm_sq, Matrix.one_mul, Matrix.mul_assoc,
    revPerm_sq, Matrix.mul_one]

/-- If `X` commutes with `J`, then `Π X Π` commutes with `J'`. -/
theorem conj_commute (v : Coefficients N) (X : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (hX : X * recurrenceMatrix v = recurrenceMatrix v * X) :
    (revPerm N * X * revPerm N) * recurrenceMatrix (revCoeff v) =
      recurrenceMatrix (revCoeff v) * (revPerm N * X * revPerm N) := by
  rw [J_rev]
  have e1 : revPerm N * X * revPerm N * (revPerm N * recurrenceMatrix v * revPerm N) =
      revPerm N * (X * recurrenceMatrix v) * revPerm N := by
    simp only [Matrix.mul_assoc]; rw [← Matrix.mul_assoc (revPerm N) (revPerm N), revPerm_sq,
      Matrix.one_mul]
  have e2 : revPerm N * recurrenceMatrix v * revPerm N * (revPerm N * X * revPerm N) =
      revPerm N * (recurrenceMatrix v * X) * revPerm N := by
    simp only [Matrix.mul_assoc]; rw [← Matrix.mul_assoc (revPerm N) (revPerm N), revPerm_sq,
      Matrix.one_mul]
  rw [e1, e2, hX]

theorem conj_mul (A B : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) :
    (revPerm N * A * revPerm N) * (revPerm N * B * revPerm N) = revPerm N * (A * B) * revPerm N := by
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (revPerm N) (revPerm N), revPerm_sq, Matrix.one_mul]

/-- `p'_t(J)` commutes with `J`. -/
theorem Rp_commute_J (v : Coefficients N) (t : ℕ) :
    Rp v t * recurrenceMatrix v = recurrenceMatrix v * Rp v t := by
  unfold Rp
  rw [J_eq_conj v, conj_mul, conj_mul, J_commute_product]

section reversal

variable (v : Coefficients N) (hv : Admissible v)
include hv

theorem rev_a_ne : ∀ i, i < N → (revCoeff v).a i ≠ 0 := fun i hi =>
  (hv.2.2.2.2.2.2.2 (N - i) (by omega) (by omega)).ne'

/-- Row `N` of `p'_t(J)` is the unit row `e_{N-t}`. -/
theorem Rp_row_N (t : ℕ) (ht : t ≤ N) (c : Fin (N + 1)) :
    Rp v t ⟨N, by omega⟩ c = if c.val + t = N then 1 else 0 := by
  unfold Rp
  rw [revPerm_conj_apply]
  have e : Fin.rev (⟨N, by omega⟩ : Fin (N + 1)) = 0 := Fin.ext (by simp)
  rw [e, row_zero (revCoeff v) (rev_a_ne v hv) t ht]
  simp only [Fin.val_rev]
  have := c.isLt
  by_cases h : c.val + t = N
  · rw [if_pos (by omega), if_pos h]
  · rw [if_neg (by omega), if_neg h]

/-- Row `N` of `p'_t(J) X` is row `N - t` of `X`. -/
theorem rowN_mul (t : ℕ) (ht : t ≤ N) (X : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (c : Fin (N + 1)) :
    (Rp v t * X) ⟨N, by omega⟩ c = X ⟨N - t, by omega⟩ c := by
  rw [Matrix.mul_apply, Finset.sum_eq_single ⟨N - t, by omega⟩]
  · rw [Rp_row_N v hv t ht, if_pos (by simp; omega), one_mul]
  · intro j _ hj
    rw [Rp_row_N v hv t ht, if_neg (fun h => hj (Fin.ext (by simp; omega))), zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

omit hv in
/-- A matrix commuting with `J` commutes with every `p'_t(J)`. -/
theorem commute_Rp (X : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (hX : X * recurrenceMatrix v = recurrenceMatrix v * X) (t : ℕ) : X * Rp v t = Rp v t * X := by
  have hc := commute_product (revCoeff v) _ (conj_commute v X hX) t
  have hXX : revPerm N * (revPerm N * X * revPerm N) * revPerm N = X := by
    simp only [Matrix.mul_assoc]
    rw [revPerm_sq, Matrix.mul_one, ← Matrix.mul_assoc, revPerm_sq, Matrix.one_mul]
  unfold Rp
  conv_lhs => rw [← hXX]
  conv_rhs => rw [← hXX]
  rw [conj_mul, conj_mul, hc]

/-- Two matrices commuting with `J` with the same row `N` are equal (`e_N` is cyclic). -/
theorem eq_of_row_N (X Y : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (hX : X * recurrenceMatrix v = recurrenceMatrix v * X)
    (hY : Y * recurrenceMatrix v = recurrenceMatrix v * Y)
    (hN : ∀ c, X ⟨N, by omega⟩ c = Y ⟨N, by omega⟩ c) : X = Y := by
  ext i c
  have e : i = ⟨N - (N - i.val), by omega⟩ := Fin.ext (by simp; omega)
  rw [e, ← rowN_mul v hv (N - i.val) (by omega) X c, ← rowN_mul v hv (N - i.val) (by omega) Y c,
    ← commute_Rp v X hX, ← commute_Rp v Y hY, Matrix.mul_apply, Matrix.mul_apply]
  simp only [hN]

/-- **Lemma 7.14** (Reversal identity): `R_N R'_t = R_{N-t}` on the support. -/
theorem reversal_identity (t : ℕ) (ht : t ≤ N) :
    productMatrix v N * Rp v t = productMatrix v (N - t) := by
  have ha : ∀ i, i < N → v.a i ≠ 0 := fun i hi => (hv.2.2.2.2.2.2.1 i hi).ne'
  apply eq_of_row_zero v ha
  · rw [Matrix.mul_assoc, Rp_commute_J, ← Matrix.mul_assoc, ← J_commute_product, Matrix.mul_assoc]
  · exact (J_commute_product v (N - t)).symm
  · intro l
    rw [row0_mul v ha N le_rfl, Rp_row_N v hv t ht, row_zero v ha (N - t) (by omega)]
    by_cases h : l.val + t = N
    · rw [if_pos h, if_pos (by omega)]
    · rw [if_neg h, if_neg (by omega)]

/-- The product identity for the reversed polynomials, evaluated at `J`. -/
theorem Rp_product (i j : ℕ) (hi : i ≤ N) (hj : j ≤ N) :
    Rp v i * Rp v j = ∑ t : Fin (N + 1), productMatrix (revCoeff v) i ⟨j, by omega⟩ t • Rp v t := by
  unfold Rp
  rw [conj_mul, product_identity (revCoeff v) (rev_a_ne v hv) i j hi hj, Matrix.mul_sum,
    Matrix.sum_mul]
  apply sum_congr rfl; intro t _
  rw [Matrix.mul_smul, Matrix.smul_mul]

/-- **Theorem 7.15**, the reduction formula
`g(x,y;z) = Σ_t g'(N-x,N-y;t) g(N,N-t;z)` (valid for all `x, y ≤ N`). -/
theorem deep_formula (x y : ℕ) (hx : x ≤ N) (hy : y ≤ N) (z : Fin (N + 1)) :
    productMatrix v x ⟨y, by omega⟩ z = ∑ t : Fin (N + 1),
      productMatrix (revCoeff v) (N - x) ⟨N - y, by omega⟩ t *
        productMatrix v N ⟨N - t.val, by omega⟩ z := by
  have ha : ∀ i, i < N → v.a i ≠ 0 := fun i hi => (hv.2.2.2.2.2.2.1 i hi).ne'
  have hPx : productMatrix v x = productMatrix v N * Rp v (N - x) := by
    rw [reversal_identity v hv (N - x) (by omega), show N - (N - x) = x by omega]
  have hPy : productMatrix v y = productMatrix v N * Rp v (N - y) := by
    rw [reversal_identity v hv (N - y) (by omega), show N - (N - y) = y by omega]
  have hcomm : ∀ s, Rp v s * productMatrix v N = productMatrix v N * Rp v s := fun s =>
    (commute_Rp v _ (J_commute_product v N).symm s).symm
  have key : productMatrix v x * productMatrix v y = ∑ t : Fin (N + 1),
      productMatrix (revCoeff v) (N - x) ⟨N - y, by omega⟩ t •
        (productMatrix v N * productMatrix v (N - t.val)) := by
    rw [hPx, hPy]
    have : productMatrix v N * Rp v (N - x) * (productMatrix v N * Rp v (N - y)) =
        productMatrix v N * (productMatrix v N * (Rp v (N - x) * Rp v (N - y))) := by
      simp only [Matrix.mul_assoc]; rw [← Matrix.mul_assoc (Rp v (N - x)), hcomm, Matrix.mul_assoc]
    rw [this, Rp_product v hv (N - x) (N - y) (by omega) (by omega), Matrix.mul_sum, Matrix.mul_sum]
    apply sum_congr rfl; intro t _
    rw [Matrix.mul_smul, Matrix.mul_smul, ← Matrix.mul_assoc,
      ← reversal_identity v hv t.val (by omega)]
    simp only [Matrix.mul_assoc]
  have h0 := congrFun (congrFun key 0) z
  rw [row0_mul v ha x hx, Matrix.sum_apply] at h0
  have hs : productMatrix v y ⟨x, by omega⟩ z = productMatrix v x ⟨y, by omega⟩ z :=
    (product_symm v ha x y hx hy z).symm
  rw [hs] at h0
  rw [h0]
  apply sum_congr rfl; intro t _
  rw [Matrix.smul_apply, smul_eq_mul, row0_mul v ha N le_rfl,
    product_symm v ha (N - t.val) N (by omega) le_rfl z]

/-- **Theorem 7.15**: `g(N,N;N-l)` is the coefficient of `R'_l` in `R_N`. -/
theorem top_expansion :
    productMatrix v N = ∑ l : Fin (N + 1), productMatrix v N ⟨N, by omega⟩ ⟨N - l.val, by omega⟩ • Rp v l := by
  apply eq_of_row_N v hv
  · exact (J_commute_product v N).symm
  · rw [Matrix.sum_mul, Matrix.mul_sum]
    apply sum_congr rfl; intro l _
    rw [Matrix.smul_mul, Matrix.mul_smul, Rp_commute_J]
  · intro c
    rw [Matrix.sum_apply, Finset.sum_eq_single ⟨N - c.val, by omega⟩]
    · rw [Matrix.smul_apply, smul_eq_mul, Rp_row_N v hv _ (by simp),
        if_pos (by simp; omega), mul_one]
      congr 1; exact Fin.ext (by simp; omega)
    · intro l _ hl
      rw [Matrix.smul_apply, smul_eq_mul, Rp_row_N v hv _ (by omega),
        if_neg (fun h => hl (Fin.ext (by simp; omega))), mul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h

end reversal

/-- A deep triple: each two indices have sum greater than `N`. -/
def Deep (N m n k : ℕ) : Prop := N < m + n ∧ N < m + k ∧ N < n + k

/-- **Theorem 7.15** (Deep reduction), positivity criterion. -/
def Stmt_deep_reduction : Prop :=
  ∀ (N : ℕ) (v : Coefficients N), Admissible v →
    (∀ m, m ≤ N → ∀ n k : Fin (N + 1), ¬Deep N m n k → 0 ≤ productMatrix v m n k) →
    (∀ i j, (h : i + j < N) → ∀ t : Fin (N + 1), 0 ≤ productMatrix (revCoeff v) i ⟨j, by omega⟩ t) →
    (∃ e : Fin (N + 1) → ℝ, (∀ l, 0 ≤ e l) ∧ productMatrix v N = ∑ l, e l • Rp v l) →
    MatrixPositivity v

theorem deep_reduction : Stmt_deep_reduction := by
  intro N v hv ha_nd hb hc
  have ha : ∀ i, i < N → v.a i ≠ 0 := fun i hi => (hv.2.2.2.2.2.2.1 i hi).ne'
  obtain ⟨e, he, hexp⟩ := hc
  -- (c) gives `g(N,N;N-l) = e_l ≥ 0`
  have hNN : ∀ l : ℕ, l ≤ N → 0 ≤ productMatrix v N ⟨N, by omega⟩ ⟨N - l, by omega⟩ := by
    intro l hl
    have h := congrFun (congrFun hexp ⟨N, by omega⟩) ⟨N - l, by omega⟩
    rw [Matrix.sum_apply, Finset.sum_eq_single ⟨l, by omega⟩] at h
    · rw [h, Matrix.smul_apply, smul_eq_mul, Rp_row_N v hv l hl, if_pos (by simp; omega), mul_one]
      exact he _
    · intro l' _ hl'
      have hl'N := l'.isLt
      rw [Matrix.smul_apply, smul_eq_mul, Rp_row_N v hv l'.val (by omega)]
      rw [if_neg (by intro h; apply hl'; ext; simp only at h ⊢; omega), mul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  -- `g(N, s; z) ≥ 0` for all `s, z`
  have hrow : ∀ s : ℕ, (hs : s ≤ N) → ∀ z : Fin (N + 1), 0 ≤ productMatrix v N ⟨s, by omega⟩ z := by
    intro s hs z
    by_cases hd : Deep N N s z.val
    · -- `π_N g(s,N;z) = π_z g(s,z;N)` and the reduction formula at `(s,z)`
      have hsym := product_symm v ha N s le_rfl hs z
      rw [hsym]
      have hpi := piW_entry v hv s ⟨N, by omega⟩ z
      have hred := deep_formula v hv s z.val hs (by omega) ⟨N, by omega⟩
      have hz : (⟨z.val, by omega⟩ : Fin (N + 1)) = z := Fin.ext rfl
      rw [hz] at hred
      have hnn : 0 ≤ productMatrix v s z ⟨N, by omega⟩ := by
        rw [hred]
        apply sum_nonneg; intro t _
        apply mul_nonneg (hb (N - s) (N - z.val) (by unfold Deep at hd; omega) t)
        -- `π_{N-t} g(N,N-t;N) = π_N g(N,N;N-t)`
        have hpi2 := piW_entry v hv N ⟨N - t.val, by omega⟩ ⟨N, by omega⟩
        have h1 := hNN t.val (by omega)
        have hp1 := piW_pos v hv (N - t.val) (by omega)
        have hp2 := piW_pos v hv N le_rfl
        have : 0 ≤ piW v (N - t.val) * productMatrix v N ⟨N - t.val, by omega⟩ ⟨N, by omega⟩ := by
          have e1 : piW v ((⟨N - t.val, by omega⟩ : Fin (N + 1)) : ℕ) = piW v (N - t.val) := rfl
          rw [← e1, hpi2]; simp only; positivity
        exact nonneg_of_mul_nonneg_right (by linarith) hp1
      have hp1 := piW_pos v hv N le_rfl
      have hp2 := piW_pos v hv z.val (by omega)
      have : 0 ≤ piW v N * productMatrix v s ⟨N, by omega⟩ z := by
        have e1 : piW v ((⟨N, by omega⟩ : Fin (N + 1)) : ℕ) = piW v N := rfl
        rw [← e1, hpi]; positivity
      exact nonneg_of_mul_nonneg_right (by linarith) hp1
    · exact ha_nd N le_rfl ⟨s, by omega⟩ z hd
  intro m hm n k
  by_cases hd : Deep N m n.val k.val
  · have hred := deep_formula v hv m n.val hm (by omega) k
    have hn : (⟨n.val, by omega⟩ : Fin (N + 1)) = n := Fin.ext rfl
    rw [hn] at hred
    rw [hred]
    apply sum_nonneg; intro t _
    exact mul_nonneg (hb (N - m) (N - n.val) (by unfold Deep at hd; omega) t)
      (hrow (N - t.val) (by omega) k)
  · exact ha_nd m hm n k hd

/-! ### Palindromic systems (Theorem 7.16, Corollary 7.17) -/

/-- Arrays agreeing on the indices `0, …, N` have the same `p_m(J)` for `m ≤ N + 1`. -/
theorem product_congr (v w : Coefficients N) (ha : ∀ i, i ≤ N → v.a i = w.a i)
    (hb : ∀ i, i ≤ N → v.b i = w.b i) (hc : ∀ i, i ≤ N → v.c i = w.c i) :
    ∀ m, m ≤ N + 1 → productMatrix v m = productMatrix w m := by
  have hJ : recurrenceMatrix v = recurrenceMatrix w := by
    ext i j; unfold recurrenceMatrix
    rw [ha i.val (by omega), hb i.val (by omega), hc i.val (by omega)]
  have pair : ∀ m, m ≤ N + 1 → productMatrix v m = productMatrix w m ∧
      (matrixPair v m).1 = (matrixPair w m).1 := by
    intro m
    induction m with
    | zero => intro _; exact ⟨rfl, rfl⟩
    | succ m ih =>
      intro hm
      obtain ⟨hP, hQ⟩ := ih (by omega)
      refine ⟨?_, hP⟩
      show (v.a m)⁻¹ • ((recurrenceMatrix v - v.b m • (1 : Matrix _ _ ℝ)) * productMatrix v m -
          v.c m • (matrixPair v m).1) = (w.a m)⁻¹ • ((recurrenceMatrix w - w.b m • (1 : Matrix _ _ ℝ)) *
          productMatrix w m - w.c m • (matrixPair w m).1)
      rw [hJ, hP, hQ, ha m (by omega), hb m (by omega), hc m (by omega)]
  exact fun m hm => (pair m hm).1

/-- If `Π J Π = J`, then `Π p_m(J) Π = p_m(J)`. -/
theorem conj_product_fixed (v : Coefficients N)
    (hJ : revPerm N * recurrenceMatrix v * revPerm N = recurrenceMatrix v) :
    ∀ m, revPerm N * productMatrix v m * revPerm N = productMatrix v m := by
  have cj_sub : ∀ A B : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ,
      revPerm N * (A - B) * revPerm N = revPerm N * A * revPerm N - revPerm N * B * revPerm N := by
    intro A B; rw [Matrix.mul_sub, Matrix.sub_mul]
  have cj_smul : ∀ (x : ℝ) (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ),
      revPerm N * (x • A) * revPerm N = x • (revPerm N * A * revPerm N) := by
    intro x A; rw [Matrix.mul_smul, Matrix.smul_mul]
  have cj_one : revPerm N * (1 : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) * revPerm N = 1 := by
    rw [Matrix.mul_one, revPerm_sq]
  have pair : ∀ m, revPerm N * productMatrix v m * revPerm N = productMatrix v m ∧
      revPerm N * (matrixPair v m).1 * revPerm N = (matrixPair v m).1 := by
    intro m
    induction m with
    | zero =>
      refine ⟨?_, ?_⟩
      · show revPerm N * 1 * revPerm N = 1; exact cj_one
      · show revPerm N * 0 * revPerm N = 0; rw [Matrix.mul_zero, Matrix.zero_mul]
    | succ m ih =>
      obtain ⟨hP, hQ⟩ := ih
      refine ⟨?_, hP⟩
      show revPerm N * ((v.a m)⁻¹ • ((recurrenceMatrix v - v.b m • (1 : Matrix _ _ ℝ)) *
          productMatrix v m - v.c m • (matrixPair v m).1)) * revPerm N = (v.a m)⁻¹ •
          ((recurrenceMatrix v - v.b m • (1 : Matrix _ _ ℝ)) * productMatrix v m -
            v.c m • (matrixPair v m).1)
      rw [cj_smul, cj_sub, cj_smul, hQ, ← conj_mul, cj_sub, cj_smul, cj_one, hJ, hP]
  exact fun m => (pair m).1

/-- `a_n = c_{N-n}` and `b_n = b_{N-n}`. -/
def Palindromic (v : Coefficients N) : Prop :=
  ∀ n, n ≤ N → v.a n = v.c (N - n) ∧ v.b n = v.b (N - n)

/-- **Theorem 7.16** (Palindromic criterion). -/
def Stmt_palindromic : Prop :=
  ∀ (N : ℕ) (v : Coefficients N), Admissible v → Palindromic v →
    ∀ σ : ℕ → ℝ, (∀ n, n ≤ N → 0 < σ n) →
    (∀ j i, j ≤ i → i + 1 ≤ N → v.b j ≤ v.b i) →
    (∀ j i, j ≤ i → i ≤ N → alphaS v σ j ≤ alphaS v σ i) →
    (∀ j i, j ≤ i → i + 2 ≤ N → alphaS v σ j + gammaS v σ j ≤ alphaS v σ i + gammaS v σ i) →
    (∀ j i, j ≤ i → i + j + 2 ≤ N → alphaS v σ j ≤ gammaS v σ i) →
    MatrixPositivity v

theorem palindromic : Stmt_palindromic := by
  intro N v hv hpal σ hσ hβ hα hαγ hedge
  have hlow := low_products N v hv σ hσ hβ hα hαγ hedge
  -- the reversed array agrees with the array on `0, …, N`
  have hra : ∀ i, i ≤ N → (revCoeff v).a i = v.a i := fun i hi => (hpal i hi).1.symm
  have hrb : ∀ i, i ≤ N → (revCoeff v).b i = v.b i := fun i hi => (hpal i hi).2.symm
  have hrc : ∀ i, i ≤ N → (revCoeff v).c i = v.c i := fun i hi => by
    show v.a (N - i) = v.c i
    rw [(hpal (N - i) (by omega)).1, show N - (N - i) = i by omega]
  have hP' := product_congr (revCoeff v) v hra hrb hrc
  have hJ' : recurrenceMatrix (revCoeff v) = recurrenceMatrix v := by
    ext i j; unfold recurrenceMatrix
    rw [hra i.val (by omega), hrb i.val (by omega), hrc i.val (by omega)]
  have hfix := conj_product_fixed v (by rw [← J_rev, hJ'])
  apply deep_reduction N v hv
  · intro m hm n k hnd
    apply hlow m hm n k
    unfold Deep at hnd; omega
  · intro i j hij t
    rw [hP' i (by omega)]
    exact hlow i (by omega) ⟨j, by omega⟩ t (Or.inl (by simp; omega))
  · refine ⟨fun l => if l.val = N then 1 else 0, fun l => by dsimp only; split_ifs <;> norm_num, ?_⟩
    rw [Finset.sum_eq_single ⟨N, by omega⟩]
    · dsimp only
      rw [if_pos rfl, one_smul]
      unfold Rp
      rw [hP' N (by omega), hfix]
    · intro l _ hl; dsimp only; rw [if_neg (fun h => hl (Fin.ext h)), zero_smul]
    · intro h; exact absurd (Finset.mem_univ _) h

/-- **Corollary 7.17** (Monotone palindromic systems). -/
def Stmt_palin_mono : Prop :=
  ∀ (N : ℕ) (v : Coefficients N), Admissible v → (∀ n, n ≤ N → v.b n = 0) →
    (∀ j i, j ≤ i → i ≤ N → v.c j ≤ v.c i) → (∀ n, n ≤ N → v.c n + v.c (N - n) = 1) →
    MatrixPositivity v

theorem palin_mono : Stmt_palin_mono := by
  intro N v hv hb hc hsym
  have hv' := hv
  obtain ⟨hN, _, _, hc0, _, hsum, _, _⟩ := hv'
  have ha : ∀ n, n ≤ N → v.a n = 1 - v.c n := fun n hn => by
    have := hsum n hn; rw [hb n hn] at this; linarith
  have hα : ∀ n, n ≤ N → alphaS v (fun _ => 1) n = v.c n := by
    intro n hn; unfold alphaS
    split_ifs with h
    · rw [h, hc0]
    · simp
  have hγ : ∀ n, n ≤ N → gammaS v (fun _ => 1) n = 1 - v.c n := by
    intro n hn; unfold gammaS; rw [ha n hn]; simp
  apply palindromic N v hv
  · intro n hn
    refine ⟨?_, ?_⟩
    · rw [ha n hn]; have := hsym n hn; linarith
    · rw [hb n hn, hb (N - n) (by omega)]
  · exact fun _ _ => one_pos
  · intro j i _ hi; rw [hb j (by omega), hb i (by omega)]
  · intro j i hji hi; rw [hα j (by omega), hα i hi]; exact hc j i hji hi
  · intro j i _ hi
    rw [hα j (by omega), hα i (by omega), hγ j (by omega), hγ i (by omega)]; ring_nf; exact le_refl _
  · intro j i _ hi
    rw [hα j (by omega), hγ i (by omega)]
    have h1 := hc j (N - i) (by omega) (by omega)
    have h2 := hsym i (by omega)
    linarith

/-- Corollary 7.17 includes the symmetric Krawtchouk array `c_n = n/N`. -/
theorem palin_mono_kraw (N : ℕ) (hN : 1 ≤ N) : MatrixPositivity (krawCoefficients N 1) := by
  apply palin_mono N _ (kraw_admissible N hN 1 one_pos le_rfl)
  · intro n _; simp [krawCoefficients]
  · intro j i hji _
    simp only [krawCoefficients, one_mul]
    apply div_le_div_of_nonneg_right (by exact_mod_cast hji) (by positivity)
  · intro n hn
    simp only [krawCoefficients, one_mul]
    have hN' : (N : ℝ) ≠ 0 := by positivity
    rw [Nat.cast_sub hn]
    field_simp
    ring

end Szkraw
