import Szkraw.AllProducts

/-!
# Theorem 7.10 (Low products) and Corollary 7.11 (Convex profiles)

Under Szwarc's inequalities on the ranges reached by products of total degree at most `N`,
`g(n,m;k) ≥ 0` whenever `n + m ≤ N`. The weights `π_i = Π_{j<i} a_j/c_{j+1}` make `π J`
symmetric, so `π_n g(m,n;k) = π_k g(m,k;n)`; hence `g(n,m;k) ≥ 0` whenever two of the three
indices have sum at most `N`.
-/

namespace Szkraw

open Finset Matrix

variable {N : ℕ}

/-- `π_i = Π_{j<i} a_j / c_{j+1}`. -/
noncomputable def piW (v : Coefficients N) (i : ℕ) : ℝ := ∏ j ∈ range i, v.a j / v.c (j + 1)

theorem piW_pos (v : Coefficients N) (hv : Admissible v) : ∀ i, i ≤ N → 0 < piW v i := by
  intro i hi; apply prod_pos; intro j hj; rw [Finset.mem_range] at hj
  exact div_pos (hv.2.2.2.2.2.2.1 j (by omega)) (hv.2.2.2.2.2.2.2 (j + 1) (by omega) (by omega))

/-- `diag(π) J = Jᵀ diag(π)`. -/
theorem piW_J (v : Coefficients N) (hv : Admissible v) :
    diagonal (fun i : Fin (N + 1) => piW v i) * recurrenceMatrix v =
      (recurrenceMatrix v)ᵀ * diagonal (fun i : Fin (N + 1) => piW v i) := by
  have hc : ∀ i, 0 < i → i ≤ N → v.c i ≠ 0 := fun i h1 h2 => (hv.2.2.2.2.2.2.2 i h1 h2).ne'
  have hs : ∀ i, i < N → piW v (i + 1) * v.c (i + 1) = piW v i * v.a i := by
    intro i hi
    unfold piW; rw [prod_range_succ]
    field_simp [hc (i + 1) (by omega) (by omega)]
  ext i l
  rw [diagonal_mul, mul_diagonal, transpose_apply]
  unfold recurrenceMatrix
  have e : (l = i) ↔ (i = l) := eq_comm
  by_cases h1 : l.val = i.val + 1
  · rw [if_pos h1, if_neg (by omega), if_neg (by omega), if_pos h1]
    rw [← hs i.val (by omega), show l.val = i.val + 1 from h1]; ring
  by_cases h2 : i.val = l.val + 1
  · rw [if_neg h1, if_neg (fun h => by rw [h] at h2; omega), if_pos h2, if_pos h2]
    rw [show i.val = l.val + 1 from h2, hs l.val (by omega)]; ring
  by_cases h3 : l = i
  · subst h3; rw [if_neg h1, if_pos rfl]; ring
  · simp only [if_neg h1, if_neg h3, if_neg h2, if_neg (fun h : i = l => h3 h.symm)]
    ring

/-- `diag(π) p_m(J) = p_m(J)ᵀ diag(π)`. -/
theorem piW_product (v : Coefficients N) (hv : Admissible v) (m : ℕ) :
    diagonal (fun i : Fin (N + 1) => piW v i) * productMatrix v m =
      (productMatrix v m)ᵀ * diagonal (fun i : Fin (N + 1) => piW v i) := by
  set D := diagonal (fun i : Fin (N + 1) => piW v i) with hD
  have hJ := piW_J v hv
  have pair : ∀ m, D * productMatrix v m = (productMatrix v m)ᵀ * D ∧
      D * (matrixPair v m).1 = ((matrixPair v m).1)ᵀ * D := by
    intro m
    induction m with
    | zero =>
      refine ⟨?_, ?_⟩
      · show D * 1 = (1 : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)ᵀ * D
        rw [transpose_one, Matrix.mul_one, Matrix.one_mul]
      · show D * 0 = (0 : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)ᵀ * D
        rw [transpose_zero, Matrix.mul_zero, Matrix.zero_mul]
    | succ m ih =>
      obtain ⟨hP, hQ⟩ := ih
      refine ⟨?_, hP⟩
      have hdef : productMatrix v (m + 1) = (v.a m)⁻¹ •
          ((recurrenceMatrix v - v.b m • (1 : Matrix _ _ ℝ)) * productMatrix v m -
            v.c m • (matrixPair v m).1) := rfl
      have hcomm : (productMatrix v m)ᵀ * (recurrenceMatrix v)ᵀ =
          (recurrenceMatrix v)ᵀ * (productMatrix v m)ᵀ := by
        rw [← transpose_mul, ← transpose_mul, J_commute_product]
      rw [hdef]
      simp only [Matrix.mul_smul, Matrix.smul_mul, transpose_smul, transpose_sub, transpose_mul,
        Matrix.mul_sub, Matrix.sub_mul, transpose_one]
      rw [← Matrix.mul_assoc, hJ, Matrix.mul_assoc, hP, ← Matrix.mul_assoc, ← hcomm,
        Matrix.mul_assoc, ← hJ, ← Matrix.mul_assoc, hQ]
      simp only [Matrix.one_mul, Matrix.mul_one, hP, Matrix.mul_assoc]
  exact (pair m).1

/-- `π_n g(m,n;k) = π_k g(m,k;n)`. -/
theorem piW_entry (v : Coefficients N) (hv : Admissible v) (m : ℕ) (n k : Fin (N + 1)) :
    piW v n * productMatrix v m n k = piW v k * productMatrix v m k n := by
  have h := congrFun (congrFun (piW_product v hv m) n) k
  rw [diagonal_mul, mul_diagonal, transpose_apply] at h
  rw [h]; ring

/-- Theorem 7.10 (Low products), including the consequence for triples with two indices of sum
at most `N`. -/
def Stmt_low_products : Prop :=
  ∀ (N : ℕ) (v : Coefficients N), Admissible v → ∀ σ : ℕ → ℝ, (∀ n, n ≤ N → 0 < σ n) →
    (∀ j i, j ≤ i → i + 1 ≤ N → v.b j ≤ v.b i) →
    (∀ j i, j ≤ i → i ≤ N → alphaS v σ j ≤ alphaS v σ i) →
    (∀ j i, j ≤ i → i + 2 ≤ N → alphaS v σ j + gammaS v σ j ≤ alphaS v σ i + gammaS v σ i) →
    (∀ j i, j ≤ i → i + j + 2 ≤ N → alphaS v σ j ≤ gammaS v σ i) →
    ∀ m, m ≤ N → ∀ n k : Fin (N + 1), (m + n.val ≤ N ∨ m + k.val ≤ N ∨ n.val + k.val ≤ N) →
      0 ≤ productMatrix v m n k

/-- Positivity on all triples with two indices of sum at most `N` follows from positivity on
`m + n ≤ N`. -/
theorem two_of_three (v : Coefficients N) (hv : Admissible v)
    (hlow : ∀ m, m ≤ N → ∀ n k : Fin (N + 1), m + n.val ≤ N → 0 ≤ productMatrix v m n k) :
    ∀ m, m ≤ N → ∀ n k : Fin (N + 1), (m + n.val ≤ N ∨ m + k.val ≤ N ∨ n.val + k.val ≤ N) →
      0 ≤ productMatrix v m n k := by
  have ha : ∀ i, i < N → v.a i ≠ 0 := fun i hi => (hv.2.2.2.2.2.2.1 i hi).ne'
  intro m hm n k h
  rcases h with h | h | h
  · exact hlow m hm n k h
  · have e := piW_entry v hv m n k
    have hk := hlow m hm k n h
    have hpn := piW_pos v hv n.val (by omega)
    have hpk := piW_pos v hv k.val (by omega)
    have : 0 ≤ piW v n * productMatrix v m n k := by rw [e]; positivity
    exact nonneg_of_mul_nonneg_right (by linarith) hpn
  · -- `g(m,n;k) = g(n,m;k)`, then as in the previous case
    have hs := product_symm v ha m n.val hm (by omega) k
    have e : (⟨n.val, by omega⟩ : Fin (N + 1)) = n := Fin.ext rfl
    rw [e] at hs
    rw [hs]
    have e2 := piW_entry v hv n.val ⟨m, by omega⟩ k
    have hk := hlow n.val (by omega) k ⟨m, by omega⟩ h
    have hpm := piW_pos v hv m hm
    have hpk := piW_pos v hv k.val (by omega)
    have : 0 ≤ piW v m * productMatrix v n.val ⟨m, by omega⟩ k := by
      have : piW v (⟨m, by omega⟩ : Fin (N + 1)) = piW v m := rfl
      rw [← this, e2]; positivity
    exact nonneg_of_mul_nonneg_right (by linarith) hpm

theorem low_products : Stmt_low_products := by
  intro N v hv σ hσ hβ hα hαγ hedge
  have hcone : ConeHypLow (alphaS v σ) v.b (gammaS v σ) N :=
    { α_nonneg := alphaS_nonneg hv hσ
      γ_nonneg := gammaS_nonneg hv hσ
      β_mono := hβ
      α_mono := hα
      αγ_mono := hαγ
      edge := hedge }
  apply two_of_three v hv
  intro m hm n k hmn
  exact product_nonneg_of_uS hv hσ k m hm n
    (cone_nonneg_low hcone (alphaS_pos hv hσ) (uS v σ k) (uS_hop hv hσ k) (uS_symm hv k)
      (uS_zero hv hσ k) m n.val hmn)

/-- Hypotheses of Corollary 7.11: constant ratio `c_i = r d_i` (`0 < r ≤ 1`) and a convex
profile (nondecreasing increments). -/
def ConvexProfile (v : Coefficients N) : Prop :=
  ∃ r : ℝ, 0 < r ∧ r ≤ 1 ∧ (∀ i, i ≤ N → v.c i = r * profile v i) ∧
    (∀ i, 1 ≤ i → i + 1 ≤ N → profile v i - profile v (i - 1) ≤ profile v (i + 1) - profile v i)

/-- Corollary 7.11 (Convex profiles). -/
def Stmt_convex_low : Prop :=
  ∀ (N : ℕ) (v : Coefficients N), Admissible v → ConvexProfile v →
    ∀ m, m ≤ N → ∀ n k : Fin (N + 1), (m + n.val ≤ N ∨ m + k.val ≤ N ∨ n.val + k.val ≤ N) →
      0 ≤ productMatrix v m n k

theorem convex_low : Stmt_convex_low := by
  intro N v hv hcp
  obtain ⟨r, hr0, hr1, hc, hconv⟩ := hcp
  obtain ⟨hN, _, hb0, hc0, haN, hsum, _, hcpos⟩ := hv
  set d := profile v with hd
  have hd0 : d 0 = 0 := by rw [hd]; unfold profile; rw [hb0, hc0]; ring
  have hd1 : 0 < d 1 := by
    have h := hcpos 1 (by omega) hN
    rw [hc 1 hN] at h
    exact pos_of_mul_pos_right h hr0.le
  -- increments are at least `d_1 > 0`
  have hinc : ∀ i, i + 1 ≤ N → d 1 ≤ d (i + 1) - d i := by
    intro i hi
    induction i with
    | zero => rw [hd0]; simp
    | succ i ih =>
      have := hconv (i + 1) (by omega) hi
      rw [Nat.add_sub_cancel] at this
      linarith [ih (by omega)]
  have hmono : ∀ j i, j ≤ i → i ≤ N → d j ≤ d i := by
    intro j i hji hi
    induction i with
    | zero => rw [Nat.le_zero.mp hji]
    | succ i ih =>
      rcases Nat.eq_or_lt_of_le hji with h | h
      · rw [h]
      · linarith [ih (by omega) (by omega), hinc i hi]
  -- superadditivity `d_i + d_j ≤ d_{i+j}`
  have hconv' : ∀ p q, p ≤ q → q + 1 ≤ N → d (p + 1) - d p ≤ d (q + 1) - d q := by
    intro p q hpq hq
    induction q with
    | zero => rw [Nat.le_zero.mp hpq]
    | succ q ih =>
      rcases Nat.eq_or_lt_of_le hpq with h | h
      · rw [h]
      · have := hconv (q + 1) (by omega) hq
        rw [Nat.add_sub_cancel] at this
        linarith [ih (by omega) (by omega)]
  have hsup : ∀ i j, i + j ≤ N → d i + d j ≤ d (i + j) := by
    intro i j hij
    induction i with
    | zero => rw [hd0]; simp
    | succ i ih =>
      have h1 := ih (by omega)
      have h2 := hconv' i (i + j) (by omega) (by omega)
      rw [show i + 1 + j = i + j + 1 by omega]
      linarith
  have ha_eq : ∀ i, i ≤ N → v.a i = 1 - d i := fun i hi => by
    have := hsum i hi; rw [hd]; unfold profile; linarith
  have hb_eq : ∀ i, i ≤ N → v.b i = (1 - r) * d i := fun i hi => by
    have := hc i hi; rw [hd] at this ⊢; unfold profile at this ⊢; linarith
  have hdN : d N = 1 := by have := ha_eq N le_rfl; rw [haN] at this; linarith
  set ρ := Real.sqrt r with hρ_def
  have hρ : 0 < ρ := Real.sqrt_pos.mpr hr0
  have hρ2 : ρ ^ 2 = r := Real.sq_sqrt hr0.le
  set σ : ℕ → ℝ := fun n => ρ ^ n with hσ
  have hαe : ∀ n, n ≤ N → alphaS v σ n = ρ * d n := by
    intro n hn
    unfold alphaS
    split_ifs with h
    · rw [h, hd0]; ring
    · obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
      rw [hc (n' + 1) hn, Nat.add_sub_cancel, ← hρ2]
      simp only [hσ]
      field_simp
      ring
  have hγe : ∀ n, n ≤ N → gammaS v σ n = ρ * (1 - d n) := by
    intro n hn
    unfold gammaS
    rw [ha_eq n hn]
    simp only [hσ]
    field_simp
    ring
  apply low_products N v ⟨hN, by assumption, hb0, hc0, haN, hsum, by assumption, hcpos⟩ σ
    (fun n _ => pow_pos hρ n)
  · intro j i hji hi
    rw [hb_eq j (by omega), hb_eq i (by omega)]
    exact mul_le_mul_of_nonneg_left (hmono j i hji (by omega)) (by linarith)
  · intro j i hji hi
    rw [hαe j (by omega), hαe i hi]
    exact mul_le_mul_of_nonneg_left (hmono j i hji hi) hρ.le
  · intro j i hji hi
    rw [hαe j (by omega), hαe i (by omega), hγe j (by omega), hγe i (by omega)]
    ring_nf; exact le_refl _
  · intro j i hji hi
    rw [hαe j (by omega), hγe i (by omega)]
    have h1 := hsup i j (by omega)
    have h2 := hmono (i + j) N (by omega) le_rfl
    rw [hdN] at h2
    exact mul_le_mul_of_nonneg_left (by linarith) hρ.le

/-- Corollary 7.11 includes every array of Theorem 2.1 (the arrays (2.3)). -/
theorem geometric_convex (v : Coefficients N) (hv : Admissible v) (hg : Geometric v) :
    ConvexProfile v := by
  obtain ⟨β, q, hβ, hq, hbc, hpos, hgeo⟩ := hg
  obtain ⟨_, _, hb0, hc0, _, _, _, _⟩ := hv
  refine ⟨1 / (1 + β), by positivity, ?_, ?_, ?_⟩
  · rw [div_le_one (by linarith)]; linarith
  · intro i hi
    unfold profile
    rcases Nat.eq_zero_or_pos i with h | h
    · subst h; rw [hb0, hc0]; ring
    · rw [hbc i h hi]; field_simp; ring
  · intro i h1 h2
    have hg' := hgeo i h1 (by omega)
    have hp := hpos i h1 (by omega)
    unfold profile
    rw [hg']
    nlinarith

end Szkraw
