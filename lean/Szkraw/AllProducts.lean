import Szkraw.ConeArgument
import Szkraw.LCAssembly
import Szkraw.RowZero

/-!
# Theorem 7.12 (All products) and Corollary 7.13 (Heavy top step)

For a positive renormalization `σ`, put `α_n = c_n σ_{n-1}/σ_n` (`α_0 = 0`),
`β_n = b_n` and `γ_n = a_n σ_{n+1}/σ_n` (so `γ_N = 0`). If `β, α` and `α + γ` are
nondecreasing on `{0,…,N}` and `γ_i ≥ α_j` for `j ≤ i ≤ N-1`, every product coefficient is
nonnegative. The product coefficients, rescaled by `w_m w_n`, satisfy `Hu = 0` on the square,
and the cone argument applies.
-/

namespace Szkraw

open Finset

variable {N : ℕ}

/-- `α_n = c_n σ_{n-1}/σ_n`, with `α_0 = 0`. -/
noncomputable def alphaS (v : Coefficients N) (σ : ℕ → ℝ) (n : ℕ) : ℝ :=
  if n = 0 then 0 else v.c n * σ (n - 1) / σ n

/-- `γ_n = a_n σ_{n+1}/σ_n`. -/
noncomputable def gammaS (v : Coefficients N) (σ : ℕ → ℝ) (n : ℕ) : ℝ := v.a n * σ (n + 1) / σ n

/-- Theorem 7.12 (All products). -/
def Stmt_all_products : Prop :=
  ∀ (N : ℕ) (v : Coefficients N), Admissible v → ∀ σ : ℕ → ℝ, (∀ n, n ≤ N → 0 < σ n) →
    (∀ j i, j ≤ i → i ≤ N → v.b j ≤ v.b i) →
    (∀ j i, j ≤ i → i ≤ N → alphaS v σ j ≤ alphaS v σ i) →
    (∀ j i, j ≤ i → i ≤ N → alphaS v σ j + gammaS v σ j ≤ alphaS v σ i + gammaS v σ i) →
    (∀ j i, j ≤ i → i + 1 ≤ N → alphaS v σ j ≤ gammaS v σ i) →
    MatrixPositivity v

/-- The product coefficients `g(m,n;k)` for fixed `k`, extended by zero off the square. -/
noncomputable def Gk (v : Coefficients N) (k : Fin (N + 1)) (m n : ℕ) : ℝ :=
  if h : m ≤ N ∧ n ≤ N then productMatrix v m ⟨n, by omega⟩ k else 0

theorem Gk_symm (v : Coefficients N) (ha : ∀ i, i < N → v.a i ≠ 0) (k : Fin (N + 1)) (m n : ℕ) :
    Gk v k m n = Gk v k n m := by
  unfold Gk
  by_cases h : m ≤ N ∧ n ≤ N
  · rw [dif_pos h, dif_pos ⟨h.2, h.1⟩, product_symm v ha m n h.1 h.2]
  · rw [dif_neg h, dif_neg (by omega)]

/-- The entry recurrence on the square: `x` acts on either factor. -/
theorem Gk_rel (v : Coefficients N) (ha : ∀ i, i < N → v.a i ≠ 0) (haN : v.a N = 0)
    (k : Fin (N + 1)) (m n : ℕ) (hm : m ≤ N) (hn : n ≤ N) :
    v.a m * Gk v k (m + 1) n + v.b m * Gk v k m n + (if 1 ≤ m then v.c m * Gk v k (m - 1) n else 0) =
      v.a n * Gk v k m (n + 1) + v.b n * Gk v k m n + (if 1 ≤ n then v.c n * Gk v k m (n - 1) else 0) := by
  -- the case `m < N`, from the definition of `productMatrix`
  have lower : ∀ m n, m < N → n ≤ N →
      v.a m * Gk v k (m + 1) n + v.b m * Gk v k m n + (if 1 ≤ m then v.c m * Gk v k (m - 1) n else 0) =
      v.a n * Gk v k m (n + 1) + v.b n * Gk v k m n + (if 1 ≤ n then v.c n * Gk v k m (n - 1) else 0) := by
    intro m n hm hn
    have hdef : productMatrix v (m + 1) = (v.a m)⁻¹ •
        ((recurrenceMatrix v - v.b m • (1 : Matrix _ _ ℝ)) * productMatrix v m -
          v.c m • (matrixPair v m).1) := rfl
    have hG1 : Gk v k (m + 1) n = productMatrix v (m + 1) ⟨n, by omega⟩ k := by
      unfold Gk; rw [dif_pos ⟨by omega, hn⟩]
    have hrow : ∀ l : Fin (N + 1), productMatrix v m l k = Gk v k m l.val := by
      intro l; unfold Gk; rw [dif_pos ⟨by omega, by omega⟩]
    have hQ : (matrixPair v m).1 ⟨n, by omega⟩ k = if 1 ≤ m then Gk v k (m - 1) n else 0 := by
      rcases m with _ | m'
      · rw [if_neg (by omega)]; rfl
      · rw [if_pos (by omega), Nat.add_sub_cancel]
        show productMatrix v m' ⟨n, by omega⟩ k = _
        unfold Gk; rw [dif_pos ⟨by omega, hn⟩]
    rw [hG1, hdef]
    simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.sub_mul, Matrix.smul_mul,
      Matrix.one_mul, smul_eq_mul]
    rw [J_mul_apply v _ (fun l => Gk v k m l) ⟨n, by omega⟩ k hrow, hQ, hrow ⟨n, by omega⟩]
    simp only
    rw [← mul_assoc, mul_inv_cancel₀ (ha m hm), one_mul]
    have e1 : (if n + 1 ≤ N then v.a n * Gk v k m (n + 1) else 0) = v.a n * Gk v k m (n + 1) := by
      split_ifs with h
      · rfl
      · have : n = N := by omega
        subst this; rw [haN]; ring
    rw [e1]
    split_ifs <;> ring
  rcases Nat.lt_or_ge m N with hmN | hmN
  · exact lower m n hmN hn
  have hmN' : m = N := by omega
  rw [hmN']
  rcases Nat.lt_or_ge n N with hnN | hnN
  · -- swap the roles, using symmetry
    have h := lower n N hnN le_rfl
    rw [Gk_symm v ha k (N + 1) n, Gk_symm v ha k N n, Gk_symm v ha k (N - 1) n,
      Gk_symm v ha k N (n + 1), Gk_symm v ha k N (n - 1)]
    linarith
  · have hn' : n = N := by omega
    rw [hn', Gk_symm v ha k (N + 1) N, Gk_symm v ha k (N - 1) N]

/-- `w_m = Π_{l<m} a_l σ_{l+1} / (c_{l+1} σ_l)`. -/
noncomputable def wS (v : Coefficients N) (σ : ℕ → ℝ) (m : ℕ) : ℝ :=
  ∏ l ∈ range m, (v.a l * σ (l + 1)) / (v.c (l + 1) * σ l)

/-- The rescaled coefficient array `u(i,j) = w_i w_j g(i,j;k)`. -/
noncomputable def uS (v : Coefficients N) (σ : ℕ → ℝ) (k : Fin (N + 1)) (i j : ℕ) : ℝ :=
  wS v σ i * wS v σ j * Gk v k i j

section rescaled

variable {v : Coefficients N} {σ : ℕ → ℝ}

theorem wS_pos (hv : Admissible v) (hσ : ∀ n, n ≤ N → 0 < σ n) : ∀ m, m ≤ N → 0 < wS v σ m := by
  intro m hm; apply prod_pos; intro l hl; rw [Finset.mem_range] at hl
  exact div_pos (mul_pos (hv.2.2.2.2.2.2.1 l (by omega)) (hσ (l + 1) (by omega)))
    (mul_pos (hv.2.2.2.2.2.2.2 (l + 1) (by omega) (by omega)) (hσ l (by omega)))

theorem alphaS_nonneg (hv : Admissible v) (hσ : ∀ n, n ≤ N → 0 < σ n) :
    ∀ i, i ≤ N → 0 ≤ alphaS v σ i := fun i hi => by
  unfold alphaS; split_ifs with h
  · exact le_refl 0
  · exact div_nonneg (mul_nonneg (hv.2.2.2.2.2.2.2 i (by omega) hi).le (hσ (i - 1) (by omega)).le)
      (hσ i hi).le

theorem alphaS_pos (hv : Admissible v) (hσ : ∀ n, n ≤ N → 0 < σ n) :
    ∀ m, 1 ≤ m → m ≤ N → 0 < alphaS v σ m := fun m h1 hm => by
  unfold alphaS; rw [if_neg (by omega)]
  exact div_pos (mul_pos (hv.2.2.2.2.2.2.2 m (by omega) hm) (hσ (m - 1) (by omega))) (hσ m hm)

theorem gammaS_nonneg (hv : Admissible v) (hσ : ∀ n, n ≤ N → 0 < σ n) :
    ∀ i, i ≤ N → 0 ≤ gammaS v σ i := fun i hi => by
  unfold gammaS
  rcases Nat.lt_or_ge i N with h | h
  · exact div_nonneg (mul_nonneg (hv.2.2.2.2.2.2.1 i h).le (hσ (i + 1) (by omega)).le) (hσ i hi).le
  · rw [show i = N by omega, hv.2.2.2.2.1]; simp

theorem gammaS_top (hv : Admissible v) : gammaS v σ N = 0 := by
  unfold gammaS; rw [hv.2.2.2.2.1]; simp

theorem uS_out (k : Fin (N + 1)) : ∀ i j, N < i ∨ N < j → uS v σ k i j = 0 := by
  intro i j h; unfold uS Gk; rw [dif_neg (by omega), mul_zero]

theorem uS_symm (hv : Admissible v) (k : Fin (N + 1)) : ∀ i j, uS v σ k i j = uS v σ k j i := by
  intro i j; unfold uS
  rw [Gk_symm v (fun i hi => (hv.2.2.2.2.2.2.1 i hi).ne') k i j]; ring

theorem uS_zero (hv : Admissible v) (hσ : ∀ n, n ≤ N → 0 < σ n) (k : Fin (N + 1)) :
    ∀ i, 0 ≤ uS v σ k i 0 := by
  intro i
  unfold uS
  by_cases hi : i ≤ N
  · unfold Gk; rw [dif_pos ⟨hi, by omega⟩]
    have hz : productMatrix v i ⟨0, by omega⟩ k = if k.val = i then 1 else 0 :=
      row_zero v (fun i hi => (hv.2.2.2.2.2.2.1 i hi).ne') i hi k
    rw [hz]
    have := wS_pos hv hσ i hi; have := wS_pos hv hσ 0 (by omega)
    split_ifs <;> positivity
  · unfold Gk; rw [dif_neg (by omega), mul_zero]

theorem uS_hop (hv : Admissible v) (hσ : ∀ n, n ≤ N → 0 < σ n) (k : Fin (N + 1)) :
    ∀ i j, i ≤ N → j ≤ N → Hop (alphaS v σ) v.b (gammaS v σ) (uS v σ k) i j = 0 := by
  obtain ⟨hN, _, _, hc0, haN, _, hapos, hcpos⟩ := hv
  have ha : ∀ i, i < N → v.a i ≠ 0 := fun i hi => (hapos i hi).ne'
  have hw_succ : ∀ m, wS v σ (m + 1) = wS v σ m * ((v.a m * σ (m + 1)) / (v.c (m + 1) * σ m)) :=
    fun m => prod_range_succ _ _
  -- the identities `α_{m+1} w_{m+1} = a_m w_m` and `γ_{m-1} w_{m-1} = c_m w_m`
  have idA : ∀ m, m < N → alphaS v σ (m + 1) * wS v σ (m + 1) = v.a m * wS v σ m := by
    intro m hm
    unfold alphaS; rw [if_neg (by omega), hw_succ, Nat.add_sub_cancel]
    have := hσ m (by omega); have := hσ (m + 1) (by omega)
    have := hcpos (m + 1) (by omega) (by omega)
    field_simp
  have idC : ∀ m, 1 ≤ m → m ≤ N → gammaS v σ (m - 1) * wS v σ (m - 1) = v.c m * wS v σ m := by
    intro m h1 hm
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    unfold gammaS; rw [hw_succ, Nat.add_sub_cancel]
    have := hσ m' (by omega); have := hσ (m' + 1) (by omega)
    have := hcpos (m' + 1) (by omega) (by omega)
    field_simp
  intro i j hi hj
  have rel := Gk_rel v ha haN k i j hi hj
  unfold Hop uS
  have tA : ∀ x y, x ≤ N → alphaS v σ (x + 1) * (wS v σ (x + 1) * wS v σ y * Gk v k (x + 1) y) =
      wS v σ x * wS v σ y * (v.a x * Gk v k (x + 1) y) := by
    intro x y hx
    rcases Nat.lt_or_ge x N with h | h
    · rw [← mul_assoc, ← mul_assoc, idA x h]; ring
    · unfold Gk; rw [dif_neg (by omega)]; ring
  have tA' : ∀ x y, y ≤ N → alphaS v σ (y + 1) * (wS v σ x * wS v σ (y + 1) * Gk v k x (y + 1)) =
      wS v σ x * wS v σ y * (v.a y * Gk v k x (y + 1)) := by
    intro x y hy
    rcases Nat.lt_or_ge y N with h | h
    · have := idA y h
      calc alphaS v σ (y + 1) * (wS v σ x * wS v σ (y + 1) * Gk v k x (y + 1))
          = wS v σ x * (alphaS v σ (y + 1) * wS v σ (y + 1)) * Gk v k x (y + 1) := by ring
        _ = _ := by rw [this]; ring
    · unfold Gk; rw [dif_neg (by omega)]; ring
  have tC : ∀ x y, x ≤ N → (if 1 ≤ x then gammaS v σ (x - 1) * (wS v σ (x - 1) * wS v σ y *
      Gk v k (x - 1) y) else 0) = wS v σ x * wS v σ y *
      (if 1 ≤ x then v.c x * Gk v k (x - 1) y else 0) := by
    intro x y hx
    split_ifs with h
    · have := idC x h hx
      calc gammaS v σ (x - 1) * (wS v σ (x - 1) * wS v σ y * Gk v k (x - 1) y)
          = (gammaS v σ (x - 1) * wS v σ (x - 1)) * wS v σ y * Gk v k (x - 1) y := by ring
        _ = _ := by rw [this]; ring
    · ring
  have tC' : ∀ x y, y ≤ N → (if 1 ≤ y then gammaS v σ (y - 1) * (wS v σ x * wS v σ (y - 1) *
      Gk v k x (y - 1)) else 0) = wS v σ x * wS v σ y *
      (if 1 ≤ y then v.c y * Gk v k x (y - 1) else 0) := by
    intro x y hy
    split_ifs with h
    · have := idC y h hy
      calc gammaS v σ (y - 1) * (wS v σ x * wS v σ (y - 1) * Gk v k x (y - 1))
          = wS v σ x * (gammaS v σ (y - 1) * wS v σ (y - 1)) * Gk v k x (y - 1) := by ring
        _ = _ := by rw [this]; ring
    · ring
  rw [tA i j hi, tA' i j hj, tC i j hi, tC' i j hj]
  linear_combination (wS v σ i * wS v σ j) * rel

/-- Nonnegativity of `u(m,n)` transfers to `g(m,n;k)`. -/
theorem product_nonneg_of_uS (hv : Admissible v) (hσ : ∀ n, n ≤ N → 0 < σ n) (k : Fin (N + 1))
    (m : ℕ) (hm : m ≤ N) (n : Fin (N + 1)) (h : 0 ≤ uS v σ k m n.val) : 0 ≤ productMatrix v m n k := by
  unfold uS Gk at h
  rw [dif_pos ⟨hm, by omega⟩] at h
  have hpos := mul_pos (wS_pos hv hσ m hm) (wS_pos hv hσ n.val (by omega))
  have e : (⟨n.val, by omega⟩ : Fin (N + 1)) = n := Fin.ext rfl
  rw [e] at h
  exact nonneg_of_mul_nonneg_right (by linarith) hpos

end rescaled

theorem all_products : Stmt_all_products := by
  intro N v hv σ hσ hβ hα hαγ hedge
  have hcone : ConeHyp (alphaS v σ) v.b (gammaS v σ) N :=
    { α_nonneg := alphaS_nonneg hv hσ
      γ_nonneg := gammaS_nonneg hv hσ
      β_mono := hβ
      α_mono := hα
      αγ_mono := hαγ
      edge := hedge }
  intro m hm n k
  exact product_nonneg_of_uS hv hσ k m hm n
    (cone_nonneg hcone (gammaS_top hv) (alphaS_pos hv hσ) (uS v σ k) (uS_out k) (uS_hop hv hσ k)
      (uS_symm hv k) (uS_zero hv hσ k) m n.val)

/-- Hypotheses of Corollary 7.13: constant ratio `c_i = r d_i` (`0 < r ≤ 1`), an increasing
profile, and `d_{N-1} ≤ 1/2`. -/
def HeavyTop (v : Coefficients N) : Prop :=
  ∃ r : ℝ, 0 < r ∧ r ≤ 1 ∧ (∀ i, i ≤ N → v.c i = r * profile v i) ∧
    (∀ i, i < N → profile v i < profile v (i + 1)) ∧ profile v (N - 1) ≤ 1 / 2

/-- Corollary 7.13 (Heavy top step). -/
def Stmt_heavy_top : Prop :=
  ∀ (N : ℕ) (v : Coefficients N), Admissible v → HeavyTop v → MatrixPositivity v

theorem heavy_top : Stmt_heavy_top := by
  intro N v hv hh
  obtain ⟨r, hr0, hr1, hc, hinc, hhalf⟩ := hh
  obtain ⟨hN, _, hb0, hc0, haN, hsum, _, _⟩ := hv
  set d := profile v with hd
  have hmono : ∀ j i, j ≤ i → i ≤ N → d j ≤ d i := by
    intro j i hji hi
    induction i with
    | zero => rw [Nat.le_zero.mp hji]
    | succ i ih =>
      rcases Nat.eq_or_lt_of_le hji with h | h
      · rw [h]
      · exact le_trans (ih (by omega) (by omega)) (hinc i (by omega)).le
  have ha_eq : ∀ i, i ≤ N → v.a i = 1 - d i := fun i hi => by
    have := hsum i hi; rw [hd]; unfold profile; linarith
  have hb_eq : ∀ i, i ≤ N → v.b i = (1 - r) * d i := fun i hi => by
    have := hc i hi; rw [hd] at this ⊢; unfold profile at this ⊢; linarith
  have hd0 : d 0 = 0 := by rw [hd]; unfold profile; rw [hb0, hc0]; ring
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
  apply all_products N v ⟨hN, by assumption, hb0, hc0, haN, hsum, by assumption, by assumption⟩ σ
    (fun n _ => pow_pos hρ n)
  · intro j i hji hi
    rw [hb_eq j (by omega), hb_eq i hi]
    exact mul_le_mul_of_nonneg_left (hmono j i hji hi) (by linarith)
  · intro j i hji hi
    rw [hαe j (by omega), hαe i hi]
    exact mul_le_mul_of_nonneg_left (hmono j i hji hi) hρ.le
  · intro j i hji hi
    rw [hαe j (by omega), hαe i hi, hγe j (by omega), hγe i hi]
    ring_nf; exact le_refl _
  · intro j i hji hi
    rw [hαe j (by omega), hγe i (by omega)]
    have h1 := hmono j i hji (by omega)
    have h2 := hmono i (N - 1) (by omega) (by omega)
    exact mul_le_mul_of_nonneg_left (by linarith) hρ.le

end Szkraw
