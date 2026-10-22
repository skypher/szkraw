import Szkraw.Reversal

/-!
# Quadratic decomposition of symmetric finite systems (paper, Theorem 7.8)

For a symmetric array (`b ≡ 0`) on `0, …, M` with `M = 2N`, the product coefficients with an
even column are those of the even component, and those with an odd column are combinations of
the odd component's coefficients. We work with the column-wise coefficient arrays
`Gk v k m n = g(m,n;k)`.
-/

namespace Szkraw

open Finset Matrix

section symmetric

variable {M : ℕ} (v : Coefficients M)

/-- The entry relation without boundary cases, for `b ≡ 0` and `c_0 = 0`. -/
theorem Gk_rel_sym (hv : Admissible v) (hb : ∀ i, i ≤ M → v.b i = 0) (k : Fin (M + 1))
    (m n : ℕ) (hm : m ≤ M) (hn : n ≤ M) :
    v.a m * Gk v k (m + 1) n + v.c m * Gk v k (m - 1) n =
      v.a n * Gk v k m (n + 1) + v.c n * Gk v k m (n - 1) := by
  have ha : ∀ i, i < M → v.a i ≠ 0 := fun i hi => (hv.2.2.2.2.2.2.1 i hi).ne'
  have h := Gk_rel v ha hv.2.2.2.2.1 k m n hm hn
  rw [hb m hm, hb n hn] at h
  have e1 : (if 1 ≤ m then v.c m * Gk v k (m - 1) n else 0) = v.c m * Gk v k (m - 1) n := by
    split_ifs with h1
    · rfl
    · rw [show m = 0 by omega, hv.2.2.2.1, zero_mul]
  have e2 : (if 1 ≤ n then v.c n * Gk v k m (n - 1) else 0) = v.c n * Gk v k m (n - 1) := by
    split_ifs with h1
    · rfl
    · rw [show n = 0 by omega, hv.2.2.2.1, zero_mul]
  rw [e1, e2] at h
  linarith

/-- Parity: `g(m,n;k) = 0` when `m + n + k` is odd. -/
theorem Gk_parity (hv : Admissible v) (hb : ∀ i, i ≤ M → v.b i = 0) (k : Fin (M + 1)) :
    ∀ m n, (m + n + k.val) % 2 = 1 → Gk v k m n = 0 := by
  have hc0 := hv.2.2.2.1
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro n hpar
    by_cases hout : M < m ∨ M < n
    · unfold Gk; rw [dif_neg (by omega)]
    push Not at hout
    rcases m with _ | m
    · -- row `0` of `p_0(J) = 1`
      unfold Gk; rw [dif_pos ⟨by omega, by omega⟩]
      show (1 : Matrix (Fin (M + 1)) (Fin (M + 1)) ℝ) _ k = 0
      rw [Matrix.one_apply, if_neg (fun h => by rw [Fin.ext_iff] at h; simp at h; omega)]
    · have h := Gk_rel_sym v hv hb k m n (by omega) hout.2
      have hz1 : Gk v k (m - 1) n = 0 ∨ v.c m = 0 := by
        rcases Nat.eq_zero_or_pos m with h0 | h0
        · right; rw [h0, hc0]
        · left; exact ih (m - 1) (by omega) n (by omega)
      have hz2 : Gk v k m (n + 1) = 0 := ih m (by omega) (n + 1) (by omega)
      have hz3 : Gk v k m (n - 1) = 0 ∨ v.c n = 0 := by
        rcases Nat.eq_zero_or_pos n with h0 | h0
        · right; rw [h0, hc0]
        · left; exact ih m (by omega) (n - 1) (by omega)
      have hz : v.a m * Gk v k (m + 1) n = 0 := by
        rcases hz1 with h1 | h1 <;> rcases hz3 with h3 | h3 <;>
          · rw [h1, hz2, h3] at h; linarith
      exact (mul_eq_zero.mp hz).resolve_left (hv.2.2.2.2.2.2.1 m (by omega)).ne'

end symmetric

section decomposition

variable {N : ℕ} (v : Coefficients (2 * N))

/-- The even component before normalization: `â_n = a_{2n}a_{2n+1}`,
`b̂_n = c_{2n}a_{2n-1} + a_{2n}c_{2n+1}`, `ĉ_n = c_{2n}c_{2n-1}`. -/
def evenRaw : Coefficients N :=
  ⟨fun n => v.a (2 * n) * v.a (2 * n + 1),
   fun n => v.c (2 * n) * v.a (2 * n - 1) + v.a (2 * n) * v.c (2 * n + 1),
   fun n => v.c (2 * n) * v.c (2 * n - 1)⟩

/-- The odd component before normalization: `ǎ_n = a_{2n+1}a_{2n+2}`,
`b̌_n = a_{2n+1}c_{2n+2} + c_{2n+1}a_{2n}`, `č_n = c_{2n+1}c_{2n}`. -/
def oddRaw : Coefficients (N - 1) :=
  ⟨fun n => v.a (2 * n + 1) * v.a (2 * n + 2),
   fun n => v.a (2 * n + 1) * v.c (2 * n + 2) + v.c (2 * n + 1) * v.a (2 * n),
   fun n => v.c (2 * n + 1) * v.c (2 * n)⟩

/-- The even-column coefficients as a function of the halved indices. -/
noncomputable def Geven (a b c : ℕ) : ℝ :=
  if h : c ≤ N then Gk v ⟨2 * c, by omega⟩ (2 * a) (2 * b) else 0

/-- `g(2a,2b;2c) = ĝ(a,b;c)` (with the unnormalized even component). -/
theorem even_block (hv : Admissible v) (hb : ∀ i, i ≤ 2 * N → v.b i = 0) :
    ∀ a, a ≤ N → ∀ b c : Fin (N + 1),
      productMatrix (evenRaw v) a b c = Geven v a b.val c.val := by
  have hc0 := hv.2.2.2.1
  have haN := hv.2.2.2.2.1
  apply product_eq_of_rec (evenRaw v) (Geven v)
  · intro i hi
    exact mul_ne_zero (hv.2.2.2.2.2.2.1 (2 * i) (by omega)).ne'
      (hv.2.2.2.2.2.2.1 (2 * i + 1) (by omega)).ne'
  · intro b c hb' hc'
    unfold Geven Gk
    rw [dif_pos hc', dif_pos ⟨by omega, by omega⟩]
    show (1 : Matrix (Fin (2 * N + 1)) (Fin (2 * N + 1)) ℝ) _ _ = _
    rw [Matrix.one_apply]
    by_cases h : b = c
    · subst h; simp
    · rw [if_neg (fun h' => h (by rw [Fin.ext_iff] at h'; simp at h'; omega)), if_neg h]
  · intro a b c ha hb' hc'
    unfold Geven
    simp only [dif_pos hc']
    set k : Fin (2 * N + 1) := ⟨2 * c, by omega⟩
    set G := Gk v k
    have rel := fun m n (hm : m ≤ 2 * N) (hn : n ≤ 2 * N) => Gk_rel_sym v hv hb k m n hm hn
    have R1 := rel (2 * a + 1) (2 * b) (by omega) (by omega)
    have R2 : v.a (2 * b) * (v.a (2 * a) * G (2 * a + 1) (2 * b + 1) + v.c (2 * a) * G (2 * a - 1) (2 * b + 1)
        - v.a (2 * b + 1) * G (2 * a) (2 * b + 2) - v.c (2 * b + 1) * G (2 * a) (2 * b)) = 0 := by
      rcases Nat.lt_or_ge b N with h | h
      · have := rel (2 * a) (2 * b + 1) (by omega) (by omega)
        rw [show 2 * a - 1 = 2 * a - 1 from rfl] at this
        simp only [show 2 * b + 1 + 1 = 2 * b + 2 by omega, show 2 * b + 1 - 1 = 2 * b by omega] at this
        rw [this]; ring
      · rw [show 2 * b = 2 * N by omega, haN, zero_mul]
    have R3 : v.c (2 * b) * (v.a (2 * a) * G (2 * a + 1) (2 * b - 1) + v.c (2 * a) * G (2 * a - 1) (2 * b - 1)
        - v.a (2 * b - 1) * G (2 * a) (2 * b) - v.c (2 * b - 1) * G (2 * a) (2 * b - 2)) = 0 := by
      rcases Nat.eq_zero_or_pos b with h | h
      · rw [h, Nat.mul_zero, hc0, zero_mul]
      · have := rel (2 * a) (2 * b - 1) (by omega) (by omega)
        simp only [show 2 * b - 1 + 1 = 2 * b by omega, show 2 * b - 1 - 1 = 2 * b - 2 by omega] at this
        rw [this]; ring
    have R4 : v.c (2 * a) * (v.a (2 * a - 1) * G (2 * a) (2 * b) + v.c (2 * a - 1) * G (2 * a - 2) (2 * b)
        - v.a (2 * b) * G (2 * a - 1) (2 * b + 1) - v.c (2 * b) * G (2 * a - 1) (2 * b - 1)) = 0 := by
      rcases Nat.eq_zero_or_pos a with h | h
      · rw [h, Nat.mul_zero, hc0, zero_mul]
      · have := rel (2 * a - 1) (2 * b) (by omega) (by omega)
        simp only [show 2 * a - 1 + 1 = 2 * a by omega, show 2 * a - 1 - 1 = 2 * a - 2 by omega] at this
        rw [this]; ring
    simp only [show 2 * a + 1 + 1 = 2 * a + 2 by omega, show 2 * a + 1 - 1 = 2 * a by omega] at R1
    -- the target, with halved indices
    unfold evenRaw
    simp only
    rw [show 2 * (a + 1) = 2 * a + 2 by ring]
    have e1 : (if b + 1 ≤ N then v.a (2 * b) * v.a (2 * b + 1) * G (2 * a) (2 * (b + 1)) else 0) =
        v.a (2 * b) * v.a (2 * b + 1) * G (2 * a) (2 * b + 2) := by
      split_ifs with h
      · rw [show 2 * (b + 1) = 2 * b + 2 by ring]
      · rw [show 2 * b = 2 * N by omega, haN]; ring
    have e2 : (if 1 ≤ b then v.c (2 * b) * v.c (2 * b - 1) * G (2 * a) (2 * (b - 1)) else 0) =
        v.c (2 * b) * v.c (2 * b - 1) * G (2 * a) (2 * b - 2) := by
      split_ifs with h
      · rw [show 2 * (b - 1) = 2 * b - 2 by omega]
      · rw [show b = 0 by omega, Nat.mul_zero, hc0]; ring
    have e3 : (if 1 ≤ a then v.c (2 * a) * v.c (2 * a - 1) * G (2 * (a - 1)) (2 * b) else 0) =
        v.c (2 * a) * v.c (2 * a - 1) * G (2 * a - 2) (2 * b) := by
      split_ifs with h
      · rw [show 2 * (a - 1) = 2 * a - 2 by omega]
      · rw [show a = 0 by omega, Nat.mul_zero, hc0]; ring
    rw [e1, e2, e3]
    linear_combination v.a (2 * a) * R1 + R2 + R3 + R4

end decomposition

/-- Column version of `product_eq_of_rec`: for a fixed column `k`, an array satisfying the entry
recurrence of `p_m(J)` with `p_0(J) = 1` in that column is the column of `productMatrix`. -/
theorem product_eq_of_rec_col {N : ℕ} (v : Coefficients N) (k : Fin (N + 1)) (G : ℕ → ℕ → ℝ)
    (ha : ∀ i, i < N → v.a i ≠ 0)
    (h0 : ∀ n : ℕ, n ≤ N → G 0 n = if n = k.val then 1 else 0)
    (hrec : ∀ m n, m + 1 ≤ N → n ≤ N →
      v.a m * G (m + 1) n =
        (if n + 1 ≤ N then v.a n * G m (n + 1) else 0) + v.b n * G m n +
        (if 1 ≤ n then v.c n * G m (n - 1) else 0) - v.b m * G m n -
        (if 1 ≤ m then v.c m * G (m - 1) n else 0)) :
    ∀ m, m ≤ N → ∀ n : Fin (N + 1), productMatrix v m n k = G m n := by
  have claim : ∀ m, m ≤ N → (∀ n : Fin (N + 1), productMatrix v m n k = G m n) ∧
      (∀ n : Fin (N + 1), (matrixPair v m).1 n k = if m = 0 then 0 else G (m - 1) n) := by
    intro m
    induction m with
    | zero =>
      intro _
      refine ⟨fun n => ?_, fun n => ?_⟩
      · show (1 : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) n k = _
        rw [Matrix.one_apply, h0 n (by omega)]
        simp only [Fin.val_inj]
      · show (0 : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) n k = _
        simp
    | succ m ih =>
      intro hm
      obtain ⟨ihP, ihQ⟩ := ih (by omega)
      refine ⟨fun n => ?_, fun n => ?_⟩
      · have hdef : productMatrix v (m + 1) = (v.a m)⁻¹ •
            ((recurrenceMatrix v - v.b m • (1 : Matrix _ _ ℝ)) * productMatrix v m -
              v.c m • (matrixPair v m).1) := rfl
        rw [hdef]
        simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.sub_mul, Matrix.smul_mul,
          Matrix.one_mul, smul_eq_mul]
        rw [J_mul_apply v _ (fun l => G m l) n k (fun l => ihP l), ihP n, ihQ n]
        have hr := hrec m n hm (by omega)
        have ham := ha m (by omega)
        have e : v.c m * (if m = 0 then (0 : ℝ) else G (m - 1) n) =
            if 1 ≤ m then v.c m * G (m - 1) n else 0 := by
          split_ifs <;> first | omega | ring
        rw [inv_mul_eq_iff_eq_mul₀ ham, hr, e]
      · show productMatrix v m n k = _
        rw [ihP n, if_neg (by omega), Nat.add_sub_cancel]
  exact fun m hm => (claim m hm).1

section oddblock

variable {N : ℕ} (v : Coefficients (2 * N))

/-- The candidate odd-column array: `H(2a,2b+1) = a_{2a}ǧ(a,b) + c_{2a}ǧ(a-1,b)`,
`H(2a+1,2b) = a_{2b}ǧ(a,b) + c_{2b}ǧ(a,b-1)`, zero otherwise. -/
noncomputable def Hodd (c : Fin (N - 1 + 1)) (m n : ℕ) : ℝ :=
  if m % 2 = 0 ∧ n % 2 = 1 then
    v.a m * Gk (oddRaw v) c (m / 2) (n / 2) + v.c m * Gk (oddRaw v) c (m / 2 - 1) (n / 2)
  else if m % 2 = 1 ∧ n % 2 = 0 then
    v.a n * Gk (oddRaw v) c (m / 2) (n / 2) + v.c n * Gk (oddRaw v) c (m / 2) (n / 2 - 1)
  else 0

theorem Hodd_eo (c : Fin (N - 1 + 1)) (a b : ℕ) : Hodd v c (2 * a) (2 * b + 1) =
    v.a (2 * a) * Gk (oddRaw v) c a b + v.c (2 * a) * Gk (oddRaw v) c (a - 1) b := by
  unfold Hodd; rw [if_pos (by omega), show 2 * a / 2 = a by omega, show (2 * b + 1) / 2 = b by omega]

theorem Hodd_oe (c : Fin (N - 1 + 1)) (a b : ℕ) : Hodd v c (2 * a + 1) (2 * b) =
    v.a (2 * b) * Gk (oddRaw v) c a b + v.c (2 * b) * Gk (oddRaw v) c a (b - 1) := by
  unfold Hodd; rw [if_neg (by omega), if_pos (by omega), show (2 * a + 1) / 2 = a by omega,
    show 2 * b / 2 = b by omega]

theorem Hodd_ee (c : Fin (N - 1 + 1)) (a b : ℕ) : Hodd v c (2 * a) (2 * b) = 0 := by
  unfold Hodd; rw [if_neg (by omega), if_neg (by omega)]

theorem Hodd_oo (c : Fin (N - 1 + 1)) (a b : ℕ) : Hodd v c (2 * a + 1) (2 * b + 1) = 0 := by
  unfold Hodd; rw [if_neg (by omega), if_neg (by omega)]

/-- The odd-column coefficients: `g(m,n;2c+1) = H(m,n)`. -/
theorem odd_block (hv : Admissible v) (hb : ∀ i, i ≤ 2 * N → v.b i = 0) (hN : 1 ≤ N)
    (c : Fin (N - 1 + 1)) :
    ∀ m, m ≤ 2 * N → ∀ n : Fin (2 * N + 1),
      productMatrix v m n ⟨2 * c.val + 1, by omega⟩ = Hodd v c m n.val := by
  have hc0 := hv.2.2.2.1
  have ha0 := hv.2.1
  have haN := hv.2.2.2.2.1
  have hoa : ∀ i, i < N - 1 → (oddRaw v).a i ≠ 0 := fun i hi =>
    mul_ne_zero (hv.2.2.2.2.2.2.1 (2 * i + 1) (by omega)).ne'
      (hv.2.2.2.2.2.2.1 (2 * i + 2) (by omega)).ne'
  have hoaN : (oddRaw v).a (N - 1) = 0 := by
    show v.a (2 * (N - 1) + 1) * v.a (2 * (N - 1) + 2) = 0
    rw [show 2 * (N - 1) + 2 = 2 * N by omega, haN, mul_zero]
  set G := Gk (oddRaw v) c
  apply product_eq_of_rec_col v _ (Hodd v c) (fun i hi => (hv.2.2.2.2.2.2.1 i hi).ne')
  · intro n hn
    obtain ⟨b, rfl | rfl⟩ : ∃ b, n = 2 * b ∨ n = 2 * b + 1 := ⟨n / 2, by omega⟩
    · rw [show (0 : ℕ) = 2 * 0 by rfl, Hodd_ee, if_neg (by simp; omega)]
    · rw [show (0 : ℕ) = 2 * 0 by rfl, Hodd_eo, Nat.mul_zero, ha0, hc0, zero_mul, add_zero, one_mul]
      show Gk (oddRaw v) c 0 b = _
      unfold Gk
      rw [dif_pos ⟨by omega, by omega⟩]
      show (1 : Matrix (Fin (N - 1 + 1)) (Fin (N - 1 + 1)) ℝ) _ c = _
      rw [Matrix.one_apply]
      by_cases h : b = c.val
      · rw [if_pos (Fin.ext h), if_pos (by simp; omega)]
      · rw [if_neg (fun h' => h (by rw [Fin.ext_iff] at h'; exact h')), if_neg (by simp; omega)]
  · intro m n hm hn
    rw [hb m (by omega), hb n hn, zero_mul, add_zero, sub_zero]
    -- remove the boundary conditions
    have e1 : (if n + 1 ≤ 2 * N then v.a n * Hodd v c m (n + 1) else 0) = v.a n * Hodd v c m (n + 1) := by
      split_ifs with h
      · rfl
      · rw [show n = 2 * N by omega, haN, zero_mul]
    have e2 : (if 1 ≤ n then v.c n * Hodd v c m (n - 1) else 0) = v.c n * Hodd v c m (n - 1) := by
      split_ifs with h
      · rfl
      · rw [show n = 0 by omega, hc0, zero_mul]
    have e3 : (if 1 ≤ m then v.c m * Hodd v c (m - 1) n else 0) = v.c m * Hodd v c (m - 1) n := by
      split_ifs with h
      · rfl
      · rw [show m = 0 by omega, hc0, zero_mul]
    rw [e1, e2, e3]
    -- `c_x H(…, x - 1)` in the form needed below
    have down_m : ∀ a n', v.c (2 * a) * Hodd v c (2 * a - 1) n' =
        if a = 0 then 0 else v.c (2 * a) * Hodd v c (2 * (a - 1) + 1) n' := by
      intro a n'
      split_ifs with h
      · rw [h, Nat.mul_zero, hc0, zero_mul]
      · rw [show 2 * a - 1 = 2 * (a - 1) + 1 by omega]
    have down_n : ∀ b m', v.c (2 * b) * Hodd v c m' (2 * b - 1) =
        if b = 0 then 0 else v.c (2 * b) * Hodd v c m' (2 * (b - 1) + 1) := by
      intro b m'
      split_ifs with h
      · rw [h, Nat.mul_zero, hc0, zero_mul]
      · rw [show 2 * b - 1 = 2 * (b - 1) + 1 by omega]
    obtain ⟨a, rfl | rfl⟩ : ∃ a, m = 2 * a ∨ m = 2 * a + 1 := ⟨m / 2, by omega⟩
    · obtain ⟨b, rfl | rfl⟩ : ∃ b, n = 2 * b ∨ n = 2 * b + 1 := ⟨n / 2, by omega⟩
      · -- even row, even column index: both sides are the same bilinear expression
        rw [Hodd_oe, Hodd_eo]
        rcases Nat.eq_zero_or_pos a with ha' | ha' <;> rcases Nat.eq_zero_or_pos b with hb' | hb'
        · subst ha'; subst hb'
          simp only [hc0, zero_mul, mul_zero, add_zero, sub_zero]
        · subst ha'
          rw [show 2 * b - 1 = 2 * (b - 1) + 1 by omega, Hodd_eo]
          simp only [hc0, zero_mul, mul_zero, add_zero, sub_zero]; ring
        · subst hb'
          rw [show 2 * a - 1 = 2 * (a - 1) + 1 by omega, Hodd_oe]
          simp only [hc0, zero_mul, mul_zero, add_zero]; ring
        · rw [show 2 * b - 1 = 2 * (b - 1) + 1 by omega, Hodd_eo,
            show 2 * a - 1 = 2 * (a - 1) + 1 by omega, Hodd_oe]
          ring
      · rw [Hodd_oo, show 2 * b + 1 + 1 = 2 * (b + 1) by ring, Hodd_ee,
          show 2 * b + 1 - 1 = 2 * b by omega, Hodd_ee, down_m]
        split_ifs
        · ring
        · rw [Hodd_oo]; ring
    · obtain ⟨b, rfl | rfl⟩ : ∃ b, n = 2 * b ∨ n = 2 * b + 1 := ⟨n / 2, by omega⟩
      · rw [show 2 * a + 1 + 1 = 2 * (a + 1) by ring, Hodd_ee, Hodd_oo, down_n,
          show 2 * a + 1 - 1 = 2 * a by omega, Hodd_ee]
        split_ifs
        · ring
        · rw [Hodd_oo]; ring
      · -- odd row, odd column index: the odd component's own relation
        rw [show 2 * a + 1 + 1 = 2 * (a + 1) by ring, Hodd_eo, show 2 * b + 1 + 1 = 2 * (b + 1) by ring,
          Hodd_oe, show 2 * b + 1 - 1 = 2 * b by omega, Hodd_oe, show 2 * a + 1 - 1 = 2 * a by omega,
          Hodd_eo]
        have rel := Gk_rel (oddRaw v) hoa hoaN c a b (by omega) (by omega)
        have ec : ∀ x, (if 1 ≤ x then (oddRaw v).c x * G (x - 1) b else 0) =
            (oddRaw v).c x * G (x - 1) b := by
          intro x; split_ifs with h
          · rfl
          · rw [show x = 0 by omega]; show (0 : ℝ) = v.c (2 * 0 + 1) * v.c (2 * 0) * _; rw [Nat.mul_zero, hc0]; ring
        have ec' : ∀ y, (if 1 ≤ y then (oddRaw v).c y * G a (y - 1) else 0) =
            (oddRaw v).c y * G a (y - 1) := by
          intro y; split_ifs with h
          · rfl
          · rw [show y = 0 by omega]; show (0 : ℝ) = v.c (2 * 0 + 1) * v.c (2 * 0) * _; rw [Nat.mul_zero, hc0]; ring
        rw [ec, ec'] at rel
        have hoa' : ∀ x, (oddRaw v).a x = v.a (2 * x + 1) * v.a (2 * x + 2) := fun x => rfl
        have hob' : ∀ x, (oddRaw v).b x = v.a (2 * x + 1) * v.c (2 * x + 2) + v.c (2 * x + 1) * v.a (2 * x) :=
          fun x => rfl
        have hoc' : ∀ x, (oddRaw v).c x = v.c (2 * x + 1) * v.c (2 * x) := fun x => rfl
        rw [hoa' a, hoa' b, hob' a, hob' b, hoc' a, hoc' b] at rel
        rw [show 2 * (a + 1) = 2 * a + 2 by ring, show 2 * (b + 1) = 2 * b + 2 by ring]
        simp only [Nat.add_sub_cancel]
        linear_combination rel

end oddblock

/-! ### Normalization -/

/-- The affine normalization `(a, b, c) ↦ (a, b - b_0, c)/a_0`. -/
noncomputable def normalize {K : ℕ} (w : Coefficients K) : Coefficients K :=
  ⟨fun n => w.a n / w.a 0, fun n => (w.b n - w.b 0) / w.a 0, fun n => w.c n / w.a 0⟩

/-- Normalization describes the same polynomials in the variable `(x - b_0)/a_0`. -/
theorem product_normalize {K : ℕ} (w : Coefficients K) (h0 : w.a 0 ≠ 0) :
    ∀ m, productMatrix (normalize w) m = productMatrix w m := by
  have hJ : recurrenceMatrix (normalize w) =
      (w.a 0)⁻¹ • (recurrenceMatrix w - w.b 0 • (1 : Matrix _ _ ℝ)) := by
    ext i j
    rw [Matrix.smul_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul,
      smul_eq_mul]
    unfold recurrenceMatrix normalize
    simp only
    by_cases h1 : j.val = i.val + 1
    · rw [if_pos h1, if_pos h1, if_neg (fun h => by rw [h] at h1; omega)]
      rw [div_eq_inv_mul]; ring
    · rw [if_neg h1, if_neg h1]
      by_cases h2 : j = i
      · subst h2; rw [if_pos rfl, if_pos rfl, if_pos rfl]
        rw [div_eq_inv_mul]; ring
      · rw [if_neg h2, if_neg h2, if_neg (Ne.symm h2)]
        by_cases h3 : i.val = j.val + 1
        · rw [if_pos h3, if_pos h3]; rw [div_eq_inv_mul]; ring
        · rw [if_neg h3, if_neg h3]; ring
  have pair : ∀ m, productMatrix (normalize w) m = productMatrix w m ∧
      (matrixPair (normalize w) m).1 = (matrixPair w m).1 := by
    intro m
    induction m with
    | zero => exact ⟨rfl, rfl⟩
    | succ m ih =>
      obtain ⟨hP, hQ⟩ := ih
      refine ⟨?_, hP⟩
      show ((normalize w).a m)⁻¹ • ((recurrenceMatrix (normalize w) - (normalize w).b m •
          (1 : Matrix _ _ ℝ)) * productMatrix (normalize w) m - (normalize w).c m •
          (matrixPair (normalize w) m).1) = (w.a m)⁻¹ • ((recurrenceMatrix w - w.b m •
          (1 : Matrix _ _ ℝ)) * productMatrix w m - w.c m • (matrixPair w m).1)
      rw [hP, hQ, hJ]
      have hX : ((w.a 0)⁻¹ • (recurrenceMatrix w - w.b 0 • (1 : Matrix _ _ ℝ)) - (normalize w).b m •
          (1 : Matrix _ _ ℝ)) = (w.a 0)⁻¹ • (recurrenceMatrix w - w.b m • (1 : Matrix _ _ ℝ)) := by
        ext i j
        simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, normalize]
        ring
      rw [hX, Matrix.smul_mul]
      unfold normalize; simp only
      rw [smul_sub, smul_sub, smul_smul, smul_smul, smul_smul]
      congr 2
      · rw [inv_div]; field_simp
      · rw [inv_div, div_mul_div_comm, mul_comm (w.a 0) (w.c m), mul_div_mul_right _ _ h0,
          div_eq_inv_mul]
  exact fun m => (pair m).1

/-! ### Theorem 7.8 -/

section theorem78

variable {N : ℕ} (v : Coefficients (2 * N))

/-- The normalized even component. -/
noncomputable def evenComp : Coefficients N := normalize (evenRaw v)

/-- The normalized odd component. -/
noncomputable def oddComp : Coefficients (N - 1) := normalize (oddRaw v)

theorem coeff_nonneg {M : ℕ} {w : Coefficients M} (hw : Admissible w) :
    ∀ i, i ≤ M → 0 ≤ w.a i ∧ 0 ≤ w.c i := by
  intro i hi
  refine ⟨?_, ?_⟩
  · rcases Nat.lt_or_ge i M with h | h
    · exact (hw.2.2.2.2.2.2.1 i h).le
    · rw [show i = M by omega, hw.2.2.2.2.1]
  · rcases Nat.eq_zero_or_pos i with h | h
    · rw [h, hw.2.2.2.1]
    · exact (hw.2.2.2.2.2.2.2 i h hi).le

theorem evenRaw_a0 (hv : Admissible v) (hN : 1 ≤ N) : 0 < (evenRaw v).a 0 := by
  show 0 < v.a (2 * 0) * v.a (2 * 0 + 1)
  rw [Nat.mul_zero, hv.2.1, one_mul]; exact hv.2.2.2.2.2.2.1 1 (by omega)

theorem oddRaw_a0 (hv : Admissible v) (hN : 2 ≤ N) : 0 < (oddRaw v).a 0 := by
  show 0 < v.a (2 * 0 + 1) * v.a (2 * 0 + 2)
  exact mul_pos (hv.2.2.2.2.2.2.1 _ (by omega)) (hv.2.2.2.2.2.2.1 _ (by omega))

/-- The normalized even component satisfies (basic). -/
theorem evenComp_admissible (hv : Admissible v) (hb : ∀ i, i ≤ 2 * N → v.b i = 0) (hN : 1 ≤ N) :
    Admissible (evenComp v) := by
  obtain ⟨_, ha0, _, hc0, haN, hsum, hapos, hcpos⟩ := hv
  have h0 := evenRaw_a0 v ⟨by omega, ha0, by assumption, hc0, haN, hsum, hapos, hcpos⟩ hN
  have hs : ∀ i, i ≤ 2 * N → v.a i + v.c i = 1 := fun i hi => by
    have := hsum i hi; rw [hb i hi] at this; linarith
  have hraw : ∀ n, n ≤ N → (evenRaw v).a n + (evenRaw v).b n + (evenRaw v).c n = 1 := by
    intro n hn
    show v.a (2 * n) * v.a (2 * n + 1) + (v.c (2 * n) * v.a (2 * n - 1) + v.a (2 * n) * v.c (2 * n + 1)) +
      v.c (2 * n) * v.c (2 * n - 1) = 1
    have e1 : v.a (2 * n) * (v.a (2 * n + 1) + v.c (2 * n + 1)) = v.a (2 * n) := by
      rcases Nat.lt_or_ge n N with h | h
      · rw [hs (2 * n + 1) (by omega), mul_one]
      · rw [show 2 * n = 2 * N by omega, haN, zero_mul]
    have e2 : v.c (2 * n) * (v.a (2 * n - 1) + v.c (2 * n - 1)) = v.c (2 * n) := by
      rcases Nat.eq_zero_or_pos n with h | h
      · rw [h, Nat.mul_zero, hc0, zero_mul]
      · rw [hs (2 * n - 1) (by omega), mul_one]
    have := hs (2 * n) (by omega)
    linear_combination e1 + e2 + this
  have hb0 : (evenRaw v).a 0 + (evenRaw v).b 0 = 1 := by
    have := hraw 0 (by omega)
    have hc : (evenRaw v).c 0 = 0 := by
      show v.c (2 * 0) * v.c (2 * 0 - 1) = 0; rw [Nat.mul_zero, hc0, zero_mul]
    linarith
  refine ⟨hN, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show (evenRaw v).a 0 / (evenRaw v).a 0 = 1; exact div_self h0.ne'
  · show ((evenRaw v).b 0 - (evenRaw v).b 0) / (evenRaw v).a 0 = 0; simp
  · show (v.c (2 * 0) * v.c (2 * 0 - 1)) / (evenRaw v).a 0 = 0; rw [Nat.mul_zero, hc0]; simp
  · show (v.a (2 * N) * v.a (2 * N + 1)) / (evenRaw v).a 0 = 0; rw [haN]; simp
  · intro i hi
    show (evenRaw v).a i / (evenRaw v).a 0 + ((evenRaw v).b i - (evenRaw v).b 0) / (evenRaw v).a 0 +
      (evenRaw v).c i / (evenRaw v).a 0 = 1
    rw [← add_div, ← add_div, div_eq_one_iff_eq h0.ne']
    linarith [hraw i hi]
  · intro i hi
    show 0 < (v.a (2 * i) * v.a (2 * i + 1)) / (evenRaw v).a 0
    exact div_pos (mul_pos (hapos _ (by omega)) (hapos _ (by omega))) h0
  · intro i h1 hi
    show 0 < (v.c (2 * i) * v.c (2 * i - 1)) / (evenRaw v).a 0
    exact div_pos (mul_pos (hcpos _ (by omega) (by omega)) (hcpos _ (by omega) (by omega))) h0

/-- The normalized odd component satisfies (basic), for `N ≥ 2`. -/
theorem oddComp_admissible (hv : Admissible v) (hb : ∀ i, i ≤ 2 * N → v.b i = 0) (hN : 2 ≤ N) :
    Admissible (oddComp v) := by
  obtain ⟨_, ha0, _, hc0, haN, hsum, hapos, hcpos⟩ := hv
  have h0 := oddRaw_a0 v ⟨by omega, ha0, by assumption, hc0, haN, hsum, hapos, hcpos⟩ hN
  have hs : ∀ i, i ≤ 2 * N → v.a i + v.c i = 1 := fun i hi => by
    have := hsum i hi; rw [hb i hi] at this; linarith
  have hraw : ∀ n, n ≤ N - 1 → (oddRaw v).a n + (oddRaw v).b n + (oddRaw v).c n = 1 := by
    intro n hn
    show v.a (2 * n + 1) * v.a (2 * n + 2) + (v.a (2 * n + 1) * v.c (2 * n + 2) + v.c (2 * n + 1) * v.a (2 * n)) +
      v.c (2 * n + 1) * v.c (2 * n) = 1
    have e1 := hs (2 * n + 2) (by omega)
    have e2 := hs (2 * n) (by omega)
    have e3 := hs (2 * n + 1) (by omega)
    linear_combination v.a (2 * n + 1) * e1 + v.c (2 * n + 1) * e2 + e3
  have hb0 : (oddRaw v).a 0 + (oddRaw v).b 0 = 1 := by
    have := hraw 0 (by omega)
    have hc : (oddRaw v).c 0 = 0 := by
      show v.c (2 * 0 + 1) * v.c (2 * 0) = 0; rw [Nat.mul_zero, hc0, mul_zero]
    linarith
  refine ⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show (oddRaw v).a 0 / (oddRaw v).a 0 = 1; exact div_self h0.ne'
  · show ((oddRaw v).b 0 - (oddRaw v).b 0) / (oddRaw v).a 0 = 0; simp
  · show (v.c (2 * 0 + 1) * v.c (2 * 0)) / (oddRaw v).a 0 = 0; rw [Nat.mul_zero, hc0]; simp
  · show (v.a (2 * (N - 1) + 1) * v.a (2 * (N - 1) + 2)) / (oddRaw v).a 0 = 0
    rw [show 2 * (N - 1) + 2 = 2 * N by omega, haN]; simp
  · intro i hi
    show (oddRaw v).a i / (oddRaw v).a 0 + ((oddRaw v).b i - (oddRaw v).b 0) / (oddRaw v).a 0 +
      (oddRaw v).c i / (oddRaw v).a 0 = 1
    rw [← add_div, ← add_div, div_eq_one_iff_eq h0.ne']
    linarith [hraw i hi]
  · intro i hi
    show 0 < (v.a (2 * i + 1) * v.a (2 * i + 2)) / (oddRaw v).a 0
    exact div_pos (mul_pos (hapos _ (by omega)) (hapos _ (by omega))) h0
  · intro i h1 hi
    show 0 < (v.c (2 * i + 1) * v.c (2 * i)) / (oddRaw v).a 0
    exact div_pos (mul_pos (hcpos _ (by omega) (by omega)) (hcpos _ (by omega) (by omega))) h0

/-- Odd-component coefficients are nonnegative when the normalized odd component has
nonnegative linearization (for `N = 1` the odd component is `L_0 = 1`). -/
theorem oddRaw_Gk_nonneg (hv : Admissible v) (hN : 1 ≤ N) (ho : MatrixPositivity (oddComp v))
    (c : Fin (N - 1 + 1)) (x y : ℕ) : 0 ≤ Gk (oddRaw v) c x y := by
  unfold Gk
  split_ifs with h
  · rcases Nat.lt_or_ge 1 N with hN2 | hN2
    · rw [← product_normalize (oddRaw v) (oddRaw_a0 v hv (by omega)).ne']
      exact ho x h.1 _ _
    · have hx : x = 0 := by omega
      subst hx
      show 0 ≤ (1 : Matrix (Fin (N - 1 + 1)) (Fin (N - 1 + 1)) ℝ) _ c
      rw [Matrix.one_apply]; split_ifs <;> norm_num
  · exact le_refl 0

/-- **Theorem 7.8**, positivity transfer: if both normalized components have nonnegative
linearization, so does the symmetric array. -/
theorem decomp_positivity (hv : Admissible v) (hb : ∀ i, i ≤ 2 * N → v.b i = 0) (hN : 1 ≤ N)
    (he : MatrixPositivity (evenComp v)) (ho : MatrixPositivity (oddComp v)) : MatrixPositivity v := by
  have hnn := coeff_nonneg hv
  intro m hm n k
  have hG : productMatrix v m n k = Gk v k m n.val := by
    unfold Gk; rw [dif_pos ⟨hm, by omega⟩]
  by_cases hpar : (m + n.val + k.val) % 2 = 1
  · rw [hG, Gk_parity v hv hb k m n.val hpar]
  obtain ⟨c, hk | hk⟩ : ∃ c, k.val = 2 * c ∨ k.val = 2 * c + 1 := ⟨k.val / 2, by omega⟩
  · -- even column
    obtain ⟨a, rfl | rfl⟩ : ∃ a, m = 2 * a ∨ m = 2 * a + 1 := ⟨m / 2, by omega⟩
    · obtain ⟨b, hb'⟩ : ∃ b, n.val = 2 * b := ⟨n.val / 2, by omega⟩
      have h1 := even_block v hv hb a (by omega) ⟨b, by omega⟩ ⟨c, by omega⟩
      rw [← product_normalize (evenRaw v) (evenRaw_a0 v hv hN).ne'] at h1
      have h2 : Geven v a b c = productMatrix v (2 * a) n k := by
        unfold Geven Gk
        rw [dif_pos (by omega), dif_pos ⟨by omega, by omega⟩]
        congr 1 <;> exact Fin.ext (by simp; omega)
      rw [← h2, ← h1]
      exact he a (by omega) _ _
    · -- `π_n g(m,n;k) = π_k g(m,k;n)` and the odd block in column `n`
      obtain ⟨b, hb'⟩ : ∃ b, n.val = 2 * b + 1 := ⟨n.val / 2, by omega⟩
      have hpi := piW_entry v hv (2 * a + 1) n k
      have hodd := odd_block v hv hb hN ⟨b, by omega⟩ (2 * a + 1) hm k
      have hn' : (⟨2 * b + 1, by omega⟩ : Fin (2 * N + 1)) = n := Fin.ext (by simp; omega)
      rw [hn'] at hodd
      rw [hodd, hk, Hodd_oe] at hpi
      have hval : 0 ≤ v.a (2 * c) * Gk (oddRaw v) ⟨b, by omega⟩ a c +
          v.c (2 * c) * Gk (oddRaw v) ⟨b, by omega⟩ a (c - 1) :=
        add_nonneg (mul_nonneg (hnn _ (by omega)).1 (oddRaw_Gk_nonneg v hv hN ho _ _ _))
          (mul_nonneg (hnn _ (by omega)).2 (oddRaw_Gk_nonneg v hv hN ho _ _ _))
      have hpn := piW_pos v hv n.val (by omega)
      have hpk := piW_pos v hv (2 * c) (by omega)
      have : 0 ≤ piW v n * productMatrix v (2 * a + 1) n k := by rw [hpi]; positivity
      exact nonneg_of_mul_nonneg_right (by linarith) hpn
  · -- odd column
    have hodd := odd_block v hv hb hN ⟨c, by omega⟩ m hm n
    have hk' : (⟨2 * c + 1, by omega⟩ : Fin (2 * N + 1)) = k := Fin.ext (by simp; omega)
    rw [hk'] at hodd
    rw [hodd]
    obtain ⟨a, ha | ha⟩ : ∃ a, m = 2 * a ∨ m = 2 * a + 1 := ⟨m / 2, by omega⟩
    · obtain ⟨b, hb'⟩ : ∃ b, n.val = 2 * b + 1 := ⟨n.val / 2, by omega⟩
      rw [ha, hb', Hodd_eo]
      exact add_nonneg (mul_nonneg (hnn _ (by omega)).1 (oddRaw_Gk_nonneg v hv hN ho _ _ _))
        (mul_nonneg (hnn _ (by omega)).2 (oddRaw_Gk_nonneg v hv hN ho _ _ _))
    · obtain ⟨b, hb'⟩ : ∃ b, n.val = 2 * b := ⟨n.val / 2, by omega⟩
      rw [ha, hb', Hodd_oe]
      exact add_nonneg (mul_nonneg (hnn _ (by omega)).1 (oddRaw_Gk_nonneg v hv hN ho _ _ _))
        (mul_nonneg (hnn _ (by omega)).2 (oddRaw_Gk_nonneg v hv hN ho _ _ _))

/-- **Theorem 7.8**, converse: nonnegative linearization of the symmetric array implies that of
its even component. -/
theorem decomp_converse (hv : Admissible v) (hb : ∀ i, i ≤ 2 * N → v.b i = 0) (hN : 1 ≤ N)
    (hp : MatrixPositivity v) : MatrixPositivity (evenComp v) := by
  intro a ha b c
  unfold evenComp
  rw [product_normalize (evenRaw v) (evenRaw_a0 v hv hN).ne', even_block v hv hb a ha b c]
  unfold Geven Gk
  rw [dif_pos (by omega), dif_pos ⟨by omega, by omega⟩]
  exact hp (2 * a) (by omega) _ _

end theorem78

end Szkraw
