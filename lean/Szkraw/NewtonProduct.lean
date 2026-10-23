import Szkraw.LCConvolution
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Int.Interval

/-!
# Proposition 8.14 (Walkup): log-concavity of Newton coefficients under products — groundwork

Layer-cake (Abel) decomposition of a symmetric sequence into centred intervals.
-/

namespace Szkraw

open Finset

/-- Telescoping increments of `u` starting from `0`. -/
def incr (u : ℕ → ℝ) (a : ℕ) : ℝ := u a - (if a = 0 then 0 else u (a - 1))

theorem sum_incr (u : ℕ → ℝ) : ∀ m, ∑ a ∈ range (m + 1), incr u a = u m
  | 0 => by simp [incr]
  | m + 1 => by
    rw [sum_range_succ, sum_incr u m]; simp [incr]

/-- Layer cake: for `u` symmetric on `[0, c]`,
`Σ_{i ≤ c} u i φ i = Σ_{a ≤ c/2} incr u a · Σ_{a ≤ i ≤ c - a} φ i`. -/
theorem layer_cake (c : ℕ) (u φ : ℕ → ℝ) (hsym : ∀ i ≤ c, u i = u (c - i)) :
    ∑ i ∈ range (c + 1), u i * φ i =
      ∑ a ∈ range (c / 2 + 1), incr u a * ∑ i ∈ Icc a (c - a), φ i := by
  have h1 : ∀ i ∈ range (c + 1), u i * φ i =
      (∑ a ∈ (range (c / 2 + 1)).filter (fun a => a ≤ i ∧ a ≤ c - i), incr u a) * φ i := by
    intro i hi
    simp only [mem_range] at hi
    have hm : (range (c / 2 + 1)).filter (fun a => a ≤ i ∧ a ≤ c - i) = range (min i (c - i) + 1) := by
      ext a; simp only [mem_filter, mem_range]; constructor
      · rintro ⟨_, h1, h2⟩; omega
      · intro h; refine ⟨by omega, by omega, by omega⟩
    rw [hm, sum_incr]
    congr 1
    rcases le_total i (c - i) with h | h
    · rw [min_eq_left h]
    · rw [min_eq_right h, ← hsym i (by omega)]
  rw [sum_congr rfl h1]
  simp only [sum_mul, mul_sum]
  rw [sum_comm' (t' := range (c / 2 + 1)) (s' := fun a => Icc a (c - a))]
  · intro i a
    simp only [mem_filter, mem_range, mem_Icc]
    constructor
    · rintro ⟨hi, ha, h1, h2⟩; exact ⟨⟨h1, by omega⟩, ha⟩
    · rintro ⟨⟨h1, h2⟩, ha⟩; refine ⟨by omega, ha, h1, by omega⟩


/-! ## The coefficients `H_k(i, j) = C(k,i) C(i,k-j)` of `(y + w + yw)^k` -/

/-- `H_k(i,j)` on natural indices. -/
def Hn (k i j : ℕ) : ℕ := if j ≤ k then k.choose i * i.choose (k - j) else 0

theorem Hn_succ (k i j : ℕ) :
    Hn (k + 1) i j = (if 1 ≤ i then Hn k (i - 1) j else 0) + (if 1 ≤ j then Hn k i (j - 1) else 0) +
      (if 1 ≤ i ∧ 1 ≤ j then Hn k (i - 1) (j - 1) else 0) := by
  rcases i with _ | i'
  · rcases j with _ | j'
    · simp [Hn, Nat.choose_eq_zero_of_lt]
    · simp only [Hn, Nat.choose_zero_right, one_mul, show ¬ (1 ≤ 0) by omega, if_false, zero_add, add_zero,
        false_and, show 1 ≤ j' + 1 by omega, if_true, Nat.add_sub_cancel]
      by_cases h : j' ≤ k
      · rw [if_pos (by omega), if_pos h, show k + 1 - (j' + 1) = k - j' by omega]
      · rw [if_neg (by omega), if_neg h]
  · simp only [show 1 ≤ i' + 1 by omega, if_true, true_and, Nat.add_sub_cancel]
    rcases j with _ | j'
    · simp only [Hn, Nat.zero_le, if_true, show ¬ (1 ≤ 0) by omega, if_false, add_zero, Nat.sub_zero]
      rw [Nat.choose_succ_succ' k i', add_mul]
      rcases lt_trichotomy i' k with h | h | h
      · rw [Nat.choose_eq_zero_of_lt (show i' + 1 < k + 1 by omega), Nat.choose_eq_zero_of_lt h]; simp
      · subst h; simp
      · rw [Nat.choose_eq_zero_of_lt h, Nat.choose_eq_zero_of_lt (show k < i' + 1 by omega)]; simp
    · simp only [show 1 ≤ j' + 1 by omega, if_true, Nat.add_sub_cancel, Hn]
      by_cases hjk : j' ≤ k
      · rw [if_pos (show j' + 1 ≤ k + 1 by omega), if_pos hjk, show k + 1 - (j' + 1) = k - j' by omega,
          Nat.choose_succ_succ' k i', add_mul]
        by_cases hj2 : j' + 1 ≤ k
        · rw [if_pos hj2]
          obtain ⟨m, hm⟩ : ∃ m, k - j' = m + 1 := ⟨k - j' - 1, by omega⟩
          rw [show k - (j' + 1) = m by omega, hm, Nat.choose_succ_succ' i' m]
          simp only [hjk, if_true]
          ring
        · rw [if_neg hj2, show k - j' = 0 by omega]; simp only [hjk, if_true]; simp; ring
      · rw [if_neg (show ¬ (j' + 1 ≤ k + 1) by omega), if_neg (show ¬ (j' + 1 ≤ k) by omega)]
        simp [hjk]

/-- `H_k(i,j)` on integer indices, zero outside the quadrant. -/
noncomputable def Hz (k : ℕ) (i j : ℤ) : ℝ := if 0 ≤ i ∧ 0 ≤ j then (Hn k i.toNat j.toNat : ℝ) else 0

theorem Hz_zero (i j : ℤ) : Hz 0 i j = if i = 0 ∧ j = 0 then 1 else 0 := by
  unfold Hz Hn
  by_cases h : 0 ≤ i ∧ 0 ≤ j
  · rw [if_pos h]
    by_cases h0 : i = 0 ∧ j = 0
    · rw [if_pos h0]; obtain ⟨rfl, rfl⟩ := h0; simp
    · rw [if_neg h0]
      rcases (show i ≠ 0 ∨ j ≠ 0 by tauto) with hi | hj
      · have : 0 < i.toNat := by omega
        by_cases hj0 : j.toNat ≤ 0
        · rw [if_pos hj0, Nat.choose_eq_zero_of_lt this]; simp
        · rw [if_neg hj0]; simp
      · have : ¬ j.toNat ≤ 0 := by omega
        rw [if_neg this]; simp
  · rw [if_neg h, if_neg (by omega)]

theorem Hz_succ (k : ℕ) (i j : ℤ) :
    Hz (k + 1) i j = Hz k (i - 1) j + Hz k i (j - 1) + Hz k (i - 1) (j - 1) := by
  unfold Hz
  by_cases hq : 0 ≤ i ∧ 0 ≤ j
  · rw [if_pos hq, Hn_succ]
    push_cast
    have ti : ((i - 1).toNat) = i.toNat - 1 := by omega
    have tj : ((j - 1).toNat) = j.toNat - 1 := by omega
    congr 1
    congr 1
    · by_cases h1 : 1 ≤ i.toNat
      · rw [if_pos h1, if_pos (by omega), ti]
      · rw [if_neg h1, if_neg (by omega)]
    · by_cases h1 : 1 ≤ j.toNat
      · rw [if_pos h1, if_pos (by omega), tj]
      · rw [if_neg h1, if_neg (by omega)]
    · by_cases h1 : 1 ≤ i.toNat ∧ 1 ≤ j.toNat
      · rw [if_pos h1, if_pos (by omega), ti, tj]
      · rw [if_neg h1, if_neg (by omega)]
  · rw [if_neg hq, if_neg (by omega), if_neg (by omega), if_neg (by omega)]; simp

theorem Hz_nonneg (k : ℕ) (i j : ℤ) : 0 ≤ Hz k i j := by
  unfold Hz; split_ifs
  · exact Nat.cast_nonneg _
  · exact le_refl 0


/-- Factorial form: `H_t(x,y) (t-x)! (t-y)! (x+y-t)! = t!` on the support. -/
theorem Hn_factorial {t x y : ℕ} (hx : x ≤ t) (hy : y ≤ t) (hxy : t ≤ x + y) :
    Hn t x y * ((t - x).factorial * (t - y).factorial * (x + y - t).factorial) = t.factorial := by
  unfold Hn; rw [if_pos hy]
  have h1 := Nat.choose_mul_factorial_mul_factorial hx
  have h2 := Nat.choose_mul_factorial_mul_factorial (show t - y ≤ x by omega)
  have e : x - (t - y) = x + y - t := by omega
  rw [e] at h2
  calc t.choose x * x.choose (t - y) * ((t - x).factorial * (t - y).factorial * (x + y - t).factorial)
      = t.choose x * (t - x).factorial * (x.choose (t - y) * (t - y).factorial * (x + y - t).factorial) := by ring
    _ = t.choose x * (t - x).factorial * x.factorial := by rw [h2]
    _ = t.factorial := by rw [← h1]; ring

theorem Hn_eq_zero {t x y : ℕ} (h : ¬ (x ≤ t ∧ y ≤ t ∧ t ≤ x + y)) : Hn t x y = 0 := by
  unfold Hn
  by_cases hy : y ≤ t
  · rw [if_pos hy]
    by_cases hx : x ≤ t
    · rw [Nat.choose_eq_zero_of_lt (show x < t - y by omega), mul_zero]
    · rw [Nat.choose_eq_zero_of_lt (show t < x by omega), zero_mul]
  · rw [if_neg hy]

theorem Hn_symm (t x y : ℕ) : Hn t x y = Hn t y x := by
  by_cases h : x ≤ t ∧ y ≤ t ∧ t ≤ x + y
  · obtain ⟨hx, hy, hxy⟩ := h
    have a := Hn_factorial hx hy hxy
    have b := Hn_factorial hy hx (by omega)
    have e : y + x - t = x + y - t := by omega
    rw [e] at b
    have hpos : 0 < (t - x).factorial * (t - y).factorial * (x + y - t).factorial := by positivity
    have : Hn t x y * ((t - x).factorial * (t - y).factorial * (x + y - t).factorial) =
        Hn t y x * ((t - x).factorial * (t - y).factorial * (x + y - t).factorial) := by
      rw [a, ← b]; ring
    exact Nat.eq_of_mul_eq_mul_right hpos this
  · rw [Hn_eq_zero h, Hn_eq_zero (by omega)]

theorem Hz_symm (t : ℕ) (i j : ℤ) : Hz t i j = Hz t j i := by
  unfold Hz
  by_cases h : 0 ≤ i ∧ 0 ≤ j
  · rw [if_pos h, if_pos ⟨h.2, h.1⟩, Hn_symm]
  · rw [if_neg h, if_neg (by tauto)]


/-! ## (T3): a log-concave sequence that is heavier on the right of `M/2` is nondecreasing up to `M/2` -/

theorem LCNZ.mono_of_reflect {g : ℕ → ℝ} (hg : LCNZ g) (M : ℕ)
    (hsym : ∀ x, 2 * x ≤ M → g x ≤ g (M - x)) {x : ℕ} (hx1 : 1 ≤ x) (hx : 2 * x ≤ M) :
    g (x - 1) ≤ g x := by
  by_contra hlt
  push Not at hlt
  have hpos : 0 < g (x - 1) := lt_of_le_of_lt (hg.1 x) hlt
  -- g is nonincreasing from x on
  have step : ∀ n, x ≤ n → g (n + 1) ≤ g n := by
    intro n hn
    have hb := hg.balanced 1 x n hx1 hn
    have e : x - 1 = x - 1 := rfl
    nlinarith [hg.1 n, hg.1 (n + 1), mul_le_mul_of_nonneg_left hlt.le (hg.1 n)]
  have desc : ∀ d, g (x + d) ≤ g x := by
    intro d
    induction d with
    | zero => simp
    | succ d ih => exact le_trans (step (x + d) (by omega)) ih
  have h1 := hsym (x - 1) (by omega)
  have h2 := desc (M - (x - 1) - x)
  have e : x + (M - (x - 1) - x) = M - (x - 1) := by omega
  rw [e] at h2
  linarith

/-! ## Binomial representation of `V(x,y) = H_t(x,y) H_t(m₁-x, m₂-y)` -/

/-- Binomial coefficient with an integer lower index, zero for negative indices. -/
noncomputable def Cz (n : ℕ) (z : ℤ) : ℝ := if 0 ≤ z then (n.choose z.toNat : ℝ) else 0

theorem Cz_nonneg (n : ℕ) (z : ℤ) : 0 ≤ Cz n z := by
  unfold Cz; split_ifs
  · exact Nat.cast_nonneg _
  · exact le_refl 0

theorem Hz_support {t : ℕ} {i j : ℤ} (h : Hz t i j ≠ 0) :
    0 ≤ i ∧ 0 ≤ j ∧ i ≤ t ∧ j ≤ t ∧ (t : ℤ) ≤ i + j := by
  unfold Hz at h
  by_cases hq : 0 ≤ i ∧ 0 ≤ j
  · rw [if_pos hq] at h
    by_contra hc
    have : ¬ (i.toNat ≤ t ∧ j.toNat ≤ t ∧ t ≤ i.toNat + j.toNat) := by omega
    rw [Hn_eq_zero this, Nat.cast_zero] at h; exact h rfl
  · rw [if_neg hq] at h; exact absurd rfl h

theorem Cz_support {n : ℕ} {z : ℤ} (h : Cz n z ≠ 0) : 0 ≤ z ∧ z ≤ n := by
  unfold Cz at h
  by_cases hz : 0 ≤ z
  · rw [if_pos hz] at h
    refine ⟨hz, ?_⟩
    by_contra hc
    rw [Nat.choose_eq_zero_of_lt (show n < z.toNat by omega), Nat.cast_zero] at h; exact h rfl
  · rw [if_neg hz] at h; exact absurd rfl h

theorem Hz_factorial {t : ℕ} {i j : ℤ} (h0i : 0 ≤ i) (h0j : 0 ≤ j) (hi : i ≤ t) (hj : j ≤ t)
    (hij : (t : ℤ) ≤ i + j) :
    Hz t i j * (((t : ℤ) - i).toNat.factorial * ((t : ℤ) - j).toNat.factorial *
      (i + j - t).toNat.factorial : ℝ) = t.factorial := by
  unfold Hz; rw [if_pos ⟨h0i, h0j⟩]
  have := Hn_factorial (t := t) (x := i.toNat) (y := j.toNat) (by omega) (by omega) (by omega)
  have e1 : ((t : ℤ) - i).toNat = t - i.toNat := by omega
  have e2 : ((t : ℤ) - j).toNat = t - j.toNat := by omega
  have e3 : (i + j - t).toNat = i.toNat + j.toNat - t := by omega
  rw [e1, e2, e3]; exact_mod_cast this

theorem Cz_factorial {n : ℕ} {z : ℤ} (h0 : 0 ≤ z) (hz : z ≤ n) :
    Cz n z * ((z.toNat.factorial * ((n : ℤ) - z).toNat.factorial : ℕ) : ℝ) = n.factorial := by
  unfold Cz; rw [if_pos h0]
  have := Nat.choose_mul_factorial_mul_factorial (show z.toNat ≤ n by omega)
  have e : ((n : ℤ) - z).toNat = n - z.toNat := by omega
  rw [e]; push_cast
  rw [← mul_assoc]; exact_mod_cast this


/-- `V(x,y) = H_t(x,y) H_t(m₁-x, m₂-y)` is a constant times
`C(n₂, t-x) C(n₁, t-y) C(n₃, x+y-t)` with `n₁ = 2t-m₂`, `n₂ = 2t-m₁`, `n₃ = m₁+m₂-2t`. -/
theorem V_repr (t : ℕ) (m1 m2 : ℤ) (h1 : m2 ≤ 2 * t) (h2 : m1 ≤ 2 * t) (h3 : 2 * (t : ℤ) ≤ m1 + m2)
    (x y : ℤ) :
    Hz t x y * Hz t (m1 - x) (m2 - y) *
      (((2 * t - m2).toNat.factorial * (2 * t - m1).toNat.factorial * (m1 + m2 - 2 * t).toNat.factorial : ℕ) : ℝ) =
    (t.factorial : ℝ) ^ 2 * (Cz (2 * t - m1).toNat (t - x) * Cz (2 * t - m2).toNat (t - y) *
      Cz (m1 + m2 - 2 * t).toNat (x + y - t)) := by
  by_cases hP : 0 ≤ x ∧ 0 ≤ y ∧ x ≤ t ∧ y ≤ t ∧ (t : ℤ) ≤ x + y ∧ 0 ≤ m1 - x ∧ 0 ≤ m2 - y ∧
      m1 - x ≤ t ∧ m2 - y ≤ t ∧ (t : ℤ) ≤ m1 - x + (m2 - y)
  · obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10⟩ := hP
    have HA := Hz_factorial a1 a2 a3 a4 a5
    have HB := Hz_factorial a6 a7 a8 a9 a10
    have C1 := Cz_factorial (n := (2 * t - m1).toNat) (z := t - x) (by omega) (by omega)
    have C2 := Cz_factorial (n := (2 * t - m2).toNat) (z := t - y) (by omega) (by omega)
    have C3 := Cz_factorial (n := (m1 + m2 - 2 * t).toNat) (z := x + y - t) (by omega) (by omega)
    -- the six factorials of the two H's are those of the three binomials
    have f1 : ((t : ℤ) - (m1 - x)).toNat = (((2 * t - m1).toNat : ℤ) - (t - x)).toNat := by omega
    have f2 : ((t : ℤ) - (m2 - y)).toNat = (((2 * t - m2).toNat : ℤ) - (t - y)).toNat := by omega
    have f3 : (m1 - x + (m2 - y) - t).toNat = (((m1 + m2 - 2 * t).toNat : ℤ) - (x + y - t)).toNat := by omega
    rw [f1, f2, f3] at HB
    push_cast at C1 C2 C3 HA HB ⊢
    set F1 := (((t : ℤ) - x).toNat.factorial : ℝ)
    set F2 := (((t : ℤ) - y).toNat.factorial : ℝ)
    set F3 := ((x + y - t).toNat.factorial : ℝ)
    set G1 := ((((2 * t - m1).toNat : ℤ) - (t - x)).toNat.factorial : ℝ)
    set G2 := ((((2 * t - m2).toNat : ℤ) - (t - y)).toNat.factorial : ℝ)
    set G3 := ((((m1 + m2 - 2 * t).toNat : ℤ) - (x + y - t)).toNat.factorial : ℝ)
    have hF : 0 < F1 * F2 * F3 * G1 * G2 * G3 := by positivity
    have key : (Hz t x y * Hz t (m1 - x) (m2 - y) *
        ((2 * t - m2).toNat.factorial * (2 * t - m1).toNat.factorial * (m1 + m2 - 2 * t).toNat.factorial)) *
          (F1 * F2 * F3 * G1 * G2 * G3) =
        ((t.factorial : ℝ) ^ 2 * (Cz (2 * t - m1).toNat (t - x) * Cz (2 * t - m2).toNat (t - y) *
          Cz (m1 + m2 - 2 * t).toNat (x + y - t))) * (F1 * F2 * F3 * G1 * G2 * G3) := by
      have e1 : (t - x).toNat = ((t : ℤ) - x).toNat := rfl
      calc _ = (Hz t x y * (F1 * F2 * F3)) * (Hz t (m1 - x) (m2 - y) * (G1 * G2 * G3)) *
              ((2 * t - m2).toNat.factorial * (2 * t - m1).toNat.factorial *
                (m1 + m2 - 2 * t).toNat.factorial) := by ring
        _ = (t.factorial : ℝ) * t.factorial * ((2 * t - m2).toNat.factorial * (2 * t - m1).toNat.factorial *
                (m1 + m2 - 2 * t).toNat.factorial) := by rw [HA, HB]
        _ = (t.factorial : ℝ) ^ 2 * ((Cz (2 * t - m1).toNat (t - x) * (F1 * G1)) *
              (Cz (2 * t - m2).toNat (t - y) * (F2 * G2)) *
              (Cz (m1 + m2 - 2 * t).toNat (x + y - t) * (F3 * G3))) := by
                rw [C1, C2, C3]; ring
        _ = _ := by ring
    exact mul_right_cancel₀ hF.ne' key
  · have lhs0 : Hz t x y * Hz t (m1 - x) (m2 - y) = 0 := by
      by_contra hne
      have hA : Hz t x y ≠ 0 := left_ne_zero_of_mul hne
      have hB : Hz t (m1 - x) (m2 - y) ≠ 0 := right_ne_zero_of_mul hne
      have sA := Hz_support hA; have sB := Hz_support hB
      exact hP (by omega)
    have rhs0 : Cz (2 * t - m1).toNat (t - x) * Cz (2 * t - m2).toNat (t - y) *
        Cz (m1 + m2 - 2 * t).toNat (x + y - t) = 0 := by
      by_contra hne
      have hC3 : Cz (m1 + m2 - 2 * t).toNat (x + y - t) ≠ 0 := right_ne_zero_of_mul hne
      have hne' := left_ne_zero_of_mul hne
      have hC1 : Cz (2 * t - m1).toNat (t - x) ≠ 0 := left_ne_zero_of_mul hne'
      have hC2 : Cz (2 * t - m2).toNat (t - y) ≠ 0 := right_ne_zero_of_mul hne'
      have s1 := Cz_support hC1; have s2 := Cz_support hC2; have s3 := Cz_support hC3
      exact hP (by omega)
    rw [lhs0, rhs0]; ring


/-! ## (T2): `V` is reverse regular of order two -/

/-- Balanced products of a binomial row dominate (integer indices). -/
theorem Cz_balanced (n : ℕ) {p q r w : ℤ} (hpq : p ≤ q) (hpr : p ≤ r) (hqw : q ≤ w) (_hrw : r ≤ w)
    (hsum : p + w = q + r) : Cz n p * Cz n w ≤ Cz n q * Cz n r := by
  by_cases hp : 0 ≤ p
  · unfold Cz
    rw [if_pos hp, if_pos (by omega), if_pos (by omega), if_pos (by omega)]
    have hb := (LCNZ.choose n).balanced
    rcases le_total q r with h | h
    · have := hb (q.toNat - p.toNat) q.toNat r.toNat (by omega) (by omega)
      have e1 : q.toNat - (q.toNat - p.toNat) = p.toNat := by omega
      have e2 : r.toNat + (q.toNat - p.toNat) = w.toNat := by omega
      rw [e1, e2] at this; exact this
    · have := hb (r.toNat - p.toNat) r.toNat q.toNat (by omega) (by omega)
      have e1 : r.toNat - (r.toNat - p.toNat) = p.toNat := by omega
      have e2 : q.toNat + (r.toNat - p.toNat) = w.toNat := by omega
      rw [e1, e2] at this; linarith
  · unfold Cz; rw [if_neg hp, zero_mul]
    exact mul_nonneg (Cz_nonneg n q) (Cz_nonneg n r)

/-- The kernel `V`. -/
noncomputable def Vk (t : ℕ) (m1 m2 x y : ℤ) : ℝ := Hz t x y * Hz t (m1 - x) (m2 - y)

theorem Vk_nonneg (t : ℕ) (m1 m2 x y : ℤ) : 0 ≤ Vk t m1 m2 x y :=
  mul_nonneg (Hz_nonneg _ _ _) (Hz_nonneg _ _ _)

theorem Vk_symm (t : ℕ) (m1 m2 x y : ℤ) : Vk t m1 m2 (m1 - x) (m2 - y) = Vk t m1 m2 x y := by
  unfold Vk; rw [sub_sub_cancel, sub_sub_cancel, mul_comm]

theorem Vk_zero_of {t : ℕ} {m1 m2 : ℤ} (h : ¬ (m2 ≤ 2 * t ∧ m1 ≤ 2 * t ∧ 2 * (t : ℤ) ≤ m1 + m2)) (x y : ℤ) :
    Vk t m1 m2 x y = 0 := by
  unfold Vk
  by_contra hne
  have sA := Hz_support (left_ne_zero_of_mul hne)
  have sB := Hz_support (right_ne_zero_of_mul hne)
  exact h (by omega)

/-- The constant of the binomial representation. -/
noncomputable def Vconst (t : ℕ) (m1 m2 : ℤ) : ℝ :=
  (t.factorial : ℝ) ^ 2 / (((2 * t - m2).toNat.factorial * (2 * t - m1).toNat.factorial *
    (m1 + m2 - 2 * t).toNat.factorial : ℕ) : ℝ)

theorem Vconst_pos (t : ℕ) (m1 m2 : ℤ) : 0 < Vconst t m1 m2 := by unfold Vconst; positivity

theorem Vk_eq {t : ℕ} {m1 m2 : ℤ} (h1 : m2 ≤ 2 * t) (h2 : m1 ≤ 2 * t) (h3 : 2 * (t : ℤ) ≤ m1 + m2)
    (x y : ℤ) : Vk t m1 m2 x y = Vconst t m1 m2 * (Cz (2 * t - m1).toNat (t - x) *
      Cz (2 * t - m2).toNat (t - y) * Cz (m1 + m2 - 2 * t).toNat (x + y - t)) := by
  have := V_repr t m1 m2 h1 h2 h3 x y
  unfold Vk Vconst
  have hpos : (0 : ℝ) < (((2 * t - m2).toNat.factorial * (2 * t - m1).toNat.factorial *
      (m1 + m2 - 2 * t).toNat.factorial : ℕ) : ℝ) := by positivity
  rw [div_mul_eq_mul_div, eq_div_iff hpos.ne']
  exact this

theorem Vk_rr2 (t : ℕ) (m1 m2 : ℤ) {x x' y y' : ℤ} (hx : x ≤ x') (hy : y ≤ y') :
    Vk t m1 m2 x y * Vk t m1 m2 x' y' ≤ Vk t m1 m2 x y' * Vk t m1 m2 x' y := by
  by_cases hm : m2 ≤ 2 * t ∧ m1 ≤ 2 * t ∧ 2 * (t : ℤ) ≤ m1 + m2
  · obtain ⟨h1, h2, h3⟩ := hm
    simp only [Vk_eq h1 h2 h3]
    set K := Vconst t m1 m2
    set A := fun z : ℤ => Cz (2 * t - m1).toNat (t - z)
    set B := fun z : ℤ => Cz (2 * t - m2).toNat (t - z)
    set Cc := fun z : ℤ => Cz (m1 + m2 - 2 * t).toNat z
    have key : Cc (x + y - t) * Cc (x' + y' - t) ≤ Cc (x + y' - t) * Cc (x' + y - t) :=
      Cz_balanced _ (by omega) (by omega) (by omega) (by omega) (by omega)
    have hK : 0 ≤ K := (Vconst_pos t m1 m2).le
    have hA : 0 ≤ A x * A x' := mul_nonneg (Cz_nonneg _ _) (Cz_nonneg _ _)
    have hB : 0 ≤ B y * B y' := mul_nonneg (Cz_nonneg _ _) (Cz_nonneg _ _)
    have := mul_le_mul_of_nonneg_left key (mul_nonneg (mul_nonneg (mul_nonneg hK hK) hA) hB)
    calc K * (A x * B y * Cc (x + y - t)) * (K * (A x' * B y' * Cc (x' + y' - t)))
        = K * K * (A x * A x') * (B y * B y') * (Cc (x + y - t) * Cc (x' + y' - t)) := by ring
      _ ≤ K * K * (A x * A x') * (B y * B y') * (Cc (x + y' - t) * Cc (x' + y - t)) := this
      _ = K * (A x * B y' * Cc (x + y' - t)) * (K * (A x' * B y * Cc (x' + y - t))) := by ring
  · simp only [Vk_zero_of hm, mul_zero, le_refl]


/-! ## (T1): marginals of `V` over intervals are log-concave -/

theorem LCNZ.zero : LCNZ (fun _ => (0 : ℝ)) :=
  ⟨fun _ => le_refl 0, fun _ => by simp, fun _ _ _ _ _ h _ => absurd h (lt_irrefl 0)⟩

theorem LCNZ.smul {u : ℕ → ℝ} (hu : LCNZ u) {c : ℝ} (hc : 0 < c) : LCNZ (fun n => c * u n) := by
  refine ⟨fun n => mul_nonneg hc.le (hu.1 n), fun n => ?_, fun i j k hij hjk hi hk => ?_⟩
  · have := hu.2.1 n
    calc c * u n * (c * u (n + 2)) = c ^ 2 * (u n * u (n + 2)) := by ring
      _ ≤ c ^ 2 * u (n + 1) ^ 2 := mul_le_mul_of_nonneg_left this (sq_nonneg c)
      _ = (c * u (n + 1)) ^ 2 := by ring
  · simp only at hi hk ⊢
    have hi' : 0 < u i := by
      by_contra h; push Not at h; nlinarith [hu.1 i]
    have hk' : 0 < u k := by
      by_contra h; push Not at h; nlinarith [hu.1 k]
    exact mul_pos hc (hu.2.2 i j k hij hjk hi' hk')

theorem LCNZ.congr {u v : ℕ → ℝ} (hu : LCNZ u) (h : ∀ n, u n = v n) : LCNZ v := by
  have : u = v := funext h
  rw [← this]; exact hu

/-- The interval sum of `Cz n1 (t - y) * Cz n3 (n + y - t)` is a convolution. -/
theorem marginal_conv (n1 n3 t : ℕ) (w1 w2 : ℤ) (n : ℕ) :
    ∑ y ∈ Icc w1 w2, Cz n1 (t - y) * Cz n3 (n + y - t) =
      conv (fun z : ℕ => if (t : ℤ) - w2 ≤ z ∧ (z : ℤ) ≤ t - w1 then (n1.choose z : ℝ) else 0)
        (fun z => (n3.choose z : ℝ)) n := by
  unfold conv
  symm
  dsimp only
  refine Finset.sum_bij_ne_zero (fun (z : ℕ) _ _ => ((t : ℤ) - (z : ℤ))) ?_ ?_ ?_ ?_
  · intro z hz hne
    simp only [mem_range] at hz
    simp only [mem_Icc]
    by_contra hc
    rw [if_neg (by omega), zero_mul] at hne; exact hne rfl
  · intro z1 _ _ z2 _ _ h; omega
  · intro y hy hne
    have s1 := Cz_support (left_ne_zero_of_mul hne)
    have s2 := Cz_support (right_ne_zero_of_mul hne)
    simp only [mem_Icc] at hy
    refine ⟨((t : ℤ) - y).toNat, by simp only [mem_range]; omega, ?_, by omega⟩
    rw [if_pos (by omega)]
    unfold Cz at hne
    rw [if_pos (by omega), if_pos (by omega)] at hne
    have e : ((n : ℤ) + y - t).toNat = n - ((t : ℤ) - y).toNat := by omega
    rw [e] at hne; exact hne
  · intro z hz hne
    simp only [mem_range] at hz
    by_cases hc : (t : ℤ) - w2 ≤ z ∧ (z : ℤ) ≤ t - w1
    · rw [if_pos hc]
      unfold Cz
      rw [if_pos (by omega), if_pos (by omega)]
      have e1 : ((t : ℤ) - ((t : ℤ) - z)).toNat = z := by omega
      have e2 : ((n : ℤ) + ((t : ℤ) - z) - t).toNat = n - z := by omega
      rw [e1, e2]
    · rw [if_neg hc, zero_mul] at hne; exact absurd rfl hne

/-- (T1) Marginals of `V` over intervals are `LCNZ` in the first coordinate. -/
theorem Vk_marginal_lcnz (t : ℕ) (m1 m2 w1 w2 : ℤ) :
    LCNZ (fun n : ℕ => ∑ y ∈ Icc w1 w2, Vk t m1 m2 n y) := by
  by_cases hm : m2 ≤ 2 * t ∧ m1 ≤ 2 * t ∧ 2 * (t : ℤ) ≤ m1 + m2
  · obtain ⟨h1, h2, h3⟩ := hm
    set n1 := (2 * (t : ℤ) - m2).toNat
    set n2 := (2 * (t : ℤ) - m1).toNat
    set n3 := (m1 + m2 - 2 * (t : ℤ)).toNat
    set a : ℕ → ℝ := fun z => if (t : ℤ) - w2 ≤ z ∧ (z : ℤ) ≤ t - w1 then (n1.choose z : ℝ) else 0
    have ha : LCNZ a := by
      by_cases hw : 0 ≤ (t : ℤ) - w1
      · refine (LCNZ.restrict (LCNZ.choose n1) ((t : ℤ) - w2).toNat ((t : ℤ) - w1).toNat).congr ?_
        intro z; simp only [a]
        by_cases hz : ((t : ℤ) - w2).toNat ≤ z ∧ z ≤ ((t : ℤ) - w1).toNat
        · rw [if_pos hz, if_pos (by omega)]
        · rw [if_neg hz, if_neg (by omega)]
      · refine LCNZ.zero.congr ?_
        intro z; simp only [a]; rw [if_neg (by omega)]
    have hconv := ha.conv (LCNZ.choose n3)
    have hrefl := (LCNZ.choose n2).reflect t
    have hprod := (hrefl.mul hconv).smul (Vconst_pos t m1 m2)
    refine hprod.congr ?_
    intro n
    simp only [Vk_eq h1 h2 h3]
    rw [← marginal_conv]
    rw [mul_sum, mul_sum]
    refine sum_congr rfl (fun y _ => ?_)
    have e : Cz n2 ((t : ℤ) - n) = if n ≤ t then (n2.choose (t - n) : ℝ) else 0 := by
      unfold Cz
      by_cases hn : n ≤ t
      · rw [if_pos (by omega), if_pos hn]; congr 2; omega
      · rw [if_neg (by omega), if_neg hn]
    rw [← e]
    have e2 : ((n : ℤ) + y - t) = (n : ℤ) + y - t := rfl
    ring
  · exact LCNZ.zero.congr (fun n => by simp [Vk_zero_of hm])


/-! ## Interval-sum bookkeeping on `ℤ` -/

theorem sum_Icc_reflect (f : ℤ → ℝ) (m p q : ℤ) :
    ∑ y ∈ Icc p q, f (m - y) = ∑ y ∈ Icc (m - q) (m - p), f y := by
  refine Finset.sum_nbij' (fun y => m - y) (fun y => m - y) ?_ ?_ ?_ ?_ ?_
  · intro y hy; simp only [mem_Icc] at hy ⊢; omega
  · intro y hy; simp only [mem_Icc] at hy ⊢; omega
  · intro y _; ring
  · intro y _; ring
  · intro y _; rfl

theorem sum_Icc_shift (f : ℤ → ℝ) (d p q : ℤ) :
    ∑ y ∈ Icc p q, f (y - d) = ∑ y ∈ Icc (p - d) (q - d), f y := by
  refine Finset.sum_nbij' (fun y => y - d) (fun y => y + d) ?_ ?_ ?_ ?_ ?_
  · intro y hy; simp only [mem_Icc] at hy ⊢; omega
  · intro y hy; simp only [mem_Icc] at hy ⊢; omega
  · intro y _; ring
  · intro y _; ring
  · intro y _; rfl

/-- Moving an interval down by one: `Σ_{[p-1,q-1]} f - Σ_{[p,q]} f = f(p-1) - f(q)` for `p ≤ q + 1`. -/
theorem sum_Icc_down (f : ℤ → ℝ) {p q : ℤ} (h : p ≤ q + 1) :
    ∑ y ∈ Icc (p - 1) (q - 1), f y - ∑ y ∈ Icc p q, f y = f (p - 1) - f q := by
  rcases eq_or_lt_of_le h with h' | h'
  · have e1 : Icc (p - 1) (q - 1) = ∅ := by ext y; simp only [mem_Icc, notMem_empty, iff_false]; omega
    have e2 : Icc p q = ∅ := by ext y; simp only [mem_Icc, notMem_empty, iff_false]; omega
    simp only [e1, e2, sum_empty]
    rw [show p - 1 = q by omega]; ring
  · have e1 : Icc (p - 1) (q - 1) = insert (p - 1) (Icc p (q - 1)) := by
      ext y; simp only [mem_Icc, mem_insert]; omega
    have e2 : Icc p q = insert q (Icc p (q - 1)) := by
      ext y; simp only [mem_Icc, mem_insert]; omega
    rw [e1, e2, sum_insert (by simp), sum_insert (by simp)]
    ring

/-! ## Pointwise (T2) and monotonicity of marginals -/

/-- (T2) pointwise: `V(x,y) ≤ V(x,y')` for `2x ≤ m₁`, `y ≤ y'`, `y + y' = m₂`. -/
theorem Vk_T2 (t : ℕ) (m1 m2 : ℤ) {x y y' : ℤ} (hx : 2 * x ≤ m1) (hy : y ≤ y') (hs : y + y' = m2) :
    Vk t m1 m2 x y ≤ Vk t m1 m2 x y' := by
  have rr := Vk_rr2 t m1 m2 (x := x) (x' := m1 - x) (y := y) (y' := y') (by omega) hy
  have s1 : Vk t m1 m2 (m1 - x) y' = Vk t m1 m2 x y := by
    rw [show y' = m2 - y by omega, Vk_symm]
  have s2 : Vk t m1 m2 (m1 - x) y = Vk t m1 m2 x y' := by
    rw [show y = m2 - y' by omega, Vk_symm]
  rw [s1, s2] at rr
  have h0 := Vk_nonneg t m1 m2 x y
  have h1 := Vk_nonneg t m1 m2 x y'
  nlinarith

theorem Vk_transpose (t : ℕ) (m1 m2 x y : ℤ) : Vk t m1 m2 x y = Vk t m2 m1 y x := by
  unfold Vk; rw [Hz_symm t x y, Hz_symm t (m1 - x) (m2 - y)]

theorem Vk_neg_left {t : ℕ} {m1 m2 x : ℤ} (hx : x < 0) (y : ℤ) : Vk t m1 m2 x y = 0 := by
  unfold Vk Hz; rw [if_neg (by omega), zero_mul]

/-- Marginal monotonicity: if `G` (a row marginal of `V` over `[w₁,w₂]`) satisfies
`G x ≤ G (m₁ - x)` whenever `2x ≤ m₁`, then `G (x-1) ≤ G x` whenever `2x ≤ m₁`. -/
theorem marginal_mono (t : ℕ) (m1 m2 w1 w2 : ℤ)
    (hsym : ∀ x : ℤ, 2 * x ≤ m1 → ∑ y ∈ Icc w1 w2, Vk t m1 m2 x y ≤ ∑ y ∈ Icc w1 w2, Vk t m1 m2 (m1 - x) y)
    {x : ℤ} (hx : 2 * x ≤ m1) :
    ∑ y ∈ Icc w1 w2, Vk t m1 m2 (x - 1) y ≤ ∑ y ∈ Icc w1 w2, Vk t m1 m2 x y := by
  by_cases h1 : 1 ≤ x
  · have hm : 0 ≤ m1 := by omega
    have lc := Vk_marginal_lcnz t m1 m2 w1 w2
    have := lc.mono_of_reflect m1.toNat (x := x.toNat) (fun n hn => ?_) (by omega) (by omega)
    · have e1 : ((x.toNat - 1 : ℕ) : ℤ) = x - 1 := by omega
      have e2 : ((x.toNat : ℕ) : ℤ) = x := by omega
      rw [e1, e2] at this; exact this
    · have e : ((m1.toNat - n : ℕ) : ℤ) = m1 - n := by omega
      rw [e]; exact hsym n (by omega)
  · rw [sum_eq_zero (fun y _ => Vk_neg_left (by omega) y)]
    exact sum_nonneg (fun y _ => Vk_nonneg _ _ _ _ _)


/-! ## The five box cases -/

/-- Row marginal of `V` over `[p, q]`. -/
noncomputable def Gm (t : ℕ) (m1 m2 p q x : ℤ) : ℝ := ∑ y ∈ Icc p q, Vk t m1 m2 x y

/-- Box sum of `V` over `[p,q] × [r,w]`. -/
noncomputable def Xb (t : ℕ) (m1 m2 p q r w : ℤ) : ℝ := ∑ x ∈ Icc p q, Gm t m1 m2 r w x

theorem Gm_reflect (t : ℕ) (m1 m2 p q x : ℤ) :
    Gm t m1 m2 p q (m1 - x) = Gm t m1 m2 (m2 - q) (m2 - p) x := by
  unfold Gm
  have : ∀ y, Vk t m1 m2 (m1 - x) y = Vk t m1 m2 x (m2 - y) := by
    intro y; rw [← Vk_symm t m1 m2 x (m2 - y), sub_sub_cancel]
  simp only [this]
  exact sum_Icc_reflect (fun y => Vk t m1 m2 x y) m2 p q

theorem Gm_down (t : ℕ) (m1 m2 p q x : ℤ) (h : p ≤ q + 1) :
    Gm t m1 m2 (p - 1) (q - 1) x - Gm t m1 m2 p q x = Vk t m1 m2 x (p - 1) - Vk t m1 m2 x q := by
  unfold Gm; exact sum_Icc_down (fun y => Vk t m1 m2 x y) h

theorem Xb_rows (t : ℕ) (m1 m2 a c1 r w : ℤ) (h : a ≤ c1 - a + 1) :
    Xb t m1 m2 (a - 1) (c1 - a - 1) r w - Xb t m1 m2 a (c1 - a) r w =
      Gm t m1 m2 r w (a - 1) - Gm t m1 m2 r w (c1 - a) := by
  unfold Xb; exact sum_Icc_down (fun x => Gm t m1 m2 r w x) h

/-- The marginal monotonicity lemma in `Gm` notation. -/
theorem Gm_mono (t : ℕ) (m1 m2 p q : ℤ)
    (hsym : ∀ x : ℤ, 2 * x ≤ m1 → Gm t m1 m2 p q x ≤ Gm t m1 m2 p q (m1 - x)) {x : ℤ} (hx : 2 * x ≤ m1) :
    Gm t m1 m2 p q (x - 1) ≤ Gm t m1 m2 p q x :=
  marginal_mono t m1 m2 p q hsym hx

/-- Case `e = e' = (1,0)`: `s = (2,0)`. -/
theorem case_10_10 (t : ℕ) {c1 c2 a b : ℤ} (ha : 2 * a ≤ c1) (_hb : 2 * b ≤ c2) :
    0 ≤ Xb t (c1 - 2) c2 (a - 1) (c1 - a - 1) b (c2 - b) - Xb t (c1 - 2) c2 a (c1 - a) b (c2 - b) := by
  rw [Xb_rows _ _ _ _ _ _ _ (by omega)]
  have e : Gm t (c1 - 2) c2 b (c2 - b) (c1 - a) = Gm t (c1 - 2) c2 b (c2 - b) (a - 1 - 1) := by
    rw [show c1 - a = (c1 - 2) - (a - 2) by ring, Gm_reflect, show c2 - (c2 - b) = b by ring,
      show a - 1 - 1 = a - 2 by ring]
  rw [e]
  have := Gm_mono t (c1 - 2) c2 b (c2 - b) (fun x _ => by
    rw [Gm_reflect, show c2 - (c2 - b) = b by ring]) (x := a - 1) (by omega)
  linarith

/-- Case `e = (1,0)`, `e' = (0,1)`: `s = (1,1)`. -/
theorem case_10_01 (t : ℕ) {c1 c2 a b : ℤ} (ha : 2 * a ≤ c1) (hb : 2 * b ≤ c2) :
    0 ≤ Xb t (c1 - 1) (c2 - 1) (a - 1) (c1 - a - 1) b (c2 - b) -
      Xb t (c1 - 1) (c2 - 1) a (c1 - a) b (c2 - b) := by
  rw [Xb_rows _ _ _ _ _ _ _ (by omega)]
  have e : Gm t (c1 - 1) (c2 - 1) b (c2 - b) (c1 - a) = Gm t (c1 - 1) (c2 - 1) (b - 1) (c2 - b - 1) (a - 1) := by
    rw [show c1 - a = (c1 - 1) - (a - 1) by ring, Gm_reflect]
    congr 1 <;> ring
  rw [e]
  have hd := Gm_down t (c1 - 1) (c2 - 1) b (c2 - b) (a - 1) (by omega)
  have ht := Vk_T2 t (c1 - 1) (c2 - 1) (x := a - 1) (y := b - 1) (y' := c2 - b) (by omega) (by omega) (by omega)
  linarith

/-- Case `e = (1,0)`, `e' = (1,1)`: `s = (2,1)`; the row step. -/
theorem case_10_11 (t : ℕ) {c1 c2 a b : ℤ} (ha : 2 * a ≤ c1) (hb : 2 * b ≤ c2) :
    0 ≤ Xb t (c1 - 2) (c2 - 1) (a - 1) (c1 - a - 1) b (c2 - b) -
      Xb t (c1 - 2) (c2 - 1) a (c1 - a) b (c2 - b) := by
  rw [Xb_rows _ _ _ _ _ _ _ (by omega)]
  set m1 := c1 - 2; set m2 := c2 - 1
  have e : Gm t m1 m2 b (c2 - b) (c1 - a) = Gm t m1 m2 (b - 1) (c2 - b - 1) (a - 1 - 1) := by
    rw [show c1 - a = m1 - (a - 2) by ring, Gm_reflect, show a - 1 - 1 = a - 2 by ring]
    congr 1 <;> ring
  rw [e]
  have hd := Gm_down t m1 m2 b (c2 - b) (a - 1) (by omega)
  have ht := Vk_T2 t m1 m2 (x := a - 1) (y := b - 1) (y' := c2 - b) (by omega) (by omega) (by omega)
  have hm := Gm_mono t m1 m2 (b - 1) (c2 - b - 1) (fun x hx => by
    rw [Gm_reflect, show m2 - (c2 - b - 1) = b by ring, show m2 - (b - 1) = c2 - b by ring]
    have := Gm_down t m1 m2 b (c2 - b) x (by omega)
    have := Vk_T2 t m1 m2 (x := x) (y := b - 1) (y' := c2 - b) hx (by omega) (by omega)
    linarith) (x := a - 1) (by omega)
  linarith


/-- Central symmetry of box sums over a row interval symmetric about `m₁/2`. -/
theorem Xb_reflect_cols (t : ℕ) (c1 m2 a p q : ℤ) :
    Xb t (c1 - 2) m2 (a - 1) (c1 - a - 1) p q = Xb t (c1 - 2) m2 (a - 1) (c1 - a - 1) (m2 - q) (m2 - p) := by
  unfold Xb
  have h := sum_Icc_reflect (fun x => Gm t (c1 - 2) m2 p q x) (c1 - 2) (a - 1) (c1 - a - 1)
  rw [show c1 - 2 - (c1 - a - 1) = a - 1 by ring, show c1 - 2 - (a - 1) = c1 - a - 1 by ring] at h
  rw [← h]
  exact sum_congr rfl (fun x _ => Gm_reflect t (c1 - 2) m2 p q x)

/-- Case `e = (1,1)`, `e' = (1,0)`: `s = (2,1)`. -/
theorem case_11_10 (t : ℕ) {c1 c2 a b : ℤ} (ha : 2 * a ≤ c1) (hb : 2 * b ≤ c2) :
    0 ≤ Xb t (c1 - 2) (c2 - 1) (a - 1) (c1 - a - 1) (b - 1) (c2 - b - 1) -
      Xb t (c1 - 2) (c2 - 1) a (c1 - a) b (c2 - b) := by
  have z := Xb_reflect_cols t c1 (c2 - 1) a (b - 1) (c2 - b - 1)
  rw [show c2 - 1 - (c2 - b - 1) = b by ring, show c2 - 1 - (b - 1) = c2 - b by ring] at z
  rw [z]
  exact case_10_11 t ha hb

/-- Case `e = e' = (1,1)`: `s = (2,2)`. -/
theorem case_11_11 (t : ℕ) {c1 c2 a b : ℤ} (ha : 2 * a ≤ c1) (hb : 2 * b ≤ c2) :
    0 ≤ Xb t (c1 - 2) (c2 - 2) (a - 1) (c1 - a - 1) (b - 1) (c2 - b - 1) -
      Xb t (c1 - 2) (c2 - 2) a (c1 - a) b (c2 - b) := by
  set m1 := c1 - 2; set m2 := c2 - 2
  -- second bracket: X(I-1, J-2) = X(I-1, J)
  have z := Xb_reflect_cols t c1 m2 a (b - 2) (c2 - b - 2)
  rw [show m2 - (c2 - b - 2) = b by ring, show m2 - (b - 2) = c2 - b by ring] at z
  -- first bracket via the column marginal K(y) = Gm t m2 m1 (a-1) (c1-a-1) y
  have colX : ∀ r w, Xb t m1 m2 (a - 1) (c1 - a - 1) r w =
      ∑ y ∈ Icc r w, Gm t m2 m1 (a - 1) (c1 - a - 1) y := by
    intro r w; unfold Xb Gm
    rw [sum_comm]
    exact sum_congr rfl (fun y _ => sum_congr rfl (fun x _ => Vk_transpose t m1 m2 x y))
  have T1 : Xb t m1 m2 (a - 1) (c1 - a - 1) (b - 1) (c2 - b - 1) -
      Xb t m1 m2 (a - 1) (c1 - a - 1) (b - 2) (c2 - b - 2) =
      Gm t m2 m1 (a - 1) (c1 - a - 1) (c2 - b - 1) - Gm t m2 m1 (a - 1) (c1 - a - 1) (b - 2) := by
    rw [colX, colX]
    have := sum_Icc_down (fun y => Gm t m2 m1 (a - 1) (c1 - a - 1) y) (p := b - 1) (q := c2 - b - 1) (by omega)
    rw [show b - 1 - 1 = b - 2 by ring, show c2 - b - 1 - 1 = c2 - b - 2 by ring] at this
    linarith
  have Ksym : Gm t m2 m1 (a - 1) (c1 - a - 1) (c2 - b - 1) = Gm t m2 m1 (a - 1) (c1 - a - 1) (b - 1) := by
    rw [show c2 - b - 1 = m2 - (b - 1) by ring, Gm_reflect]
    congr 1 <;> ring
  have Kmono := Gm_mono t m2 m1 (a - 1) (c1 - a - 1) (fun y _ => by
    rw [Gm_reflect, show m1 - (c1 - a - 1) = a - 1 by ring, show m1 - (a - 1) = c1 - a - 1 by ring])
    (x := b - 1) (by omega)
  rw [show b - 1 - 1 = b - 2 by ring] at Kmono
  -- third bracket: rows
  have R := Xb_rows t m1 m2 a c1 b (c2 - b) (by omega)
  have e : Gm t m1 m2 b (c2 - b) (c1 - a) = Gm t m1 m2 (b - 2) (c2 - b - 2) (a - 2) := by
    rw [show c1 - a = m1 - (a - 2) by ring, Gm_reflect]
    congr 1 <;> ring
  have diff : ∀ x : ℤ, 2 * x ≤ m1 → Gm t m1 m2 (b - 2) (c2 - b - 2) x ≤ Gm t m1 m2 b (c2 - b) x := by
    intro x hx
    have d1 := Gm_down t m1 m2 b (c2 - b) x (by omega)
    have d2 := Gm_down t m1 m2 (b - 1) (c2 - b - 1) x (by omega)
    rw [show b - 1 - 1 = b - 2 by ring, show c2 - b - 1 - 1 = c2 - b - 2 by ring] at d2
    have t1 := Vk_T2 t m1 m2 (x := x) (y := b - 2) (y' := c2 - b) hx (by omega) (by omega)
    have t2 := Vk_T2 t m1 m2 (x := x) (y := b - 1) (y' := c2 - b - 1) hx (by omega) (by omega)
    linarith
  have Gmono := Gm_mono t m1 m2 (b - 2) (c2 - b - 2) (fun x hx => by
    rw [Gm_reflect, show m2 - (c2 - b - 2) = b by ring, show m2 - (b - 2) = c2 - b by ring]
    exact diff x hx) (x := a - 1) (by omega)
  rw [show a - 1 - 1 = a - 2 by ring] at Gmono
  have d := diff (a - 1) (by omega)
  linarith


/-! ## The box identity and `D_c(B) ≥ 0` -/

theorem Xb_transpose (t : ℕ) (m1 m2 p q r w : ℤ) : Xb t m1 m2 p q r w = Xb t m2 m1 r w p q := by
  unfold Xb Gm; rw [sum_comm]
  exact sum_congr rfl (fun y _ => sum_congr rfl (fun x _ => Vk_transpose t m1 m2 x y))

/-- Shifted double sums of products of `H`'s are box sums of `V`. -/
theorem shift_box (t : ℕ) (e1 e2 f1 f2 c1 c2 a1 a2 b1 b2 : ℤ) :
    ∑ x ∈ Icc a1 a2, ∑ y ∈ Icc b1 b2, Hz t (x - e1) (y - e2) * Hz t (c1 - x - f1) (c2 - y - f2) =
      Xb t (c1 - (e1 + f1)) (c2 - (e2 + f2)) (a1 - e1) (a2 - e1) (b1 - e2) (b2 - e2) := by
  unfold Xb Gm Vk
  rw [← sum_Icc_shift]
  refine sum_congr rfl (fun x _ => ?_)
  rw [← sum_Icc_shift]
  refine sum_congr rfl (fun y _ => ?_)
  congr 2 <;> ring

/-- The box sum `D_c(B)` of `T_c` with `k = t + 1`. -/
noncomputable def Dbox (t : ℕ) (c1 c2 a b : ℤ) : ℝ :=
  ∑ x ∈ Icc a (c1 - a), ∑ y ∈ Icc b (c2 - b),
    (Hz (t + 1) x y * Hz (t + 1) (c1 - x) (c2 - y) - Hz t x y * Hz (t + 2) (c1 - x) (c2 - y))

/-- `D_c(B) ≥ 0` for centred boxes. -/
theorem Dbox_nonneg (t : ℕ) {c1 c2 a b : ℤ} (ha : 2 * a ≤ c1) (hb : 2 * b ≤ c2) :
    0 ≤ Dbox t c1 c2 a b := by
  -- pointwise expansion into nine differences
  have pt : ∀ x y : ℤ, Hz (t + 1) x y * Hz (t + 1) (c1 - x) (c2 - y) - Hz t x y * Hz (t + 2) (c1 - x) (c2 - y) =
      (Hz t (x - 1) (y - 0) * Hz t (c1 - x - 1) (c2 - y - 0) - Hz t (x - 0) (y - 0) * Hz t (c1 - x - 2) (c2 - y - 0)) +
      (Hz t (x - 1) (y - 0) * Hz t (c1 - x - 0) (c2 - y - 1) - Hz t (x - 0) (y - 0) * Hz t (c1 - x - 1) (c2 - y - 1)) +
      (Hz t (x - 1) (y - 0) * Hz t (c1 - x - 1) (c2 - y - 1) - Hz t (x - 0) (y - 0) * Hz t (c1 - x - 2) (c2 - y - 1)) +
      (Hz t (x - 0) (y - 1) * Hz t (c1 - x - 1) (c2 - y - 0) - Hz t (x - 0) (y - 0) * Hz t (c1 - x - 1) (c2 - y - 1)) +
      (Hz t (x - 0) (y - 1) * Hz t (c1 - x - 0) (c2 - y - 1) - Hz t (x - 0) (y - 0) * Hz t (c1 - x - 0) (c2 - y - 2)) +
      (Hz t (x - 0) (y - 1) * Hz t (c1 - x - 1) (c2 - y - 1) - Hz t (x - 0) (y - 0) * Hz t (c1 - x - 1) (c2 - y - 2)) +
      (Hz t (x - 1) (y - 1) * Hz t (c1 - x - 1) (c2 - y - 0) - Hz t (x - 0) (y - 0) * Hz t (c1 - x - 2) (c2 - y - 1)) +
      (Hz t (x - 1) (y - 1) * Hz t (c1 - x - 0) (c2 - y - 1) - Hz t (x - 0) (y - 0) * Hz t (c1 - x - 1) (c2 - y - 2)) +
      (Hz t (x - 1) (y - 1) * Hz t (c1 - x - 1) (c2 - y - 1) - Hz t (x - 0) (y - 0) * Hz t (c1 - x - 2) (c2 - y - 2)) := by
    intro x y
    rw [Hz_succ t x y, Hz_succ t (c1 - x) (c2 - y), show t + 2 = (t + 1) + 1 by ring, Hz_succ (t + 1) (c1 - x) (c2 - y),
      Hz_succ t (c1 - x - 1) (c2 - y), Hz_succ t (c1 - x) (c2 - y - 1), Hz_succ t (c1 - x - 1) (c2 - y - 1)]
    rw [show c1 - x - 1 - 1 = c1 - x - 2 by ring, show c2 - y - 1 - 1 = c2 - y - 2 by ring]
    simp only [sub_zero]
    ring
  unfold Dbox
  simp only [pt, sum_add_distrib, sum_sub_distrib]
  -- rewrite all eighteen double sums as box sums
  simp only [shift_box]
  simp only [sub_zero, zero_add, add_zero, show (1 : ℤ) + 1 = 2 by norm_num]
  -- the nine differences
  have k1 := case_10_10 t ha hb
  have k2 := case_10_01 t ha hb
  have k3 := case_10_11 t ha hb
  have k4 : 0 ≤ Xb t (c1 - 1) (c2 - 1) a (c1 - a) (b - 1) (c2 - b - 1) - Xb t (c1 - 1) (c2 - 1) a (c1 - a) b (c2 - b) := by
    rw [Xb_transpose, Xb_transpose t (c1 - 1)]; exact case_10_01 t hb ha
  have k5 : 0 ≤ Xb t c1 (c2 - 2) a (c1 - a) (b - 1) (c2 - b - 1) - Xb t c1 (c2 - 2) a (c1 - a) b (c2 - b) := by
    rw [Xb_transpose, Xb_transpose t c1]; exact case_10_10 t hb ha
  have k6 : 0 ≤ Xb t (c1 - 1) (c2 - 2) a (c1 - a) (b - 1) (c2 - b - 1) - Xb t (c1 - 1) (c2 - 2) a (c1 - a) b (c2 - b) := by
    rw [Xb_transpose, Xb_transpose t (c1 - 1)]; exact case_10_11 t hb ha
  have k7 := case_11_10 t ha hb
  have k8 : 0 ≤ Xb t (c1 - 1) (c2 - 2) (a - 1) (c1 - a - 1) (b - 1) (c2 - b - 1) -
      Xb t (c1 - 1) (c2 - 2) a (c1 - a) b (c2 - b) := by
    rw [Xb_transpose, Xb_transpose t (c1 - 1)]; exact case_11_10 t hb ha
  have k9 := case_11_11 t ha hb
  linarith

end Szkraw
