import Szkraw.LCConvolution
import Mathlib.Algebra.BigOperators.Intervals

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

end Szkraw
