import Szkraw.LCSequences
import Mathlib.Tactic.LinearCombination

/-!
# Convolution preserves log-concavity without internal zeros

Used for property (T1) in the proof of Proposition 8.14 (products of Newton sequences).
The proof is the 2×2 Cauchy–Binet formula for the Toeplitz kernels of the two sequences.
-/

namespace Szkraw

open Finset

/-- The 2×2 Cauchy–Binet identity for finite sums. -/
theorem cauchyBinet2 (A1 A2 B1 B2 : ℕ → ℝ) : ∀ M : ℕ,
    (∑ y ∈ range M, A1 y * B1 y) * (∑ y ∈ range M, A2 y * B2 y) -
      (∑ y ∈ range M, A1 y * B2 y) * (∑ y ∈ range M, A2 y * B1 y) =
    ∑ y' ∈ range M, ∑ y ∈ range y', (A1 y * A2 y' - A1 y' * A2 y) * (B1 y * B2 y' - B1 y' * B2 y)
  | 0 => by simp
  | M + 1 => by
    have ih := cauchyBinet2 A1 A2 B1 B2 M
    have key : ∑ y ∈ range M, (A1 y * A2 M - A1 M * A2 y) * (B1 y * B2 M - B1 M * B2 y) =
        (∑ y ∈ range M, A1 y * B1 y) * (A2 M * B2 M) + (A1 M * B1 M) * (∑ y ∈ range M, A2 y * B2 y) -
          (∑ y ∈ range M, A1 y * B2 y) * (A2 M * B1 M) -
          (A1 M * B2 M) * (∑ y ∈ range M, A2 y * B1 y) := by
      rw [sum_mul, sum_mul, mul_sum, mul_sum, ← sum_add_distrib, ← sum_sub_distrib, ← sum_sub_distrib]
      exact sum_congr rfl (fun y _ => by ring)
    rw [sum_range_succ, sum_range_succ, sum_range_succ, sum_range_succ, sum_range_succ (fun y' => ∑ y ∈ range y', _), key]
    linear_combination ih

/-- Convolution of two sequences. -/
def conv (a b : ℕ → ℝ) (n : ℕ) : ℝ := ∑ i ∈ range (n + 1), a i * b (n - i)

theorem LCNZ.conv_nonneg {a b : ℕ → ℝ} (ha : LCNZ a) (hb : LCNZ b) (n : ℕ) : 0 ≤ conv a b n :=
  sum_nonneg (fun i _ => mul_nonneg (ha.1 i) (hb.1 _))

/-- Log-concavity of the convolution. -/
theorem LCNZ.conv_lc {a b : ℕ → ℝ} (ha : LCNZ a) (hb : LCNZ b) (n : ℕ) :
    conv a b n * conv a b (n + 2) ≤ conv a b (n + 1) ^ 2 := by
  set A1 : ℕ → ℝ := fun y => a y
  set A2 : ℕ → ℝ := fun y => if y = 0 then 0 else a (y - 1)
  set B1 : ℕ → ℝ := fun y => if y ≤ n + 1 then b (n + 1 - y) else 0
  set B2 : ℕ → ℝ := fun y => if y ≤ n + 2 then b (n + 2 - y) else 0
  have cb := cauchyBinet2 A1 A2 B1 B2 (n + 3)
  have s11 : ∑ y ∈ range (n + 3), A1 y * B1 y = conv a b (n + 1) := by
    rw [sum_range_succ]; simp only [A1, B1, conv]
    rw [if_neg (by omega), mul_zero, add_zero]
    exact sum_congr rfl (fun y hy => by rw [if_pos (by simp at hy; omega)])
  have s22 : ∑ y ∈ range (n + 3), A2 y * B2 y = conv a b (n + 1) := by
    rw [sum_range_succ']; simp only [A2, B2, conv]
    simp only [if_true, zero_mul, add_zero]
    refine sum_congr rfl (fun y hy => ?_)
    simp at hy
    rw [if_neg (by omega), if_pos (by omega)]
    congr 2; omega
  have s12 : ∑ y ∈ range (n + 3), A1 y * B2 y = conv a b (n + 2) := by
    simp only [A1, B2, conv]
    exact sum_congr rfl (fun y hy => by rw [if_pos (by simp at hy; omega)])
  have s21 : ∑ y ∈ range (n + 3), A2 y * B1 y = conv a b n := by
    rw [sum_range_succ', sum_range_succ]
    have h0 : A2 0 = 0 := by simp [A2]
    have hlast : B1 (n + 1 + 1) = 0 := by simp only [B1]; rw [if_neg (by omega)]
    rw [h0, hlast, zero_mul, mul_zero, add_zero, add_zero]
    unfold conv
    refine sum_congr rfl (fun y hy => ?_)
    simp only [mem_range] at hy
    simp only [A2, B1]
    rw [if_neg (by omega), if_pos (by omega)]
    congr 2; omega
  rw [s11, s22, s12, s21] at cb
  have hterm : ∀ y' ∈ range (n + 3), ∀ y ∈ range y',
      0 ≤ (A1 y * A2 y' - A1 y' * A2 y) * (B1 y * B2 y' - B1 y' * B2 y) := by
    intro y' hy' y hy
    simp only [mem_range] at hy hy'
    apply mul_nonneg
    · simp only [A1, A2]
      rw [if_neg (by omega)]
      by_cases h0 : y = 0
      · rw [if_pos h0, mul_zero, sub_zero]; exact mul_nonneg (ha.1 _) (ha.1 _)
      · rw [if_neg h0]
        have := ha.balanced 1 y (y' - 1) (by omega) (by omega)
        have e : y' - 1 + 1 = y' := by omega
        rw [e] at this; linarith
    · simp only [B1, B2]
      by_cases hy2 : y' ≤ n + 1
      · rw [if_pos (by omega), if_pos (by omega), if_pos hy2, if_pos (by omega)]
        have := hb.balanced 1 (n + 2 - y') (n + 1 - y) (by omega) (by omega)
        have e1 : n + 2 - y' - 1 = n + 1 - y' := by omega
        have e2 : n + 1 - y + 1 = n + 2 - y := by omega
        rw [e1, e2] at this; linarith
      · rw [if_pos (by omega), if_pos (by omega), if_neg hy2, zero_mul, sub_zero]
        exact mul_nonneg (hb.1 _) (hb.1 _)
  have hsum := sum_nonneg (fun y' hy' => sum_nonneg (hterm y' hy'))
  nlinarith [cb, hsum]

/-- No internal zeros for the convolution. -/
theorem LCNZ.conv_interval {a b : ℕ → ℝ} (ha : LCNZ a) (hb : LCNZ b) (i j k : ℕ) (hij : i ≤ j)
    (hjk : j ≤ k) (hi : 0 < conv a b i) (hk : 0 < conv a b k) : 0 < conv a b j := by
  have pos_of : ∀ m, 0 < conv a b m → ∃ t, t ≤ m ∧ 0 < a t ∧ 0 < b (m - t) := by
    intro m hm
    by_contra h
    push Not at h
    have : conv a b m ≤ 0 := by
      apply sum_nonpos
      intro t ht
      simp only [mem_range] at ht
      by_cases hat : 0 < a t
      · have := h t (by omega) hat
        have hb0 : b (m - t) = 0 := le_antisymm this (hb.1 _)
        rw [hb0, mul_zero]
      · have ha0 : a t = 0 := le_antisymm (not_lt.mp hat) (ha.1 _)
        rw [ha0, zero_mul]
    linarith
  obtain ⟨i1, hi1, hai, hbi⟩ := pos_of i hi
  obtain ⟨k1, hk1, hak, hbk⟩ := pos_of k hk
  have mk : ∀ t, t ≤ j → 0 < a t → 0 < b (j - t) → 0 < conv a b j := by
    intro t ht h1 h2
    unfold conv
    apply sum_pos' (fun s _ => mul_nonneg (ha.1 s) (hb.1 _))
    exact ⟨t, by simp; omega, mul_pos h1 h2⟩
  rcases le_or_gt i1 k1 with hik | hik
  · by_cases hcase : j ≤ i + (k1 - i1)
    · -- t on the first leg, b-index i - i1
      refine mk (i1 + (j - i)) (by omega) ?_ ?_
      · rcases eq_or_lt_of_le (show i1 + (j - i) ≤ k1 by omega) with h | h
        · rw [h]; exact hak
        · exact ha.2.2 i1 _ k1 (by omega) h.le hai hak
      · have e : j - (i1 + (j - i)) = i - i1 := by omega
        rw [e]; exact hbi
    · refine mk k1 (by omega) hak ?_
      exact hb.2.2 (i - i1) (j - k1) (k - k1) (by omega) (by omega) hbi hbk
  · refine mk i1 (by omega) hai ?_
    exact hb.2.2 (i - i1) (j - i1) (k - k1) (by omega) (by omega) hbi hbk

theorem LCNZ.conv {a b : ℕ → ℝ} (ha : LCNZ a) (hb : LCNZ b) : LCNZ (conv a b) := by
  refine ⟨ha.conv_nonneg hb, fun n => ha.conv_lc hb n, ?_⟩
  intro i j k hij hjk hi hk
  exact ha.conv_interval hb i j k hij hjk hi hk

end Szkraw
