import Szkraw.CubicDetours
import Szkraw.CubicKeyForms
set_option linter.unusedSectionVars false
namespace Szkraw
open Finset

/-- A function vanishing beyond `a` may be summed over any `range K` with `K ≥ a + 1`. -/
theorem cE_sumExt (G : ℕ → ℝ) (a K : ℕ) (hK : a + 1 ≤ K) (hG : ∀ k, a < k → G k = 0) :
    ∑ n ∈ range K, G n = ∑ n ∈ range (a + 1), G n :=
  (sum_subset (by intro x hx; simp only [mem_range] at hx ⊢; omega)
    fun k _ hk => hG k (by simp only [mem_range, not_lt] at hk; omega)).symm

/-- Shift of a sum whose first `s` terms vanish. -/
theorem cE_shiftSum (G : ℕ → ℝ) (s K : ℕ) (hG : ∀ k < s, G k = 0) :
    ∑ n ∈ range (K + s), G n = ∑ n ∈ range K, G (n + s) := by
  have h0 : ∑ k ∈ range s, G k = 0 := sum_eq_zero fun k hk => hG k (mem_range.mp hk)
  rw [add_comm K s, sum_range_add, h0, zero_add]
  exact sum_congr rfl fun x _ => by rw [add_comm]

/-- Shifted weighted sum: `Σ_n w_n c f_{n-s} = c Σ_m w_{m+s} f_m`. -/
theorem cE_piece (w f : ℕ → ℝ) (a s : ℕ) (c : ℝ) (hw0 : ∀ k < s, w k = 0)
    (hwa : ∀ k, a < k → w k = 0) :
    ∑ n ∈ range (a + 1), w n * (c * f (n - s)) = c * ∑ m ∈ range (a + 1), w (m + s) * f m := by
  have hA : ∑ n ∈ range (a + 1), w n * f (n - s) = ∑ n ∈ range (a + 1 + s), w n * f (n - s) :=
    (cE_sumExt (fun n => w n * f (n - s)) a (a + 1 + s) (by omega)
      (fun k hk => by simp [hwa k hk])).symm
  have hB : ∑ n ∈ range (a + 1 + s), w n * f (n - s) = ∑ n ∈ range (a + 1), w (n + s) * f n :=
    (cE_shiftSum (fun n => w n * f (n - s)) s (a + 1) (fun k hk => by simp [hw0 k hk])).trans
      (sum_congr rfl fun n _ => by simp)
  have h1 : ∑ n ∈ range (a + 1), w n * (c * f (n - s)) = c * ∑ n ∈ range (a + 1), w n * f (n - s) := by
    rw [mul_sum]; exact sum_congr rfl fun n _ => by ring
  rw [h1, hA, hB, mul_sum]

/-- The σ-part of `cubicE`: `Σ_n (n-2) C(a,n) C(n,3)(...)`, written with `cfW3`. -/
theorem cE_sigma (f : ℕ → ℝ) (a : ℕ) :
    ∑ n ∈ range (a + 1), cfW3 a n * (3 * f (n - 1) + 3 * f (n - 2) + f (n - 3)) =
      c3 a * f 0 + lf (a + 1) (cfE3 a) f := by
  have hw0 : ∀ k < 3, cfW3 a k = 0 := fun k hk => cfW3_le2 (a := a) (k := k) (by omega)
  have hwa : ∀ k, a < k → cfW3 a k = 0 := by
    intro k hk
    by_cases h : k ≤ 2
    · exact cfW3_le2 (a := a) (k := k) h
    · rw [cfW3_ge3 (a := a) (k := k) (by omega)]
      simp [Nat.choose_eq_zero_of_lt hk]
  have hw3 : cfW3 a 3 = c3 a := by
    rw [cfW3_ge3 (a := a) (k := 3) le_rfl]
    unfold c3
    rw [choose3_real a, Nat.choose_self]
    norm_num
  have hw1 : cfW3 a 1 = 0 := cfW3_le2 (a := a) (k := 1) (by norm_num)
  have hw2 : cfW3 a 2 = 0 := cfW3_le2 (a := a) (k := 2) (by norm_num)
  simp only [mul_add]
  rw [sum_add_distrib, sum_add_distrib,
    cE_piece (cfW3 a) f a 1 3 (fun k hk => hw0 k (by omega)) hwa,
    cE_piece (cfW3 a) f a 2 3 (fun k hk => hw0 k (by omega)) hwa]
  have hR := cE_piece (cfW3 a) f a 3 1 (fun k hk => hw0 k (by omega)) hwa
  simp only [one_mul] at hR
  rw [hR]
  have h2 : ∑ m ∈ range (a + 1), (if m = 0 then cfW3 a 3 * f 0 else 0) = cfW3 a 3 * f 0 := by
    simp
  have key : ∑ m ∈ range (a + 1), cfE3 a m * f m + cfW3 a 3 * f 0 =
      3 * ∑ m ∈ range (a + 1), cfW3 a (m + 1) * f m + 3 * ∑ m ∈ range (a + 1), cfW3 a (m + 2) * f m +
        ∑ m ∈ range (a + 1), cfW3 a (m + 3) * f m := by
    calc ∑ m ∈ range (a + 1), cfE3 a m * f m + cfW3 a 3 * f 0
        = ∑ m ∈ range (a + 1), (cfE3 a m * f m + (if m = 0 then cfW3 a 3 * f 0 else 0)) := by
          rw [sum_add_distrib, h2]
      _ = ∑ m ∈ range (a + 1), (3 * (cfW3 a (m + 1) * f m) + 3 * (cfW3 a (m + 2) * f m) +
            cfW3 a (m + 3) * f m) := by
          refine sum_congr rfl fun m _ => ?_
          rcases Nat.eq_zero_or_pos m with rfl | hm
          · simp [cfE3_zero, hw1, hw2]
          · rw [cfE3_pos (a := a) (show 1 ≤ m by omega), if_neg (show m ≠ 0 by omega), add_zero]
            ring
      _ = 3 * ∑ m ∈ range (a + 1), cfW3 a (m + 1) * f m + 3 * ∑ m ∈ range (a + 1), cfW3 a (m + 2) * f m +
            ∑ m ∈ range (a + 1), cfW3 a (m + 3) * f m := by
          rw [sum_add_distrib, sum_add_distrib, mul_sum, mul_sum]
  rw [hw3] at key
  unfold lf
  linarith [key]

/-- Splitting `cubicE` at `j = 1`: the `τ + σℓ` part is `quadWw`, the `σ` part is a sum with `cfW3`. -/
theorem cE_split (τ σ : ℝ) (ν : ℕ → ℝ) (ℓ a : ℕ) :
    cubicE τ σ ν 1 ℓ a = quadWw (τ + σ * ℓ) ν 1 ℓ a +
      σ * ∑ n ∈ range (a + 1), cfW3 a n * (3 * Szkraw.iterShift ν ℓ (n - 1) +
        3 * Szkraw.iterShift ν ℓ (n - 2) + Szkraw.iterShift ν ℓ (n - 3)) := by
  unfold cubicE quadWw WtF eC wQ
  rw [mul_sum, ← sum_add_distrib]
  refine sum_congr rfl fun n _ => ?_
  by_cases hn : 3 ≤ n
  · have hc : (((n - (2 * 1 + 1) + 1).choose 1 : ℕ) : ℝ) = (n : ℝ) - 2 := by
      rw [Nat.choose_one_right, show n - (2 * 1 + 1) + 1 = n - 2 by omega,
        Nat.cast_sub (by omega : 2 ≤ n)]
      norm_num
    rw [if_pos (by omega : 2 * 1 + 1 ≤ n), hc, cfW3_ge3 (a := a) (k := n) hn, choose2_real n]
    ring
  · rw [if_neg (by omega : ¬ (2 * 1 + 1 ≤ n)), cfW3_le2 (a := a) (k := n) (by omega)]
    ring

theorem cubicE1_eq (τ σ : ℝ) (ν : ℕ → ℝ) (ℓ a : ℕ) (ha : 3 ≤ a) :
    cubicE τ σ ν 1 ℓ a = (τ + σ * ℓ) * sWs (Szkraw.iterShift ν ℓ) a +
      σ * (c3 a * Szkraw.iterShift ν ℓ 0 + lf (a + 1) (cfE3 a) (Szkraw.iterShift ν ℓ)) := by
  rw [cE_split, quadW1_eq, cE_sigma (Szkraw.iterShift ν ℓ) a]

end Szkraw
