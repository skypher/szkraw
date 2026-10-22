import Szkraw.LCSequences
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.IntervalCases

/-!
# Detour inequalities (paper, Lemma 8.4)

For an `LCNZ` sequence `u` put `f ℓ n = iterShift u ℓ n` (so `f ℓ n = Σ_h C(ℓ,h) u (n+h)`) and
`W p q ℓ a = Σ_{p ≤ n ≤ a} C(n-p+q, q) C(a,n) f ℓ n`.
-/

namespace Szkraw

open Finset

/-- `W p q ℓ a = Σ_{n ≤ a, p ≤ n} C(n-p+q, q) C(a,n) f_n(ℓ)`. -/
noncomputable def Wt (u : ℕ → ℝ) (p q ℓ a : ℕ) : ℝ :=
  ∑ n ∈ range (a + 1), (if p ≤ n then ((n - p + q).choose q : ℝ) else 0) *
    (a.choose n : ℝ) * Szkraw.iterShift u ℓ n

theorem iterShift_nonneg {u : ℕ → ℝ} (hu : LCNZ u) (ℓ n : ℕ) : 0 ≤ Szkraw.iterShift u ℓ n :=
  (hu.iterShift ℓ).1 n

theorem Wt_nonneg {u : ℕ → ℝ} (hu : LCNZ u) (p q ℓ a : ℕ) : 0 ≤ Wt u p q ℓ a := by
  unfold Wt
  refine sum_nonneg (fun n _ => mul_nonneg (mul_nonneg ?_ (Nat.cast_nonneg _)) (iterShift_nonneg hu ℓ n))
  split_ifs <;> positivity

/-- A single term bounds `W` from below. -/
theorem Wt_ge_term {u : ℕ → ℝ} (hu : LCNZ u) (p q ℓ a n : ℕ) (hpn : p ≤ n) (hna : n ≤ a) :
    ((n - p + q).choose q : ℝ) * (a.choose n : ℝ) * Szkraw.iterShift u ℓ n ≤ Wt u p q ℓ a := by
  unfold Wt
  have hmem : n ∈ range (a + 1) := mem_range.mpr (by omega)
  have := single_le_sum (f := fun n => (if p ≤ n then ((n - p + q).choose q : ℝ) else 0) *
      (a.choose n : ℝ) * Szkraw.iterShift u ℓ n)
    (fun i _ => mul_nonneg (mul_nonneg (by split_ifs <;> positivity) (Nat.cast_nonneg _))
      (iterShift_nonneg hu ℓ i)) hmem
  simpa [hpn] using this

/-- Integer inequality behind the A-family: `4 C(m-j-1, j) ≤ C(m+1,2) C(m-j-2, j-1)`
for `j ≥ 1`, `m ≥ 2j+1`. -/
theorem coeffA (j m : ℕ) (hj : 1 ≤ j) (hm : 2 * j + 1 ≤ m) :
    4 * (m - j - 1).choose j ≤ (m + 1).choose 2 * (m - j - 2).choose (j - 1) := by
  -- (m-j-1) C(m-j-2, j-1) = j C(m-j-1, j)
  have key := Nat.add_one_mul_choose_eq (m - j - 2) (j - 1)
  have e1 : m - j - 2 + 1 = m - j - 1 := by omega
  have e2 : j - 1 + 1 = j := by omega
  rw [e1, e2] at key
  -- key : (m-j-1) * C(m-j-2, j-1) = C(m-j-1, j) * j
  have hc2 : (m + 1).choose 2 * 2 = (m + 1) * m := by
    have := Nat.add_one_mul_choose_eq m 1
    norm_num [Nat.choose_one_right] at this; linarith
  set X := (m - j - 2).choose (j - 1)
  set Y := (m - j - 1).choose j
  -- 2 j * [C(m+1,2) X] = j (m+1) m X ≥ 8 (m-j-1) X = 8 j Y
  have h8 : 8 * (m - j - 1) ≤ j * ((m + 1) * m) := by
    have : 8 * (m - j - 1) ≤ 8 * (m - 2) := by omega
    have h2 : 8 * (m - 2) ≤ (m + 1) * m := by
      rcases Nat.lt_or_ge m 5 with h | h
      · interval_cases m <;> omega
      · have h2' : 2 ≤ m := by omega
        zify [h2']
        nlinarith [sq_nonneg ((m : ℤ) - 4)]
    calc 8 * (m - j - 1) ≤ (m + 1) * m := le_trans this h2
      _ ≤ j * ((m + 1) * m) := Nat.le_mul_of_pos_left _ (by omega)
  have : 2 * j * (4 * Y) ≤ 2 * j * ((m + 1).choose 2 * X) := by
    have lhs : 2 * j * (4 * Y) = 8 * (Y * j) := by ring
    have rhs : 2 * j * ((m + 1).choose 2 * X) = j * ((m + 1).choose 2 * 2) * X := by ring
    rw [lhs, rhs, ← key, hc2]
    calc 8 * ((m - j - 1) * X) = (8 * (m - j - 1)) * X := by ring
      _ ≤ (j * ((m + 1) * m)) * X := Nat.mul_le_mul_right _ h8
      _ = j * ((m + 1) * m) * X := rfl
  exact Nat.le_of_mul_le_mul_left this (by omega)

theorem choose_two_mul (m : ℕ) : m.choose 2 * 2 = m * (m - 1) := by
  rcases Nat.eq_zero_or_pos m with h | h
  · subst h; simp
  · have := Nat.add_one_mul_choose_eq (m - 1) 1
    have e : m - 1 + 1 = m := by omega
    rw [e] at this; norm_num [Nat.choose_one_right] at this; linarith

/-- B-family: `4 C(m-j-2, j) ≤ C(m,2) C(m-j-3, j-1)` for `j ≥ 1`, `m ≥ 2j+2`. -/
theorem coeffB (j m : ℕ) (hj : 1 ≤ j) (hm : 2 * j + 2 ≤ m) :
    4 * (m - j - 2).choose j ≤ m.choose 2 * (m - j - 3).choose (j - 1) := by
  have key := Nat.add_one_mul_choose_eq (m - j - 3) (j - 1)
  have e1 : m - j - 3 + 1 = m - j - 2 := by omega
  have e2 : j - 1 + 1 = j := by omega
  rw [e1, e2] at key
  have hc2 := choose_two_mul m
  set X := (m - j - 3).choose (j - 1)
  set Y := (m - j - 2).choose j
  have h8 : 8 * (m - j - 2) ≤ j * (m * (m - 1)) := by
    have h2 : 8 * (m - 3) ≤ m * (m - 1) := by
      have h3 : 3 ≤ m := by omega
      zify [h3, (by omega : 1 ≤ m)]
      nlinarith [sq_nonneg ((m : ℤ) - 4)]
    calc 8 * (m - j - 2) ≤ 8 * (m - 3) := by omega
      _ ≤ m * (m - 1) := h2
      _ ≤ j * (m * (m - 1)) := Nat.le_mul_of_pos_left _ (by omega)
  have : 2 * j * (4 * Y) ≤ 2 * j * (m.choose 2 * X) := by
    have lhs : 2 * j * (4 * Y) = 8 * (Y * j) := by ring
    have rhs : 2 * j * (m.choose 2 * X) = j * (m.choose 2 * 2) * X := by ring
    rw [lhs, rhs, ← key, hc2]
    calc 8 * ((m - j - 2) * X) = (8 * (m - j - 2)) * X := by ring
      _ ≤ (j * (m * (m - 1))) * X := Nat.mul_le_mul_right _ h8
  exact Nat.le_of_mul_le_mul_left this (by omega)

/-- C-family: `4 C(m-j-1, j+1) ≤ C(m,2) C(m-j-2, j)` for `j ≥ 1`, `m ≥ 2j+2`. -/
theorem coeffC (j m : ℕ) (hj : 1 ≤ j) (hm : 2 * j + 2 ≤ m) :
    4 * (m - j - 1).choose (j + 1) ≤ m.choose 2 * (m - j - 2).choose j := by
  have key := Nat.add_one_mul_choose_eq (m - j - 2) j
  have e1 : m - j - 2 + 1 = m - j - 1 := by omega
  rw [e1] at key
  have hc2 := choose_two_mul m
  set X := (m - j - 2).choose j
  set Y := (m - j - 1).choose (j + 1)
  have h8 : 8 * (m - j - 1) ≤ (j + 1) * (m * (m - 1)) := by
    have h2 : 8 * (m - 2) ≤ 2 * (m * (m - 1)) := by
      have h3 : 2 ≤ m := by omega
      zify [h3, (by omega : 1 ≤ m)]
      nlinarith [sq_nonneg ((m : ℤ) - 3)]
    calc 8 * (m - j - 1) ≤ 8 * (m - 2) := by omega
      _ ≤ 2 * (m * (m - 1)) := h2
      _ ≤ (j + 1) * (m * (m - 1)) := Nat.mul_le_mul_right _ (by omega)
  have : 2 * (j + 1) * (4 * Y) ≤ 2 * (j + 1) * (m.choose 2 * X) := by
    have lhs : 2 * (j + 1) * (4 * Y) = 8 * (Y * (j + 1)) := by ring
    have rhs : 2 * (j + 1) * (m.choose 2 * X) = (j + 1) * (m.choose 2 * 2) * X := by ring
    rw [lhs, rhs, ← key, hc2]
    calc 8 * ((m - j - 1) * X) = (8 * (m - j - 1)) * X := by ring
      _ ≤ ((j + 1) * (m * (m - 1))) * X := Nat.mul_le_mul_right _ h8
  exact Nat.le_of_mul_le_mul_left this (by omega)

end Szkraw
