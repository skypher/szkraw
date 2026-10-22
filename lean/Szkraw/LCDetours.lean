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

theorem reindex1 (G : ℕ → ℝ) (a : ℕ) (hG0 : G 0 = 0) :
    ∑ n ∈ range a, G (n + 1) = ∑ m ∈ range (a + 1), G m := by
  rw [sum_range_succ' G a, hG0, add_zero]

theorem reindex2 (G : ℕ → ℝ) (a : ℕ) (hG0 : G 0 = 0) (hG1 : G 1 = 0) :
    ∑ n ∈ range a, G (n + 2) = ∑ m ∈ range (a + 2), G m := by
  rw [sum_range_succ' G (a + 1), sum_range_succ' (fun m => G (m + 1)) a, hG0, hG1]
  simp

/-- First detour bound for the A-family:
`Σ_m [2j+1 ≤ m] C(m-j-2, j-1) m C(a,m) F0 f_m(ℓ) ≤ W_{1,0}(ℓ,a) W_{2j,j-1}(ℓ+1,a-1)`. -/
theorem detourA_first {u : ℕ → ℝ} (hu : LCNZ u) (j ℓ a : ℕ) (hj : 1 ≤ j) (ha : 1 ≤ a) :
    ∑ m ∈ range (a + 1), (if 2 * j + 1 ≤ m then ((m - j - 2).choose (j - 1) : ℝ) else 0) *
        ((m : ℝ) * (a.choose m : ℝ)) * (Szkraw.iterShift u (ℓ + 1) 0 * Szkraw.iterShift u ℓ m) ≤
      Wt u 1 0 ℓ a * Wt u (2 * j) (j - 1) (ℓ + 1) (a - 1) := by
  set G : ℕ → ℝ := fun m => (if 2 * j + 1 ≤ m then ((m - j - 2).choose (j - 1) : ℝ) else 0) *
        ((m : ℝ) * (a.choose m : ℝ)) * (Szkraw.iterShift u (ℓ + 1) 0 * Szkraw.iterShift u ℓ m) with hG
  have hW10 : (a : ℝ) * Szkraw.iterShift u ℓ 1 ≤ Wt u 1 0 ℓ a := by
    have := Wt_ge_term hu 1 0 ℓ a 1 le_rfl ha
    simpa using this
  have hsplit : a - 1 + 1 = a := by omega
  calc ∑ m ∈ range (a + 1), G m = ∑ n ∈ range a, G (n + 1) := (reindex1 G a (by simp [hG])).symm
    _ ≤ ∑ n ∈ range a, (if 2 * j ≤ n then ((n - 2 * j + (j - 1)).choose (j - 1) : ℝ) else 0) *
          ((a - 1).choose n : ℝ) * Szkraw.iterShift u (ℓ + 1) n *
          ((a : ℝ) * Szkraw.iterShift u ℓ 1) := by
        refine sum_le_sum (fun n _ => ?_)
        simp only [hG]
        by_cases hn : 2 * j ≤ n
        · rw [if_pos (by omega), if_pos hn]
          have e1 : n + 1 - j - 2 = n - 2 * j + (j - 1) := by omega
          rw [e1]
          have hc := Nat.add_one_mul_choose_eq (a - 1) n
          rw [hsplit] at hc
          have hc' : ((n + 1 : ℕ) : ℝ) * (a.choose (n + 1) : ℝ) = (a : ℝ) * ((a - 1).choose n : ℝ) := by
            have : ((a * (a - 1).choose n : ℕ) : ℝ) = ((a.choose (n + 1) * (n + 1) : ℕ) : ℝ) := by rw [hc]
            push_cast at this ⊢; linarith
          rw [hc']
          have key := lemma_8_3 hu ℓ (i := 1) (l := n) le_rfl (by omega)
          rw [add_comm 1 n] at key
          have hC : (0 : ℝ) ≤ ((n - 2 * j + (j - 1)).choose (j - 1) : ℝ) := Nat.cast_nonneg _
          have hA : (0 : ℝ) ≤ (a : ℝ) * ((a - 1).choose n : ℝ) := by positivity
          calc ((n - 2 * j + (j - 1)).choose (j - 1) : ℝ) * ((a : ℝ) * ((a - 1).choose n : ℝ)) *
                (Szkraw.iterShift u (ℓ + 1) 0 * Szkraw.iterShift u ℓ (n + 1))
              ≤ ((n - 2 * j + (j - 1)).choose (j - 1) : ℝ) * ((a : ℝ) * ((a - 1).choose n : ℝ)) *
                (Szkraw.iterShift u ℓ 1 * Szkraw.iterShift u (ℓ + 1) n) :=
                mul_le_mul_of_nonneg_left key (mul_nonneg hC hA)
            _ = _ := by ring
        · rw [if_neg (by omega), if_neg hn]; simp
    _ = ((a : ℝ) * Szkraw.iterShift u ℓ 1) * Wt u (2 * j) (j - 1) (ℓ + 1) (a - 1) := by
        rw [Wt, hsplit, mul_sum]; refine sum_congr rfl (fun n _ => by ring)
    _ ≤ Wt u 1 0 ℓ a * Wt u (2 * j) (j - 1) (ℓ + 1) (a - 1) :=
        mul_le_mul_of_nonneg_right hW10 (Wt_nonneg hu _ _ _ _)

/-- Second detour bound for the A-family:
`Σ_m [2j+1 ≤ m] C(m-j-2, j-1) C(m,2) C(a,m) F0 f_m(ℓ) ≤ W_{2,0}(ℓ,a) W_{2j-1,j-1}(ℓ+1,a-2)`. -/
theorem detourA_second {u : ℕ → ℝ} (hu : LCNZ u) (j ℓ a : ℕ) (hj : 1 ≤ j) (ha : 2 ≤ a) :
    ∑ m ∈ range (a + 1), (if 2 * j + 1 ≤ m then ((m - j - 2).choose (j - 1) : ℝ) else 0) *
        ((m.choose 2 : ℝ) * (a.choose m : ℝ)) * (Szkraw.iterShift u (ℓ + 1) 0 * Szkraw.iterShift u ℓ m) ≤
      Wt u 2 0 ℓ a * Wt u (2 * j - 1) (j - 1) (ℓ + 1) (a - 2) := by
  set G : ℕ → ℝ := fun m => (if 2 * j + 1 ≤ m then ((m - j - 2).choose (j - 1) : ℝ) else 0) *
        ((m.choose 2 : ℝ) * (a.choose m : ℝ)) * (Szkraw.iterShift u (ℓ + 1) 0 * Szkraw.iterShift u ℓ m) with hG
  have hW20 : (a.choose 2 : ℝ) * Szkraw.iterShift u ℓ 2 ≤ Wt u 2 0 ℓ a := by
    have := Wt_ge_term hu 2 0 ℓ a 2 le_rfl ha
    simpa using this
  have hsplit : a - 2 + 1 + 1 = a + 1 - 1 := by omega
  have hsplit' : a - 2 + 1 = a - 1 := by omega
  have hre : ∑ m ∈ range (a + 1), G m = ∑ n ∈ range (a - 1), G (n + 2) := by
    rw [reindex2 G (a - 1) (by simp [hG]) (by simp [hG]), show a - 1 + 2 = a + 1 by omega]
  calc ∑ m ∈ range (a + 1), G m = ∑ n ∈ range (a - 1), G (n + 2) := hre
    _ ≤ ∑ n ∈ range (a - 1), (if 2 * j - 1 ≤ n then ((n - (2 * j - 1) + (j - 1)).choose (j - 1) : ℝ) else 0) *
          ((a - 2).choose n : ℝ) * Szkraw.iterShift u (ℓ + 1) n *
          ((a.choose 2 : ℝ) * Szkraw.iterShift u ℓ 2) := by
        refine sum_le_sum (fun n _ => ?_)
        simp only [hG]
        by_cases hn : 2 * j - 1 ≤ n
        · rw [if_pos (by omega), if_pos hn]
          have e1 : n + 2 - j - 2 = n - (2 * j - 1) + (j - 1) := by omega
          rw [e1]
          have hc := Nat.choose_mul (n := a) (k := n + 2) (s := 2) (by omega)
          have e2 : n + 2 - 2 = n := by omega
          rw [e2] at hc
          have hc' : ((n + 2).choose 2 : ℝ) * (a.choose (n + 2) : ℝ) = (a.choose 2 : ℝ) * ((a - 2).choose n : ℝ) := by
            have : ((a.choose (n + 2) * (n + 2).choose 2 : ℕ) : ℝ) = ((a.choose 2 * (a - 2).choose n : ℕ) : ℝ) := by
              rw [hc]
            push_cast at this; linarith
          rw [hc']
          have key := lemma_8_3 hu ℓ (i := 2) (l := n) (by omega) (by omega)
          rw [add_comm 2 n] at key
          have hC : (0 : ℝ) ≤ ((n - (2 * j - 1) + (j - 1)).choose (j - 1) : ℝ) := Nat.cast_nonneg _
          have hA : (0 : ℝ) ≤ (a.choose 2 : ℝ) * ((a - 2).choose n : ℝ) := by positivity
          calc ((n - (2 * j - 1) + (j - 1)).choose (j - 1) : ℝ) * ((a.choose 2 : ℝ) * ((a - 2).choose n : ℝ)) *
                (Szkraw.iterShift u (ℓ + 1) 0 * Szkraw.iterShift u ℓ (n + 2))
              ≤ ((n - (2 * j - 1) + (j - 1)).choose (j - 1) : ℝ) * ((a.choose 2 : ℝ) * ((a - 2).choose n : ℝ)) *
                (Szkraw.iterShift u ℓ 2 * Szkraw.iterShift u (ℓ + 1) n) :=
                mul_le_mul_of_nonneg_left key (mul_nonneg hC hA)
            _ = _ := by ring
        · rw [if_neg (by omega), if_neg hn]; simp
    _ = ((a.choose 2 : ℝ) * Szkraw.iterShift u ℓ 2) * Wt u (2 * j - 1) (j - 1) (ℓ + 1) (a - 2) := by
        rw [Wt, hsplit', mul_sum]; refine sum_congr rfl (fun n _ => by ring)
    _ ≤ Wt u 2 0 ℓ a * Wt u (2 * j - 1) (j - 1) (ℓ + 1) (a - 2) :=
        mul_le_mul_of_nonneg_right hW20 (Wt_nonneg hu _ _ _ _)

theorem Wt_eq_zero {u : ℕ → ℝ} (p q ℓ a : ℕ) (h : a < p) : Wt u p q ℓ a = 0 := by
  unfold Wt
  refine sum_eq_zero (fun n hn => ?_)
  rw [mem_range] at hn
  rw [if_neg (by omega)]; simp

/-- Generic second detour: for `p ≥ 1`,
`Σ_m [p+2 ≤ m] C(m-2-p+q, q) C(m,2) C(a,m) F0 f_m(ℓ) ≤ W_{2,0}(ℓ,a) W_{p,q}(ℓ+1,a-2)`. -/
theorem detour_second {u : ℕ → ℝ} (hu : LCNZ u) (p q ℓ a : ℕ) (hp : 1 ≤ p) (ha : 2 ≤ a) :
    ∑ m ∈ range (a + 1), (if p + 2 ≤ m then ((m - 2 - p + q).choose q : ℝ) else 0) *
        ((m.choose 2 : ℝ) * (a.choose m : ℝ)) * (Szkraw.iterShift u (ℓ + 1) 0 * Szkraw.iterShift u ℓ m) ≤
      Wt u 2 0 ℓ a * Wt u p q (ℓ + 1) (a - 2) := by
  set G : ℕ → ℝ := fun m => (if p + 2 ≤ m then ((m - 2 - p + q).choose q : ℝ) else 0) *
        ((m.choose 2 : ℝ) * (a.choose m : ℝ)) * (Szkraw.iterShift u (ℓ + 1) 0 * Szkraw.iterShift u ℓ m) with hG
  have hW20 : (a.choose 2 : ℝ) * Szkraw.iterShift u ℓ 2 ≤ Wt u 2 0 ℓ a := by
    have := Wt_ge_term hu 2 0 ℓ a 2 le_rfl ha
    simpa using this
  have hsplit' : a - 2 + 1 = a - 1 := by omega
  have hre : ∑ m ∈ range (a + 1), G m = ∑ n ∈ range (a - 1), G (n + 2) := by
    rw [reindex2 G (a - 1) (by simp [hG]) (by simp [hG]), show a - 1 + 2 = a + 1 by omega]
  calc ∑ m ∈ range (a + 1), G m = ∑ n ∈ range (a - 1), G (n + 2) := hre
    _ ≤ ∑ n ∈ range (a - 1), (if p ≤ n then ((n - p + q).choose q : ℝ) else 0) *
          ((a - 2).choose n : ℝ) * Szkraw.iterShift u (ℓ + 1) n *
          ((a.choose 2 : ℝ) * Szkraw.iterShift u ℓ 2) := by
        refine sum_le_sum (fun n _ => ?_)
        simp only [hG]
        by_cases hn : p ≤ n
        · rw [if_pos (by omega), if_pos hn]
          have e1 : n + 2 - 2 - p + q = n - p + q := by omega
          rw [e1]
          have hc := Nat.choose_mul (n := a) (k := n + 2) (s := 2) (by omega)
          have e2 : n + 2 - 2 = n := by omega
          rw [e2] at hc
          have hc' : ((n + 2).choose 2 : ℝ) * (a.choose (n + 2) : ℝ) = (a.choose 2 : ℝ) * ((a - 2).choose n : ℝ) := by
            have : ((a.choose (n + 2) * (n + 2).choose 2 : ℕ) : ℝ) = ((a.choose 2 * (a - 2).choose n : ℕ) : ℝ) := by
              rw [hc]
            push_cast at this; linarith
          rw [hc']
          have key := lemma_8_3 hu ℓ (i := 2) (l := n) (by omega) (by omega)
          rw [add_comm 2 n] at key
          have hC : (0 : ℝ) ≤ ((n - p + q).choose q : ℝ) := Nat.cast_nonneg _
          have hA : (0 : ℝ) ≤ (a.choose 2 : ℝ) * ((a - 2).choose n : ℝ) := by positivity
          calc ((n - p + q).choose q : ℝ) * ((a.choose 2 : ℝ) * ((a - 2).choose n : ℝ)) *
                (Szkraw.iterShift u (ℓ + 1) 0 * Szkraw.iterShift u ℓ (n + 2))
              ≤ ((n - p + q).choose q : ℝ) * ((a.choose 2 : ℝ) * ((a - 2).choose n : ℝ)) *
                (Szkraw.iterShift u ℓ 2 * Szkraw.iterShift u (ℓ + 1) n) :=
                mul_le_mul_of_nonneg_left key (mul_nonneg hC hA)
            _ = _ := by ring
        · rw [if_neg (by omega), if_neg hn]; simp
    _ = ((a.choose 2 : ℝ) * Szkraw.iterShift u ℓ 2) * Wt u p q (ℓ + 1) (a - 2) := by
        rw [Wt, hsplit', mul_sum]; refine sum_congr rfl (fun n _ => by ring)
    _ ≤ Wt u 2 0 ℓ a * Wt u p q (ℓ + 1) (a - 2) :=
        mul_le_mul_of_nonneg_right hW20 (Wt_nonneg hu _ _ _ _)

/-- Lemma 8.4, A-family:
`4 d_{ℓ+1} A_j(ℓ,a) ≤ A_0(ℓ,a) B_{j-1}(ℓ+1,a-1) + B_0(ℓ,a) A_{j-1}(ℓ+1,a-2)`. -/
theorem lemma_8_4_A {u : ℕ → ℝ} (hu : LCNZ u) (j ℓ a : ℕ) (hj : 1 ≤ j) :
    4 * Szkraw.iterShift u (ℓ + 1) 0 * Wt u (2 * j + 1) j ℓ a ≤
      Wt u 1 0 ℓ a * Wt u (2 * j) (j - 1) (ℓ + 1) (a - 1) +
      Wt u 2 0 ℓ a * Wt u (2 * j - 1) (j - 1) (ℓ + 1) (a - 2) := by
  have hF0 := iterShift_nonneg hu (ℓ + 1) 0
  by_cases ha : a < 2 * j + 1
  · rw [Wt_eq_zero _ _ _ _ ha, mul_zero]
    exact add_nonneg (mul_nonneg (Wt_nonneg hu _ _ _ _) (Wt_nonneg hu _ _ _ _))
      (mul_nonneg (Wt_nonneg hu _ _ _ _) (Wt_nonneg hu _ _ _ _))
  push Not at ha
  have h1 := detourA_first hu j ℓ a hj (by omega)
  have h2 := detour_second hu (2 * j - 1) (j - 1) ℓ a (by omega) (by omega)
  refine le_trans ?_ (add_le_add h1 h2)
  rw [← sum_add_distrib, Wt, mul_sum]
  refine sum_le_sum (fun m _ => ?_)
  by_cases hm : 2 * j + 1 ≤ m
  · rw [if_pos hm, if_pos hm, if_pos (by omega)]
    have e1 : m - (2 * j + 1) + j = m - j - 1 := by omega
    have e2 : m - 2 - (2 * j - 1) + (j - 1) = m - j - 2 := by omega
    rw [e1, e2]
    have hco := coeffA j m hj hm
    have hpas : (m + 1).choose 2 = m + m.choose 2 := by
      rw [show (2 : ℕ) = 1 + 1 from rfl, Nat.choose_succ_succ, Nat.choose_one_right]
    rw [hpas] at hco
    have hco' : (4 : ℝ) * ((m - j - 1).choose j : ℝ) ≤ ((m : ℝ) + (m.choose 2 : ℝ)) * ((m - j - 2).choose (j - 1) : ℝ) := by
      exact_mod_cast hco
    have hf := iterShift_nonneg hu ℓ m
    have hc : (0 : ℝ) ≤ (a.choose m : ℝ) := Nat.cast_nonneg _
    have : 4 * Szkraw.iterShift u (ℓ + 1) 0 * (((m - j - 1).choose j : ℝ) * (a.choose m : ℝ) * Szkraw.iterShift u ℓ m) =
        (4 * ((m - j - 1).choose j : ℝ)) * ((a.choose m : ℝ) * (Szkraw.iterShift u (ℓ + 1) 0 * Szkraw.iterShift u ℓ m)) := by ring
    rw [this]
    have rhs : ((m - j - 2).choose (j - 1) : ℝ) * ((m : ℝ) * (a.choose m : ℝ)) *
          (Szkraw.iterShift u (ℓ + 1) 0 * Szkraw.iterShift u ℓ m) +
        ((m - j - 2).choose (j - 1) : ℝ) * ((m.choose 2 : ℝ) * (a.choose m : ℝ)) *
          (Szkraw.iterShift u (ℓ + 1) 0 * Szkraw.iterShift u ℓ m) =
        (((m : ℝ) + (m.choose 2 : ℝ)) * ((m - j - 2).choose (j - 1) : ℝ)) *
          ((a.choose m : ℝ) * (Szkraw.iterShift u (ℓ + 1) 0 * Szkraw.iterShift u ℓ m)) := by ring
    rw [rhs]
    exact mul_le_mul_of_nonneg_right hco' (mul_nonneg hc (mul_nonneg hF0 hf))
  · rw [if_neg hm, if_neg hm, if_neg (by omega)]; simp

/-- Lemma 8.4, B-family: `4 d_{ℓ+1} B_j(ℓ,a) ≤ B_0(ℓ,a) B_{j-1}(ℓ+1,a-2)`. -/
theorem lemma_8_4_B {u : ℕ → ℝ} (hu : LCNZ u) (j ℓ a : ℕ) (hj : 1 ≤ j) :
    4 * Szkraw.iterShift u (ℓ + 1) 0 * Wt u (2 * j + 2) j ℓ a ≤
      Wt u 2 0 ℓ a * Wt u (2 * j) (j - 1) (ℓ + 1) (a - 2) := by
  have hF0 := iterShift_nonneg hu (ℓ + 1) 0
  by_cases ha : a < 2 * j + 2
  · rw [Wt_eq_zero _ _ _ _ ha, mul_zero]
    exact mul_nonneg (Wt_nonneg hu _ _ _ _) (Wt_nonneg hu _ _ _ _)
  push Not at ha
  refine le_trans ?_ (detour_second hu (2 * j) (j - 1) ℓ a (by omega) (by omega))
  rw [Wt, mul_sum]
  refine sum_le_sum (fun m _ => ?_)
  by_cases hm : 2 * j + 2 ≤ m
  · rw [if_pos hm, if_pos hm]
    have e1 : m - (2 * j + 2) + j = m - j - 2 := by omega
    have e2 : m - 2 - 2 * j + (j - 1) = m - j - 3 := by omega
    rw [e1, e2]
    have hco' : (4 : ℝ) * ((m - j - 2).choose j : ℝ) ≤ (m.choose 2 : ℝ) * ((m - j - 3).choose (j - 1) : ℝ) := by
      exact_mod_cast coeffB j m hj hm
    have hf := iterShift_nonneg hu ℓ m
    have hc : (0 : ℝ) ≤ (a.choose m : ℝ) := Nat.cast_nonneg _
    calc 4 * Szkraw.iterShift u (ℓ + 1) 0 * (((m - j - 2).choose j : ℝ) * (a.choose m : ℝ) * Szkraw.iterShift u ℓ m)
        = (4 * ((m - j - 2).choose j : ℝ)) * ((a.choose m : ℝ) * (Szkraw.iterShift u (ℓ + 1) 0 * Szkraw.iterShift u ℓ m)) := by ring
      _ ≤ ((m.choose 2 : ℝ) * ((m - j - 3).choose (j - 1) : ℝ)) * ((a.choose m : ℝ) * (Szkraw.iterShift u (ℓ + 1) 0 * Szkraw.iterShift u ℓ m)) :=
          mul_le_mul_of_nonneg_right hco' (mul_nonneg hc (mul_nonneg hF0 hf))
      _ = _ := by ring
  · rw [if_neg hm, if_neg hm]; simp

/-- Lemma 8.4, C-family: `4 d_{ℓ+1} C_j(ℓ,a) ≤ B_0(ℓ,a) C_{j-1}(ℓ+1,a-2)`. -/
theorem lemma_8_4_C {u : ℕ → ℝ} (hu : LCNZ u) (j ℓ a : ℕ) (hj : 1 ≤ j) :
    4 * Szkraw.iterShift u (ℓ + 1) 0 * Wt u (2 * j + 2) (j + 1) ℓ a ≤
      Wt u 2 0 ℓ a * Wt u (2 * j) j (ℓ + 1) (a - 2) := by
  have hF0 := iterShift_nonneg hu (ℓ + 1) 0
  by_cases ha : a < 2 * j + 2
  · rw [Wt_eq_zero _ _ _ _ ha, mul_zero]
    exact mul_nonneg (Wt_nonneg hu _ _ _ _) (Wt_nonneg hu _ _ _ _)
  push Not at ha
  refine le_trans ?_ (detour_second hu (2 * j) j ℓ a (by omega) (by omega))
  rw [Wt, mul_sum]
  refine sum_le_sum (fun m _ => ?_)
  by_cases hm : 2 * j + 2 ≤ m
  · rw [if_pos hm, if_pos hm]
    have e1 : m - (2 * j + 2) + (j + 1) = m - j - 1 := by omega
    have e2 : m - 2 - 2 * j + j = m - j - 2 := by omega
    rw [e1, e2]
    have hco' : (4 : ℝ) * ((m - j - 1).choose (j + 1) : ℝ) ≤ (m.choose 2 : ℝ) * ((m - j - 2).choose j : ℝ) := by
      exact_mod_cast coeffC j m hj hm
    have hf := iterShift_nonneg hu ℓ m
    have hc : (0 : ℝ) ≤ (a.choose m : ℝ) := Nat.cast_nonneg _
    calc 4 * Szkraw.iterShift u (ℓ + 1) 0 * (((m - j - 1).choose (j + 1) : ℝ) * (a.choose m : ℝ) * Szkraw.iterShift u ℓ m)
        = (4 * ((m - j - 1).choose (j + 1) : ℝ)) * ((a.choose m : ℝ) * (Szkraw.iterShift u (ℓ + 1) 0 * Szkraw.iterShift u ℓ m)) := by ring
      _ ≤ ((m.choose 2 : ℝ) * ((m - j - 2).choose j : ℝ)) * ((a.choose m : ℝ) * (Szkraw.iterShift u (ℓ + 1) 0 * Szkraw.iterShift u ℓ m)) :=
          mul_le_mul_of_nonneg_right hco' (mul_nonneg hc (mul_nonneg hF0 hf))
      _ = _ := by ring
  · rw [if_neg hm, if_neg hm]; simp

end Szkraw
