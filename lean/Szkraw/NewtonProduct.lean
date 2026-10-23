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

end Szkraw
