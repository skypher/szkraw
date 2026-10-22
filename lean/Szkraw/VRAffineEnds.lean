import Szkraw.VRAffineKey

/-!
# Theorem 8.9: the endpoint inequalities of the key inequality (paper, proof of Theorem 8.9)

For a log-concave sequence `u` without internal zeros with `u 1 = 1`, `a ≥ 3`, `q = u 2 > 0` and
`y_n = C(a,n) u_n`: with `Y = Σ_{n≥2} y_n`, `J = Σ_{2≤n≤a-1} C(a-1,n) u_n`,
`Y' = Σ_{j≥2} C(a-1,j)(u_j + u_{j+1})`, `H_* = Σ_{n≥3} (n-2) y_n` and
`T = Σ_{n≥2} (n-3)(a-n) y_n`, the function
`F(z) = z Y Y' + (z+1) Y J - (z+1)(4 z H_* + 2T)` is nonnegative on `[0, 1/q]`: it is concave,
`F(0) = YJ - 2T ≥ 0` and `F(1/q) ≥ 0`.
-/

set_option linter.unusedSectionVars false

namespace Szkraw

open Finset

/-- `Y = Σ_{n ≥ 2} C(a,n) u_n`. -/
noncomputable def sY (u : ℕ → ℝ) (a : ℕ) : ℝ :=
  ∑ n ∈ range (a + 1), (if 2 ≤ n then (a.choose n : ℝ) else 0) * u n

/-- `J = Σ_{2 ≤ n ≤ a-1} C(a-1,n) u_n`. -/
noncomputable def sJ (u : ℕ → ℝ) (a : ℕ) : ℝ :=
  ∑ n ∈ range a, (if 2 ≤ n then ((a - 1).choose n : ℝ) else 0) * u n

/-- `Y' = Σ_{j ≥ 2} C(a-1,j) (u_j + u_{j+1})`. -/
noncomputable def sYp (u : ℕ → ℝ) (a : ℕ) : ℝ :=
  ∑ j ∈ range a, (if 2 ≤ j then ((a - 1).choose j : ℝ) else 0) * (u j + u (j + 1))

/-- `H_* = Σ_{n ≥ 3} (n-2) C(a,n) u_n`. -/
noncomputable def sH (u : ℕ → ℝ) (a : ℕ) : ℝ :=
  ∑ n ∈ range (a + 1), (if 3 ≤ n then ((n : ℝ) - 2) * (a.choose n : ℝ) else 0) * u n

/-- `T = Σ_{n ≥ 2} (n-3)(a-n) C(a,n) u_n`. -/
noncomputable def sT (u : ℕ → ℝ) (a : ℕ) : ℝ :=
  ∑ n ∈ range (a + 1), (if 2 ≤ n then ((n : ℝ) - 3) * ((a : ℝ) - n) * (a.choose n : ℝ) else 0) * u n

/-- `F(z)`. -/
noncomputable def Fz (u : ℕ → ℝ) (a : ℕ) (z : ℝ) : ℝ :=
  z * sY u a * sYp u a + (z + 1) * sY u a * sJ u a - (z + 1) * (4 * z * sH u a + 2 * sT u a)

section Ends

variable {u : ℕ → ℝ}

theorem LCNZ.pair (hu : LCNZ u) {i j : ℕ} (hi : 1 ≤ i) (hj : 1 ≤ j) :
    u 1 * u (i + j - 1) ≤ u i * u j := by
  rcases le_total i j with h | h
  · have := hu.balanced (i - 1) i j (by omega) h
    rwa [show i - (i - 1) = 1 by omega, show j + (i - 1) = i + j - 1 by omega] at this
  · have := hu.balanced (j - 1) j i (by omega) h
    rw [show j - (j - 1) = 1 by omega, show i + (j - 1) = i + j - 1 by omega] at this
    linarith [mul_comm (u i) (u j)]

theorem sY_nonneg (hu : LCNZ u) (a : ℕ) : 0 ≤ sY u a :=
  sum_nonneg fun n _ => mul_nonneg (by split_ifs <;> positivity) (hu.1 n)

theorem sJ_nonneg (hu : LCNZ u) (a : ℕ) : 0 ≤ sJ u a :=
  sum_nonneg fun n _ => mul_nonneg (by split_ifs <;> positivity) (hu.1 n)

theorem sYp_nonneg (hu : LCNZ u) (a : ℕ) : 0 ≤ sYp u a :=
  sum_nonneg fun n _ => mul_nonneg (by split_ifs <;> positivity) (add_nonneg (hu.1 _) (hu.1 _))

theorem sH_nonneg (hu : LCNZ u) (a : ℕ) : 0 ≤ sH u a := by
  refine sum_nonneg fun n _ => mul_nonneg ?_ (hu.1 n)
  split_ifs with h
  · have : (3 : ℝ) ≤ n := by exact_mod_cast h
    exact mul_nonneg (by linarith) (Nat.cast_nonneg _)
  · exact le_rfl

/-- `Y ≥ C(a,2) u_2 + C(a,3) u_3` for `a ≥ 3`. -/
theorem sY_ge (hu : LCNZ u) {a : ℕ} (ha : 3 ≤ a) :
    (a.choose 2 : ℝ) * u 2 + (a.choose 3 : ℝ) * u 3 ≤ sY u a := by
  unfold sY
  have h2 : 2 ∈ range (a + 1) := mem_range.mpr (by omega)
  have h3 : 3 ∈ (range (a + 1)).erase 2 := mem_erase.mpr ⟨by omega, mem_range.mpr (by omega)⟩
  rw [← add_sum_erase _ _ h2, ← add_sum_erase _ _ h3]
  simp only [show (2 : ℕ) ≤ 2 from le_rfl, show (2 : ℕ) ≤ 3 by omega, if_true]
  have : 0 ≤ ∑ x ∈ ((range (a + 1)).erase 2).erase 3, (if 2 ≤ x then (a.choose x : ℝ) else 0) * u x :=
    sum_nonneg fun n _ => mul_nonneg (by split_ifs <;> positivity) (hu.1 n)
  linarith

/-- `u_2 J ≥ Σ_{m ≥ 3} C(a-1, m-1) u_m` for `u 1 = 1`. -/
theorem u2J_ge (hu : LCNZ u) (hu1 : u 1 = 1) (a : ℕ) :
    ∑ m ∈ range (a + 1), (if 3 ≤ m then ((a - 1).choose (m - 1) : ℝ) else 0) * u m ≤ u 2 * sJ u a := by
  set G : ℕ → ℝ := fun m => (if 3 ≤ m then ((a - 1).choose (m - 1) : ℝ) else 0) * u m with hG
  rw [← reindex1 G a (by simp [hG]), sJ, mul_sum]
  refine sum_le_sum fun n _ => ?_
  simp only [hG]
  by_cases h : 2 ≤ n
  · rw [if_pos (by omega), if_pos h, show n + 1 - 1 = n by omega]
    have := hu.pair (i := 2) (j := n) (by norm_num) (by omega)
    rw [hu1, one_mul, show 2 + n - 1 = n + 1 by omega] at this
    have hc : (0 : ℝ) ≤ ((a - 1).choose n : ℝ) := Nat.cast_nonneg _
    nlinarith
  · rw [if_neg (by omega), if_neg h]; simp

/-- `u_3 J ≥ Σ_{m ≥ 4} C(a-1, m-2) u_m` (terms `m ≤ a`) for `u 1 = 1`. -/
theorem u3J_ge (hu : LCNZ u) (hu1 : u 1 = 1) (a : ℕ) :
    ∑ m ∈ range (a + 1), (if 4 ≤ m then ((a - 1).choose (m - 2) : ℝ) else 0) * u m ≤ u 3 * sJ u a := by
  set G : ℕ → ℝ := fun m => (if 4 ≤ m then ((a - 1).choose (m - 2) : ℝ) else 0) * u m with hG
  have hnn : ∀ m, 0 ≤ G m := fun m => mul_nonneg (by split_ifs <;> positivity) (hu.1 m)
  calc ∑ m ∈ range (a + 1), G m ≤ ∑ m ∈ range (a + 2), G m :=
        sum_le_sum_of_subset_of_nonneg (range_subset_range.mpr (by omega)) fun m _ _ => hnn m
    _ = ∑ n ∈ range a, G (n + 2) := (reindex2 G a (by simp [hG]) (by simp [hG])).symm
    _ ≤ u 3 * sJ u a := by
        rw [sJ, mul_sum]
        refine sum_le_sum fun n _ => ?_
        simp only [hG]
        by_cases h : 2 ≤ n
        · rw [if_pos (by omega), if_pos h, show n + 2 - 2 = n by omega]
          have := hu.pair (i := 3) (j := n) (by norm_num) (by omega)
          rw [hu1, one_mul, show 3 + n - 1 = n + 2 by omega] at this
          have hc : (0 : ℝ) ≤ ((a - 1).choose n : ℝ) := Nat.cast_nonneg _
          nlinarith
        · rw [if_neg (by omega), if_neg h]; simp

/-- `L_3 = 3/2`, `L_n = n(n+2)/6`. -/
noncomputable def Lc (n : ℕ) : ℝ := if n = 3 then 3 / 2 else (n : ℝ) * (n + 2) / 6

/-- The coefficient bound behind (10). -/
theorem coeff10 {a m : ℕ} (hm3 : 3 ≤ m) (hma : m + 1 ≤ a) :
    Lc m * ((a : ℝ) - m) * (a.choose m : ℝ) ≤
      (a.choose 2 : ℝ) * ((a - 1).choose (m - 1) : ℝ) +
        (if 4 ≤ m then (a.choose 3 : ℝ) * ((a - 1).choose (m - 2) : ℝ) else 0) := by
  -- `C(a,2) C(a-2,m-1) = C(a,m+1) C(m+1,2)` and `C(a,m+1)(m+1) = C(a,m)(a-m)`
  have e1 := Nat.choose_mul (n := a) (k := m + 1) (s := 2) (by omega)
  rw [show m + 1 - 2 = m - 1 by omega] at e1
  have e2 := Nat.choose_succ_right_eq a m
  have mono1 : (a - 2).choose (m - 1) ≤ (a - 1).choose (m - 1) := Nat.choose_le_choose _ (by omega)
  have hsub : ((a - m : ℕ) : ℝ) = (a : ℝ) - m := by rw [Nat.cast_sub (by omega)]
  have r2 : ((a.choose (m + 1) : ℝ)) * ((m : ℝ) + 1) = (a.choose m : ℝ) * ((a : ℝ) - m) := by
    rw [← hsub]; exact_mod_cast e2
  have r1 : (a.choose (m + 1) : ℝ) * ((m + 1).choose 2 : ℝ) = (a.choose 2 : ℝ) * ((a - 2).choose (m - 1) : ℝ) := by
    exact_mod_cast e1
  have hc2 : ((m + 1).choose 2 : ℝ) * 2 = ((m : ℝ) + 1) * m := by
    have := choose_two_mul (m + 1); rw [show m + 1 - 1 = m by omega] at this; exact_mod_cast this
  have m1 : ((a - 2).choose (m - 1) : ℝ) ≤ ((a - 1).choose (m - 1) : ℝ) := by exact_mod_cast mono1
  have hC2 : (0 : ℝ) ≤ (a.choose 2 : ℝ) := Nat.cast_nonneg _
  have hm : (3 : ℝ) ≤ m := by exact_mod_cast hm3
  have hCm1 : (0 : ℝ) ≤ (a.choose (m + 1) : ℝ) := Nat.cast_nonneg _
  by_cases h4 : 4 ≤ m
  · rw [if_pos h4]
    have e3 := Nat.choose_mul (n := a) (k := m + 1) (s := 3) (by omega)
    rw [show m + 1 - 3 = m - 2 by omega] at e3
    have mono2 : (a - 3).choose (m - 2) ≤ (a - 1).choose (m - 2) := Nat.choose_le_choose _ (by omega)
    have r3 : (a.choose (m + 1) : ℝ) * ((m + 1).choose 3 : ℝ) = (a.choose 3 : ℝ) * ((a - 3).choose (m - 2) : ℝ) := by
      exact_mod_cast e3
    have m2 : ((a - 3).choose (m - 2) : ℝ) ≤ ((a - 1).choose (m - 2) : ℝ) := by exact_mod_cast mono2
    have hc3 : ((m + 1).choose 3 : ℝ) * 6 = ((m : ℝ) + 1) * m * (m - 1) := by
      have h2 := choose_two_mul m
      have : ((m + 1).choose 3 * 3 : ℕ) = (m + 1) * m.choose 2 := by
        have := Nat.add_one_mul_choose_eq m 2; linarith
      have hr : (((m + 1).choose 3 * 3 : ℕ) : ℝ) = (((m + 1) * m.choose 2 : ℕ) : ℝ) := by rw [this]
      have hr2 : ((m.choose 2 * 2 : ℕ) : ℝ) = ((m * (m - 1) : ℕ) : ℝ) := by rw [h2]
      push_cast at hr hr2
      rw [Nat.cast_sub (by omega)] at hr2; push_cast at hr2
      nlinarith
    have hC3 : (0 : ℝ) ≤ (a.choose 3 : ℝ) := Nat.cast_nonneg _
    rw [Lc, if_neg (by omega)]
    have key : (a.choose (m + 1) : ℝ) * (((m + 1).choose 2 : ℝ) + ((m + 1).choose 3 : ℝ)) =
        (m : ℝ) * (m + 2) / 6 * ((a : ℝ) - m) * (a.choose m : ℝ) := by
      have : ((m + 1).choose 2 : ℝ) + ((m + 1).choose 3 : ℝ) = ((m : ℝ) + 1) * (m * (m + 2) / 6) := by
        nlinarith [hc2, hc3]
      rw [this]; linear_combination ((m : ℝ) * (m + 2) / 6) * r2
    have l1 : (a.choose 2 : ℝ) * ((a - 2).choose (m - 1) : ℝ) ≤ (a.choose 2 : ℝ) * ((a - 1).choose (m - 1) : ℝ) :=
      mul_le_mul_of_nonneg_left m1 hC2
    have l2 : (a.choose 3 : ℝ) * ((a - 3).choose (m - 2) : ℝ) ≤ (a.choose 3 : ℝ) * ((a - 1).choose (m - 2) : ℝ) :=
      mul_le_mul_of_nonneg_left m2 hC3
    nlinarith [key, r1, r3]
  · rw [if_neg h4, add_zero]
    have hm3' : m = 3 := by omega
    subst hm3'
    rw [Lc, if_pos rfl]
    have hc42 : ((3 + 1).choose 2 : ℝ) = 6 := by norm_num [Nat.choose]
    rw [hc42] at r1
    have l1 : (a.choose 2 : ℝ) * ((a - 2).choose (3 - 1) : ℝ) ≤ (a.choose 2 : ℝ) * ((a - 1).choose (3 - 1) : ℝ) :=
      mul_le_mul_of_nonneg_left m1 hC2
    push_cast at r2
    nlinarith [r1, r2, l1]

/-- (10): `Y J ≥ Σ_{3 ≤ m ≤ a-1} L_m (a-m) C(a,m) u_m`. -/
theorem YJ_ge (hu : LCNZ u) (hu1 : u 1 = 1) {a : ℕ} (ha : 3 ≤ a) :
    ∑ m ∈ range (a + 1), (if 3 ≤ m ∧ m + 1 ≤ a then Lc m * ((a : ℝ) - m) * (a.choose m : ℝ) else 0) * u m ≤
      sY u a * sJ u a := by
  have hJ := sJ_nonneg hu a
  have h1 := mul_le_mul_of_nonneg_right (sY_ge hu ha) hJ
  have h2 := u2J_ge hu hu1 a
  have h3 := u3J_ge hu hu1 a
  have hC2 : (0 : ℝ) ≤ (a.choose 2 : ℝ) := Nat.cast_nonneg _
  have hC3 : (0 : ℝ) ≤ (a.choose 3 : ℝ) := Nat.cast_nonneg _
  have step : ∑ m ∈ range (a + 1), (if 3 ≤ m ∧ m + 1 ≤ a then Lc m * ((a : ℝ) - m) * (a.choose m : ℝ) else 0) * u m ≤
      (a.choose 2 : ℝ) * ∑ m ∈ range (a + 1), (if 3 ≤ m then ((a - 1).choose (m - 1) : ℝ) else 0) * u m +
      (a.choose 3 : ℝ) * ∑ m ∈ range (a + 1), (if 4 ≤ m then ((a - 1).choose (m - 2) : ℝ) else 0) * u m := by
    rw [mul_sum, mul_sum, ← sum_add_distrib]
    refine sum_le_sum fun m hm => ?_
    have hum := hu.1 m
    by_cases hc : 3 ≤ m ∧ m + 1 ≤ a
    · rw [if_pos hc, if_pos hc.1]
      have := coeff10 (a := a) hc.1 hc.2
      by_cases h4 : 4 ≤ m
      · rw [if_pos h4] at this ⊢; nlinarith
      · rw [if_neg h4] at this ⊢; nlinarith
    · rw [if_neg hc, zero_mul]
      refine add_nonneg (mul_nonneg hC2 (mul_nonneg (by split_ifs <;> positivity) hum))
        (mul_nonneg hC3 (mul_nonneg (by split_ifs <;> positivity) hum))
  nlinarith [mul_le_mul_of_nonneg_left h2 hC2, mul_le_mul_of_nonneg_left h3 hC3]

/-- (11): `Y Y' ≥ (u_2 + 1) Σ_{m ≥ 3} m(a-1)/2 · C(a,m) u_m`. -/
theorem YYp_ge (hu : LCNZ u) (hu1 : u 1 = 1) {a : ℕ} (ha : 3 ≤ a) :
    (u 2 + 1) * ∑ m ∈ range (a + 1), (if 3 ≤ m then (m : ℝ) * ((a : ℝ) - 1) / 2 * (a.choose m : ℝ) else 0) * u m ≤
      sY u a * sYp u a := by
  have hY : (a.choose 2 : ℝ) * u 2 ≤ sY u a := by
    have := sY_ge hu ha; have : 0 ≤ (a.choose 3 : ℝ) * u 3 := mul_nonneg (Nat.cast_nonneg _) (hu.1 3); linarith
  have hYp := sYp_nonneg hu a
  set G : ℕ → ℝ := fun m => (if 3 ≤ m then ((a - 1).choose (m - 1) : ℝ) else 0) * u m with hG
  have hstep : (u 2 + 1) * ∑ m ∈ range (a + 1), G m ≤ u 2 * sYp u a := by
    rw [← reindex1 G a (by simp [hG]), sYp, mul_sum, mul_sum]
    refine sum_le_sum fun j _ => ?_
    simp only [hG]
    by_cases h : 2 ≤ j
    · rw [if_pos (by omega), if_pos h, show j + 1 - 1 = j by omega]
      have := hu.pair (i := 2) (j := j) (by norm_num) (by omega)
      rw [hu1, one_mul, show 2 + j - 1 = j + 1 by omega] at this
      have hc : (0 : ℝ) ≤ ((a - 1).choose j : ℝ) := Nat.cast_nonneg _
      nlinarith
    · rw [if_neg (by omega), if_neg h]; simp
  have hcoef : ∀ m : ℕ, 3 ≤ m → (m : ℝ) * ((a : ℝ) - 1) / 2 * (a.choose m : ℝ) =
      (a.choose 2 : ℝ) * ((a - 1).choose (m - 1) : ℝ) := by
    intro m hm
    have e := Nat.add_one_mul_choose_eq (a - 1) (m - 1)
    rw [show a - 1 + 1 = a by omega, show m - 1 + 1 = m by omega] at e
    have e' : (a : ℝ) * ((a - 1).choose (m - 1) : ℝ) = (a.choose m : ℝ) * m := by exact_mod_cast e
    have c2 : (a.choose 2 : ℝ) * 2 = (a : ℝ) * ((a : ℝ) - 1) := by
      have := choose_two_mul a
      have h' : ((a.choose 2 * 2 : ℕ) : ℝ) = ((a * (a - 1) : ℕ) : ℝ) := by rw [this]
      push_cast [Nat.cast_sub (show 1 ≤ a by omega)] at h'; linarith
    have ha0 : (0 : ℝ) < a := by exact_mod_cast (show 0 < a by omega)
    field_simp
    nlinarith [e', c2]
  have hsum : ∑ m ∈ range (a + 1), (if 3 ≤ m then (m : ℝ) * ((a : ℝ) - 1) / 2 * (a.choose m : ℝ) else 0) * u m =
      (a.choose 2 : ℝ) * ∑ m ∈ range (a + 1), G m := by
    rw [mul_sum]; refine sum_congr rfl fun m _ => ?_
    simp only [hG]; split_ifs with h
    · rw [hcoef m h]; ring
    · ring
  rw [hsum]
  have hC2 : (0 : ℝ) ≤ (a.choose 2 : ℝ) := Nat.cast_nonneg _
  nlinarith [mul_le_mul_of_nonneg_right hY hYp, mul_le_mul_of_nonneg_left hstep hC2]

/-- `E_m = 2(m² - 5)/(m+1)`. -/
noncomputable def Ec (m : ℕ) : ℝ := 2 * ((m : ℝ) ^ 2 - 5) / ((m : ℝ) + 1)

/-- (15): `(4/q) H_* + 2T ≤ Σ_{m ≥ 2} E_m (a-m) C(a,m) u_m` for `q = u_2 > 0`. -/
theorem HT_le (hu : LCNZ u) (hu1 : u 1 = 1) {a : ℕ} (hq : 0 < u 2) :
    4 / u 2 * sH u a + 2 * sT u a ≤
      ∑ m ∈ range (a + 1), (if 2 ≤ m then Ec m * ((a : ℝ) - m) * (a.choose m : ℝ) else 0) * u m := by
  -- `H_*/q ≤ Σ_{m ≥ 2} (m-1)(a-m)/(m+1) C(a,m) u_m`
  set G : ℕ → ℝ := fun n => (if 3 ≤ n then ((n : ℝ) - 2) * (a.choose n : ℝ) else 0) * u (n - 1) with hG
  have h1 : sH u a / u 2 ≤ ∑ n ∈ range (a + 1), G n := by
    rw [sH, sum_div]
    refine sum_le_sum fun n _ => ?_
    simp only [hG]
    split_ifs with h
    · rw [div_le_iff₀ hq]
      have := hu.pair (i := 2) (j := n - 1) (by norm_num) (by omega)
      rw [hu1, one_mul, show 2 + (n - 1) - 1 = n by omega] at this
      have hc : (0 : ℝ) ≤ ((n : ℝ) - 2) * (a.choose n : ℝ) :=
        mul_nonneg (by linarith [show (3 : ℝ) ≤ n by exact_mod_cast h]) (Nat.cast_nonneg _)
      nlinarith
    · simp
  have h2 : ∑ n ∈ range (a + 1), G n = ∑ m ∈ range (a + 1),
      (if 2 ≤ m then ((m : ℝ) - 1) * ((a : ℝ) - m) / ((m : ℝ) + 1) * (a.choose m : ℝ) else 0) * u m := by
    rw [← reindex1 G a (by simp [hG]), sum_range_succ _ a]
    have hlast : (if 2 ≤ a then ((a : ℝ) - 1) * ((a : ℝ) - a) / ((a : ℝ) + 1) * (a.choose a : ℝ) else 0) * u a = 0 := by
      split_ifs <;> ring
    rw [hlast, add_zero]
    refine sum_congr rfl fun m hm => ?_
    rw [mem_range] at hm
    simp only [hG]
    by_cases h : 2 ≤ m
    · rw [if_pos (by omega), if_pos h, show m + 1 - 1 = m by omega]
      have e := Nat.choose_succ_right_eq a m
      have e' : (a.choose (m + 1) : ℝ) * ((m : ℝ) + 1) = (a.choose m : ℝ) * ((a : ℝ) - m) := by
        have : ((a.choose (m + 1) * (m + 1) : ℕ) : ℝ) = ((a.choose m * (a - m) : ℕ) : ℝ) := by rw [e]
        push_cast [Nat.cast_sub (show m ≤ a by omega)] at this; linarith
      have hm1 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
      push_cast
      field_simp
      linear_combination ((m : ℝ) - 1) * u m * e'
    · rw [if_neg (by omega), if_neg h]; simp
  have h3 : 4 / u 2 * sH u a = 4 * (sH u a / u 2) := by ring
  rw [h3]
  have h4 : 4 * (sH u a / u 2) + 2 * sT u a ≤ 4 * (∑ m ∈ range (a + 1),
      (if 2 ≤ m then ((m : ℝ) - 1) * ((a : ℝ) - m) / ((m : ℝ) + 1) * (a.choose m : ℝ) else 0) * u m) + 2 * sT u a := by
    rw [← h2]; linarith
  refine le_trans h4 (le_of_eq ?_)
  rw [sT, mul_sum, mul_sum, ← sum_add_distrib]
  refine sum_congr rfl fun m _ => ?_
  unfold Ec
  split_ifs with h
  · have hm1 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
    field_simp; ring
  · ring

theorem Lc_facts (m : ℕ) (hm : 3 ≤ m) : 2 * ((m : ℝ) - 3) ≤ Lc m ∧ Ec m ≤ Lc m + (m : ℝ) / 2 := by
  have hm' : (3 : ℝ) ≤ m := by exact_mod_cast hm
  unfold Lc Ec
  by_cases h3 : m = 3
  · subst h3; norm_num
  · rw [if_neg h3]
    have hm4 : (4 : ℝ) ≤ m := by exact_mod_cast (show 4 ≤ m by omega)
    constructor
    · nlinarith [sq_nonneg ((m : ℝ) - 5)]
    · rw [div_le_iff₀ (by positivity)]
      nlinarith [sq_nonneg ((m : ℝ) - 4), mul_nonneg (by linarith : (0 : ℝ) ≤ (m : ℝ) - 4) (sq_nonneg ((m : ℝ) - 4))]

/-- `F(0) ≥ 0`. -/
theorem Fz_zero (hu : LCNZ u) (hu1 : u 1 = 1) {a : ℕ} (ha : 3 ≤ a) : 0 ≤ Fz u a 0 := by
  have hYJ := YJ_ge hu hu1 ha
  have e : Fz u a 0 = sY u a * sJ u a - 2 * sT u a := by unfold Fz; ring
  rw [e]
  suffices h : 0 ≤ ∑ m ∈ range (a + 1), (if 3 ≤ m ∧ m + 1 ≤ a then Lc m * ((a : ℝ) - m) * (a.choose m : ℝ) else 0) * u m -
      2 * sT u a by linarith
  rw [sT, mul_sum, ← sum_sub_distrib]
  refine sum_nonneg fun m hm => ?_
  rw [mem_range] at hm
  have hum := hu.1 m
  have hC : (0 : ℝ) ≤ (a.choose m : ℝ) := Nat.cast_nonneg _
  have hma : (m : ℝ) ≤ a := by exact_mod_cast (show m ≤ a by omega)
  by_cases h2 : 2 ≤ m
  · rw [if_pos h2]
    by_cases hc : 3 ≤ m ∧ m + 1 ≤ a
    · rw [if_pos hc]
      have := (Lc_facts m hc.1).1
      have : 0 ≤ (Lc m - 2 * ((m : ℝ) - 3)) * ((a : ℝ) - m) * (a.choose m : ℝ) * u m :=
        mul_nonneg (mul_nonneg (mul_nonneg (by linarith) (by linarith)) hC) hum
      nlinarith
    · rw [if_neg hc]
      rcases Nat.lt_or_ge m 3 with h | h
      · have : m = 2 := by omega
        subst this
        have : (3 : ℝ) ≤ a := by exact_mod_cast ha
        have : 0 ≤ ((a : ℝ) - 2) * (a.choose 2 : ℝ) * u 2 := mul_nonneg (mul_nonneg (by linarith) hC) hum
        norm_num; nlinarith
      · have : m = a := by omega
        subst this; simp
  · rw [if_neg h2, if_neg (by omega)]; simp

/-- `F(1/q) ≥ 0`. -/
theorem Fz_top (hu : LCNZ u) (hu1 : u 1 = 1) {a : ℕ} (ha : 3 ≤ a) (hq : 0 < u 2) : 0 ≤ Fz u a (1 / u 2) := by
  have hYJ := YJ_ge hu hu1 ha
  have hYY := YYp_ge hu hu1 ha
  have hHT := HT_le hu hu1 (a := a) hq
  set q := u 2
  have e : Fz u a (1 / q) = (1 / q + 1) * (sY u a * sYp u a / (q + 1) + sY u a * sJ u a - (4 / q * sH u a + 2 * sT u a)) := by
    unfold Fz; field_simp; ring
  rw [e]
  refine mul_nonneg (by positivity) ?_
  have hYY' : ∑ m ∈ range (a + 1), (if 3 ≤ m then (m : ℝ) * ((a : ℝ) - 1) / 2 * (a.choose m : ℝ) else 0) * u m ≤
      sY u a * sYp u a / (q + 1) := by
    rw [le_div_iff₀ (by positivity)]; linarith
  suffices h : 0 ≤ ∑ m ∈ range (a + 1), (if 3 ≤ m then (m : ℝ) * ((a : ℝ) - 1) / 2 * (a.choose m : ℝ) else 0) * u m +
      ∑ m ∈ range (a + 1), (if 3 ≤ m ∧ m + 1 ≤ a then Lc m * ((a : ℝ) - m) * (a.choose m : ℝ) else 0) * u m -
      ∑ m ∈ range (a + 1), (if 2 ≤ m then Ec m * ((a : ℝ) - m) * (a.choose m : ℝ) else 0) * u m by linarith
  rw [← sum_add_distrib, ← sum_sub_distrib]
  refine sum_nonneg fun m hm => ?_
  rw [mem_range] at hm
  have hum := hu.1 m
  have hC : (0 : ℝ) ≤ (a.choose m : ℝ) := Nat.cast_nonneg _
  have hma : (m : ℝ) ≤ a := by exact_mod_cast (show m ≤ a by omega)
  by_cases h3 : 3 ≤ m
  · rw [if_pos h3, if_pos (show 2 ≤ m by omega)]
    have hf := Lc_facts m h3
    have hm3 : (3 : ℝ) ≤ m := by exact_mod_cast h3
    by_cases hc : m + 1 ≤ a
    · rw [if_pos ⟨h3, hc⟩]
      have : 0 ≤ ((m : ℝ) * ((a : ℝ) - 1) / 2 - (m : ℝ) * ((a : ℝ) - m) / 2) * (a.choose m : ℝ) * u m :=
        mul_nonneg (mul_nonneg (by nlinarith) hC) hum
      have : 0 ≤ (Lc m + (m : ℝ) / 2 - Ec m) * ((a : ℝ) - m) * (a.choose m : ℝ) * u m :=
        mul_nonneg (mul_nonneg (mul_nonneg (by linarith) (by linarith)) hC) hum
      nlinarith
    · rw [if_neg (fun h => hc h.2)]
      have : m = a := by omega
      subst this
      have : 0 ≤ (m : ℝ) * ((m : ℝ) - 1) / 2 * (m.choose m : ℝ) * u m := by
        have : (0 : ℝ) ≤ (m : ℝ) - 1 := by linarith
        positivity
      simp only [sub_self, mul_zero, zero_mul, add_zero, sub_zero]; linarith
  · rw [if_neg h3, if_neg (fun h => h3 h.1)]
    by_cases h2 : 2 ≤ m
    · rw [if_pos h2]
      have : m = 2 := by omega
      subst this
      unfold Ec
      have : (2 : ℝ) ≤ a := by exact_mod_cast (show 2 ≤ a by omega)
      have : 0 ≤ ((a : ℝ) - 2) * (a.choose 2 : ℝ) * u 2 := mul_nonneg (mul_nonneg (by linarith) hC) hum
      norm_num; nlinarith
    · rw [if_neg h2]; simp

theorem Fz_interp (u : ℕ → ℝ) (a : ℕ) {q : ℝ} (hq : q ≠ 0) (z : ℝ) :
    Fz u a z = (1 - q * z) * Fz u a 0 + q * z * Fz u a (1 / q) + 4 * sH u a * z * (1 / q - z) := by
  unfold Fz; field_simp; ring

theorem LCNZ.zero_from (hu : LCNZ u) (h1 : 0 < u 1) (h2 : u 2 = 0) {n : ℕ} (hn : 2 ≤ n) : u n = 0 := by
  by_contra h
  have hpos : 0 < u n := lt_of_le_of_ne (hu.1 n) (Ne.symm h)
  have := hu.2.2 1 2 n (by norm_num) hn h1 hpos
  rw [h2] at this; exact lt_irrefl 0 this

/-- `F(z) ≥ 0` on `[0, 1/q]`. -/
theorem Fz_nonneg (hu : LCNZ u) (hu1 : u 1 = 1) {a : ℕ} (ha : 3 ≤ a) {z : ℝ} (hz : 0 ≤ z) (hzq : z * u 2 ≤ 1) :
    0 ≤ Fz u a z := by
  rcases eq_or_lt_of_le (hu.1 2) with h2 | h2
  · -- `u 2 = 0`: all sums vanish
    have hz2 : ∀ n, 2 ≤ n → u n = 0 := fun n hn => hu.zero_from (by rw [hu1]; norm_num) h2.symm hn
    have hY : sY u a = 0 := sum_eq_zero fun n _ => by
      by_cases h : 2 ≤ n
      · rw [hz2 n h, mul_zero]
      · rw [if_neg h, zero_mul]
    have hJ : sJ u a = 0 := sum_eq_zero fun n _ => by
      by_cases h : 2 ≤ n
      · rw [hz2 n h, mul_zero]
      · rw [if_neg h, zero_mul]
    have hH : sH u a = 0 := sum_eq_zero fun n _ => by
      split_ifs with h
      · rw [hz2 n (by omega), mul_zero]
      · simp
    have hT : sT u a = 0 := sum_eq_zero fun n _ => by
      by_cases h : 2 ≤ n
      · rw [hz2 n h, mul_zero]
      · rw [if_neg h, zero_mul]
    unfold Fz; rw [hY, hJ, hH, hT]; simp
  · rw [Fz_interp u a h2.ne' z]
    have hf0 := Fz_zero hu hu1 ha
    have hf1 := Fz_top hu hu1 ha h2
    have hH := sH_nonneg hu a
    have hz1 : z ≤ 1 / u 2 := by rw [le_div_iff₀ h2]; linarith
    have a1 : 0 ≤ 1 - u 2 * z := by linarith [mul_comm z (u 2)]
    have a2 : 0 ≤ u 2 * z := mul_nonneg h2.le hz
    have a3 : 0 ≤ 4 * sH u a * z * (1 / u 2 - z) := mul_nonneg (mul_nonneg (by linarith) hz) (by linarith)
    nlinarith [mul_nonneg a1 hf0, mul_nonneg a2 hf1]

end Ends

end Szkraw
