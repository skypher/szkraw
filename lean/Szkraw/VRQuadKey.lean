import Szkraw.VRAffineKey2

/-!
# Theorem 8.11: the key inequality with the `W₁` term (paper, eq. `quad-key`)

The interpolation of the proof of Theorem 8.9 keeps a surplus: `F(z) ≥ (2/3)(z+1)(a-2) C(a,2) u₂`.
With `s = Δρ(ℓ+a-1)` in place of `t`, the reduced inequality
`A Y' + Y A'' ≥ D(4α H_* + 2 s T + 4τ Z - τ W_*)` follows for `α u₁ ≥ s u₀` and `s ≥ τ(a-1)`.
-/

set_option linter.unusedSectionVars false

namespace Szkraw

open Finset

section Surplus

variable {u : ℕ → ℝ}

/-- `F(0) ≥ 2(a-2) C(a,2) u₂`. -/
theorem Fz_zero_sur (hu : LCNZ u) (hu1 : u 1 = 1) {a : ℕ} (ha : 3 ≤ a) :
    2 * ((a : ℝ) - 2) * (a.choose 2 : ℝ) * u 2 ≤ Fz u a 0 := by
  have hYJ := YJ_ge hu hu1 ha
  have e : Fz u a 0 = sY u a * sJ u a - 2 * sT u a := by unfold Fz; ring
  rw [e]
  set g : ℕ → ℝ := fun m => (if 3 ≤ m ∧ m + 1 ≤ a then Lc m * ((a : ℝ) - m) * (a.choose m : ℝ) else 0) * u m -
    2 * ((if 2 ≤ m then ((m : ℝ) - 3) * ((a : ℝ) - m) * (a.choose m : ℝ) else 0) * u m) with hg
  have hsum : ∑ m ∈ range (a + 1), (if 3 ≤ m ∧ m + 1 ≤ a then Lc m * ((a : ℝ) - m) * (a.choose m : ℝ) else 0) * u m -
      2 * sT u a = ∑ m ∈ range (a + 1), g m := by
    rw [sT, mul_sum, ← sum_sub_distrib]
  have hnn : ∀ m ∈ range (a + 1), 0 ≤ g m := by
    intro m hm
    rw [mem_range] at hm
    simp only [hg]
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
  have h2 := single_le_sum hnn (mem_range.mpr (show 2 < a + 1 by omega))
  have hg2 : g 2 = 2 * ((a : ℝ) - 2) * (a.choose 2 : ℝ) * u 2 := by
    simp only [hg, show ¬ (3 ≤ 2 ∧ 2 + 1 ≤ a) by omega, if_false, show (2 : ℕ) ≤ 2 from le_rfl, if_true]
    push_cast; ring
  linarith

/-- `F(1/q) ≥ (2/3)(1/q + 1)(a-2) C(a,2) u₂`. -/
theorem Fz_top_sur (hu : LCNZ u) (hu1 : u 1 = 1) {a : ℕ} (ha : 3 ≤ a) (hq : 0 < u 2) :
    2 / 3 * ((a : ℝ) - 2) * (a.choose 2 : ℝ) * u 2 * (1 / u 2 + 1) ≤ Fz u a (1 / u 2) := by
  have hYJ := YJ_ge hu hu1 ha
  have hYY := YYp_ge hu hu1 ha
  have hHT := HT_le hu hu1 (a := a) hq
  set q := u 2
  have e : Fz u a (1 / q) = (1 / q + 1) * (sY u a * sYp u a / (q + 1) + sY u a * sJ u a - (4 / q * sH u a + 2 * sT u a)) := by
    unfold Fz; field_simp; ring
  rw [e, mul_comm (2 / 3 * ((a : ℝ) - 2) * (a.choose 2 : ℝ) * q)]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have hYY' : ∑ m ∈ range (a + 1), (if 3 ≤ m then (m : ℝ) * ((a : ℝ) - 1) / 2 * (a.choose m : ℝ) else 0) * u m ≤
      sY u a * sYp u a / (q + 1) := by
    rw [le_div_iff₀ (by positivity)]; linarith
  set g : ℕ → ℝ := fun m => (if 3 ≤ m then (m : ℝ) * ((a : ℝ) - 1) / 2 * (a.choose m : ℝ) else 0) * u m +
      (if 3 ≤ m ∧ m + 1 ≤ a then Lc m * ((a : ℝ) - m) * (a.choose m : ℝ) else 0) * u m -
      (if 2 ≤ m then Ec m * ((a : ℝ) - m) * (a.choose m : ℝ) else 0) * u m with hg
  suffices h : 2 / 3 * ((a : ℝ) - 2) * (a.choose 2 : ℝ) * q ≤ ∑ m ∈ range (a + 1), g m by
    have hs : ∑ m ∈ range (a + 1), g m =
        ∑ m ∈ range (a + 1), (if 3 ≤ m then (m : ℝ) * ((a : ℝ) - 1) / 2 * (a.choose m : ℝ) else 0) * u m +
        ∑ m ∈ range (a + 1), (if 3 ≤ m ∧ m + 1 ≤ a then Lc m * ((a : ℝ) - m) * (a.choose m : ℝ) else 0) * u m -
        ∑ m ∈ range (a + 1), (if 2 ≤ m then Ec m * ((a : ℝ) - m) * (a.choose m : ℝ) else 0) * u m := by
      simp only [hg]; rw [← sum_add_distrib, ← sum_sub_distrib]
    linarith
  have hnn : ∀ m ∈ range (a + 1), 0 ≤ g m := by
    intro m hm
    rw [mem_range] at hm
    simp only [hg]
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
  have h2 := single_le_sum hnn (mem_range.mpr (show 2 < a + 1 by omega))
  have hg2 : g 2 = 2 / 3 * ((a : ℝ) - 2) * (a.choose 2 : ℝ) * q := by
    simp only [hg, show ¬ (3 ≤ 2) by omega, if_false, show (2 : ℕ) ≤ 2 from le_rfl, if_true, Ec, false_and]
    push_cast; ring
  linarith

/-- `F(z) ≥ (2/3)(z+1)(a-2) C(a,2) u₂` on `[0, 1/q]`. -/
theorem Fz_sur (hu : LCNZ u) (hu1 : u 1 = 1) {a : ℕ} (ha : 3 ≤ a) {z : ℝ} (hz : 0 ≤ z) (hzq : z * u 2 ≤ 1) :
    2 / 3 * ((a : ℝ) - 2) * (a.choose 2 : ℝ) * u 2 * (z + 1) ≤ Fz u a z := by
  rcases eq_or_lt_of_le (hu.1 2) with h2 | h2
  · rw [← h2, mul_zero, zero_mul]; exact Fz_nonneg hu hu1 ha hz hzq
  · set g : ℝ → ℝ := fun x => 2 / 3 * ((a : ℝ) - 2) * (a.choose 2 : ℝ) * u 2 * (x + 1) with hgdef
    have hlin : g z = (1 - u 2 * z) * g 0 + u 2 * z * g (1 / u 2) := by
      simp only [hgdef]; field_simp; ring
    rw [show 2 / 3 * ((a : ℝ) - 2) * (a.choose 2 : ℝ) * u 2 * (z + 1) = g z from rfl, hlin,
      Fz_interp u a h2.ne' z]
    have hf0 := Fz_zero_sur hu hu1 ha
    have hf1 := Fz_top_sur hu hu1 ha h2
    have hH := sH_nonneg hu a
    have hz1 : z ≤ 1 / u 2 := by rw [le_div_iff₀ h2]; linarith
    have a1 : 0 ≤ 1 - u 2 * z := by linarith [mul_comm z (u 2)]
    have a2 : 0 ≤ u 2 * z := mul_nonneg h2.le hz
    have a3 : 0 ≤ 4 * sH u a * z * (1 / u 2 - z) := mul_nonneg (mul_nonneg (by linarith) hz) (by linarith)
    have g0 : g 0 = 2 / 3 * ((a : ℝ) - 2) * (a.choose 2 : ℝ) * u 2 * (0 + 1) := rfl
    have g1 : g (1 / u 2) = 2 / 3 * ((a : ℝ) - 2) * (a.choose 2 : ℝ) * u 2 * (1 / u 2 + 1) := rfl
    have ha2 : (0 : ℝ) ≤ (a : ℝ) - 2 := by
      have : (3 : ℝ) ≤ a := by exact_mod_cast ha
      linarith
    have hpos : 0 ≤ 2 / 3 * ((a : ℝ) - 2) * (a.choose 2 : ℝ) * u 2 :=
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) ha2) (Nat.cast_nonneg _)) h2.le
    have b0 : g 0 ≤ Fz u a 0 := by rw [g0]; linarith
    have b1 : g (1 / u 2) ≤ Fz u a (1 / u 2) := by rw [g1]; exact hf1
    have c0 := mul_le_mul_of_nonneg_left b0 a1
    have c1 := mul_le_mul_of_nonneg_left b1 a2
    linarith

/-- Unnormalized: `G ≥ (2/3)(a-2) C(a,2) u₁ u₂ (u₀ + u₁)`. -/
theorem G_sur (hu : LCNZ u) (hu1 : 0 < u 1) {a : ℕ} (ha : 3 ≤ a) :
    2 / 3 * ((a : ℝ) - 2) * (a.choose 2 : ℝ) * u 1 * u 2 * (u 0 + u 1) ≤
      u 0 * sY u a * sYp u a + (u 0 + u 1) * sY u a * sJ u a -
        (u 0 + u 1) * (4 * u 0 * sH u a + 2 * u 1 * sT u a) := by
  set v : ℕ → ℝ := fun n => u n / u 1 with hv
  have hvl : LCNZ v := hu.scale hu1
  have hv1 : v 1 = 1 := by simp [hv, hu1.ne']
  have hz : 0 ≤ u 0 / u 1 := div_nonneg (hu.1 0) hu1.le
  have hzq : u 0 / u 1 * v 2 ≤ 1 := by
    simp only [hv]
    rw [div_mul_div_comm, div_le_one (by positivity)]
    have := hu.2.1 0; simpa [sq] using this
  have hF := Fz_sur hvl hv1 ha hz hzq
  have e : u 0 * sY u a * sYp u a + (u 0 + u 1) * sY u a * sJ u a - (u 0 + u 1) * (4 * u 0 * sH u a + 2 * u 1 * sT u a) =
      u 1 ^ 3 * Fz v a (u 0 / u 1) := by
    unfold Fz
    rw [sY_div, sJ_div, sYp_div, sH_div, sT_div]
    field_simp
  rw [e]
  have h3 : 0 < u 1 ^ 3 := by positivity
  have key := mul_le_mul_of_nonneg_left hF h3.le
  have e2 : u 1 ^ 3 * (2 / 3 * ((a : ℝ) - 2) * (a.choose 2 : ℝ) * v 2 * (u 0 / u 1 + 1)) =
      2 / 3 * ((a : ℝ) - 2) * (a.choose 2 : ℝ) * u 1 * u 2 * (u 0 + u 1) := by
    simp only [hv]; field_simp
  linarith

end Surplus

section GammaOf

/-- Products `u₁ Y'`. -/
theorem gamma1_of {ν : ℕ → ℝ} (hν : LCNZ ν) (ℓ a : ℕ) (ha : 1 ≤ a) :
    dd ν (ℓ + 1) * ∑ n ∈ range (a + 1), (if 3 ≤ n then (n : ℝ) * (a.choose n : ℝ) else 0) *
        Szkraw.iterShift ν ℓ n ≤
      a * Szkraw.iterShift ν ℓ 1 * Wt ν 2 0 (ℓ + 1) (a - 1) := by
  set D := dd ν (ℓ + 1)
  set G : ℕ → ℝ := fun n => (if 3 ≤ n then (n : ℝ) * (a.choose n : ℝ) else 0) * (D * Szkraw.iterShift ν ℓ n)
    with hG
  calc D * ∑ n ∈ range (a + 1), (if 3 ≤ n then (n : ℝ) * (a.choose n : ℝ) else 0) * Szkraw.iterShift ν ℓ n
      = ∑ n ∈ range (a + 1), G n := by rw [mul_sum]; exact sum_congr rfl fun n _ => by simp only [hG]; ring
    _ = ∑ j ∈ range a, G (j + 1) := (reindex1 G a (by simp [hG])).symm
    _ ≤ ∑ j ∈ range a, (if 2 ≤ j then (a : ℝ) * ((a - 1).choose j : ℝ) else 0) *
          (Szkraw.iterShift ν ℓ 1 * Szkraw.iterShift ν (ℓ + 1) j) := by
        refine sum_le_sum fun j hj => ?_
        rw [mem_range] at hj
        simp only [hG]
        by_cases h2 : 2 ≤ j
        · rw [if_pos (by omega), if_pos h2]
          have hc := Nat.add_one_mul_choose_eq (a - 1) j
          rw [show a - 1 + 1 = a by omega] at hc
          have hc' : ((j + 1 : ℕ) : ℝ) * (a.choose (j + 1) : ℝ) = (a : ℝ) * ((a - 1).choose j : ℝ) := by
            have : ((a * (a - 1).choose j : ℕ) : ℝ) = ((a.choose (j + 1) * (j + 1) : ℕ) : ℝ) := by rw [hc]
            push_cast at this ⊢; linarith
          rw [hc']
          have key := lemma_8_3 hν ℓ (i := 1) (l := j) le_rfl (by omega)
          rw [add_comm 1 j] at key
          exact mul_le_mul_of_nonneg_left key (by positivity)
        · rw [if_neg (by omega), if_neg h2]; simp
    _ = a * Szkraw.iterShift ν ℓ 1 * Wt ν 2 0 (ℓ + 1) (a - 1) := by
        unfold Wt
        rw [show a - 1 + 1 = a by omega, mul_sum]
        refine sum_congr rfl fun j _ => ?_
        by_cases h2 : 2 ≤ j
        · rw [if_pos h2, if_pos h2]; simp; ring
        · rw [if_neg h2, if_neg h2]; ring

/-- Products `Y f₁(ℓ+1)`. -/
theorem gamma3_of {ν : ℕ → ℝ} (hν : LCNZ ν) (ℓ a : ℕ) (ha : 3 ≤ a) :
    dd ν (ℓ + 1) * ∑ n ∈ range (a + 1), (if 3 ≤ n then (n : ℝ) * (a.choose n : ℝ) else 0) *
        Szkraw.iterShift ν ℓ n ≤
      ((a : ℝ) - 2) * Wt ν 2 0 ℓ a * Szkraw.iterShift ν (ℓ + 1) 1 := by
  set D := dd ν (ℓ + 1)
  have hD : 0 ≤ D := iterShift_nonneg hν (ℓ + 1) 0
  set G : ℕ → ℝ := fun n => (if 3 ≤ n then ((a : ℝ) - 2) * (a.choose (n - 1) : ℝ) else 0) *
    (D * Szkraw.iterShift ν ℓ n) with hG
  calc D * ∑ n ∈ range (a + 1), (if 3 ≤ n then (n : ℝ) * (a.choose n : ℝ) else 0) * Szkraw.iterShift ν ℓ n
      ≤ ∑ n ∈ range (a + 1), G n := by
        rw [mul_sum]
        refine sum_le_sum fun n hn => ?_
        simp only [hG]
        by_cases h3 : 3 ≤ n
        · rw [if_pos h3, if_pos h3]
          have hc := Nat.choose_succ_right_eq a (n - 1)
          rw [show n - 1 + 1 = n by omega] at hc
          have hle : a - (n - 1) ≤ a - 2 := by omega
          have hc' : (n : ℝ) * (a.choose n : ℝ) ≤ ((a : ℝ) - 2) * (a.choose (n - 1) : ℝ) := by
            have h1 : (a.choose n * n : ℕ) ≤ a.choose (n - 1) * (a - 2) := by
              rw [hc]; exact Nat.mul_le_mul_left _ hle
            have h2 : ((a.choose n * n : ℕ) : ℝ) ≤ ((a.choose (n - 1) * (a - 2) : ℕ) : ℝ) := by exact_mod_cast h1
            rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_sub (by omega)] at h2
            push_cast at h2; linarith
          have hu := iterShift_nonneg hν ℓ n
          calc D * ((n : ℝ) * (a.choose n : ℝ) * Szkraw.iterShift ν ℓ n)
              = ((n : ℝ) * (a.choose n : ℝ)) * (D * Szkraw.iterShift ν ℓ n) := by ring
            _ ≤ (((a : ℝ) - 2) * (a.choose (n - 1) : ℝ)) * (D * Szkraw.iterShift ν ℓ n) :=
                mul_le_mul_of_nonneg_right hc' (mul_nonneg hD hu)
        · rw [if_neg h3, if_neg h3]; simp
    _ = ∑ i ∈ range a, G (i + 1) := (reindex1 G a (by simp [hG])).symm
    _ ≤ ∑ i ∈ range (a + 1), (if 2 ≤ i then ((a : ℝ) - 2) * (a.choose i : ℝ) else 0) *
          (Szkraw.iterShift ν ℓ i * Szkraw.iterShift ν (ℓ + 1) 1) := by
        rw [sum_range_succ _ a]
        have hlast : 0 ≤ (if 2 ≤ a then ((a : ℝ) - 2) * (a.choose a : ℝ) else 0) *
            (Szkraw.iterShift ν ℓ a * Szkraw.iterShift ν (ℓ + 1) 1) := by
          rw [if_pos (by omega)]
          have : (2 : ℝ) ≤ a := by exact_mod_cast (show 2 ≤ a by omega)
          exact mul_nonneg (mul_nonneg (by linarith) (Nat.cast_nonneg _))
            (mul_nonneg (iterShift_nonneg hν _ _) (iterShift_nonneg hν _ _))
        refine le_add_of_le_of_nonneg (sum_le_sum fun i hi => ?_) hlast
        simp only [hG]
        by_cases h2 : 2 ≤ i
        · rw [if_pos (by omega), if_pos h2, show i + 1 - 1 = i by omega]
          have key := lemma_8_3 hν ℓ (i := i) (l := 1) (by omega) le_rfl
          have : (2 : ℝ) ≤ a := by exact_mod_cast (show 2 ≤ a by omega)
          exact mul_le_mul_of_nonneg_left key (mul_nonneg (by linarith) (Nat.cast_nonneg _))
        · rw [if_neg (by omega), if_neg h2]; simp
    _ = ((a : ℝ) - 2) * Wt ν 2 0 ℓ a * Szkraw.iterShift ν (ℓ + 1) 1 := by
        unfold Wt
        rw [mul_sum, sum_mul]
        refine sum_congr rfl fun i _ => ?_
        by_cases h2 : 2 ≤ i
        · rw [if_pos h2, if_pos h2]; simp; ring
        · rw [if_neg h2, if_neg h2]; ring

/-- Products `u₂ X''` with `X'' = W_{2,0}(ℓ+1,a-2)`. -/
theorem gamma4_of {ν : ℕ → ℝ} (hν : LCNZ ν) (ℓ a : ℕ) (ha : 2 ≤ a) :
    dd ν (ℓ + 1) * ∑ n ∈ range (a + 1), (if 4 ≤ n then (n.choose 2 : ℝ) * (a.choose n : ℝ) else 0) *
        Szkraw.iterShift ν ℓ n ≤
      Wt ν 2 0 ℓ a * Wt ν 2 0 (ℓ + 1) (a - 2) := by
  set D := dd ν (ℓ + 1)
  have hD : 0 ≤ D := iterShift_nonneg hν (ℓ + 1) 0
  have hY : (a.choose 2 : ℝ) * Szkraw.iterShift ν ℓ 2 ≤ Wt ν 2 0 ℓ a := by
    have := Wt_ge_term hν 2 0 ℓ a 2 le_rfl ha
    simpa using this
  have hX'' : 0 ≤ Wt ν 2 0 (ℓ + 1) (a - 2) := Wt_nonneg hν _ _ _ _
  set G : ℕ → ℝ := fun n => (if 4 ≤ n then (a.choose 2 : ℝ) * ((a - 2).choose (n - 2) : ℝ) else 0) *
    (D * Szkraw.iterShift ν ℓ n) with hG
  calc D * ∑ n ∈ range (a + 1), (if 4 ≤ n then (n.choose 2 : ℝ) * (a.choose n : ℝ) else 0) * Szkraw.iterShift ν ℓ n
      = ∑ n ∈ range (a + 1), G n := by
        rw [mul_sum]
        refine sum_congr rfl fun n hn => ?_
        simp only [hG]
        by_cases h4 : 4 ≤ n
        · rw [if_pos h4, if_pos h4]
          have hc := Nat.choose_mul (n := a) (k := n) (s := 2) (by omega)
          have hc' : (n.choose 2 : ℝ) * (a.choose n : ℝ) = (a.choose 2 : ℝ) * ((a - 2).choose (n - 2) : ℝ) := by
            have : ((a.choose n * n.choose 2 : ℕ) : ℝ) = ((a.choose 2 * (a - 2).choose (n - 2) : ℕ) : ℝ) := by
              rw [hc]
            push_cast at this; linarith
          rw [← hc']; ring
        · rw [if_neg h4, if_neg h4]; ring
    _ = ∑ j ∈ range (a - 1), G (j + 2) := by
        rw [reindex2 G (a - 1) (by simp [hG]) (by simp [hG]), show a - 1 + 2 = a + 1 by omega]
    _ ≤ ∑ j ∈ range (a - 1), (if 2 ≤ j then (a.choose 2 : ℝ) * ((a - 2).choose j : ℝ) else 0) *
          (Szkraw.iterShift ν ℓ 2 * Szkraw.iterShift ν (ℓ + 1) j) := by
        refine sum_le_sum fun j hj => ?_
        simp only [hG]
        by_cases h2 : 2 ≤ j
        · rw [if_pos (by omega), if_pos h2, show j + 2 - 2 = j by omega]
          have key := lemma_8_3 hν ℓ (i := 2) (l := j) (by norm_num) (by omega)
          rw [add_comm 2 j] at key
          exact mul_le_mul_of_nonneg_left key (by positivity)
        · rw [if_neg (by omega), if_neg h2]; simp
    _ = (a.choose 2 : ℝ) * Szkraw.iterShift ν ℓ 2 * Wt ν 2 0 (ℓ + 1) (a - 2) := by
        unfold Wt
        rw [show a - 2 + 1 = a - 1 by omega, mul_sum]
        refine sum_congr rfl fun j _ => ?_
        by_cases h2 : 2 ≤ j
        · rw [if_pos h2, if_pos h2]; simp; ring
        · rw [if_neg h2, if_neg h2]; ring
    _ ≤ Wt ν 2 0 ℓ a * Wt ν 2 0 (ℓ + 1) (a - 2) := mul_le_mul_of_nonneg_right hY hX''

/-- `XY' + YX' ≥ D Γ`. -/
theorem gamma_bound_of {ν : ℕ → ℝ} (hν : LCNZ ν) (ℓ a : ℕ) (ha : 3 ≤ a) :
    dd ν (ℓ + 1) * gammaSum ν ℓ a ≤
      Wt ν 1 0 ℓ a * Wt ν 2 0 (ℓ + 1) (a - 1) + Wt ν 2 0 ℓ a * Wt ν 1 0 (ℓ + 1) (a - 2) := by
  have g1 := gamma1_of hν ℓ a (by omega)
  have g3 := gamma3_of hν ℓ a ha
  have g4 := gamma4_of hν ℓ a (by omega)
  have hsplit : gammaSum ν ℓ a =
      2 * ∑ n ∈ range (a + 1), (if 3 ≤ n then (n : ℝ) * (a.choose n : ℝ) else 0) * Szkraw.iterShift ν ℓ n +
      ∑ n ∈ range (a + 1), (if 4 ≤ n then (n.choose 2 : ℝ) * (a.choose n : ℝ) else 0) * Szkraw.iterShift ν ℓ n := by
    unfold gammaSum
    rw [mul_sum, ← sum_add_distrib]
    exact sum_congr rfl fun n _ => by ring
  rw [Wt_one_split ν ℓ a, Wt_one_split ν (ℓ + 1) (a - 2), Nat.cast_sub (by omega : 2 ≤ a)]
  have hYY : 0 ≤ Wt ν 2 0 ℓ a * Wt ν 2 0 (ℓ + 1) (a - 1) :=
    mul_nonneg (Wt_nonneg hν _ _ _ _) (Wt_nonneg hν _ _ _ _)
  rw [hsplit]
  push_cast
  nlinarith [g1, g3, g4, hYY]


end GammaOf

/-- `Z = Σ_{n ≥ 2} C(a-n,2) C(a,n) u_n`. -/
noncomputable def sZ (u : ℕ → ℝ) (a : ℕ) : ℝ :=
  ∑ n ∈ range (a + 1), (if 2 ≤ n then ((a - n).choose 2 : ℝ) * (a.choose n : ℝ) else 0) * u n

/-- `W_* = Σ_n n C(a-n,2) C(a,n) u_n`, so that `W₁ = τ W_*`. -/
noncomputable def sWs (u : ℕ → ℝ) (a : ℕ) : ℝ :=
  ∑ n ∈ range (a + 1), ((n : ℝ) * ((a - n).choose 2 : ℝ) * (a.choose n : ℝ)) * u n

theorem choose2_real (n : ℕ) : (n.choose 2 : ℝ) = (n : ℝ) * ((n : ℝ) - 1) / 2 := by
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; simp
  · have := choose_two_mul n
    have h' : ((n.choose 2 * 2 : ℕ) : ℝ) = ((n * (n - 1) : ℕ) : ℝ) := by rw [this]
    push_cast [Nat.cast_sub (show 1 ≤ n by omega)] at h'; linarith

/-- The `τ`-part of the key inequality is nonnegative termwise. -/
theorem tau_part_nonneg {u : ℕ → ℝ} (hu : ∀ n, 0 ≤ u n) {a : ℕ} (ha : 3 ≤ a) :
    0 ≤ ((a - 1).choose 2 : ℝ) * sY u a - 4 * sZ u a + sWs u a +
      2 / 3 * ((a : ℝ) - 1) * ((a : ℝ) - 2) * (a.choose 2 : ℝ) * u 2 := by
  have hu2 : 2 / 3 * ((a : ℝ) - 1) * ((a : ℝ) - 2) * (a.choose 2 : ℝ) * u 2 =
      ∑ n ∈ range (a + 1), (if n = 2 then 2 / 3 * ((a : ℝ) - 1) * ((a : ℝ) - 2) * (a.choose 2 : ℝ) * u n else 0) := by
    rw [sum_ite_eq', if_pos (mem_range.mpr (by omega))]
  rw [hu2, sY, sZ, sWs, mul_sum, mul_sum, ← sum_sub_distrib, ← sum_add_distrib, ← sum_add_distrib]
  refine sum_nonneg fun n hn => ?_
  rw [mem_range] at hn
  have hun := hu n
  have hC : (0 : ℝ) ≤ (a.choose n : ℝ) := Nat.cast_nonneg _
  have ha3 : (3 : ℝ) ≤ a := by exact_mod_cast ha
  rcases Nat.lt_or_ge n 2 with h | h
  · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    simp only [mul_zero, zero_mul, sub_zero, zero_add, add_zero]
    exact mul_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) hC) hun
  rcases Nat.eq_or_lt_of_le h with e | h3
  · subst e
    rw [if_pos le_rfl, if_pos le_rfl, if_pos rfl, choose2_real (a - 1), choose2_real (a - 2),
      Nat.cast_sub (show 1 ≤ a by omega), Nat.cast_sub (show 2 ≤ a by omega)]
    have : 0 ≤ ((a : ℝ) - 2) * ((a : ℝ) + 11) / 6 * (a.choose 2 : ℝ) * u 2 :=
      mul_nonneg (mul_nonneg (div_nonneg (mul_nonneg (by linarith) (by linarith)) (by norm_num)) hC) hun
    push_cast
    nlinarith [this]
  · rw [if_pos (by omega), if_pos (by omega), if_neg (by omega)]
    have hm : (3 : ℝ) ≤ n := by exact_mod_cast h3
    rcases Nat.eq_or_lt_of_le h3 with e | h4
    · subst e
      have hmono : ((a - 3).choose 2 : ℝ) ≤ ((a - 1).choose 2 : ℝ) := by
        exact_mod_cast Nat.choose_le_choose 2 (show a - 3 ≤ a - 1 by omega)
      have : 0 ≤ (((a - 1).choose 2 : ℝ) - ((a - 3).choose 2 : ℝ)) * (a.choose 3 : ℝ) * u 3 :=
        mul_nonneg (mul_nonneg (by linarith) hC) hun
      push_cast
      nlinarith [this]
    · have hm4 : (4 : ℝ) ≤ n := by exact_mod_cast h4
      have hc1 : (0 : ℝ) ≤ ((a - 1).choose 2 : ℝ) := Nat.cast_nonneg _
      have hc2 : (0 : ℝ) ≤ ((a - n).choose 2 : ℝ) := Nat.cast_nonneg _
      have : 0 ≤ (((a - 1).choose 2 : ℝ) + ((n : ℝ) - 4) * ((a - n).choose 2 : ℝ)) * (a.choose n : ℝ) * u n :=
        mul_nonneg (mul_nonneg (add_nonneg hc1 (mul_nonneg (by linarith) hc2)) hC) hun
      nlinarith [this]

/-- **The reduced key inequality for quadratic ratios**: for `α u₁ ≥ s u₀`, `s ≥ τ(a-1)`. -/
theorem quad_key_red {ν : ℕ → ℝ} (hν : LCNZ ν) (hν1 : 0 < ν 1) (ℓ a : ℕ) (ha : 3 ≤ a) {α s τ : ℝ}
    (hs : 0 ≤ s) (hτ : 0 ≤ τ) (hα : s * dd ν ℓ ≤ α * Szkraw.iterShift ν ℓ 1)
    (hsτ : τ * ((a : ℝ) - 1) ≤ s) :
    0 ≤ (α * Wt ν 1 0 ℓ a - s * a * dd ν ℓ + τ * (a.choose 2 : ℝ) * dd ν ℓ) * Wt ν 2 0 (ℓ + 1) (a - 1) +
      Wt ν 2 0 ℓ a * ((α + s) * Wt ν 1 0 (ℓ + 1) (a - 2) - s * ((a : ℝ) - 2) * dd ν (ℓ + 1) +
        τ * ((a - 1).choose 2 : ℝ) * dd ν (ℓ + 1)) -
      dd ν (ℓ + 1) * (4 * α * sH (Szkraw.iterShift ν ℓ) a + 2 * s * sT (Szkraw.iterShift ν ℓ) a +
        4 * τ * sZ (Szkraw.iterShift ν ℓ) a - τ * sWs (Szkraw.iterShift ν ℓ) a) := by
  set u := Szkraw.iterShift ν ℓ with hu
  set D := dd ν (ℓ + 1) with hD
  set X := Wt ν 1 0 ℓ a with hX
  set Y := Wt ν 2 0 ℓ a with hY
  set X' := Wt ν 1 0 (ℓ + 1) (a - 2) with hX'
  set Y' := Wt ν 2 0 (ℓ + 1) (a - 1) with hY'
  have hU := hν.iterShift ℓ
  have hu1 : 0 < u 1 := iterShift_one_pos hν hν1 ℓ
  have hDu : D = u 0 + u 1 := rfl
  have hu0 : u 0 = dd ν ℓ := rfl
  have eX : X = (a : ℝ) * u 1 + sY u a := by rw [hX, Wt_one_split, Wt20_eq]
  have eY : Y = sY u a := Wt20_eq ν ℓ a
  have eX' : X' = ((a : ℝ) - 2) * u 1 + sJ u a := Wt10_succ_eq ν ℓ a ha
  have eY' : Y' = sYp u a := Wt20_succ_eq ν ℓ a (by omega)
  -- `K ≥ 0`
  have hK : 0 ≤ X * Y' + Y * X' - 4 * D * sH u a := by
    have hg := gamma_bound_of hν ℓ a ha
    have hgs : 4 * sH u a ≤ gammaSum ν ℓ a := by
      unfold sH gammaSum; rw [mul_sum]
      refine sum_le_sum fun n _ => ?_
      have hun := iterShift_nonneg hν ℓ n
      by_cases h3 : 3 ≤ n
      · rw [if_pos h3, if_pos h3]
        have hn : (3 : ℝ) ≤ n := by exact_mod_cast h3
        have hC : (0 : ℝ) ≤ (a.choose n : ℝ) := Nat.cast_nonneg _
        have hcoef : 4 * ((n : ℝ) - 2) ≤ 2 * n + (if 4 ≤ n then (n.choose 2 : ℝ) else 0) := by
          split_ifs with h4
          · rw [choose2_real]; nlinarith [sq_nonneg ((n : ℝ) - 5 / 2)]
          · have : n = 3 := by omega
            subst this; norm_num
        have : (2 * (n : ℝ) + (if 4 ≤ n then (n.choose 2 : ℝ) else 0)) * (a.choose n : ℝ) * u n =
            (2 * ((n : ℝ) * (a.choose n : ℝ)) + (if 4 ≤ n then (n.choose 2 : ℝ) * (a.choose n : ℝ) else 0)) * u n := by
          split_ifs <;> ring
        rw [← this]
        have := mul_le_mul_of_nonneg_right hcoef (mul_nonneg hC hun)
        linarith
      · rw [if_neg h3, if_neg h3, if_neg (by omega)]; simp
    have hD0 : 0 ≤ D := iterShift_nonneg hν (ℓ + 1) 0
    have := mul_le_mul_of_nonneg_left hgs hD0
    linarith
  -- the `t`-part with surplus
  have hG := G_sur hU hu1 ha
  have h1 : 0 ≤ α * u 1 - s * u 0 := by rw [hu0]; linarith
  have hE0 : 2 / 3 * ((a : ℝ) - 2) * (a.choose 2 : ℝ) * u 2 * D * s ≤
      (α * X - s * a * u 0) * Y' + Y * ((α + s) * X' - s * ((a : ℝ) - 2) * D) - D * (4 * α * sH u a + 2 * s * sT u a) := by
    have e : u 1 * ((α * X - s * a * u 0) * Y' + Y * ((α + s) * X' - s * ((a : ℝ) - 2) * D) -
        D * (4 * α * sH u a + 2 * s * sT u a)) =
        (α * u 1 - s * u 0) * (X * Y' + Y * X' - 4 * D * sH u a) +
        s * (u 0 * sY u a * sYp u a + (u 0 + u 1) * sY u a * sJ u a -
          (u 0 + u 1) * (4 * u 0 * sH u a + 2 * u 1 * sT u a)) := by
      rw [eX, eY, eX', eY', hDu]; ring
    have k1 := mul_nonneg h1 hK
    have k2 := mul_le_mul_of_nonneg_left hG hs
    have k3 : u 1 * (2 / 3 * ((a : ℝ) - 2) * (a.choose 2 : ℝ) * u 2 * D * s) ≤
        u 1 * ((α * X - s * a * u 0) * Y' + Y * ((α + s) * X' - s * ((a : ℝ) - 2) * D) -
          D * (4 * α * sH u a + 2 * s * sT u a)) := by
      rw [e]
      have eq : u 1 * (2 / 3 * ((a : ℝ) - 2) * (a.choose 2 : ℝ) * u 2 * D * s) =
          s * (2 / 3 * ((a : ℝ) - 2) * (a.choose 2 : ℝ) * u 1 * u 2 * (u 0 + u 1)) := by rw [hDu]; ring
      linarith [k1, k2, eq]
    exact le_of_mul_le_mul_left k3 hu1
  -- the `τ`-part
  have hτp := tau_part_nonneg (u := u) (fun n => iterShift_nonneg hν ℓ n) ha
  have hD0 : 0 ≤ D := iterShift_nonneg hν (ℓ + 1) 0
  have hY'0 : 0 ≤ Y' := Wt_nonneg hν _ _ _ _
  have hu00 : 0 ≤ u 0 := iterShift_nonneg hν ℓ 0
  have ha3' : (3 : ℝ) ≤ a := by exact_mod_cast ha
  have ha2 : (0 : ℝ) ≤ (a : ℝ) - 2 := by linarith
  have hsur : τ * (2 / 3 * ((a : ℝ) - 1) * ((a : ℝ) - 2) * (a.choose 2 : ℝ) * u 2) * D ≤
      2 / 3 * ((a : ℝ) - 2) * (a.choose 2 : ℝ) * u 2 * D * s := by
    have hu2 := iterShift_nonneg hν ℓ 2
    have hc : 0 ≤ 2 / 3 * ((a : ℝ) - 2) * (a.choose 2 : ℝ) * u 2 * D :=
      mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) ha2) (Nat.cast_nonneg _)) hu2) hD0
    have := mul_le_mul_of_nonneg_left hsτ hc
    nlinarith [this]
  have hτD : 0 ≤ τ * D * (((a - 1).choose 2 : ℝ) * sY u a - 4 * sZ u a + sWs u a +
      2 / 3 * ((a : ℝ) - 1) * ((a : ℝ) - 2) * (a.choose 2 : ℝ) * u 2) := mul_nonneg (mul_nonneg hτ hD0) hτp
  have hτY : 0 ≤ τ * (a.choose 2 : ℝ) * u 0 * Y' := by positivity
  have e2 : (α * X - s * a * u 0 + τ * (a.choose 2 : ℝ) * u 0) * Y' +
      Y * ((α + s) * X' - s * ((a : ℝ) - 2) * D + τ * ((a - 1).choose 2 : ℝ) * D) -
      D * (4 * α * sH u a + 2 * s * sT u a + 4 * τ * sZ u a - τ * sWs u a) =
      ((α * X - s * a * u 0) * Y' + Y * ((α + s) * X' - s * ((a : ℝ) - 2) * D) - D * (4 * α * sH u a + 2 * s * sT u a)) +
      τ * (a.choose 2 : ℝ) * u 0 * Y' +
      τ * D * (((a - 1).choose 2 : ℝ) * sY u a - 4 * sZ u a + sWs u a) := by
    rw [eY]; ring
  rw [hu0] at e2
  rw [e2]
  have hexp : τ * D * (((a - 1).choose 2 : ℝ) * sY u a - 4 * sZ u a + sWs u a +
      2 / 3 * ((a : ℝ) - 1) * ((a : ℝ) - 2) * (a.choose 2 : ℝ) * u 2) =
      τ * D * (((a - 1).choose 2 : ℝ) * sY u a - 4 * sZ u a + sWs u a) +
      τ * (2 / 3 * ((a : ℝ) - 1) * ((a : ℝ) - 2) * (a.choose 2 : ℝ) * u 2) * D := by ring
  have hτY' : 0 ≤ τ * (a.choose 2 : ℝ) * dd ν ℓ * Y' := by rw [← hu0]; exact hτY
  have hE0' := hE0
  rw [hu0] at hE0'
  linarith [hE0', hsur, hτD, hτY', hexp]

end Szkraw
