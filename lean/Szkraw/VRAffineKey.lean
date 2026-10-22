import Szkraw.VRAffineWeights

/-!
# Theorem 8.9: the key inequality (paper, eq. `affine-key`)

`A₀(ℓ,a) B₀(ℓ+1,a-1) + B₀(ℓ,a) A₀(ℓ+1,a-2) ≥ c_{ℓ+1} (4 H₁(ℓ,a) - 2 V₁(ℓ,a))` on `Ω`, `a ≥ 3`.
With `u_n = f_n(ℓ)`, `D = d_{ℓ+1}`, `X = W_{1,0}(ℓ,a)`, `Y = W_{2,0}(ℓ,a)`, `X' = W_{1,0}(ℓ+1,a-2)`,
`Y' = W_{2,0}(ℓ+1,a-1)` (all formed from `f`): Lemma 8.3 gives
`XY' + YX' ≥ D Σ_n (2n [n ≥ 3] + C(n,2) [n ≥ 4]) C(a,n) u_n` from four families of products
(the paper's `γ_n` keeps all of them; these suffice), and the coefficients are then compared.
-/

set_option linter.unusedSectionVars false

namespace Szkraw

open Finset

theorem Wt_one_split (v : ℕ → ℝ) (ℓ a : ℕ) :
    Wt v 1 0 ℓ a = a * Szkraw.iterShift v ℓ 1 + Wt v 2 0 ℓ a := by
  unfold Wt
  have h : ∀ n ∈ range (a + 1), (if 1 ≤ n then ((n - 1 + 0).choose 0 : ℝ) else 0) * (a.choose n : ℝ) *
      Szkraw.iterShift v ℓ n = (if n = 1 then (a.choose n : ℝ) * Szkraw.iterShift v ℓ n else 0) +
      (if 2 ≤ n then ((n - 2 + 0).choose 0 : ℝ) else 0) * (a.choose n : ℝ) * Szkraw.iterShift v ℓ n := by
    intro n _
    rcases n with _ | _ | n <;> simp
  rw [sum_congr rfl h, sum_add_distrib, sum_ite_eq']
  split_ifs with h1
  · simp
  · have : a = 0 := by simp at h1; omega
    subst this; simp

/-- The sum `Γ = Σ_n (2n [n ≥ 3] + C(n,2) [n ≥ 4]) C(a,n) u_n`. -/
noncomputable def gammaSum (ν : ℕ → ℝ) (ℓ a : ℕ) : ℝ :=
  ∑ n ∈ range (a + 1), (2 * (if 3 ≤ n then (n : ℝ) * (a.choose n : ℝ) else 0) +
    (if 4 ≤ n then (n.choose 2 : ℝ) * (a.choose n : ℝ) else 0)) * Szkraw.iterShift ν ℓ n

/-- `V₁(ℓ,a) = t Σ_{n ≥ 2} (n-1)(a-n) C(a,n) u_n`. -/
theorem V1_reindex (t : ℝ) (ν : ℕ → ℝ) (ℓ a : ℕ) :
    affV t ν 1 ℓ a = ∑ n ∈ range (a + 1),
      (if 2 ≤ n then ((n : ℝ) - 1) * ((a : ℝ) - n) else 0) * (a.choose n : ℝ) * (t * Szkraw.iterShift ν ℓ n) := by
  unfold affV WtF vFn
  set G : ℕ → ℝ := fun n => (if 2 * 1 + 1 ≤ n then ((n - (2 * 1 + 1) + 1).choose 1 : ℝ) else 0) *
    (a.choose n : ℝ) * (t * n * Szkraw.iterShift ν ℓ (n - 1)) with hG
  rw [← reindex1 G a (by simp [hG]), sum_range_succ _ a]
  have hlast : (if 2 ≤ a then ((a : ℝ) - 1) * ((a : ℝ) - a) else 0) * (a.choose a : ℝ) *
      (t * Szkraw.iterShift ν ℓ a) = 0 := by split_ifs <;> ring
  rw [hlast, add_zero]
  refine sum_congr rfl fun m hm => ?_
  rw [mem_range] at hm
  simp only [hG]
  by_cases h2 : 2 ≤ m
  · rw [if_pos (by omega), if_pos h2, show m + 1 - 1 = m by omega,
      show m + 1 - (2 * 1 + 1) + 1 = m - 1 by omega, Nat.choose_one_right]
    have hc := Nat.choose_succ_right_eq a m
    have hc' : (a.choose (m + 1) : ℝ) * ((m : ℝ) + 1) = (a.choose m : ℝ) * ((a : ℝ) - m) := by
      have : ((a.choose (m + 1) * (m + 1) : ℕ) : ℝ) = ((a.choose m * (a - m) : ℕ) : ℝ) := by rw [hc]
      rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_sub (by omega)] at this
      push_cast at this; linarith
    rw [Nat.cast_sub (by omega)]
    push_cast
    linear_combination (((m : ℝ) - 1) * t * Szkraw.iterShift ν ℓ m) * hc'
  · rw [if_neg (by omega), if_neg h2]; ring

section Key

variable {N : ℕ} {r t : ℝ} {ν : ℕ → ℝ} (S : AffSetting N r t ν)
include S

/-- `Y' = Y - (a-1) u₂`. -/
theorem AffSetting.Yprime (ℓ a : ℕ) (ha : 1 ≤ a) :
    Wt ν 2 0 (ℓ + 1) (a - 1) = Wt ν 2 0 ℓ a - ((a : ℝ) - 1) * Szkraw.iterShift ν ℓ 2 := by
  have h1 := Wt_one_split ν (ℓ + 1) (a - 1)
  have h2 := Wt_one_split ν ℓ a
  rw [Wt_one_zero] at h1 h2
  rw [show ℓ + 1 + (a - 1) = ℓ + a by omega] at h1
  have hd : dd ν (ℓ + 1) = dd ν ℓ + Szkraw.iterShift ν ℓ 1 := rfl
  have hf : Szkraw.iterShift ν (ℓ + 1) 1 = Szkraw.iterShift ν ℓ 1 + Szkraw.iterShift ν ℓ 2 := rfl
  rw [hd, hf, Nat.cast_sub ha] at h1
  push_cast at h1
  linarith

theorem AffSetting.h83 (ℓ : ℕ) {i l : ℕ} (hi : 1 ≤ i) (hl : 1 ≤ l) :
    dd ν (ℓ + 1) * Szkraw.iterShift ν ℓ (i + l) ≤ Szkraw.iterShift ν ℓ i * Szkraw.iterShift ν (ℓ + 1) l :=
  lemma_8_3 S.hν ℓ hi hl

/-- Products `u₁ Y'`. -/
theorem AffSetting.gamma1 (ℓ a : ℕ) (ha : 1 ≤ a) :
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
          have key := S.h83 ℓ (i := 1) (l := j) le_rfl (by omega)
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
theorem AffSetting.gamma3 (ℓ a : ℕ) (ha : 3 ≤ a) :
    dd ν (ℓ + 1) * ∑ n ∈ range (a + 1), (if 3 ≤ n then (n : ℝ) * (a.choose n : ℝ) else 0) *
        Szkraw.iterShift ν ℓ n ≤
      ((a : ℝ) - 2) * Wt ν 2 0 ℓ a * Szkraw.iterShift ν (ℓ + 1) 1 := by
  set D := dd ν (ℓ + 1)
  have hD : 0 ≤ D := S.f_nonneg (ℓ + 1) 0
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
          have hu := S.f_nonneg ℓ n
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
            (mul_nonneg (S.f_nonneg _ _) (S.f_nonneg _ _))
        refine le_add_of_le_of_nonneg (sum_le_sum fun i hi => ?_) hlast
        simp only [hG]
        by_cases h2 : 2 ≤ i
        · rw [if_pos (by omega), if_pos h2, show i + 1 - 1 = i by omega]
          have key := S.h83 ℓ (i := i) (l := 1) (by omega) le_rfl
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
theorem AffSetting.gamma4 (ℓ a : ℕ) (ha : 2 ≤ a) :
    dd ν (ℓ + 1) * ∑ n ∈ range (a + 1), (if 4 ≤ n then (n.choose 2 : ℝ) * (a.choose n : ℝ) else 0) *
        Szkraw.iterShift ν ℓ n ≤
      Wt ν 2 0 ℓ a * Wt ν 2 0 (ℓ + 1) (a - 2) := by
  set D := dd ν (ℓ + 1)
  have hD : 0 ≤ D := S.f_nonneg (ℓ + 1) 0
  have hY : (a.choose 2 : ℝ) * Szkraw.iterShift ν ℓ 2 ≤ Wt ν 2 0 ℓ a := by
    have := Wt_ge_term S.hν 2 0 ℓ a 2 le_rfl ha
    simpa using this
  have hX'' : 0 ≤ Wt ν 2 0 (ℓ + 1) (a - 2) := Wt_nonneg S.hν _ _ _ _
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
          have key := S.h83 ℓ (i := 2) (l := j) (by norm_num) (by omega)
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
theorem AffSetting.gamma_bound (ℓ a : ℕ) (ha : 3 ≤ a) :
    dd ν (ℓ + 1) * gammaSum ν ℓ a ≤
      Wt ν 1 0 ℓ a * Wt ν 2 0 (ℓ + 1) (a - 1) + Wt ν 2 0 ℓ a * Wt ν 1 0 (ℓ + 1) (a - 2) := by
  have g1 := S.gamma1 ℓ a (by omega)
  have g3 := S.gamma3 ℓ a ha
  have g4 := S.gamma4 ℓ a (by omega)
  have hsplit : gammaSum ν ℓ a =
      2 * ∑ n ∈ range (a + 1), (if 3 ≤ n then (n : ℝ) * (a.choose n : ℝ) else 0) * Szkraw.iterShift ν ℓ n +
      ∑ n ∈ range (a + 1), (if 4 ≤ n then (n.choose 2 : ℝ) * (a.choose n : ℝ) else 0) * Szkraw.iterShift ν ℓ n := by
    unfold gammaSum
    rw [mul_sum, ← sum_add_distrib]
    exact sum_congr rfl fun n _ => by ring
  rw [Wt_one_split ν ℓ a, Wt_one_split ν (ℓ + 1) (a - 2), Nat.cast_sub (by omega : 2 ≤ a)]
  have hYY : 0 ≤ Wt ν 2 0 ℓ a * Wt ν 2 0 (ℓ + 1) (a - 1) :=
    mul_nonneg (Wt_nonneg S.hν _ _ _ _) (Wt_nonneg S.hν _ _ _ _)
  rw [hsplit]
  push_cast
  nlinarith [g1, g3, g4, hYY]

/-- The coefficient comparison: `α Γ ≥ t(aY' + (a-2)Y) + 4H₁ - 2V₁`. -/
theorem AffSetting.coeff_final {ℓ a : ℕ} (h : ℓ + a ≤ N) (ha : 3 ≤ a) :
    t * ((a : ℝ) * Wt ν 2 0 (ℓ + 1) (a - 1) + ((a : ℝ) - 2) * Wt ν 2 0 ℓ a) +
        4 * affH r t ν 1 ℓ a - 2 * affV t ν 1 ℓ a ≤
      (1 - r - t * ((ℓ : ℝ) + a)) * gammaSum ν ℓ a := by
  set α := 1 - r - t * ((ℓ : ℝ) + a) with hα
  have hαt : t * ((a : ℝ) - 1) ≤ α := by
    have h1 : ℓ + 2 * a ≤ 2 * N := by omega
    have h2 : ((ℓ + 2 * a : ℕ) : ℝ) ≤ 2 * (N : ℝ) := by exact_mod_cast h1
    push_cast at h2
    nlinarith [S.hts, S.ht]
  have ht := S.ht
  have ha1 : (1 : ℝ) ≤ a := by exact_mod_cast (show 1 ≤ a by omega)
  rw [S.Yprime ℓ a (by omega), V1_reindex]
  unfold affH WtF hFn gammaSum
  unfold Wt
  -- write everything as one sum
  have hu2 : ((a : ℝ) * ((a : ℝ) - 1)) * Szkraw.iterShift ν ℓ 2 =
      ∑ n ∈ range (a + 1), if n = 2 then ((a : ℝ) * ((a : ℝ) - 1)) * Szkraw.iterShift ν ℓ n else 0 := by
    rw [sum_ite_eq']; rw [if_pos (mem_range.mpr (by omega))]
  have hrw : t * ((a : ℝ) * (∑ n ∈ range (a + 1), (if 2 ≤ n then ((n - 2 + 0).choose 0 : ℝ) else 0) *
        (a.choose n : ℝ) * Szkraw.iterShift ν ℓ n - ((a : ℝ) - 1) * Szkraw.iterShift ν ℓ 2) +
      ((a : ℝ) - 2) * ∑ n ∈ range (a + 1), (if 2 ≤ n then ((n - 2 + 0).choose 0 : ℝ) else 0) *
        (a.choose n : ℝ) * Szkraw.iterShift ν ℓ n) =
      t * ((2 * (a : ℝ) - 2) * ∑ n ∈ range (a + 1), (if 2 ≤ n then ((n - 2 + 0).choose 0 : ℝ) else 0) *
        (a.choose n : ℝ) * Szkraw.iterShift ν ℓ n - ((a : ℝ) * ((a : ℝ) - 1)) * Szkraw.iterShift ν ℓ 2) := by
    ring
  rw [hrw, hu2]
  rw [← sub_nonneg]
  simp only [mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
  refine sum_nonneg fun n hn => ?_
  rw [mem_range] at hn
  have hu := S.f_nonneg ℓ n
  have hc : (0 : ℝ) ≤ (a.choose n : ℝ) := Nat.cast_nonneg _
  rcases n with _ | _ | _ | _ | m
  · simp
  · simp
  · -- n = 2: the coefficient vanishes
    have hc2 := choose_two_mul a
    have hc2' : (a.choose 2 : ℝ) * 2 = (a : ℝ) * ((a : ℝ) - 1) := by
      have : ((a.choose 2 * 2 : ℕ) : ℝ) = ((a * (a - 1) : ℕ) : ℝ) := by rw [hc2]
      rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_sub (by omega)] at this
      push_cast at this; linarith
    simp only [show ¬ (3 ≤ 2) by omega, show ¬ (4 ≤ 2) by omega, show 2 ≤ 2 from le_rfl, if_true, if_false,
      show (0 + 1 + 1 : ℕ) = 2 from rfl]
    norm_num
    exact le_of_eq (by linear_combination (t * Szkraw.iterShift ν ℓ 2) * hc2')
  · -- n = 3
    simp only [show 3 ≤ 0 + 1 + 1 + 1 by omega, show ¬ (4 ≤ 0 + 1 + 1 + 1) by omega,
      show 2 ≤ 0 + 1 + 1 + 1 by omega, if_true, if_false, show ¬ (0 + 1 + 1 + 1 = 2) by omega]
    norm_num
    have : 0 ≤ (a.choose 3 : ℝ) * Szkraw.iterShift ν ℓ 3 * (2 * α - 2 * (t * ((a : ℝ) - 1))) :=
      mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (S.f_nonneg ℓ 3)) (by linarith)
    nlinarith [this]
  · -- n = m + 4
    have hm4 : 3 ≤ m + 1 + 1 + 1 + 1 := by omega
    simp only [hm4, show 4 ≤ m + 1 + 1 + 1 + 1 by omega, show 2 ≤ m + 1 + 1 + 1 + 1 by omega, if_true,
      show ¬ (m + 1 + 1 + 1 + 1 = 2) by omega, if_false]
    rw [show m + 1 + 1 + 1 + 1 - 2 + 0 = m + 2 by omega, show m + 1 + 1 + 1 + 1 - (2 * 1 + 1) + 1 = m + 2 by omega,
      Nat.choose_zero_right, Nat.choose_one_right]
    have hcn := choose_two_mul (m + 1 + 1 + 1 + 1)
    have hcn' : ((m + 1 + 1 + 1 + 1).choose 2 : ℝ) = ((m : ℝ) + 4) * ((m : ℝ) + 3) / 2 := by
      have : (((m + 1 + 1 + 1 + 1).choose 2 * 2 : ℕ) : ℝ) = (((m + 1 + 1 + 1 + 1) * (m + 1 + 1 + 1 + 1 - 1) : ℕ) : ℝ) := by
        rw [hcn]
      rw [show m + 1 + 1 + 1 + 1 - 1 = m + 3 by omega] at this
      push_cast at this; linarith
    rw [hcn']
    push_cast
    set n : ℝ := (m : ℝ) + 4 with hn
    set Q : ℝ := (n ^ 2 - 5 * n + 16) / 2 with hQ
    have hQ0 : 0 ≤ Q := by nlinarith [sq_nonneg (n - 5 / 2)]
    have hQ1 : 0 ≤ (n ^ 2 - 9 * n + 24) / 2 := by nlinarith [sq_nonneg (n - 9 / 2)]
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    have f1 : 0 ≤ (α - t * ((a : ℝ) - 1)) * Q := mul_nonneg (by linarith) hQ0
    have f2 : 0 ≤ t * ((a : ℝ) - 1) * ((n ^ 2 - 9 * n + 24) / 2) := mul_nonneg (mul_nonneg ht (by linarith)) hQ1
    have f3 : 0 ≤ t * (n - 1) * (2 * n - 6) := mul_nonneg (mul_nonneg ht (by linarith)) (by linarith)
    have hbr : 0 ≤ α * (2 * n + n * (n - 1) / 2) - t * (2 * (a : ℝ) - 2) -
        4 * (n - 2) * (1 - r - t * ((ℓ : ℝ) + n)) + 2 * ((n - 1) * ((a : ℝ) - n)) * t := by
      have e : 1 - r - t * ((ℓ : ℝ) + n) = α + t * ((a : ℝ) - n) := by rw [hα]; ring
      rw [e]
      nlinarith [f1, f2, f3]
    have hpos : 0 ≤ (a.choose (m + 1 + 1 + 1 + 1) : ℝ) * Szkraw.iterShift ν ℓ (m + 1 + 1 + 1 + 1) :=
      mul_nonneg (Nat.cast_nonneg _) (S.f_nonneg _ _)
    have := mul_nonneg hpos hbr
    rw [hn] at this
    nlinarith [this]

/-- **The key inequality** (paper, eq. `affine-key`), on `Ω` with `a ≥ 3`. -/
theorem AffSetting.key {ℓ a : ℕ} (h : ℓ + a ≤ N) (ha : 3 ≤ a) :
    4 * dd (affU N r t ν) (ℓ + 1) * affH r t ν 1 ℓ a ≤
      Wt (affW N r t ν) 1 0 ℓ a * Wt (affU N r t ν) 2 0 (ℓ + 1) (a - 1) +
      Wt (affU N r t ν) 2 0 ℓ a * Wt (affW N r t ν) 1 0 (ℓ + 1) (a - 2) +
      2 * dd (affU N r t ν) (ℓ + 1) * affV t ν 1 ℓ a := by
  set ρ := r + t * ((ℓ : ℝ) + 1) with hρ
  set D := dd ν (ℓ + 1) with hD
  set u0 := dd ν ℓ with hu0
  set X := Wt ν 1 0 ℓ a with hX
  set Y := Wt ν 2 0 ℓ a with hY
  set X' := Wt ν 1 0 (ℓ + 1) (a - 2) with hX'
  set Y' := Wt ν 2 0 (ℓ + 1) (a - 1) with hY'
  set α := 1 - r - t * ((ℓ : ℝ) + a) with hα
  set Γ := gammaSum ν ℓ a with hΓ
  set H := affH r t ν 1 ℓ a with hH
  set V := affV t ν 1 ℓ a with hV
  have ht := S.ht
  have hρ0 : 0 < ρ := by have := S.hr; positivity
  have hcc : dd (affU N r t ν) (ℓ + 1) = ρ * D := by rw [S.dd_U (by omega)]; push_cast; ring
  have hA0 : Wt (affW N r t ν) 1 0 ℓ a = α * X - t * a * u0 := S.A0_eq h
  have hA0'' : Wt (affW N r t ν) 1 0 (ℓ + 1) (a - 2) = (α + t) * X' - t * ((a : ℝ) - 2) * D := by
    rw [S.A0_eq (by omega), Nat.cast_sub (by omega : 2 ≤ a)]
    push_cast; ring
  have nA0 := S.A0_nn h
  have nA0'' := S.A0_nn (show ℓ + 1 + (a - 2) ≤ N by omega)
  have hB0 : ρ * Y ≤ Wt (affU N r t ν) 2 0 ℓ a := S.B0_ge h
  have hB0' : ρ * Y' ≤ Wt (affU N r t ν) 2 0 (ℓ + 1) (a - 1) := by
    have := S.B0_ge (ℓ := ℓ + 1) (a := a - 1) (by omega)
    have hY'0 : 0 ≤ Y' := Wt_nonneg S.hν _ _ _ _
    push_cast at this
    have : ρ * Y' ≤ (r + t * ((ℓ : ℝ) + 1 + 1)) * Y' := mul_le_mul_of_nonneg_right (by linarith) hY'0
    linarith
  have hY0 : 0 ≤ Y := Wt_nonneg S.hν _ _ _ _
  have hY'0 : 0 ≤ Y' := Wt_nonneg S.hν _ _ _ _
  have hX'0 : 0 ≤ X' := Wt_nonneg S.hν _ _ _ _
  have hDu : u0 ≤ D := by
    have : D = u0 + Szkraw.iterShift ν ℓ 1 := rfl
    linarith [S.f_nonneg ℓ 1]
  have hα0 : 0 ≤ α := by
    have := S.s_ge (ℓ + a) h; push_cast at this; linarith
  have hΓb := S.gamma_bound ℓ a ha
  have hfin := S.coeff_final h ha
  have ha0 : (0 : ℝ) ≤ a := Nat.cast_nonneg a
  have p1 : 0 ≤ (α * X - t * a * u0) * (Wt (affU N r t ν) 2 0 (ℓ + 1) (a - 1) - ρ * Y') := by
    rw [← hA0]; exact mul_nonneg nA0 (by linarith)
  have p2 : 0 ≤ (Wt (affU N r t ν) 2 0 ℓ a - ρ * Y) * ((α + t) * X' - t * ((a : ℝ) - 2) * D) := by
    rw [← hA0'']; exact mul_nonneg (by linarith) nA0''
  have p3 : 0 ≤ ρ * (t * a * (D - u0) * Y') :=
    mul_nonneg hρ0.le (mul_nonneg (mul_nonneg (mul_nonneg ht ha0) (by linarith)) hY'0)
  have p4 : 0 ≤ ρ * (t * Y * X') := mul_nonneg hρ0.le (mul_nonneg (mul_nonneg ht hY0) hX'0)
  have p5 : 0 ≤ ρ * (α * (X * Y' + Y * X' - D * Γ)) := mul_nonneg hρ0.le (mul_nonneg hα0 (by linarith))
  have p6 : 0 ≤ ρ * (D * (α * Γ - (t * ((a : ℝ) * Y' + ((a : ℝ) - 2) * Y) + 4 * H - 2 * V))) :=
    mul_nonneg hρ0.le (mul_nonneg (S.f_nonneg (ℓ + 1) 0) (by linarith))
  rw [hcc, hA0, hA0'']
  linear_combination p1 + p2 + p3 + p4 + p5 + p6

end Key

end Szkraw
