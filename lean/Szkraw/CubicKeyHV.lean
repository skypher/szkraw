import Szkraw.CubicDetours
import Szkraw.CubicKeyForms
set_option linter.unusedSectionVars false
namespace Szkraw
open Finset

/-! ### Reindexing `V` and the binomial helpers -/

/-- Reindex `V₁`: `V₁ = Σ_{n ≥ 2} (n-1)(a-n) C(a,n) Γ_{n+1}(ℓ) f_n`. -/
theorem cubicV_reindex (t τ σ : ℝ) (ν : ℕ → ℝ) (ℓ a : ℕ) :
    cubicV t τ σ ν 1 ℓ a = ∑ n ∈ range (a + 1),
      (if 2 ≤ n then ((n : ℝ) - 1) * ((a : ℝ) - n) else 0) * (a.choose n : ℝ) *
        (GammaC t τ σ ℓ (n + 1) * Szkraw.iterShift ν ℓ n) := by
  set G : ℕ → ℝ := fun n => (if 2 * 1 + 1 ≤ n then ((n - (2 * 1 + 1) + 1).choose 1 : ℝ) else 0) *
    (a.choose n : ℝ) * ((n : ℝ) * GammaC t τ σ ℓ n * Szkraw.iterShift ν ℓ (n - 1)) with hG
  have e0 : cubicV t τ σ ν 1 ℓ a = ∑ n ∈ range (a + 1), G n := rfl
  rw [e0, ← reindex1 G a (by simp [hG]), sum_range_succ _ a]
  have hlast : (if 2 ≤ a then ((a : ℝ) - 1) * ((a : ℝ) - a) else 0) * (a.choose a : ℝ) *
      (GammaC t τ σ ℓ (a + 1) * Szkraw.iterShift ν ℓ a) = 0 := by
    split_ifs <;> ring
  rw [hlast, add_zero]
  refine sum_congr rfl fun m hm => ?_
  rw [mem_range] at hm
  simp only [hG]
  by_cases h2 : 2 ≤ m
  · rw [if_pos (show 2 * 1 + 1 ≤ m + 1 by omega), if_pos h2, show m + 1 - 1 = m by omega,
      show m + 1 - (2 * 1 + 1) + 1 = m - 1 by omega, Nat.choose_one_right]
    have hc' : ((a.choose (m + 1) : ℕ) : ℝ) * ((m : ℝ) + 1) = (a.choose m : ℝ) * ((a : ℝ) - m) :=
      choose_succ_real' a m
    have hm1 : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega)]; norm_num
    rw [hm1]
    push_cast
    linear_combination ((m : ℝ) - 1) * GammaC t τ σ ℓ (m + 1) * Szkraw.iterShift ν ℓ m * hc'
  · rw [if_neg (show ¬ (2 * 1 + 1 ≤ m + 1) by omega), if_neg h2]
    ring

/-- `C(a-n,2)` for `n ≤ a`. -/
theorem choose2_sub_real (a n : ℕ) (h : n ≤ a) :
    (((a - n).choose 2 : ℕ) : ℝ) = ((a : ℝ) - n) * ((a : ℝ) - n - 1) / 2 := by
  rw [choose2_real, Nat.cast_sub h]

/-- `C(n-3+1,1) = n - 2` for `n ≥ 3` (the weight of `H`). -/
theorem wt1_eq_of_three_le {n : ℕ} (h : 3 ≤ n) :
    ((n - (2 * 1 + 1) + 1).choose 1 : ℝ) = (n : ℝ) - 2 := by
  rw [show n - (2 * 1 + 1) + 1 = n - 2 by omega, Nat.choose_one_right,
    Nat.cast_sub (show 2 ≤ n by omega)]
  norm_num

/-- The weight `wgtH n = n - 2` for `n ≥ 3`. -/
theorem wgtH_real {n : ℕ} (h : 3 ≤ n) : ((n - 3 + 1).choose 1 : ℝ) = (n : ℝ) - 2 := by
  rw [show n - 3 + 1 = n - 2 by omega, Nat.choose_one_right, Nat.cast_sub (show 2 ≤ n by omega)]
  norm_num

/-! ### The identity -/

/-- `4 H₁ - 2 V₁ = 4 (1 - ρ(ℓ+a)) H_* + 2 (Δρ(ℓ) + (a-1)(τ+σℓ)) T + 4 (τ+σℓ) Z + 4 σ Σ cfT3 f`. -/
theorem cubicHV_eq (r t τ σ : ℝ) (ν : ℕ → ℝ) (ℓ a : ℕ) (ha : 3 ≤ a) :
    4 * cubicH r t τ σ ν 1 ℓ a - 2 * cubicV t τ σ ν 1 ℓ a =
      4 * (1 - rhoC r t τ σ (ℓ + a)) * sH (Szkraw.iterShift ν ℓ) a +
      2 * (drhoC t τ σ ℓ + ((a : ℝ) - 1) * (τ + σ * ℓ)) * sT (Szkraw.iterShift ν ℓ) a +
      4 * (τ + σ * ℓ) * sZ (Szkraw.iterShift ν ℓ) a + 4 * σ * lf (a + 1) (cfT3 a) (Szkraw.iterShift ν ℓ) := by
  rw [cubicV_reindex]
  unfold cubicH WtF hC sH sT sZ lf cfT3 cfH wgtH rhoC drhoC GammaC
  simp only [mul_sum]
  rw [← sum_sub_distrib, ← sum_add_distrib, ← sum_add_distrib, ← sum_add_distrib]
  refine sum_congr rfl fun n hn => ?_
  rw [mem_range] at hn
  rcases Nat.lt_or_ge n 2 with h | h
  · have hA : ¬ (2 * 1 + 1 ≤ n) := by omega
    have hB : ¬ (3 ≤ n) := by omega
    have hC : ¬ (2 ≤ n) := by omega
    simp only [hA, hC, ↓reduceIte]
    ring
  rcases Nat.eq_or_lt_of_le h with e | h3
  · subst e
    have hA : ¬ (2 * 1 + 1 ≤ 2) := by omega
    have hB : ¬ (3 ≤ 2) := by omega
    simp only [hA, ↓reduceIte, show (2 ≤ 2) from le_rfl]
    rw [choose2_sub_real a 2 (by omega), choose2_real ℓ]
    push_cast
    ring
  · have h3' : 3 ≤ n := by omega
    have hA : 2 * 1 + 1 ≤ n := by omega
    have hC : 2 ≤ n := by omega
    simp only [if_pos hA, if_pos hC]
    rw [wt1_eq_of_three_le h3', choose2_sub_real a n (by omega),
      choose2_real (ℓ + n), choose2_real (ℓ + a), choose2_real ℓ,
      choose3_real (ℓ + n), choose3_real (ℓ + a), choose3_real a, choose3_real n]
    push_cast
    ring

end Szkraw
