import Szkraw.VRQuadDetours
import Szkraw.VRAffineMain

/-!
# Theorem 8.11 (convex quadratic ratio)

The key inequality (eq. `quad-key`) in the setting `QuadSetting`, the weights of the recurrence of
Theorem 8.6 satisfy `ResumWeights2`, so the kernels are nonnegative (`gkernel_resum2`) and the array
has property (P) (`matrixPositivity_of_kernel`).
-/

set_option linter.unusedSectionVars false

namespace Szkraw

open Finset

theorem PhiQ_nonneg {r t τ : ℝ} (hr : 0 < r) (ht : 0 ≤ t) (hτ : 0 ≤ τ) {v : ℕ → ℝ} (hv : ∀ k, 0 ≤ v k)
    (ℓ n : ℕ) : 0 ≤ PhiQ r t τ ℓ n v := by
  unfold PhiQ
  rw [rhoQ_add]
  have h1 : 0 ≤ rhoN r t τ (ℓ + n) := by unfold rhoN; positivity
  have h2 : 0 ≤ (n : ℝ) * drhoQ t τ ((ℓ : ℝ) + n - 1) * v (n - 1) := by
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; simp
    · have hx : (0 : ℝ) ≤ (ℓ : ℝ) + n - 1 := by
        have : (1 : ℝ) ≤ n := by exact_mod_cast hn
        have := (Nat.cast_nonneg ℓ : (0 : ℝ) ≤ ℓ); linarith
      have hd : 0 ≤ drhoQ t τ ((ℓ : ℝ) + n - 1) := by unfold drhoQ; exact add_nonneg ht (mul_nonneg hτ hx)
      exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hd) (hv _)
  have h3 : 0 ≤ (n : ℝ) * ((n : ℝ) - 1) / 2 * τ * v (n - 2) := by
    rw [← choose2_real]; exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hτ) (hv _)
  exact add_nonneg (add_nonneg (mul_nonneg h1 (hv _)) h2) h3

/-! ### Reindexing `V₁` and `W₁` -/

/-- `V₁ = Σ_{n ≥ 2} (n-1)(a-n) C(a,n) Δρ(ℓ+n) f_n`. -/
theorem quadV1_reindex (t τ : ℝ) (ν : ℕ → ℝ) (ℓ a : ℕ) :
    quadV t τ ν 1 ℓ a = ∑ n ∈ range (a + 1),
      (if 2 ≤ n then ((n : ℝ) - 1) * ((a : ℝ) - n) else 0) * (a.choose n : ℝ) *
        ((t + τ * ((ℓ : ℝ) + n)) * Szkraw.iterShift ν ℓ n) := by
  set G : ℕ → ℝ := fun n => (if 2 * 1 + 1 ≤ n then ((n - (2 * 1 + 1) + 1).choose 1 : ℝ) else 0) *
    (a.choose n : ℝ) * ((n : ℝ) * drhoQ t τ ((ℓ : ℝ) + n - 1) * Szkraw.iterShift ν ℓ (n - 1)) with hG
  have e0 : quadV t τ ν 1 ℓ a = ∑ n ∈ range (a + 1), G n := rfl
  rw [e0, ← reindex1 G a (by simp [hG]), sum_range_succ _ a]
  have hlast : (if 2 ≤ a then ((a : ℝ) - 1) * ((a : ℝ) - a) else 0) * (a.choose a : ℝ) *
      ((t + τ * ((ℓ : ℝ) + a)) * Szkraw.iterShift ν ℓ a) = 0 := by split_ifs <;> ring
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
    unfold drhoQ
    push_cast
    linear_combination (((m : ℝ) - 1) * (t + τ * ((ℓ : ℝ) + m)) * Szkraw.iterShift ν ℓ m) * hc'
  · rw [if_neg (by omega), if_neg h2]; ring

/-- `W₁ = τ W_*`. -/
theorem quadW1_eq (τ : ℝ) (ν : ℕ → ℝ) (ℓ a : ℕ) :
    quadWw τ ν 1 ℓ a = τ * sWs (Szkraw.iterShift ν ℓ) a := by
  set G : ℕ → ℝ := fun n => (if 2 * 1 + 1 ≤ n then ((n - (2 * 1 + 1) + 1).choose 1 : ℝ) else 0) *
    (a.choose n : ℝ) * ((n : ℝ) * ((n : ℝ) - 1) / 2 * τ * Szkraw.iterShift ν ℓ (n - 2)) with hG
  have e0 : quadWw τ ν 1 ℓ a = ∑ n ∈ range (a + 1), G n := rfl
  have hext : ∑ n ∈ range (a + 1), G n = ∑ n ∈ range (a + 1 + 2), G n := by
    rw [show a + 1 + 2 = a + 1 + 1 + 1 by ring, sum_range_succ G (a + 1 + 1), sum_range_succ G (a + 1)]
    have h1 : G (a + 1) = 0 := by
      simp only [hG]; rw [Nat.choose_eq_zero_of_lt (show a < a + 1 by omega)]; simp
    have h2 : G (a + 1 + 1) = 0 := by
      simp only [hG]; rw [Nat.choose_eq_zero_of_lt (show a < a + 1 + 1 by omega)]; simp
    rw [h1, h2]; ring
  rw [e0, hext, ← reindex2 G (a + 1) (by simp [hG]) (by simp [hG])]
  unfold sWs
  rw [mul_sum]
  refine sum_congr rfl fun k hk => ?_
  simp only [hG]
  by_cases h1 : 1 ≤ k
  · rw [if_pos (by omega), show k + 2 - (2 * 1 + 1) + 1 = k by omega, Nat.choose_one_right,
      show k + 2 - 2 = k by omega]
    have hc := Nat.choose_mul (n := a) (k := k + 2) (s := k) (by omega)
    rw [show k + 2 - k = 2 by omega, Nat.choose_symm_add] at hc
    have hc' : (a.choose (k + 2) : ℝ) * (((k : ℝ) + 2) * ((k : ℝ) + 1) / 2) =
        (a.choose k : ℝ) * ((a - k).choose 2 : ℝ) := by
      have e := choose2_real (k + 2)
      have : ((a.choose (k + 2) * (k + 2).choose 2 : ℕ) : ℝ) = ((a.choose k * (a - k).choose 2 : ℕ) : ℝ) := by
        rw [hc]
      push_cast at this e
      rw [e] at this
      linear_combination this
    push_cast
    linear_combination ((k : ℝ) * τ * Szkraw.iterShift ν ℓ k) * hc'
  · have : k = 0 := by omega
    subst this
    simp

/-- `4 H₁ - 2 V₁ = 4 α H_* + 2 s T + 4 τ Z` with `α = 1 - ρ(ℓ+a)`, `s = Δρ(ℓ+a-1)`. -/
theorem quadHV_eq (r t τ : ℝ) (ν : ℕ → ℝ) (ℓ a : ℕ) :
    4 * quadH r t τ ν 1 ℓ a - 2 * quadV t τ ν 1 ℓ a =
      4 * (1 - rhoN r t τ (ℓ + a)) * sH (Szkraw.iterShift ν ℓ) a +
      2 * (t + τ * ((ℓ : ℝ) + a - 1)) * sT (Szkraw.iterShift ν ℓ) a + 4 * τ * sZ (Szkraw.iterShift ν ℓ) a := by
  rw [quadV1_reindex]
  unfold quadH WtF hQ sH sT sZ
  rw [mul_sum, mul_sum, mul_sum, mul_sum, mul_sum, ← sum_sub_distrib, ← sum_add_distrib, ← sum_add_distrib]
  refine sum_congr rfl fun n hn => ?_
  rw [mem_range] at hn
  rcases Nat.lt_or_ge n 2 with h | h
  · rw [if_neg (show ¬ (2 * 1 + 1 ≤ n) by omega), if_neg (show ¬ (2 ≤ n) by omega),
      if_neg (show ¬ (3 ≤ n) by omega), if_neg (show ¬ (2 ≤ n) by omega), if_neg (show ¬ (2 ≤ n) by omega)]
    ring
  rcases Nat.eq_or_lt_of_le h with e | h3
  · subst e
    rw [if_neg (show ¬ (2 * 1 + 1 ≤ 2) by omega), if_pos (show 2 ≤ 2 from le_rfl),
      if_neg (show ¬ (3 ≤ 2) by omega), if_pos (show 2 ≤ 2 from le_rfl), if_pos (show 2 ≤ 2 from le_rfl),
      choose2_real (a - 2), Nat.cast_sub (show 2 ≤ a by omega)]
    push_cast; ring
  · rw [if_pos (show 2 * 1 + 1 ≤ n by omega), if_pos (show 2 ≤ n by omega),
      if_pos (show 3 ≤ n by omega), if_pos (show 2 ≤ n by omega), if_pos (show 2 ≤ n by omega),
      show n - (2 * 1 + 1) + 1 = n - 2 by omega, Nat.choose_one_right,
      choose2_real (a - n), Nat.cast_sub (show n ≤ a by omega), Nat.cast_sub (show 2 ≤ n by omega)]
    unfold rhoN
    rw [choose2_real (ℓ + n), choose2_real (ℓ + a)]
    push_cast; ring

/-! ### The key inequality -/

section Key

variable {N : ℕ} {r t τ : ℝ} {ν u : ℕ → ℝ} (S : QuadSetting N r t τ ν u)
include S

/-- `α u₁ ≥ s u₀` with `α = 1 - ρ(ℓ+a)`, `s = Δρ(ℓ+a-1)`, from the monotonicity of `b` at `ℓ+a-1`. -/
theorem QuadSetting.alpha_ge {ℓ a : ℕ} (h : ℓ + a ≤ N) (ha : 1 ≤ a) :
    (t + τ * ((ℓ : ℝ) + a - 1)) * dd ν ℓ ≤ (1 - rhoN r t τ (ℓ + a)) * Szkraw.iterShift ν ℓ 1 := by
  obtain ⟨m, hm⟩ : ∃ m, ℓ + a = m + 1 := ⟨ℓ + a - 1, by omega⟩
  have hstep := S.hb m (by omega)
  rw [S.dd_w (by omega), S.dd_w (by omega)] at hstep
  have e1 : dd ν (m + 1) = dd ν m + Szkraw.iterShift ν m 1 := rfl
  rw [e1] at hstep
  have hρ : rhoN r t τ (m + 1) = rhoN r t τ m + 1 * (t + τ * m) + τ * ((1 : ℕ).choose 2 : ℝ) :=
    by exact_mod_cast rhoN_add r t τ m 1
  rw [Nat.choose_eq_zero_of_lt (show 1 < 2 by norm_num), Nat.cast_zero, mul_zero, add_zero, one_mul] at hρ
  have hm1 : (ℓ : ℝ) + a - 1 = m := by
    have : ((ℓ + a : ℕ) : ℝ) = ((m + 1 : ℕ) : ℝ) := by rw [hm]
    push_cast at this; linarith
  rw [hm1, hm]
  have hb' : (t + τ * m) * dd ν m ≤ (1 - rhoN r t τ (m + 1)) * Szkraw.iterShift ν m 1 := by
    rw [hρ] at hstep ⊢; nlinarith [hstep]
  have hs : 0 ≤ t + τ * (m : ℝ) := add_nonneg S.ht (mul_nonneg S.hτ (Nat.cast_nonneg m))
  have hch := R_chain_of S.hν S.hν1 ℓ (m - ℓ)
  rw [show ℓ + (m - ℓ) = m by omega] at hch
  have hfm := S.f1_pos m
  have hfl := S.f1_pos ℓ
  have k1 : (t + τ * (m : ℝ)) * (dd ν ℓ * Szkraw.iterShift ν m 1) ≤
      (t + τ * (m : ℝ)) * (dd ν m * Szkraw.iterShift ν ℓ 1) := mul_le_mul_of_nonneg_left hch hs
  have k2 : (t + τ * (m : ℝ)) * dd ν m * Szkraw.iterShift ν ℓ 1 ≤
      (1 - rhoN r t τ (m + 1)) * Szkraw.iterShift ν m 1 * Szkraw.iterShift ν ℓ 1 :=
    mul_le_mul_of_nonneg_right hb' hfl.le
  have k3 : (t + τ * (m : ℝ)) * dd ν ℓ * Szkraw.iterShift ν m 1 ≤
      (1 - rhoN r t τ (m + 1)) * Szkraw.iterShift ν ℓ 1 * Szkraw.iterShift ν m 1 := by
    linear_combination k1 + k2
  exact le_of_mul_le_mul_right k3 hfm

/-- **The key inequality** (paper, eq. `quad-key`), on `Ω` with `a ≥ 3`. -/
theorem QuadSetting.key {ℓ a : ℕ} (h : ℓ + a ≤ N) (ha : 3 ≤ a) :
    4 * dd u (ℓ + 1) * quadH r t τ ν 1 ℓ a ≤
      Wt (quadW ν u) 1 0 ℓ a * Wt u 2 0 (ℓ + 1) (a - 1) + Wt u 2 0 ℓ a * Wt (quadW ν u) 1 0 (ℓ + 1) (a - 2) +
      2 * dd u (ℓ + 1) * quadV t τ ν 1 ℓ a + dd u (ℓ + 1) * quadWw τ ν 1 ℓ a := by
  have hA0 : Wt (quadW ν u) 1 0 ℓ a = (1 - rhoN r t τ (ℓ + a)) * Wt ν 1 0 ℓ a -
      (t + τ * ((ℓ : ℝ) + a - 1)) * a * dd ν ℓ + τ * (a.choose 2 : ℝ) * dd ν ℓ := by
    rw [Wt_one_zero, Wt_one_zero, S.dd_w h, S.dd_w (by omega), rhoN_add r t τ ℓ a, choose2_real a]
    ring
  have hA0'' : Wt (quadW ν u) 1 0 (ℓ + 1) (a - 2) =
      ((1 - rhoN r t τ (ℓ + a)) + (t + τ * ((ℓ : ℝ) + a - 1))) * Wt ν 1 0 (ℓ + 1) (a - 2) -
      (t + τ * ((ℓ : ℝ) + a - 1)) * ((a : ℝ) - 2) * dd ν (ℓ + 1) +
      τ * ((a - 1).choose 2 : ℝ) * dd ν (ℓ + 1) := by
    obtain ⟨k, rfl⟩ : ∃ k, a = k + 3 := ⟨a - 3, by omega⟩
    rw [Wt_one_zero, Wt_one_zero, show ℓ + 1 + (k + 3 - 2) = ℓ + 1 + (k + 1) by omega,
      S.dd_w (by omega), S.dd_w (by omega), show ℓ + (k + 3) = ℓ + 1 + (k + 1) + 1 by omega,
      rhoN_add r t τ (ℓ + 1 + (k + 1)) 1, rhoN_add r t τ (ℓ + 1) (k + 1), show k + 3 - 1 = k + 2 by omega,
      choose2_real (k + 2), choose2_real (k + 1), choose2_real 1]
    push_cast; ring
  have hB0 : rhoN r t τ (ℓ + 1) * Wt ν 2 0 ℓ a ≤ Wt u 2 0 ℓ a := S.B0_ge h
  have hB0' : rhoN r t τ (ℓ + 1) * Wt ν 2 0 (ℓ + 1) (a - 1) ≤ Wt u 2 0 (ℓ + 1) (a - 1) := by
    have h1 := S.B0_ge (ℓ := ℓ + 1) (a := a - 1) (by omega)
    have h2 : rhoN r t τ (ℓ + 1) ≤ rhoN r t τ (ℓ + 1 + 1) := S.rho_mono (by omega)
    have h3 : 0 ≤ Wt ν 2 0 (ℓ + 1) (a - 1) := Wt_nonneg S.hν _ _ _ _
    nlinarith
  have hcc : dd u (ℓ + 1) = rhoN r t τ (ℓ + 1) * dd ν (ℓ + 1) := S.dd_u (by omega)
  have nA0 := S.A0_nn h
  have nA0'' := S.A0_nn (show ℓ + 1 + (a - 2) ≤ N by omega)
  have hx : (0 : ℝ) ≤ (ℓ : ℝ) + a - 1 := by
    have : (1 : ℝ) ≤ a := by exact_mod_cast (show 1 ≤ a by omega)
    have := (Nat.cast_nonneg ℓ : (0 : ℝ) ≤ ℓ); linarith
  have hs : 0 ≤ t + τ * ((ℓ : ℝ) + a - 1) := add_nonneg S.ht (mul_nonneg S.hτ hx)
  have hα := S.alpha_ge h (by omega)
  have hsτ : τ * ((a : ℝ) - 1) ≤ t + τ * ((ℓ : ℝ) + a - 1) := by
    have : 0 ≤ t + τ * (ℓ : ℝ) := add_nonneg S.ht (mul_nonneg S.hτ (Nat.cast_nonneg ℓ))
    linarith
  have hred := quad_key_red S.hν S.hν1 ℓ a ha (α := 1 - rhoN r t τ (ℓ + a)) (s := t + τ * ((ℓ : ℝ) + a - 1))
    hs S.hτ hα hsτ
  have hp := (S.rho_pos (ℓ + 1)).le
  have p1 : 0 ≤ Wt (quadW ν u) 1 0 ℓ a * (Wt u 2 0 (ℓ + 1) (a - 1) - rhoN r t τ (ℓ + 1) * Wt ν 2 0 (ℓ + 1) (a - 1)) :=
    mul_nonneg nA0 (by linarith)
  have p2 : 0 ≤ (Wt u 2 0 ℓ a - rhoN r t τ (ℓ + 1) * Wt ν 2 0 ℓ a) * Wt (quadW ν u) 1 0 (ℓ + 1) (a - 2) :=
    mul_nonneg (by linarith) nA0''
  have p3 := mul_nonneg hp hred
  have hHV := quadHV_eq r t τ ν ℓ a
  have hW1 := quadW1_eq τ ν ℓ a
  linear_combination p1 + p2 + p3 + (-(rhoN r t τ (ℓ + 1) * Wt ν 2 0 (ℓ + 1) (a - 1))) * hA0 +
    (-(rhoN r t τ (ℓ + 1) * Wt ν 2 0 ℓ a)) * hA0'' +
    (-(2 * quadV t τ ν 1 ℓ a + quadWw τ ν 1 ℓ a - 4 * quadH r t τ ν 1 ℓ a)) * hcc +
    (rhoN r t τ (ℓ + 1) * dd ν (ℓ + 1)) * hHV + (-(rhoN r t τ (ℓ + 1) * dd ν (ℓ + 1))) * hW1

end Key

/-- The kernel nonnegativity in the setting of Theorem 8.11. -/
theorem quad_kernel_nonneg {N : ℕ} {r t τ : ℝ} {ν u : ℕ → ℝ} (S : QuadSetting N r t τ ν u)
    (hd1 : ∀ m, m ≤ N → dd ν m ≤ 1) (hT : dd (quadW ν u) N + dd u N = 1)
    {k : ℕ} (hk : k ≤ N) : ∀ ℓ a, 0 ≤ kerFnV u (quadW ν u) k ℓ a := by
  have hw : ResumWeights2 (dd u) (wA (quadW ν u)) (wB u) (wC u (quadW ν u)) (quadH r t τ ν) (quadV t τ ν)
      (quadWw τ ν) (wSV u (quadW ν u)) N := by
    refine ⟨fun n hn => dd_pos_of S.hu_nn S.hu1 hn, fun j ℓ a hj h => S.A_split h, fun ℓ a h => ?_,
      fun j ℓ a _ => Wt_nonneg_of S.hu_nn _ _ _ _, fun j ℓ a _ => ?_, fun j ℓ a h => S.H_nn h,
      fun j ℓ a _ => S.V_nn j ℓ a, fun j ℓ a _ => S.W_nn j ℓ a, fun ℓ a h => ?_,
      fun j ℓ a hj h => ?_, fun j ℓ a hj h => ?_, fun j ℓ a hj h => ?_, fun j ℓ a hj h => ?_,
      fun j ℓ a hj h => ?_, fun ℓ a h ha => ?_⟩
    · unfold wA; simpa using S.A0_nn h
    · rw [S.wC_eq]; exact Wt_nonneg S.hν _ _ _ _
    · unfold wSV
      have e : dd (quadW ν u) (ℓ + a) + dd u (ℓ + a) = dd ν (ℓ + a) := by
        unfold dd quadW; rw [iterShift_sub]; ring
      linarith [hd1 (ℓ + a) h]
    · have := S.domB (ℓ := ℓ) (a := a) hj h
      unfold wB; rw [show 2 * (j - 1) + 2 = 2 * j by omega]; simpa using this
    · rw [S.wC_eq, S.wC_eq, show 2 * (j - 1) + 2 = 2 * j by omega, show j - 1 + 1 = j by omega]
      have := S.domC (ℓ := ℓ) (a := a) hj h
      unfold wB; simpa using this
    · have := S.domH (ℓ := ℓ) (a := a) hj h
      unfold wB; simpa using this
    · have := S.domV (ℓ := ℓ) (a := a) hj h
      unfold wB; simpa using this
    · have := S.domW (ℓ := ℓ) (a := a) hj h
      unfold wB; simpa using this
    · have := S.key h ha
      unfold wA wB; simpa using this
  exact gkernel_resum2 S.hN hw (genRec_of S.hu_nn S.hu1)
    (fun a => by rw [kerFnV_zero]; split_ifs <;> norm_num) (kerFnV_supp S.hu_nn S.hu1 N hk hT)

/-- Hypotheses of Theorem 8.11: `c_i = (r + t i + τ C(i,2)) d_i` with `r > 0` and `t, τ ≥ 0`, the
diagonal coefficients `b_0 ≤ b_1 ≤ ⋯ ≤ b_N` nondecreasing, and a profile `d = b + c` whose Newton
coefficients are log-concave without internal zeros. -/
def QuadRatioHyp {N : ℕ} (vv : Coefficients N) : Prop :=
  ∃ r t τ : ℝ, 0 < r ∧ 0 ≤ t ∧ 0 ≤ τ ∧ (∀ i, i < N → vv.b i ≤ vv.b (i + 1)) ∧
    (∀ i, i ≤ N → vv.c i = (r + t * i + τ * (i.choose 2 : ℝ)) * profile vv i) ∧
    LogConcaveNoInternalZeros N (newtonCoeff (profile vv))

/-- Theorem 8.11 (convex quadratic ratio), matrix-positivity conclusion. -/
def Stmt_quadratic_ratio : Prop :=
  ∀ (N : ℕ) (vv : Coefficients N), Admissible vv → QuadRatioHyp vv → MatrixPositivity vv

/-- **Theorem 8.11** (convex quadratic ratio). -/
theorem quadratic_ratio_matrix : Stmt_quadratic_ratio := by
  intro N vv hv hyp
  obtain ⟨r, t, τ, hr, ht, hτ, hbmono, hc, hlc⟩ := hyp
  have hv' := hv
  obtain ⟨hN, _, hb0, hc0, haN, hsum, hapos, hcpos⟩ := hv'
  set d := profile vv with hd
  set ν := padNewton N (newtonCoeff d) with hν_def
  set u := padNewton N (newtonCoeff vv.c) with hu_def
  have hd0 : d 0 = 0 := by simp [hd, profile, hb0, hc0]
  have hν0 : ν 0 = 0 := padNewton_zero _ _
  have hν := padNewton_lcnz hlc
  have hν1 : 0 < ν 1 := by rw [hν_def]; unfold padNewton; rw [if_pos ⟨le_rfl, hN⟩]; exact hlc.1
  have hdd : ∀ i, i ≤ N → dd ν i = d i := fun i hi => dd_padNewton d hd0 N i hi
  have hcN : ∀ i, i ≤ N → vv.c i = rhoN r t τ i * dd ν i := fun i hi => by rw [hc i hi, hdd i hi]; rfl
  have hφ : ∀ ℓ n, ℓ + n ≤ N → Szkraw.iterShift u ℓ n = PhiQ r t τ ℓ n (Szkraw.iterShift ν ℓ) := by
    intro ℓ n h
    rw [hu_def, iterShift_padNewton vv.c hc0 N ℓ n h, ← leibniz_quad]
    exact fwdDiff_iter_congr n ℓ fun i _ hi => hcN i (by omega)
  have hw_eq : padNewton N (newtonCoeff vv.b) = quadW ν u := by
    funext i
    unfold quadW
    rw [hν_def, hu_def]
    unfold padNewton
    split_ifs
    · rw [← newtonCoeff_sub]
      exact newtonCoeff_congr fun j _ => by simp [hd, profile]
    · ring
  have hu_nn : ∀ i, 0 ≤ u i := by
    intro i
    by_cases hi : i ≤ N
    · have e : u i = Szkraw.iterShift u 0 i := rfl
      rw [e, hφ 0 i (by omega)]
      exact PhiQ_nonneg hr ht hτ (fun k => iterShift_nonneg hν 0 k) 0 i
    · rw [hu_def]; unfold padNewton; rw [if_neg (by omega)]
  have hddc : ∀ i, i ≤ N → dd u i = vv.c i := fun i hi => dd_padNewton vv.c hc0 N i hi
  have hddb : ∀ i, i ≤ N → dd (quadW ν u) i = vv.b i := fun i hi => by
    rw [← hw_eq]; exact dd_padNewton vv.b hb0 N i hi
  have S : QuadSetting N r t τ ν u := by
    refine ⟨hN, hr, ht, hτ, hν, hν0, hν1, hu_nn, hφ, fun m hm => ?_⟩
    rw [hddb m hm.le, hddb (m + 1) hm]; exact hbmono m hm
  have hd1 : ∀ m, m ≤ N → dd ν m ≤ 1 := fun m hm => by
    rw [hdd m hm, hd]
    unfold profile
    have := hsum m hm
    rcases Nat.lt_or_ge m N with h | h
    · linarith [hapos m h]
    · rw [show m = N by omega] at this ⊢; rw [haN] at this; linarith
  have hT : dd (quadW ν u) N + dd u N = 1 := by
    rw [hddb N le_rfl, hddc N le_rfl]; have := hsum N le_rfl; rw [haN] at this; linarith
  exact matrixPositivity_of_kernel vv hv hu_nn S.hu1 (padNewton_zero _ _) hddc hddb
    (fun k hk => quad_kernel_nonneg S hd1 hT hk)

theorem rhoN_mono {r t τ : ℝ} (ht : 0 ≤ t) (hτ : 0 ≤ τ) {i j : ℕ} (h : i ≤ j) : rhoN r t τ i ≤ rhoN r t τ j := by
  unfold rhoN
  have hij : (i : ℝ) ≤ j := by exact_mod_cast h
  have hc : (i.choose 2 : ℝ) ≤ (j.choose 2 : ℝ) := by exact_mod_cast Nat.choose_le_choose 2 h
  have := mul_le_mul_of_nonneg_left hij ht
  have := mul_le_mul_of_nonneg_left hc hτ
  linarith

/-- **After Theorem 8.11**: for the arrays of Theorem 8.11 without the monotonicity hypothesis, `b` is
nondecreasing exactly when `t(N+R) + τ(C(N,2) + (N-1)R) ≤ 1 - r`, where `R = d_{N-1}/(1 - d_{N-1})`. The assumption `r > 0` is not needed. -/
theorem quadratic_bmono_iff {N : ℕ} (vv : Coefficients N) (hv : Admissible vv) {r t τ : ℝ}
    (ht : 0 ≤ t) (hτ : 0 ≤ τ)
    (hc : ∀ i, i ≤ N → vv.c i = (r + t * i + τ * (i.choose 2 : ℝ)) * profile vv i)
    (hlc : LogConcaveNoInternalZeros N (newtonCoeff (profile vv))) :
    (∀ i, i < N → vv.b i ≤ vv.b (i + 1)) ↔
      t * (N + profile vv (N - 1) / (1 - profile vv (N - 1))) +
        τ * ((N.choose 2 : ℝ) + ((N : ℝ) - 1) * (profile vv (N - 1) / (1 - profile vv (N - 1)))) ≤ 1 - r := by
  obtain ⟨hN, _, hb0, hc0, haN, hsum, hapos, hcpos⟩ := hv
  set d := profile vv with hd
  set ν := padNewton N (newtonCoeff d) with hν_def
  have hd0 : d 0 = 0 := by simp [hd, profile, hb0, hc0]
  have hν := padNewton_lcnz hlc
  have hν1 : 0 < ν 1 := by rw [hν_def]; unfold padNewton; rw [if_pos ⟨le_rfl, hN⟩]; exact hlc.1
  have hdd : ∀ i, i ≤ N → dd ν i = d i := fun i hi => dd_padNewton d hd0 N i hi
  have hfpos : ∀ i, 0 < Szkraw.iterShift ν i 1 := iterShift_one_pos hν hν1
  have hf : ∀ i, i < N → d (i + 1) - d i = Szkraw.iterShift ν i 1 := fun i hi => by
    have e1 : dd ν (i + 1) = dd ν i + Szkraw.iterShift ν i 1 := rfl
    rw [← hdd (i + 1) hi, ← hdd i hi.le, e1]; ring
  have hg : ∀ i : ℕ, rhoN r t τ (i + 1) - rhoN r t τ i = t + τ * i := fun i => by
    rw [rhoN_add r t τ i 1, Nat.choose_eq_zero_of_lt (show 1 < 2 by norm_num)]; push_cast; ring
  have hbv : ∀ i, i ≤ N → vv.b i = (1 - rhoN r t τ i) * d i := fun i hi => by
    have e : vv.b i = d i - vv.c i := by simp [hd, profile]
    rw [e, hc i hi]; unfold rhoN; ring
  -- `b_{i+1} - b_i = (1 - ρ(i+1)) f₁(i) - Δρ(i) d_i`
  have hinc : ∀ i, i < N → vv.b (i + 1) - vv.b i =
      (1 - rhoN r t τ (i + 1)) * Szkraw.iterShift ν i 1 - (t + τ * i) * d i := fun i hi => by
    rw [hbv (i + 1) hi, hbv i hi.le, ← hf i hi, ← hg i]; ring
  have hR : ∀ i, i ≤ N - 1 → d i * Szkraw.iterShift ν (N - 1) 1 ≤ d (N - 1) * Szkraw.iterShift ν i 1 := by
    intro i hi
    have hch := R_chain_of hν hν1 i (N - 1 - i)
    rw [show i + (N - 1 - i) = N - 1 by omega, hdd i (by omega), hdd (N - 1) (by omega)] at hch
    exact hch
  have hNm : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by push_cast [Nat.cast_sub (show 1 ≤ N by omega)]; ring
  have hdN : d N = 1 := by have := hsum N le_rfl; rw [haN] at this; simp [hd, profile]; linarith
  have hd1 : 1 - d (N - 1) = Szkraw.iterShift ν (N - 1) 1 := by
    have := hf (N - 1) (by omega)
    rw [show N - 1 + 1 = N by omega, hdN] at this; exact this
  have hPpos : 0 < 1 - d (N - 1) := by rw [hd1]; exact hfpos _
  -- the last increment is nonnegative exactly when the stated inequality holds
  have hlast : (0 ≤ vv.b N - vv.b (N - 1)) ↔
      t * (N + d (N - 1) / (1 - d (N - 1))) +
        τ * ((N.choose 2 : ℝ) + ((N : ℝ) - 1) * (d (N - 1) / (1 - d (N - 1)))) ≤ 1 - r := by
    have hi := hinc (N - 1) (by omega)
    rw [show N - 1 + 1 = N by omega, hNm, ← hd1] at hi
    rw [hi]
    have key : t * (N + d (N - 1) / (1 - d (N - 1))) +
        τ * ((N.choose 2 : ℝ) + ((N : ℝ) - 1) * (d (N - 1) / (1 - d (N - 1)))) - (1 - r) =
        -((1 - rhoN r t τ N) * (1 - d (N - 1)) - (t + τ * ((N : ℝ) - 1)) * d (N - 1)) / (1 - d (N - 1)) := by
      have hne := hPpos.ne'
      unfold rhoN
      field_simp; ring
    constructor
    · intro h
      have : t * (N + d (N - 1) / (1 - d (N - 1))) +
          τ * ((N.choose 2 : ℝ) + ((N : ℝ) - 1) * (d (N - 1) / (1 - d (N - 1)))) - (1 - r) ≤ 0 := by
        rw [key, neg_div]; exact neg_nonpos.mpr (div_nonneg h hPpos.le)
      linarith
    · intro h
      have : -((1 - rhoN r t τ N) * (1 - d (N - 1)) - (t + τ * ((N : ℝ) - 1)) * d (N - 1)) /
          (1 - d (N - 1)) ≤ 0 := by
        rw [← key]; linarith
      rw [neg_div, neg_nonpos] at this
      by_contra hneg; push Not at hneg
      have := div_neg_of_neg_of_pos hneg hPpos; linarith
  constructor
  · intro hb
    have h1' := hb (N - 1) (by omega)
    rw [show N - 1 + 1 = N by omega] at h1'
    exact hlast.mp (by linarith)
  · intro hk i hi
    have hl := hlast.mpr hk
    have hl' := hinc (N - 1) (by omega)
    rw [show N - 1 + 1 = N by omega, hNm] at hl'
    have hA : (t + τ * ((N : ℝ) - 1)) * d (N - 1) ≤ (1 - rhoN r t τ N) * Szkraw.iterShift ν (N - 1) 1 := by
      linarith
    have hch := hR i (by omega)
    have hfi := hfpos i
    have hfN := hfpos (N - 1)
    have hdN1 : 0 ≤ d (N - 1) := by rw [← hdd (N - 1) (by omega)]; exact iterShift_nonneg hν _ 0
    have hiN : (i : ℝ) ≤ (N : ℝ) - 1 := by rw [← hNm]; exact_mod_cast (show i ≤ N - 1 by omega)
    have hρ : rhoN r t τ (i + 1) ≤ rhoN r t τ N := rhoN_mono ht hτ (by omega)
    have hti : 0 ≤ t + τ * (i : ℝ) := by positivity
    -- `Δρ(i) d_i f₁(N-1) ≤ Δρ(N-1) d_{N-1} f₁(i) ≤ (1 - ρ(N)) f₁(N-1) f₁(i)`
    have k1 : (t + τ * (i : ℝ)) * (d i * Szkraw.iterShift ν (N - 1) 1) ≤
        (t + τ * (i : ℝ)) * (d (N - 1) * Szkraw.iterShift ν i 1) := mul_le_mul_of_nonneg_left hch hti
    have k2 : (t + τ * (i : ℝ)) * d (N - 1) ≤ (t + τ * ((N : ℝ) - 1)) * d (N - 1) :=
      mul_le_mul_of_nonneg_right (by nlinarith) hdN1
    have k3 : (t + τ * (i : ℝ)) * d i * Szkraw.iterShift ν (N - 1) 1 ≤
        (1 - rhoN r t τ (i + 1)) * Szkraw.iterShift ν i 1 * Szkraw.iterShift ν (N - 1) 1 := by
      have a1 := mul_le_mul_of_nonneg_right k2 hfi.le
      have a2 := mul_le_mul_of_nonneg_right hA hfi.le
      have a3 : (1 - rhoN r t τ N) * Szkraw.iterShift ν (N - 1) 1 * Szkraw.iterShift ν i 1 ≤
          (1 - rhoN r t τ (i + 1)) * Szkraw.iterShift ν (N - 1) 1 * Szkraw.iterShift ν i 1 :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) hfN.le) hfi.le
      nlinarith
    have k4 := le_of_mul_le_mul_right k3 hfN
    have := hinc i hi
    linarith

end Szkraw
