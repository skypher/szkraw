import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
# The logarithmic potential of `[0,1]`

`U(x) = ∫_0^1 log|x - t| dt` defines the region `Ω = {U ≤ -1}` of the Nörlund–Rice bound
(Lemma 9.5). This file proves the closed form of `U`, its continuity, its values on `[0,1]`, its
growth at infinity, and the Riemann-sum lower bound `Σ_{k=0}^N log|x - k/N| ≥ N U(x) - 1/d + log d`
for `x` at distance at least `d` from `[0,1]`.
-/

namespace Szkraw

open Complex MeasureTheory intervalIntegral Set Finset Filter Topology
open scoped Interval

/-- The logarithmic potential `U(x) = ∫_0^1 log|x - t| dt`. -/
noncomputable def Ulog (x : ℂ) : ℝ := ∫ t : ℝ in (0 : ℝ)..1, Real.log ‖x - t‖

theorem log_norm_sub_ofReal (x : ℂ) (t : ℝ) :
    Real.log ‖x - t‖ = Real.log ((t - x.re) ^ 2 + x.im ^ 2) / 2 := by
  rw [norm_eq_sqrt_sq_add_sq, Real.log_sqrt (by positivity)]
  congr 2
  simp only [sub_re, ofReal_re, sub_im, ofReal_im, sub_zero]
  ring

theorem Ulog_eq_of_im_ne (x : ℂ) (hb : x.im ≠ 0) :
    Ulog x = x.re * Real.log ‖x‖ + (1 - x.re) * Real.log ‖x - 1‖ - 1 +
      x.im * (Real.arctan ((1 - x.re) / x.im) + Real.arctan (x.re / x.im)) := by
  set a := x.re
  set b := x.im
  have hb2 : 0 < b ^ 2 := by positivity
  have hQ : ∀ t : ℝ, 0 < (t - a) ^ 2 + b ^ 2 := fun t => by positivity
  have hderiv : ∀ t : ℝ, HasDerivAt (fun t : ℝ => (t - a) * (Real.log ((t - a) ^ 2 + b ^ 2) / 2) - (t - a) +
      b * Real.arctan ((t - a) / b)) (Real.log ((t - a) ^ 2 + b ^ 2) / 2) t := by
    intro t
    have h0 : HasDerivAt (fun t : ℝ => t - a) 1 t := (hasDerivAt_id' t).sub_const a
    have h1 : HasDerivAt (fun t : ℝ => (t - a) ^ 2 + b ^ 2) (2 * (t - a)) t :=
      ((h0.pow 2).add_const (b ^ 2)).congr_deriv (by ring)
    have h2 := (h0.mul ((h1.log (hQ t).ne').div_const 2)).sub h0
    have h3 := (h0.div_const b).arctan.const_mul b
    refine (h2.add h3).congr_deriv ?_
    have hQt := (hQ t).ne'
    field_simp
    ring
  have hcont : Continuous fun t : ℝ => Real.log ((t - a) ^ 2 + b ^ 2) / 2 :=
    ((Continuous.log (by fun_prop) fun t => (hQ t).ne').div_const 2)
  have hint := integral_eq_sub_of_hasDerivAt (fun t _ => hderiv t) (hcont.intervalIntegrable 0 1)
  have e : Ulog x = ∫ t : ℝ in (0 : ℝ)..1, Real.log ((t - a) ^ 2 + b ^ 2) / 2 :=
    integral_congr fun t _ => log_norm_sub_ofReal x t
  have e0 : Real.log ‖x‖ = Real.log ((0 - a) ^ 2 + b ^ 2) / 2 := by
    rw [← log_norm_sub_ofReal x 0]; simp
  have e1 : Real.log ‖x - 1‖ = Real.log ((1 - a) ^ 2 + b ^ 2) / 2 := by
    rw [← log_norm_sub_ofReal x 1]; simp
  rw [e, hint, e0, e1, zero_sub, neg_div, Real.arctan_neg]
  ring

theorem Ulog_eq_of_im_eq (x : ℂ) (hb : x.im = 0) :
    Ulog x = x.re * Real.log ‖x‖ + (1 - x.re) * Real.log ‖x - 1‖ - 1 := by
  set a := x.re
  have hpt : ∀ t : ℝ, Real.log ‖x - t‖ = Real.log (a - t) := by
    intro t
    rw [log_norm_sub_ofReal, hb, zero_pow two_ne_zero, add_zero, Real.log_pow,
      show t - a = -(a - t) by ring, Real.log_neg_eq_log]
    push_cast; ring
  have e : Ulog x = ∫ t : ℝ in (0 : ℝ)..1, Real.log (a - t) := integral_congr fun t _ => hpt t
  have e0 : Real.log ‖x‖ = Real.log (a - 0) := by rw [← hpt 0]; simp
  have e1 : Real.log ‖x - 1‖ = Real.log (a - 1) := by rw [← hpt 1]; simp
  rw [e, intervalIntegral.integral_comp_sub_left (fun s => Real.log s), integral_log, e0, e1,
    show a - 1 = -(1 - a) by ring, Real.log_neg_eq_log]
  ring

/-- **Closed form of `U`.** -/
theorem Ulog_eq (x : ℂ) :
    Ulog x = x.re * Real.log ‖x‖ + (1 - x.re) * Real.log ‖x - 1‖ - 1 +
      x.im * (Real.arctan ((1 - x.re) / x.im) + Real.arctan (x.re / x.im)) := by
  by_cases hb : x.im = 0
  · rw [Ulog_eq_of_im_eq x hb, hb, zero_mul, add_zero]
  · exact Ulog_eq_of_im_ne x hb

theorem continuousAt_of_abs_le {φ g : ℂ → ℝ} {x₀ : ℂ} (hg : ContinuousAt g x₀) (hg0 : g x₀ = 0)
    (hφ0 : φ x₀ = 0) (hle : ∀ x, |φ x| ≤ |g x|) : ContinuousAt φ x₀ := by
  unfold ContinuousAt
  rw [hφ0]
  have : Tendsto (fun x => |g x|) (𝓝 x₀) (𝓝 0) := by
    have := hg.tendsto.abs
    rwa [hg0, abs_zero] at this
  exact squeeze_zero_norm (fun x => by rw [Real.norm_eq_abs]; exact hle x) this

theorem continuous_re_mul_log : Continuous fun x : ℂ => x.re * Real.log ‖x‖ := by
  rw [continuous_iff_continuousAt]
  intro x₀
  by_cases hx0 : x₀ = 0
  · subst hx0
    refine continuousAt_of_abs_le (g := fun x => ‖x‖ * Real.log ‖x‖)
      (Real.continuous_mul_log.comp continuous_norm).continuousAt (by simp) (by simp) fun x => ?_
    rw [abs_mul, abs_mul, abs_norm]
    exact mul_le_mul_of_nonneg_right (abs_re_le_norm x) (abs_nonneg _)
  · exact continuous_re.continuousAt.mul (continuous_norm.continuousAt.log (norm_ne_zero_iff.mpr hx0))

theorem abs_arctan_le (y : ℝ) : |Real.arctan y| ≤ Real.pi / 2 :=
  abs_le.mpr ⟨(Real.neg_pi_div_two_lt_arctan y).le, (Real.arctan_lt_pi_div_two y).le⟩

theorem continuous_im_mul_arctan :
    Continuous fun x : ℂ => x.im * (Real.arctan ((1 - x.re) / x.im) + Real.arctan (x.re / x.im)) := by
  rw [continuous_iff_continuousAt]
  intro x₀
  by_cases hb : x₀.im = 0
  · refine continuousAt_of_abs_le (g := fun x => Real.pi * x.im) (by fun_prop) (by simp [hb]) (by simp [hb])
      fun x => ?_
    rw [abs_mul, abs_mul, abs_of_pos Real.pi_pos, mul_comm Real.pi]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    calc _ ≤ |Real.arctan ((1 - x.re) / x.im)| + |Real.arctan (x.re / x.im)| := abs_add_le _ _
      _ ≤ Real.pi / 2 + Real.pi / 2 := add_le_add (abs_arctan_le _) (abs_arctan_le _)
      _ = Real.pi := by ring
  · have h1 : ContinuousAt (fun x : ℂ => (1 - x.re) / x.im) x₀ :=
      ((continuous_const.sub continuous_re).continuousAt).div continuous_im.continuousAt hb
    have h2 : ContinuousAt (fun x : ℂ => x.re / x.im) x₀ :=
      continuous_re.continuousAt.div continuous_im.continuousAt hb
    exact continuous_im.continuousAt.mul ((Real.continuous_arctan.continuousAt.comp h1).add
      (Real.continuous_arctan.continuousAt.comp h2))

/-- `U` is continuous. -/
theorem continuous_Ulog : Continuous Ulog := by
  have e : Ulog = fun x => x.re * Real.log ‖x‖ - (x - 1).re * Real.log ‖x - 1‖ - 1 +
      x.im * (Real.arctan ((1 - x.re) / x.im) + Real.arctan (x.re / x.im)) := by
    funext x; rw [Ulog_eq, sub_re, one_re]; ring
  rw [e]
  exact ((continuous_re_mul_log.sub (continuous_re_mul_log.comp (continuous_id.sub continuous_const))).sub
    continuous_const).add continuous_im_mul_arctan

theorem Ulog_ofReal (t : ℝ) : Ulog t = t * Real.log t + (1 - t) * Real.log (1 - t) - 1 := by
  rw [Ulog_eq_of_im_eq _ (ofReal_im t), ofReal_re, norm_real, Real.norm_eq_abs, Real.log_abs,
    show (t : ℂ) - 1 = ((t - 1 : ℝ) : ℂ) by push_cast; ring, norm_real, Real.norm_eq_abs, Real.log_abs,
    show t - 1 = -(1 - t) by ring, Real.log_neg_eq_log]

/-- `U ≤ -1` on `[0,1]`. -/
theorem Ulog_le_of_mem {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : Ulog t ≤ -1 := by
  rw [Ulog_ofReal]
  have := Real.mul_log_nonpos ht0 ht1
  have := Real.mul_log_nonpos (by linarith : 0 ≤ 1 - t) (by linarith : 1 - t ≤ 1)
  linarith

theorem contOn_log_norm_sub {x : ℂ} {s : Set ℝ} (hx : ∀ t ∈ s, x ≠ t) :
    ContinuousOn (fun t : ℝ => Real.log ‖x - t‖) s := fun t ht =>
  ((show Continuous fun t : ℝ => x - (t : ℂ) by fun_prop).norm.continuousAt.log
    (by rw [norm_ne_zero_iff, sub_ne_zero]; exact hx t ht)).continuousWithinAt

/-- If `x` stays at distance at least `m > 0` from `[0,1]`, then `U(x) ≥ log m`. -/
theorem log_le_Ulog {x : ℂ} {m : ℝ} (hm : 0 < m) (hx : ∀ t ∈ Icc (0 : ℝ) 1, m ≤ ‖x - t‖) :
    Real.log m ≤ Ulog x := by
  have hne : ∀ t ∈ Icc (0 : ℝ) 1, x ≠ t := fun t ht h => by
    have := hx t ht; rw [h, sub_self, norm_zero] at this; linarith
  have := intervalIntegral.integral_mono_on zero_le_one
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => Real.log m) volume 0 1)
    ((contOn_log_norm_sub hne).intervalIntegrable_of_Icc zero_le_one)
    fun t ht => Real.log_le_log hm (hx t ht)
  simpa [Ulog] using this

/-- Sublevel sets of `U` are bounded. -/
theorem norm_le_of_Ulog_le {x : ℂ} {c : ℝ} (h : Ulog x ≤ c) : ‖x‖ ≤ 1 + Real.exp c := by
  by_contra hlt
  push Not at hlt
  have hm : 0 < ‖x‖ - 1 := by linarith [Real.exp_pos c]
  have hU := log_le_Ulog hm fun t ht => by
    have := norm_sub_norm_le x t
    rw [norm_real, Real.norm_eq_abs, abs_of_nonneg ht.1] at this
    linarith [ht.2]
  have : c < Real.log (‖x‖ - 1) := by rw [Real.lt_log_iff_exp_lt hm]; linarith
  linarith

/-- Lipschitz bound for `t ↦ log|x - t|` away from `x`. -/
theorem log_norm_sub_le {x : ℂ} {d : ℝ} (hd : 0 < d) {s t : ℝ} (hs : d ≤ ‖x - s‖) (ht : d ≤ ‖x - t‖) :
    Real.log ‖x - t‖ ≤ Real.log ‖x - s‖ + |t - s| / d := by
  have hs0 : 0 < ‖x - s‖ := lt_of_lt_of_le hd hs
  have ht0 : 0 < ‖x - t‖ := lt_of_lt_of_le hd ht
  have h1 := Real.log_le_sub_one_of_pos (div_pos ht0 hs0)
  rw [Real.log_div ht0.ne' hs0.ne'] at h1
  have h2 : ‖x - t‖ - ‖x - s‖ ≤ |t - s| := by
    have := norm_sub_norm_le (x - t) (x - s)
    rwa [show x - t - (x - s) = ((s - t : ℝ) : ℂ) by push_cast; ring, norm_real, Real.norm_eq_abs,
      abs_sub_comm] at this
  have h3 : ‖x - t‖ / ‖x - s‖ - 1 ≤ |t - s| / d := by
    rw [div_sub_one hs0.ne']
    calc (‖x - t‖ - ‖x - s‖) / ‖x - s‖ ≤ |t - s| / ‖x - s‖ := div_le_div_of_nonneg_right h2 hs0.le
      _ ≤ |t - s| / d := div_le_div_of_nonneg_left (abs_nonneg _) hd hs
  linarith

/-- **Riemann-sum lower bound**: if `x` stays at distance at least `d > 0` from `[0,1]`, then
`Σ_{k=0}^N log|x - k/N| ≥ N U(x) - 1/d + log d`. -/
theorem riemann_lower {x : ℂ} {d : ℝ} (hd : 0 < d) (hx : ∀ t ∈ Icc (0 : ℝ) 1, d ≤ ‖x - t‖) {N : ℕ}
    (hN : 1 ≤ N) :
    N * Ulog x - 1 / d + Real.log d ≤ ∑ k ∈ range (N + 1), Real.log ‖x - (k : ℂ) / N‖ := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hne : ∀ t ∈ Icc (0 : ℝ) 1, x ≠ t := fun t ht h => by
    have := hx t ht; rw [h, sub_self, norm_zero] at this; linarith
  have hcont := contOn_log_norm_sub hne
  set a : ℕ → ℝ := fun k => (k : ℝ) / N
  have ha : ∀ k ≤ N, a k ∈ Icc (0 : ℝ) 1 := fun k hk =>
    ⟨by positivity, by rw [div_le_one hN0]; exact_mod_cast hk⟩
  have hsub : ∀ k < N, Icc (a k) (a (k + 1)) ⊆ Icc 0 1 := fun k hk =>
    Icc_subset_Icc (ha k hk.le).1 (ha (k + 1) hk).2
  have hle : ∀ k < N, a k ≤ a (k + 1) := fun k _ => by
    simp only [a]; gcongr; linarith
  have hint : ∀ k < N, IntervalIntegrable (fun t : ℝ => Real.log ‖x - t‖) volume (a k) (a (k + 1)) :=
    fun k hk => (hcont.mono (hsub k hk)).intervalIntegrable_of_Icc (hle k hk)
  have hU : Ulog x = ∑ k ∈ range N, ∫ t : ℝ in a k..a (k + 1), Real.log ‖x - t‖ := by
    rw [sum_integral_adjacent_intervals hint]
    simp only [a, Nat.cast_zero, zero_div, div_self hN0.ne']
    rfl
  -- each piece is at most `(log|x - (k+1)/N| + 1/(dN))/N`
  have hpiece : ∀ k < N, ∫ t : ℝ in a k..a (k + 1), Real.log ‖x - t‖ ≤
      (Real.log ‖x - (a (k + 1) : ℂ)‖ + 1 / (d * N)) / N := by
    intro k hk
    have := intervalIntegral.integral_mono_on (hle k hk) (hint k hk)
      (intervalIntegrable_const :
        IntervalIntegrable (fun _ : ℝ => Real.log ‖x - (a (k + 1) : ℂ)‖ + 1 / (d * N)) volume _ _)
      fun t ht => by
        have h1 := log_norm_sub_le hd (hx _ (ha (k + 1) hk)) (hx t (hsub k hk ht))
        have h2 : |t - a (k + 1)| ≤ 1 / N := by
          rw [abs_sub_comm, abs_of_nonneg (by linarith [ht.2])]
          have : a (k + 1) - a k = 1 / N := by simp only [a]; push_cast; ring
          linarith [ht.1]
        have h3 : |t - a (k + 1)| / d ≤ 1 / (d * N) := by
          rw [div_le_iff₀ hd]
          calc |t - a (k + 1)| ≤ 1 / N := h2
            _ = 1 / (d * N) * d := by field_simp
        linarith
    rw [intervalIntegral.integral_const, smul_eq_mul] at this
    have e : a (k + 1) - a k = 1 / N := by simp only [a]; push_cast; ring
    rw [e] at this
    calc _ ≤ 1 / N * (Real.log ‖x - (a (k + 1) : ℂ)‖ + 1 / (d * N)) := this
      _ = _ := by ring
  have hsum : Ulog x ≤ ∑ k ∈ range N, (Real.log ‖x - (a (k + 1) : ℂ)‖ + 1 / (d * N)) / N := by
    rw [hU]; exact sum_le_sum fun k hk => hpiece k (mem_range.mp hk)
  rw [← sum_div, sum_add_distrib, sum_const, card_range, nsmul_eq_mul, le_div_iff₀ hN0] at hsum
  have hc : (N : ℝ) * (1 / (d * N)) = 1 / d := by field_simp
  rw [hc] at hsum
  have h0 : Real.log d ≤ Real.log ‖x - (((0 : ℕ) : ℂ) / N)‖ := by
    have := hx 0 ⟨le_rfl, zero_le_one⟩
    rw [ofReal_zero] at this
    rw [Nat.cast_zero, zero_div]
    exact Real.log_le_log hd this
  have e : ∀ k ∈ range N, Real.log ‖x - (a (k + 1) : ℂ)‖ = Real.log ‖x - ((k + 1 : ℕ) : ℂ) / N‖ := by
    intro k _; simp only [a]; push_cast; rfl
  rw [sum_congr rfl e] at hsum
  rw [sum_range_succ']
  linarith

end Szkraw
