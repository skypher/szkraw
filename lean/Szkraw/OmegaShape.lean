import Szkraw.NorlundU
import Mathlib.Analysis.SpecialFunctions.Complex.Arctan
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# The shape of `Ω = {U ≤ -1}` (Section 9, before Lemma 9.5)

The paper describes `Ω`: it contains `[0,1]`, has nonanalytic boundary points with vertical
tangents at `0` and `1`, and meets the line `Re x = 1/2` at `Im x = ±0.26276…`.

* `Ulog_conj`, `Ulog_one_sub`: `U` is symmetric under `x ↦ x̄` and `x ↦ 1 - x`.
* `omega_half_line`: `1/2 + iy ∈ Ω` iff `|y| ≤ y₀`, for some `0.26276 < y₀ < 0.26277`.
-/

namespace Szkraw

open Complex Finset Filter Topology

/-- The region `Ω = {U ≤ -1}`. -/
def Omega : Set ℂ := {x | Ulog x ≤ -1}

theorem Ulog_conj (x : ℂ) : Ulog (starRingEnd ℂ x) = Ulog x := by
  unfold Ulog
  refine intervalIntegral.integral_congr fun t _ => ?_
  rw [← Complex.conj_ofReal t, ← map_sub, Complex.norm_conj, Complex.conj_ofReal]

theorem Ulog_one_sub (x : ℂ) : Ulog (1 - x) = Ulog x := by
  unfold Ulog
  have h := intervalIntegral.integral_comp_sub_left (a := 0) (b := 1) (fun s : ℝ => Real.log ‖x - s‖) 1
  simp only [sub_zero, sub_self] at h
  rw [← h]
  refine intervalIntegral.integral_congr fun t _ => ?_
  rw [← norm_neg]
  congr 2
  push_cast
  ring

/-! ### The line `Re x = 1/2` -/

/-- `k(y) = ½ log(¼ + y²) + π y - 2y arctan(2y)`; `U(1/2 + iy) = k(|y|) - 1`. -/
noncomputable def kHalf (y : ℝ) : ℝ :=
  Real.log (1 / 4 + y ^ 2) / 2 + Real.pi * y - 2 * y * Real.arctan (2 * y)

theorem log_norm_re_im (x b : ℝ) : Real.log ‖(x : ℂ) + b * I‖ = Real.log (x ^ 2 + b ^ 2) / 2 := by
  rw [norm_eq_sqrt_sq_add_sq, Real.log_sqrt (by positivity)]
  simp

theorem Ulog_half (y : ℝ) : Ulog (1 / 2 + y * I) = kHalf |y| - 1 := by
  rw [Ulog_eq]
  have hre : ((1 / 2 : ℂ) + y * I).re = 1 / 2 := by simp
  have him : ((1 / 2 : ℂ) + y * I).im = y := by simp
  have e1 : Real.log ‖(1 / 2 : ℂ) + y * I‖ = Real.log (1 / 4 + y ^ 2) / 2 := by
    rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; rfl, log_norm_re_im]; norm_num
  have e2 : Real.log ‖(1 / 2 : ℂ) + y * I - 1‖ = Real.log (1 / 4 + y ^ 2) / 2 := by
    rw [show (1 / 2 : ℂ) + y * I - 1 = ((-1 / 2 : ℝ) : ℂ) + y * I by push_cast; ring, log_norm_re_im]
    norm_num
  rw [hre, him, e1, e2, kHalf]
  rcases lt_trichotomy y 0 with hy | hy | hy
  · have h2 : 0 < 2 * -y := by linarith
    have ha : Real.arctan ((1 - 1 / 2) / y) = -(Real.pi / 2 - Real.arctan (2 * -y)) := by
      rw [← Real.arctan_inv_of_pos h2, ← Real.arctan_neg]; congr 1; field_simp; ring
    have hb : Real.arctan (1 / 2 / y) = Real.arctan ((1 - 1 / 2) / y) := by norm_num
    rw [hb, ha, abs_of_neg hy]
    ring_nf
  · subst hy; simp; ring
  · have h2 : 0 < 2 * y := by linarith
    have ha : Real.arctan ((1 - 1 / 2) / y) = Real.pi / 2 - Real.arctan (2 * y) := by
      rw [← Real.arctan_inv_of_pos h2]; congr 1; field_simp; ring
    have hb : Real.arctan (1 / 2 / y) = Real.arctan ((1 - 1 / 2) / y) := by norm_num
    rw [hb, ha, abs_of_pos hy]
    ring

theorem kHalf_hasDerivAt (y : ℝ) : HasDerivAt kHalf (Real.pi - 2 * Real.arctan (2 * y)) y := by
  have hQ : 0 < 1 / 4 + y ^ 2 := by positivity
  have h0 : HasDerivAt (fun y : ℝ => 1 / 4 + y ^ 2) (2 * y) y :=
    ((hasDerivAt_pow 2 y).const_add (1 / 4)).congr_deriv (by ring)
  have h1 := (h0.log hQ.ne').div_const 2
  have h2 := (hasDerivAt_id' y).const_mul Real.pi
  have h3 := ((hasDerivAt_id' y).const_mul 2).mul (((hasDerivAt_id' y).const_mul 2).arctan)
  refine ((h1.add h2).sub h3).congr_deriv ?_
  have : (1 : ℝ) + (2 * y) ^ 2 ≠ 0 := by positivity
  field_simp
  ring

theorem kHalf_strictMono : StrictMono kHalf :=
  strictMono_of_deriv_pos fun y => by
    rw [(kHalf_hasDerivAt y).deriv]
    linarith [Real.arctan_lt_pi_div_two (2 * y)]

/-- Alternating-series bounds for `arctan x`, `0 ≤ x < 1`. -/
theorem arctan_series_bounds {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) (k : ℕ) :
    ∑ i ∈ range (2 * k), (-1) ^ i * (x ^ (2 * i + 1) / (2 * i + 1)) ≤ Real.arctan x ∧
      Real.arctan x ≤ ∑ i ∈ range (2 * k + 1), (-1) ^ i * (x ^ (2 * i + 1) / (2 * i + 1)) := by
  have hs := Real.hasSum_arctan (x := x) (by rw [Real.norm_eq_abs, abs_of_nonneg hx0]; exact hx1)
  have ht : Tendsto (fun n => ∑ i ∈ range n, (-1) ^ i * (x ^ (2 * i + 1) / (2 * i + 1)))
      atTop (𝓝 (Real.arctan x)) := by
    have := hs.tendsto_sum_nat
    simp only [mul_div_assoc] at this
    convert this using 3
    push_cast; ring
  have hanti : Antitone fun i : ℕ => x ^ (2 * i + 1) / (2 * i + 1) := by
    refine antitone_nat_of_succ_le fun n => ?_
    apply div_le_div₀ (by positivity) (pow_le_pow_of_le_one hx0 hx1.le (by omega)) (by positivity)
    push_cast; linarith
  exact ⟨hanti.alternating_series_le_tendsto ht k, hanti.tendsto_le_alternating_series ht k⟩

theorem kHalf_lower : kHalf (26276 / 100000) < 0 := by
  have hlog := Real.abs_log_sub_add_sum_range_le (x := -(43151761 / 156250000)) (by norm_num) 12
  rw [abs_le] at hlog
  simp only [sum_range_succ, sum_range_zero] at hlog
  norm_num at hlog
  have harc := (arctan_series_bounds (x := 6569 / 12500) (by norm_num) (by norm_num) 5).1
  simp only [sum_range_succ, sum_range_zero] at harc
  norm_num at harc
  have hq : (1 / 4 + (26276 / 100000 : ℝ) ^ 2) = (199401761 / 156250000) / 4 := by norm_num
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  have l2 := Real.log_two_gt_d9
  have hpi := Real.pi_lt_d6
  norm_num at l2 hpi
  rw [kHalf, hq, Real.log_div (by norm_num) (by norm_num), h4,
    show 2 * (26276 / 100000 : ℝ) = 6569 / 12500 by norm_num]
  nlinarith [hlog.1, hlog.2]

theorem kHalf_upper : 0 < kHalf (26277 / 100000) := by
  have hlog := Real.abs_log_sub_add_sum_range_le (x := -(690480729 / 2500000000)) (by norm_num) 12
  rw [abs_le] at hlog
  simp only [sum_range_succ, sum_range_zero] at hlog
  norm_num at hlog
  have harc := (arctan_series_bounds (x := 26277 / 50000) (by norm_num) (by norm_num) 5).2
  simp only [sum_range_succ, sum_range_zero] at harc
  norm_num at harc
  have hq : (1 / 4 + (26277 / 100000 : ℝ) ^ 2) = (3190480729 / 2500000000) / 4 := by norm_num
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  have l2 := Real.log_two_lt_d9
  have hpi := Real.pi_gt_d6
  norm_num at l2 hpi
  rw [kHalf, hq, Real.log_div (by norm_num) (by norm_num), h4,
    show 2 * (26277 / 100000 : ℝ) = 26277 / 50000 by norm_num]
  nlinarith [hlog.1, hlog.2]

/-- **`Ω` on the line `Re x = 1/2`**: there is `y₀` with `0.26276 < y₀ < 0.26277` such that
`1/2 + iy ∈ Ω` iff `|y| ≤ y₀`. -/
theorem omega_half_line :
    ∃ y₀ : ℝ, 26276 / 100000 < y₀ ∧ y₀ < 26277 / 100000 ∧
      ∀ y : ℝ, (1 / 2 + y * I : ℂ) ∈ Omega ↔ |y| ≤ y₀ := by
  have hcont : ContinuousOn kHalf (Set.Icc (26276 / 100000) (26277 / 100000)) :=
    fun y _ => (kHalf_hasDerivAt y).continuousAt.continuousWithinAt
  obtain ⟨y₀, ⟨h1, h2⟩, hy₀⟩ := intermediate_value_Ioo (by norm_num) hcont ⟨kHalf_lower, kHalf_upper⟩
  refine ⟨y₀, h1, h2, fun y => ?_⟩
  rw [Omega, Set.mem_ofPred_eq, Ulog_half, ← kHalf_strictMono.le_iff_le (a := |y|) (b := y₀), hy₀]
  constructor <;> intro h <;> linarith

/-! ### The corners at `0` and `1` -/

/-- `U(x + ib)` in real coordinates. -/
theorem Ulog_re_im (x b : ℝ) : Ulog ((x : ℂ) + b * I) =
    x * (Real.log (x ^ 2 + b ^ 2) / 2) + (1 - x) * (Real.log ((x - 1) ^ 2 + b ^ 2) / 2) - 1 +
      b * (Real.arctan ((1 - x) / b) + Real.arctan (x / b)) := by
  rw [Ulog_eq]
  have hre : ((x : ℂ) + b * I).re = x := by simp
  have him : ((x : ℂ) + b * I).im = b := by simp
  have e2 : Real.log ‖(x : ℂ) + b * I - 1‖ = Real.log ((x - 1) ^ 2 + b ^ 2) / 2 := by
    rw [show (x : ℂ) + b * I - 1 = ((x - 1 : ℝ) : ℂ) + b * I by push_cast; ring, log_norm_re_im]
  rw [hre, him, log_norm_re_im, e2]

theorem Ulog_neg_im (x b : ℝ) : Ulog ((x : ℂ) + (-b : ℝ) * I) = Ulog ((x : ℂ) + b * I) := by
  rw [← Ulog_conj]
  congr 1
  simp [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]

theorem Ulog_reflect (x b : ℝ) : Ulog (((1 - x : ℝ) : ℂ) + b * I) = Ulog ((x : ℂ) + b * I) := by
  rw [← Ulog_one_sub, ← Ulog_neg_im]
  congr 1
  push_cast
  ring

/-- `∂U/∂x = log|x + ib| - log|x + ib - 1|` for `b ≠ 0`. -/
theorem Ulog_re_hasDerivAt {b : ℝ} (hb : b ≠ 0) (x : ℝ) :
    HasDerivAt (fun x : ℝ => Ulog ((x : ℂ) + b * I))
      (Real.log (x ^ 2 + b ^ 2) / 2 - Real.log ((x - 1) ^ 2 + b ^ 2) / 2) x := by
  have hfun : (fun x : ℝ => Ulog ((x : ℂ) + b * I)) = fun x =>
      x * (Real.log (x ^ 2 + b ^ 2) / 2) + (1 - x) * (Real.log ((x - 1) ^ 2 + b ^ 2) / 2) - 1 +
        b * (Real.arctan ((1 - x) / b) + Real.arctan (x / b)) := funext fun x => Ulog_re_im x b
  rw [hfun]
  have hb2 : 0 < b ^ 2 := by positivity
  have hQ1 : 0 < x ^ 2 + b ^ 2 := by positivity
  have hQ2 : 0 < (x - 1) ^ 2 + b ^ 2 := by positivity
  have d1 : HasDerivAt (fun x : ℝ => x ^ 2 + b ^ 2) (2 * x) x :=
    ((hasDerivAt_pow 2 x).add_const _).congr_deriv (by ring)
  have d2 : HasDerivAt (fun x : ℝ => (x - 1) ^ 2 + b ^ 2) (2 * (x - 1)) x :=
    ((((hasDerivAt_id' x).sub_const 1).pow 2).add_const _).congr_deriv (by ring)
  have t1 := (hasDerivAt_id' x).mul ((d1.log hQ1.ne').div_const 2)
  have t2 := ((hasDerivAt_id' x).const_sub 1).mul ((d2.log hQ2.ne').div_const 2)
  have t3 := ((((hasDerivAt_id' x).const_sub 1).div_const b).arctan.add
    (((hasDerivAt_id' x).div_const b).arctan)).const_mul b
  refine (((t1.add t2).sub_const 1).add t3).congr_deriv ?_
  have h3 : 1 + ((1 - x) / b) ^ 2 ≠ 0 := by positivity
  have h4 : 1 + (x / b) ^ 2 ≠ 0 := by positivity
  field_simp
  ring

/-- For each `b`, `x ↦ U(x + ib)` is strictly decreasing on `x ≤ 1/2`. -/
theorem Ulog_strictAntiOn (b : ℝ) : StrictAntiOn (fun x : ℝ => Ulog ((x : ℂ) + b * I)) (Set.Iic (1 / 2)) := by
  have hcont : Continuous (fun x : ℝ => Ulog ((x : ℂ) + b * I)) := continuous_Ulog.comp (by fun_prop)
  by_cases hb : b = 0
  · subst hb
    have hfun : (fun x : ℝ => Ulog ((x : ℂ) + ((0 : ℝ) : ℂ) * I)) =
        fun x => x * Real.log x + (1 - x) * Real.log (1 - x) - 1 := by
      funext x; rw [ofReal_zero, zero_mul, add_zero, Ulog_ofReal]
    have hderiv : ∀ x : ℝ, x ≠ 0 → x < 1 / 2 → HasDerivAt (fun x : ℝ => Ulog ((x : ℂ) + ((0 : ℝ) : ℂ) * I))
        (Real.log x - Real.log (1 - x)) x := by
      intro x hx0 hx
      rw [hfun]
      have h1 := Real.hasDerivAt_mul_log hx0
      have h2 := (Real.hasDerivAt_mul_log (show 1 - x ≠ 0 by intro h; linarith)).comp x
        ((hasDerivAt_id' x).const_sub 1)
      exact ((h1.add h2).sub_const 1).congr_deriv (by ring)
    have hneg : ∀ x : ℝ, x ≠ 0 → x < 1 / 2 → Real.log x - Real.log (1 - x) < 0 := by
      intro x hx0 hx
      have : Real.log x < Real.log (1 - x) := by
        rw [← Real.log_abs x]
        exact Real.log_lt_log (abs_pos.mpr hx0) (by cases abs_cases x <;> linarith)
      linarith
    have hA : StrictAntiOn (fun x : ℝ => Ulog ((x : ℂ) + ((0 : ℝ) : ℂ) * I)) (Set.Iic 0) :=
      strictAntiOn_of_deriv_neg (convex_Iic 0) hcont.continuousOn fun x hx => by
        rw [interior_Iic] at hx
        have hx' : x < 0 := hx
        rw [(hderiv x hx'.ne (by linarith)).deriv]
        exact hneg x hx'.ne (by linarith)
    have hB : StrictAntiOn (fun x : ℝ => Ulog ((x : ℂ) + ((0 : ℝ) : ℂ) * I)) (Set.Icc 0 (1 / 2)) :=
      strictAntiOn_of_deriv_neg (convex_Icc 0 _) hcont.continuousOn fun x hx => by
        rw [interior_Icc] at hx
        rw [(hderiv x hx.1.ne' hx.2).deriv]
        exact hneg x hx.1.ne' hx.2
    intro x hx y hy hxy
    rcases le_or_gt x 0 with h1 | h1 <;> rcases le_or_gt y 0 with h2 | h2
    · exact hA h1 h2 hxy
    · exact lt_of_lt_of_le (hB ⟨le_rfl, by norm_num⟩ ⟨h2.le, hy⟩ h2)
        (hA.antitoneOn h1 (le_refl (0 : ℝ)) h1)
    · linarith
    · exact hB ⟨h1.le, hx⟩ ⟨h2.le, hy⟩ hxy
  · refine strictAntiOn_of_deriv_neg (convex_Iic _) hcont.continuousOn fun x hx => ?_
    rw [interior_Iic] at hx
    have hx' : x < 1 / 2 := hx
    rw [(Ulog_re_hasDerivAt hb x).deriv]
    have : Real.log (x ^ 2 + b ^ 2) < Real.log ((x - 1) ^ 2 + b ^ 2) :=
      Real.log_lt_log (by positivity) (by nlinarith)
    linarith

/-- On the imaginary axis `U ≥ -1`, with equality only at `0`. -/
theorem Ulog_imag_gt {b : ℝ} (hb : b ≠ 0) : -1 < Ulog (((0 : ℝ) : ℂ) + b * I) := by
  rw [Ulog_re_im, zero_div, Real.arctan_zero, add_zero]
  have e : (0 : ℝ) * (Real.log (0 ^ 2 + b ^ 2) / 2) + (1 - 0) * (Real.log ((0 - 1) ^ 2 + b ^ 2) / 2) - 1 +
      b * Real.arctan ((1 - 0) / b) = Real.log ((0 - 1) ^ 2 + b ^ 2) / 2 - 1 + b * Real.arctan ((1 - 0) / b) := by
    ring
  rw [e]
  have h1 : 0 ≤ Real.log ((0 - 1) ^ 2 + b ^ 2) := Real.log_nonneg (by nlinarith)
  have h2 : 0 < b * Real.arctan ((1 - 0) / b) := by
    rcases lt_or_gt_of_ne hb with h | h
    · exact mul_pos_of_neg_of_neg h (Real.arctan_lt_zero.mpr (by rw [sub_zero]; exact div_neg_of_pos_of_neg one_pos h))
    · exact mul_pos h (Real.arctan_pos.mpr (by positivity))
  generalize Real.log ((0 - 1) ^ 2 + b ^ 2) = A at h1 ⊢
  generalize b * Real.arctan ((1 - 0) / b) = B at h2 ⊢
  linarith

theorem Ulog_zero : Ulog 0 = -1 := by
  have := Ulog_ofReal 0
  simp at this
  exact this

theorem arctan_le_self {s : ℝ} (hs : 0 ≤ s) : Real.arctan s ≤ s := by
  have h := Real.le_tan (Real.arctan_nonneg.mpr hs) (Real.arctan_lt_pi_div_two s)
  rwa [Real.tan_arctan] at h

/-- Near `0`, the boundary of `Ω` is to the left of `x = ε|b|`: `U(εb + ib) < -1` for small `b > 0`. -/
theorem Ulog_corner_upper {ε b : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hb : 0 < b)
    (hbε : b < Real.exp (-4 / ε - 1)) : Ulog (((ε * b : ℝ) : ℂ) + b * I) < -1 := by
  rw [Ulog_re_im]
  have h4 : 0 < 4 / ε := by positivity
  have h4' : -4 / ε = -(4 / ε) := by ring
  have hb1 : b < 1 := hbε.trans (Real.exp_lt_one_iff.mpr (by linarith))
  set x := ε * b with hx
  have hx0 : 0 ≤ x := by positivity
  have hxb : x ≤ b := by nlinarith
  have t1 : x * (Real.log (x ^ 2 + b ^ 2) / 2) ≤ x * (1 + Real.log b) := by
    apply mul_le_mul_of_nonneg_left _ hx0
    have h1 : Real.log (x ^ 2 + b ^ 2) ≤ Real.log (2 * b ^ 2) := Real.log_le_log (by positivity) (by nlinarith)
    have h2 : Real.log (2 * b ^ 2) = Real.log 2 + 2 * Real.log b := by
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]; push_cast; ring
    have h3 : Real.log 2 < 1 := by have := Real.log_two_lt_d9; norm_num at this; linarith
    linarith
  have t2 : (1 - x) * (Real.log ((x - 1) ^ 2 + b ^ 2) / 2) ≤ b ^ 2 / 2 := by
    have hL : Real.log ((x - 1) ^ 2 + b ^ 2) ≤ b ^ 2 := by
      have := Real.log_le_sub_one_of_pos (show 0 < (x - 1) ^ 2 + b ^ 2 by positivity)
      nlinarith
    have h : (1 - x) * (Real.log ((x - 1) ^ 2 + b ^ 2) / 2) ≤ (1 - x) * (b ^ 2 / 2) :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    nlinarith
  have t3 : b * (Real.arctan ((1 - x) / b) + Real.arctan (x / b)) ≤ b * Real.pi := by
    have h1 := Real.arctan_lt_pi_div_two ((1 - x) / b)
    have h2 := Real.arctan_lt_pi_div_two (x / b)
    nlinarith
  have hlog : Real.log b < -4 / ε - 1 := by rwa [Real.log_lt_iff_lt_exp hb]
  have hεlog : ε * (1 + Real.log b) < -4 := by
    have h := mul_lt_mul_of_pos_left hlog hε
    have e : ε * (-4 / ε - 1) = -4 - ε := by field_simp
    linarith
  have hprod : b * (ε * (1 + Real.log b)) < b * (-4) := mul_lt_mul_of_pos_left hεlog hb
  have e : x * (1 + Real.log b) = b * (ε * (1 + Real.log b)) := by rw [hx]; ring
  have hpi := Real.pi_lt_d2
  norm_num at hpi
  nlinarith

/-- Near `0`, the boundary of `Ω` is to the right of `x = b / (2 log (1/b))`. -/
theorem Ulog_corner_lower {b : ℝ} (hb : 0 < b) (hb8 : b ≤ 1 / 8) :
    -1 < Ulog (((b / (2 * Real.log b⁻¹) : ℝ) : ℂ) + b * I) := by
  set L := Real.log b⁻¹ with hLdef
  have hL : 1 ≤ L := by
    have h8 : (8 : ℝ) ≤ b⁻¹ := by rw [le_inv_comm₀ (by norm_num) hb]; linarith
    have h1 : Real.log 8 ≤ L := Real.log_le_log (by norm_num) h8
    have h2 : Real.log 8 = 3 * Real.log 2 := by
      rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; push_cast; ring
    have h3 := Real.log_two_gt_d9
    norm_num at h3
    linarith
  set x := b / (2 * L) with hx
  have hx0 : 0 ≤ x := by positivity
  have hxb : x ≤ b / 2 := by
    rw [hx, div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  have h1x : 0 < 1 - x := by linarith
  rw [Ulog_re_im]
  have t1 : -(b / 2) ≤ x * (Real.log (x ^ 2 + b ^ 2) / 2) := by
    have h : Real.log (b ^ 2) ≤ Real.log (x ^ 2 + b ^ 2) := Real.log_le_log (by positivity) (by nlinarith)
    have hb2 : Real.log (b ^ 2) = -2 * L := by
      rw [Real.log_pow, hLdef, Real.log_inv]; push_cast; ring
    have h' : x * (-L) ≤ x * (Real.log (x ^ 2 + b ^ 2) / 2) := mul_le_mul_of_nonneg_left (by linarith) hx0
    have hxL : x * L = b / 2 := by rw [hx]; field_simp
    linarith
  have t2 : -x ≤ (1 - x) * (Real.log ((x - 1) ^ 2 + b ^ 2) / 2) := by
    have h : Real.log ((1 - x) ^ 2) ≤ Real.log ((x - 1) ^ 2 + b ^ 2) :=
      Real.log_le_log (by positivity) (by nlinarith)
    have h2 : Real.log ((1 - x) ^ 2) = 2 * Real.log (1 - x) := by rw [Real.log_pow]; push_cast; ring
    have h3 : 1 - (1 - x)⁻¹ ≤ Real.log (1 - x) := Real.one_sub_inv_le_log_of_pos h1x
    have h4 : (1 - x) * (1 - (1 - x)⁻¹) = -x := by field_simp; ring
    have h5 : (1 - x) * Real.log (1 - x) ≤ (1 - x) * (Real.log ((x - 1) ^ 2 + b ^ 2) / 2) :=
      mul_le_mul_of_nonneg_left (by linarith) h1x.le
    have h6 : (1 - x) * (1 - (1 - x)⁻¹) ≤ (1 - x) * Real.log (1 - x) := mul_le_mul_of_nonneg_left h3 h1x.le
    linarith
  have t3 : b * (Real.pi / 2) - 2 * b ^ 2 ≤ b * Real.arctan ((1 - x) / b) := by
    have hpos : 0 < b / (1 - x) := by positivity
    have e : Real.arctan ((1 - x) / b) = Real.pi / 2 - Real.arctan (b / (1 - x)) := by
      rw [← Real.arctan_inv_of_pos hpos, inv_div]
    have hle : Real.arctan (b / (1 - x)) ≤ b / (1 - x) := arctan_le_self hpos.le
    have hbx : b / (1 - x) ≤ 2 * b := by rw [div_le_iff₀ h1x]; nlinarith
    rw [e]
    nlinarith
  have t4 : 0 ≤ b * Real.arctan (x / b) := mul_nonneg hb.le (Real.arctan_nonneg.mpr (by positivity))
  have hpi := Real.pi_gt_three
  nlinarith

theorem log_inv_ge_one {b : ℝ} (hb : 0 < b) (hb8 : b ≤ 1 / 8) : 1 ≤ Real.log b⁻¹ := by
  have h8 : (8 : ℝ) ≤ b⁻¹ := by rw [le_inv_comm₀ (by norm_num) hb]; linarith
  have h1 : Real.log 8 ≤ Real.log b⁻¹ := Real.log_le_log (by norm_num) h8
  have h2 : Real.log 8 = 3 * Real.log 2 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; push_cast; ring
  have h3 := Real.log_two_gt_d9
  norm_num at h3
  linarith

/-- `Ω` contains `[0,1]`. -/
theorem omega_contains {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : (t : ℂ) ∈ Omega := Ulog_le_of_mem ht0 ht1

theorem frontier_omega_iff (z : ℂ) :
    z ∈ frontier Omega ↔ Ulog z ≤ -1 ∧ ∀ ε > 0, ∃ w, dist w z < ε ∧ -1 < Ulog w := by
  have hcl : IsClosed Omega := isClosed_le continuous_Ulog continuous_const
  rw [frontier_eq_closure_inter_closure, hcl.closure_eq, Set.mem_inter_iff, Metric.mem_closure_iff]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun ε hε => ?_⟩
    obtain ⟨w, hw, hd⟩ := h2 ε hε
    exact ⟨w, by rwa [dist_comm], lt_of_not_ge hw⟩
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun ε hε => ?_⟩
    obtain ⟨w, hd, hw⟩ := h2 ε hε
    exact ⟨w, not_le.mpr hw, by rwa [dist_comm]⟩

/-- The frontier of `Ω` is invariant under `z ↦ 1 - z̄`. -/
theorem frontier_omega_sigma (z : ℂ) : (1 - starRingEnd ℂ z) ∈ frontier Omega ↔ z ∈ frontier Omega := by
  have hU : ∀ w : ℂ, Ulog (1 - starRingEnd ℂ w) = Ulog w := fun w => by rw [Ulog_one_sub, Ulog_conj]
  have hd : ∀ w v : ℂ, dist (1 - starRingEnd ℂ w) (1 - starRingEnd ℂ v) = dist w v := by
    intro w v
    rw [dist_eq_norm, dist_eq_norm, show 1 - starRingEnd ℂ w - (1 - starRingEnd ℂ v) = starRingEnd ℂ (v - w) by
      rw [map_sub]; ring, Complex.norm_conj, norm_sub_rev]
  have hinv : ∀ w : ℂ, 1 - starRingEnd ℂ (1 - starRingEnd ℂ w) = w := fun w => by
    rw [map_sub, map_one, Complex.conj_conj]; ring
  rw [frontier_omega_iff, frontier_omega_iff, hU]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun ε hε => ?_⟩
    obtain ⟨w, hw, hwU⟩ := h2 ε hε
    refine ⟨1 - starRingEnd ℂ w, ?_, by rwa [hU]⟩
    rw [← hd, hinv]; exact hw
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun ε hε => ?_⟩
    obtain ⟨w, hw, hwU⟩ := h2 ε hε
    exact ⟨1 - starRingEnd ℂ w, by rw [hd]; exact hw, by rwa [hU]⟩

/-- **The corner of `Ω` at `0`.** Near `0`, `Ω` is the region `x ≥ a(b)` to the right of a curve
`x = a(b)`, which is the frontier of `Ω` there. The curve has a vertical tangent at `0`
(`a(b)/b → 0`), and `a` is not analytic at `0`. -/
theorem omega_corner_zero :
    ∃ β > 0, ∃ a : ℝ → ℝ, a 0 = 0 ∧ (∀ b, |b| < β → 0 ≤ a b ∧ a b ≤ |b|) ∧
      (∀ x b : ℝ, |x| < β → |b| < β → ((x : ℂ) + b * I ∈ Omega ↔ a b ≤ x)) ∧
      (∀ x b : ℝ, |x| < β → |b| < β → ((x : ℂ) + b * I ∈ frontier Omega ↔ x = a b)) ∧
      Tendsto (fun b => a b / b) (𝓝[≠] 0) (𝓝 0) ∧ ¬AnalyticAt ℝ a 0 := by
  set β := min (1 / 8 : ℝ) (Real.exp (-5)) with hβdef
  have hβ0 : 0 < β := lt_min (by norm_num) (Real.exp_pos _)
  have hβ8 : β ≤ 1 / 8 := min_le_left _ _
  have hβe : β ≤ Real.exp (-5) := min_le_right _ _
  have hanti : ∀ b : ℝ, StrictAntiOn (fun x : ℝ => Ulog ((x : ℂ) + b * I)) (Set.Iic (1 / 2)) :=
    Ulog_strictAntiOn
  have hcont : ∀ b : ℝ, Continuous (fun x : ℝ => Ulog ((x : ℂ) + b * I)) :=
    fun b => continuous_Ulog.comp (by fun_prop)
  have habs : ∀ b x : ℝ, Ulog ((x : ℂ) + b * I) = Ulog ((x : ℂ) + |b| * I) := by
    intro b x
    rcases abs_cases b with ⟨h, -⟩ | ⟨h, -⟩
    · rw [h]
    · rw [h, Ulog_neg_im]
  have h0 : ∀ b : ℝ, b ≠ 0 → -1 < Ulog (((0 : ℝ) : ℂ) + b * I) := fun b hb => Ulog_imag_gt hb
  have hupper : ∀ ε b : ℝ, 0 < ε → ε ≤ 1 → 0 < |b| → |b| < Real.exp (-4 / ε - 1) →
      Ulog (((ε * |b| : ℝ) : ℂ) + b * I) < -1 := by
    intro ε b hε hε1 hb hbe
    rw [habs]; exact Ulog_corner_upper hε hε1 hb hbe
  -- the boundary point on each horizontal line
  have hex : ∀ b : ℝ, ∃ x : ℝ, |b| < β → 0 ≤ x ∧ x ≤ |b| ∧ Ulog ((x : ℂ) + b * I) = -1 := by
    intro b
    by_cases hb0 : b = 0
    · refine ⟨0, fun _ => ⟨le_rfl, by simp [hb0], ?_⟩⟩
      subst hb0
      simpa using Ulog_zero
    by_cases hbβ : |b| < β
    · have hbpos : 0 < |b| := abs_pos.mpr hb0
      have hlow := h0 b hb0
      have hup : Ulog (((|b| : ℝ) : ℂ) + b * I) < -1 := by
        have := hupper 1 b one_pos le_rfl hbpos (by
          rw [show (-4 : ℝ) / 1 - 1 = -5 by norm_num]; linarith)
        rwa [one_mul] at this
      obtain ⟨x, hx, hxv⟩ := intermediate_value_Icc' hbpos.le (hcont b).continuousOn ⟨hup.le, hlow.le⟩
      exact ⟨x, fun _ => ⟨hx.1, hx.2, hxv⟩⟩
    · exact ⟨0, fun h => absurd h hbβ⟩
  choose a ha using hex
  have ha0 : a 0 = 0 := by
    obtain ⟨h1, h2, -⟩ := ha 0 (by simpa using hβ0)
    simp at h2
    linarith
  have hIic : ∀ y : ℝ, |y| < β → y ∈ Set.Iic (1 / 2 : ℝ) := fun y hy => by
    have := (abs_lt.mp hy).2
    show y ≤ 1 / 2
    linarith
  have haβ : ∀ b : ℝ, |b| < β → |a b| < β := fun b hb => by
    rw [abs_of_nonneg (ha b hb).1]; linarith [(ha b hb).2.1]
  have hkey : ∀ x b : ℝ, |x| < β → |b| < β → (Ulog ((x : ℂ) + b * I) ≤ -1 ↔ a b ≤ x) := by
    intro x b hx hb
    rw [← (ha b hb).2.2]
    exact StrictAntiOn.le_iff_ge (hanti b) (hIic x hx) (hIic _ (haβ b hb))
  -- the frontier
  have hfront : ∀ x b : ℝ, |x| < β → |b| < β → ((x : ℂ) + b * I ∈ frontier Omega ↔ x = a b) := by
    intro x b hx hb
    rw [frontier_omega_iff]
    constructor
    · rintro ⟨h1, h2⟩
      have hle := (hkey x b hx hb).mp h1
      by_contra hne
      have hlt : a b < x := lt_of_le_of_ne hle (Ne.symm hne)
      have hzlt : Ulog ((x : ℂ) + b * I) < -1 := by
        rw [← (ha b hb).2.2]; exact (hanti b) (hIic _ (haβ b hb)) (hIic x hx) hlt
      obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp
        (continuous_Ulog.continuousAt.eventually (gt_mem_nhds hzlt))
      obtain ⟨w, hw, hwU⟩ := h2 ε hε
      exact absurd (hball hw) (not_lt.mpr hwU.le)
    · intro hxa
      refine ⟨(hkey x b hx hb).mpr hxa.ge, fun ε hε => ?_⟩
      set t := min (ε / 2) (β / 2) with htdef
      have ht0 : 0 < t := lt_min (by positivity) (by positivity)
      have ht1 : t ≤ ε / 2 := min_le_left _ _
      have ht2 : t ≤ β / 2 := min_le_right _ _
      refine ⟨((x - t : ℝ) : ℂ) + b * I, ?_, ?_⟩
      · rw [dist_eq_norm, show ((x - t : ℝ) : ℂ) + b * I - ((x : ℂ) + b * I) = ((-t : ℝ) : ℂ) by push_cast; ring,
          norm_real, Real.norm_eq_abs, abs_neg, abs_of_pos ht0]
        linarith
      · have hx0 : 0 ≤ x := hxa ▸ (ha b hb).1
        have hxt : |x - t| < β := by
          rw [abs_lt]; constructor <;> linarith [(abs_lt.mp hx).2]
        by_contra hle
        push Not at hle
        have := (hkey (x - t) b hxt hb).mp hle
        linarith
  -- vertical tangent
  have htan : Tendsto (fun b => a b / b) (𝓝[≠] 0) (𝓝 0) := by
    rw [Metric.tendsto_nhdsWithin_nhds]
    intro ε hε
    set ε₁ := min (ε / 2) 1 with hε₁def
    have hε₁ : 0 < ε₁ := lt_min (by positivity) one_pos
    have hε₁1 : ε₁ ≤ 1 := min_le_right _ _
    have hε₁ε : ε₁ < ε := lt_of_le_of_lt (min_le_left _ _) (by linarith)
    refine ⟨min β (Real.exp (-4 / ε₁ - 1)), lt_min hβ0 (Real.exp_pos _), fun {b} hb hbd => ?_⟩
    rw [Real.dist_eq, sub_zero] at hbd ⊢
    have hb0 : b ≠ 0 := hb
    have hbpos : 0 < |b| := abs_pos.mpr hb0
    have hbβ : |b| < β := lt_of_lt_of_le hbd (min_le_left _ _)
    have hbe : |b| < Real.exp (-4 / ε₁ - 1) := lt_of_lt_of_le hbd (min_le_right _ _)
    have hup := hupper ε₁ b hε₁ hε₁1 hbpos hbe
    have hx : abs (ε₁ * |b|) < β := by
      rw [abs_of_nonneg (by positivity)]
      calc ε₁ * |b| ≤ 1 * |b| := mul_le_mul_of_nonneg_right hε₁1 (abs_nonneg _)
        _ < β := by rw [one_mul]; exact hbβ
    have hle : a b ≤ ε₁ * |b| := (hkey _ b hx hbβ).mp hup.le
    have hnn := (ha b hbβ).1
    rw [abs_div, abs_of_nonneg hnn, div_lt_iff₀ hbpos]
    calc a b ≤ ε₁ * |b| := hle
      _ < ε * |b| := mul_lt_mul_of_pos_right hε₁ε hbpos
  -- the lower bound `a(b) > b / (2 log (1/b))`
  have hlower : ∀ b : ℝ, 0 < b → b < β → b / (2 * Real.log b⁻¹) < a b := by
    intro b hb hbβ
    have hbβ' : |b| < β := by rwa [abs_of_pos hb]
    have hL := log_inv_ge_one hb (by linarith)
    have h := Ulog_corner_lower hb (by linarith)
    have hx0 : 0 ≤ b / (2 * Real.log b⁻¹) := by positivity
    have hxb : b / (2 * Real.log b⁻¹) ≤ b / 2 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
    have hx : |b / (2 * Real.log b⁻¹)| < β := by rw [abs_of_nonneg hx0]; linarith
    by_contra hle
    push Not at hle
    have := (hkey _ b hx hbβ').mpr hle
    linarith
  -- `a` is not analytic at `0`
  have hnotan : ¬AnalyticAt ℝ a 0 := by
    rintro ⟨p, hp⟩
    have hc0 : (p 1 fun _ => 1) = 0 := by
      have h1 := hasDerivAt_iff_tendsto_slope.mp hp.hasDerivAt
      have h2 : Tendsto (slope a 0) (𝓝[≠] 0) (𝓝 0) :=
        htan.congr fun b => by simp [slope_def_field, ha0]
      exact tendsto_nhds_unique h1 h2
    have hps : ∀ y : ℝ, p.partialSum 2 y = 0 := by
      intro y
      simp only [FormalMultilinearSeries.partialSum, Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
      rw [hp.coeff_zero, ha0, zero_add, FormalMultilinearSeries.apply_eq_pow_smul_coeff]
      have : p.coeff 1 = 0 := hc0
      rw [this, smul_zero]
    have hO := hp.isBigO_sub_partialSum_pow 2
    simp only [zero_add, hps, sub_zero] at hO
    obtain ⟨C, hC⟩ := hO.bound
    have hlim : Tendsto (fun b : ℝ => b * Real.log b⁻¹) (𝓝 0) (𝓝 0) := by
      have h1 : Tendsto (fun b : ℝ => b * Real.log b) (𝓝 0) (𝓝 0) := by
        simpa using Real.continuous_mul_log.tendsto 0
      simpa [Real.log_inv] using h1.neg
    have hev : ∀ᶠ b in 𝓝[>] (0 : ℝ), 2 * C * (b * Real.log b⁻¹) < 1 :=
      ((hlim.mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))).const_mul (2 * C)).eventually
        (gt_mem_nhds (show 2 * C * 0 < 1 by norm_num))
    have hev2 : ∀ᶠ b in 𝓝[>] (0 : ℝ), b ∈ Set.Ioo 0 β := Ioo_mem_nhdsGT hβ0
    obtain ⟨b, ⟨hCb, hsmall⟩, hbpos, hbβ⟩ := (((hC.filter_mono nhdsWithin_le_nhds).and hev).and hev2).exists
    have hlb := hlower b hbpos hbβ
    have hL := log_inv_ge_one hbpos (by linarith)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_pow, abs_norm, Real.norm_eq_abs, sq_abs] at hCb
    have h1 : b < C * b ^ 2 * (2 * Real.log b⁻¹) := by
      have := lt_of_lt_of_le hlb ((le_abs_self _).trans hCb)
      rwa [div_lt_iff₀ (by positivity)] at this
    nlinarith [mul_pos hbpos (sub_pos.mpr hsmall)]
  exact ⟨β, hβ0, a, ha0, fun b hb => ⟨(ha b hb).1, (ha b hb).2.1⟩, hkey, hfront, htan, hnotan⟩

/-- **The corner of `Ω` at `1`**, the mirror image of the corner at `0` under `z ↦ 1 - z̄`. -/
theorem omega_corner_one :
    ∃ β > 0, ∃ a : ℝ → ℝ, a 0 = 1 ∧
      (∀ x b : ℝ, |x - 1| < β → |b| < β → ((x : ℂ) + b * I ∈ Omega ↔ x ≤ a b)) ∧
      (∀ x b : ℝ, |x - 1| < β → |b| < β → ((x : ℂ) + b * I ∈ frontier Omega ↔ x = a b)) ∧
      Tendsto (fun b => (a b - 1) / b) (𝓝[≠] 0) (𝓝 0) ∧ ¬AnalyticAt ℝ a 0 := by
  obtain ⟨β, hβ, a, ha0, -, hmem, hfr, htan, hna⟩ := omega_corner_zero
  refine ⟨β, hβ, fun b => 1 - a b, by simp [ha0], fun x b hx hb => ?_, fun x b hx hb => ?_, ?_, ?_⟩
  · have hx' : |1 - x| < β := by rwa [abs_sub_comm]
    have h := hmem (1 - x) b hx' hb
    have e : ((x : ℂ) + b * I ∈ Omega) ↔ (((1 - x : ℝ) : ℂ) + b * I ∈ Omega) := by
      simp only [Omega, Set.mem_ofPred_eq, Ulog_reflect]
    rw [e, h]
    constructor <;> intro h' <;> linarith
  · have hx' : |1 - x| < β := by rwa [abs_sub_comm]
    have hσ : (1 : ℂ) - starRingEnd ℂ ((x : ℂ) + b * I) = ((1 - x : ℝ) : ℂ) + b * I := by
      simp only [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
      push_cast; ring
    rw [← frontier_omega_sigma, hσ, hfr (1 - x) b hx' hb]
    constructor <;> intro h' <;> linarith
  · have h := htan.neg
    rw [neg_zero] at h
    exact h.congr fun b => by ring
  · intro h
    apply hna
    have e : a = fun b => 1 - (1 - a b) := by funext b; ring
    rw [e]
    exact analyticAt_const.sub h

end Szkraw
