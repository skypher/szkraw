import Szkraw.GenMain
import Szkraw.GenMM1S20
import Szkraw.VRQuadMain
import Szkraw.VRLowDegree
import Szkraw.VRAffineMain
import Szkraw.CubicLeib
import Szkraw.ComboCounterexamples
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# P2: exact remarks outside the numbered results

* After Corollary 3.2: the strict-ratio example (`strict_ratio_example`), the mixed-sign Newton coefficients of
  `b = (0,1,1,1)/91` (`openEx1_b_newton`), and the concave diagonal of linear ratios on the linear profile
  (`linear_ratio_concave_b`).
* Section 5: exponential ratios (`exponential_ratio`), the internal zeros of the cubic counterexample's ratio
  (`cubic_example_ratio_newton`), the containments of Theorems 4.1, Corollary 5.2 and the case `t² ≥ rτ` of
  Theorem 4.2 in Theorem 5.5 (`general_contains`), and the non-comparability of Theorem 4.2 and Corollary 5.2
  (`quad_lowdeg_incomparable`).
* Proof of Theorem 5.5: `ρ(x) = 1 + x/2 + x²/2` has log-concave Newton coefficients but `(log ρ)''(0) > 0`
  (`log_rho_not_concave`).
-/

namespace Szkraw

open Finset Filter Topology

/-! ### After Corollary 3.2 -/

/-- If `c_i = κ₁ i + κ₂ C(i,2)` with `κ₁, κ₂ > 0` and `b_i = w₁ κ₁ i + w₂ κ₂ C(i,2)` with `w₁ > w₂ ≥ 0` (any common
positive scaling), the ratio `c_i/(b_i + c_i)` increases strictly for `i ≥ 1`. -/
theorem strict_ratio_example (κ₁ κ₂ w₁ w₂ s : ℝ) (hκ₁ : 0 < κ₁) (hκ₂ : 0 < κ₂) (hw : w₂ < w₁) (hw₂ : 0 ≤ w₂)
    (hs : 0 < s) (i : ℕ) (hi : 1 ≤ i) :
    let c := fun n : ℕ => s * (κ₁ * n + κ₂ * (n.choose 2 : ℝ))
    let b := fun n : ℕ => s * (w₁ * κ₁ * n + w₂ * κ₂ * (n.choose 2 : ℝ))
    c i / (b i + c i) < c (i + 1) / (b (i + 1) + c (i + 1)) := by
  intro c b
  simp only [c, b, choose2_real]
  push_cast
  have hi' : (1 : ℝ) ≤ i := by exact_mod_cast hi
  have hx : (0 : ℝ) ≤ i * (i - 1) / 2 := div_nonneg (mul_nonneg (by linarith) (by linarith)) (by norm_num)
  have hx' : (0 : ℝ) ≤ (i + 1) * (i + 1 - 1) / 2 := div_nonneg (mul_nonneg (by linarith) (by linarith)) (by norm_num)
  have hw₁ : 0 < w₁ := by linarith
  have h1 : 0 < κ₁ * i + κ₂ * (i * (i - 1) / 2) := by
    have := mul_pos hκ₁ (by linarith : (0 : ℝ) < i); nlinarith [mul_nonneg hκ₂.le hx]
  have h2 : 0 < κ₁ * (i + 1) + κ₂ * ((i + 1) * (i + 1 - 1) / 2) := by
    have := mul_pos hκ₁ (by linarith : (0 : ℝ) < i + 1); nlinarith [mul_nonneg hκ₂.le hx']
  have hb1 : 0 ≤ w₁ * κ₁ * i + w₂ * κ₂ * (i * (i - 1) / 2) := by
    have := mul_nonneg (mul_nonneg hw₁.le hκ₁.le) (by linarith : (0 : ℝ) ≤ i)
    nlinarith [mul_nonneg (mul_nonneg hw₂ hκ₂.le) hx]
  have hb2 : 0 ≤ w₁ * κ₁ * (i + 1) + w₂ * κ₂ * ((i + 1) * (i + 1 - 1) / 2) := by
    have := mul_nonneg (mul_nonneg hw₁.le hκ₁.le) (by linarith : (0 : ℝ) ≤ i + 1)
    nlinarith [mul_nonneg (mul_nonneg hw₂ hκ₂.le) hx']
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  have key : 0 < s ^ 2 * (w₁ - w₂) * κ₁ * κ₂ * ((i : ℝ) * (i + 1) / 2) := by
    have : 0 < w₁ - w₂ := by linarith
    have : (0 : ℝ) < i * (i + 1) / 2 := by positivity
    positivity
  have e : s * (κ₁ * i + κ₂ * (i * (i - 1) / 2)) * (s * (w₁ * κ₁ * (i + 1) + w₂ * κ₂ * ((i + 1) * (i + 1 - 1) / 2)) +
      s * (κ₁ * (i + 1) + κ₂ * ((i + 1) * (i + 1 - 1) / 2))) -
      s * (κ₁ * (i + 1) + κ₂ * ((i + 1) * (i + 1 - 1) / 2)) * (s * (w₁ * κ₁ * i + w₂ * κ₂ * (i * (i - 1) / 2)) +
      s * (κ₁ * i + κ₂ * (i * (i - 1) / 2))) = -(s ^ 2 * (w₁ - w₂) * κ₁ * κ₂ * ((i : ℝ) * (i + 1) / 2)) := by ring
  linarith

/-- The counterexample `d = (0,25,55,91)/91`, `c = (0,24,54,90)/91` has `b = (0,1,1,1)/91`, whose Newton coefficients
have both signs. -/
theorem openEx1_b_newton :
    let b : ℕ → ℝ := fun i => if i = 0 then 0 else 1 / 91
    0 < newtonCoeff b 1 ∧ newtonCoeff b 2 < 0 := by
  intro b
  simp only [newtonCoeff, b, sum_range_succ, sum_range_zero]
  norm_num [Nat.choose]

/-- For `N ≥ 1`, the quadratic extension of the diagonal associated with
`ρ_i = r + κ i/N` and `d_i = i/N` has constant second difference
`-2κ/N² < 0`. For `N ≥ 2`, this is an in-range negative Newton
coefficient, excluding the array from Corollary 3.2. -/
theorem linear_ratio_concave_b (N : ℕ) (hN : 1 ≤ N) (r κ : ℝ) (hκ : 0 < κ) :
    let b : ℕ → ℝ := fun i => (1 - (r + κ * i / N)) * (i / N)
    (∀ i, b (i + 2) - 2 * b (i + 1) + b i = -2 * κ / N ^ 2) ∧ newtonCoeff b 2 = -2 * κ / N ^ 2 ∧
      newtonCoeff b 2 < 0 := by
  intro b
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have h2 : ∀ i, b (i + 2) - 2 * b (i + 1) + b i = -2 * κ / N ^ 2 := fun i => by
    simp only [b]; push_cast; field_simp; ring
  have hn2 : newtonCoeff b 2 = -2 * κ / N ^ 2 := by
    rw [← h2 0]; simp only [newtonCoeff, sum_range_succ, sum_range_zero]; norm_num [Nat.choose]; ring
  exact ⟨h2, hn2, by rw [hn2]; exact div_neg_of_neg_of_pos (by linarith) (by positivity)⟩

/-! ### Section 5 -/

/-- Exponential ratios `ρ(x) = r(1+ε)^x`, `r > 0`, `ε ≥ 0`: the Newton coefficients are `r ε^k`, they are log-concave
without internal zeros, and the arrays with this ratio, a log-concave Newton profile and nondecreasing `b` satisfy
the hypothesis of Theorem 5.5, hence have property (P). -/
theorem exponential_ratio (r ε : ℝ) (hr : 0 < r) (hε : 0 ≤ ε) :
    (∀ k, newtonCoeff (fun i => r * (1 + ε) ^ i) k = r * ε ^ k) ∧ LCNZ (fun k => r * ε ^ k) ∧
    ∀ (N : ℕ) (v : Coefficients N), Admissible v → LogConcaveNoInternalZeros N (newtonCoeff (profile v)) →
      (∀ i, i < N → v.b i ≤ v.b (i + 1)) → (∀ i, i ≤ N → v.c i = r * (1 + ε) ^ i * profile v i) →
      GenRatioHyp v ∧ MatrixPositivity v := by
  have hnc : ∀ k, newtonCoeff (fun i => r * (1 + ε) ^ i) k = r * ε ^ k := fun k => by
    have := newtonCoeff_const_geom 0 r (1 + ε) k
    simp only [zero_add, zero_mul, add_sub_cancel_left] at this
    exact this
  have hlc : LCNZ (fun k => r * ε ^ k) := by
    refine ⟨fun i => by positivity, fun i => by ring_nf; exact le_refl _, fun i j k hij hjk hi hk => ?_⟩
    rcases eq_or_lt_of_le hε with h | h
    · subst h
      rcases Nat.eq_zero_or_pos k with rfl | hk0
      · have : j = 0 := by omega
        subst this; simpa using hr
      · simp [zero_pow (by omega : k ≠ 0)] at hk
    · positivity
  have hdd : ∀ i, dd (fun k => r * ε ^ k) i = r * (1 + ε) ^ i := fun i => by
    unfold dd
    rw [iterShift_eq, add_comm 1 ε, add_pow]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun h _ => by simp; ring
  refine ⟨hnc, hlc, fun N v hv hprof hb hc => ?_⟩
  have hg : GenRatioHyp v := ⟨fun k => r * ε ^ k, hlc, by simpa using hr, hb,
    fun i hi => by rw [hc i hi, hdd], hprof⟩
  exact ⟨hg, lc_general N v hv hg⟩

/-- The ratio of the cubic counterexample (`N = 4`), Newton coefficients `ν_0, …, ν_4 = (19/20, 0, 0, 1/320, 0)`:
nonnegative and satisfying every log-concavity inequality `ν_k ν_{k+2} ≤ ν_{k+1}²`, `k + 2 ≤ 4`, but with internal
zeros (`ν_0, ν_3 > 0 = ν_1`). -/
theorem cubic_example_ratio_newton :
    let ρ : ℕ → ℝ := fun i => 19 / 20 + (i.choose 3 : ℝ) / 320
    newtonCoeff ρ 0 = 19 / 20 ∧ newtonCoeff ρ 1 = 0 ∧ newtonCoeff ρ 2 = 0 ∧ newtonCoeff ρ 3 = 1 / 320 ∧
      newtonCoeff ρ 4 = 0 ∧ (∀ k, k + 2 ≤ 4 → newtonCoeff ρ k * newtonCoeff ρ (k + 2) ≤ newtonCoeff ρ (k + 1) ^ 2) ∧
      (0 < newtonCoeff ρ 0 ∧ newtonCoeff ρ 1 = 0 ∧ 0 < newtonCoeff ρ 3) := by
  intro ρ
  have h : newtonCoeff ρ 0 = 19 / 20 ∧ newtonCoeff ρ 1 = 0 ∧ newtonCoeff ρ 2 = 0 ∧ newtonCoeff ρ 3 = 1 / 320 ∧
      newtonCoeff ρ 4 = 0 := by
    simp only [newtonCoeff, ρ, sum_range_succ, sum_range_zero]; norm_num [Nat.choose]
  obtain ⟨h0, h1, h2, h3, h4⟩ := h
  refine ⟨h0, h1, h2, h3, h4, fun k hk => ?_, by rw [h0]; norm_num, h1, by rw [h3]; norm_num⟩
  have : k ≤ 2 := by omega
  interval_cases k <;> simp [h0, h1, h2, h3, h4]

/-- Theorem 5.5 contains Theorem 4.1, Corollary 5.2 and the case `t² ≥ rτ` of Theorem 4.2: their hypotheses imply
those of Theorem 5.5. -/
theorem general_contains {N : ℕ} (hN : 1 ≤ N) (v : Coefficients N) :
    (AffineRatioHyp v → GenRatioHyp v) ∧ (LowDegRatioHyp v → GenRatioHyp v) ∧
    ((∃ r t τ : ℝ, 0 < r ∧ 0 ≤ t ∧ 0 ≤ τ ∧ r * τ ≤ t ^ 2 ∧ (∀ i, i < N → v.b i ≤ v.b (i + 1)) ∧
      (∀ i, i ≤ N → v.c i = (r + t * i + τ * (i.choose 2 : ℝ)) * profile v i) ∧
      LogConcaveNoInternalZeros N (newtonCoeff (profile v))) → GenRatioHyp v) := by
  -- the three-term ratio `(r, t, τ, 0, …)`
  have three : ∀ r t τ : ℝ, 0 < r → 0 ≤ t → 0 ≤ τ → r * τ ≤ t ^ 2 →
      LCNZ (fun k => if k = 0 then r else if k = 1 then t else if k = 2 then τ else 0) ∧
      ∀ i : ℕ, dd (fun k => if k = 0 then r else if k = 1 then t else if k = 2 then τ else 0) i =
        r + t * i + τ * (i.choose 2 : ℝ) := by
    intro r t τ hr ht hτ hrt
    refine ⟨⟨fun i => by dsimp only; split_ifs <;> linarith, fun i => ?_, fun i j k hij hjk hi hk => ?_⟩, fun i => ?_⟩
    · rcases i with _ | _ | i <;> simp <;> nlinarith
    · simp only at hi hk ⊢
      split_ifs at hi hk ⊢ <;> first | linarith | omega | (by_contra hc; nlinarith)
    · unfold dd
      rw [iterShift_eq]
      rcases Nat.lt_or_ge i 2 with hi2 | hi2
      · interval_cases i <;> simp [Finset.sum_range_succ]
      · have hf : ∀ h : ℕ, (if h = 0 then r else if h = 1 then t else if h = 2 then τ else 0) =
            (if h = 0 then r else 0) + (if h = 1 then t else 0) + (if h = 2 then τ else 0) := fun h => by
          split_ifs <;> first | omega | ring
        simp only [zero_add, hf, mul_add, Finset.sum_add_distrib, mul_ite, mul_zero, Finset.sum_ite_eq',
          Finset.mem_range, if_pos (show 0 < i + 1 by omega), if_pos (show 1 < i + 1 by omega),
          if_pos (show 2 < i + 1 by omega)]
        simp
        ring
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · obtain ⟨r, κ, hr, hr1, hκ, hb, hc, hlc⟩ := h
    have hN' : (0 : ℝ) < N := by exact_mod_cast hN
    obtain ⟨hl, hd⟩ := three r (κ / N) 0 hr (by positivity) le_rfl (by simp; positivity)
    exact ⟨_, hl, by simpa using hr, hb, fun i hi => by rw [hc i hi, hd]; congr 1; ring, hlc⟩
  · obtain ⟨ν1, ν2, ρ, hν1, hν2, hρ, hρ0, hprof, hc, hb⟩ := h
    refine ⟨ρ, hρ, hρ0, hb, fun i hi => ?_, ?_⟩
    · rw [hc i hi, dd, iterShift_eq]; simp only [zero_add]
    · -- Newton coefficients `(0, ν1, ν2, 0, …)` on `0 ≤ k ≤ N`
      have hn : ∀ k, k ≤ N → newtonCoeff (profile v) k =
          if k = 1 then ν1 else if k = 2 then ν2 else 0 := by
        intro k hk
        rw [newtonCoeff_congr (d' := fun i => (ν1 - ν2 / 2) * (i : ℝ) + (ν2 / 2) * (i : ℝ) ^ 2) (fun i hi => by
          rw [hprof i (by omega), choose2_real]; ring)]
        rw [newtonCoeff_eq_iter]
        have e : (fun i : ℕ => (ν1 - ν2 / 2) * (i : ℝ) + (ν2 / 2) * (i : ℝ) ^ 2) =
            fun i : ℕ => (fun x : ℝ => (ν1 - ν2 / 2) * x ^ 1 + (ν2 / 2) * x ^ 2) (i : ℝ) := by
          funext i; simp
        rcases k with _ | _ | _ | k
        · simp
        · simp [fwdDiff]; try ring
        · simp [fwdDiff]; try ring
        · -- third and higher differences of a quadratic vanish
          have h3 : ∀ m : ℕ, (fwdDiff 1)^[m + 3] (fun i : ℕ => (ν1 - ν2 / 2) * (i : ℝ) + (ν2 / 2) * (i : ℝ) ^ 2) = 0 := by
            intro m
            have hq : (fwdDiff 1)^[3] (fun i : ℕ => (ν1 - ν2 / 2) * (i : ℝ) + (ν2 / 2) * (i : ℝ) ^ 2) = 0 := by
              funext x; simp [fwdDiff]; ring
            rw [Function.iterate_add_apply, hq]
            induction m with
            | zero => rfl
            | succ m ih => rw [Function.iterate_succ_apply', ih]; funext x; simp [fwdDiff]
          rw [show k + 1 + 1 + 1 = k + 3 by omega, h3]; simp
      refine ⟨by rw [hn 1 hN]; simpa, fun k hk1 hkN => ?_, fun k hk2 hkN => ?_, fun k hk1 hkN h0 => ?_⟩
      · rw [hn k hkN]; split_ifs <;> linarith
      · rw [hn (k - 1) (by omega), hn k (by omega), hn (k + 1) hkN]
        split_ifs <;> first | omega | nlinarith | simp | positivity
      · rw [hn (k + 1) (by omega)]
        rw [hn k (by omega)] at h0
        split_ifs at h0 ⊢ <;> first | omega | rfl | linarith | (exfalso; linarith)
  · obtain ⟨r, t, τ, hr, ht, hτ, hrt, hb, hc, hlc⟩ := h
    obtain ⟨hl, hd⟩ := three r t τ hr ht hτ hrt
    exact ⟨_, hl, by simpa using hr, hb, fun i hi => by rw [hc i hi, hd], hlc⟩

/-! ### Proof of Theorem 5.5: log-concavity on integers only -/

theorem newton_examples_quad (ν₁ ν₂ : ℝ) (k : ℕ) :
    newtonCoeff (fun i : ℕ => ν₁ * i + ν₂ * (i.choose 2 : ℝ)) k = if k = 1 then ν₁ else if k = 2 then ν₂ else 0 := by
  rw [newtonCoeff_congr (d' := fun i => (ν₁ - ν₂ / 2) * (i : ℝ) + (ν₂ / 2) * (i : ℝ) ^ 2)
    (fun i _ => by rw [choose2_real]; ring), newtonCoeff_eq_iter]
  rcases k with _ | _ | _ | k
  · simp
  · simp [fwdDiff]; try ring
  · simp [fwdDiff]; try ring
  · have hq : (fwdDiff 1)^[3] (fun i : ℕ => (ν₁ - ν₂ / 2) * (i : ℝ) + (ν₂ / 2) * (i : ℝ) ^ 2) = 0 := by
      funext x; simp [fwdDiff]; ring
    rw [show k + 1 + 1 + 1 = k + 3 by omega, Function.iterate_add_apply, hq]
    have h0 : ∀ m : ℕ, (fwdDiff 1)^[m] (0 : ℕ → ℝ) = 0 := by
      intro m
      induction m with
      | zero => rfl
      | succ m ih => rw [Function.iterate_succ_apply', ih]; funext x; simp [fwdDiff]
    rw [h0]; simp

/-- `ρ(x) = 1 + x/2 + x²/2` has Newton coefficients `(1, 1, 1, 0, …)` (log-concave without internal zeros) but
`(log ρ)''(0) = 3/4 > 0`. -/
theorem log_rho_not_concave :
    let ρ : ℕ → ℝ := fun i => 1 + (i : ℝ) / 2 + (i : ℝ) ^ 2 / 2
    (∀ k : ℕ, newtonCoeff ρ k = if k ≤ 2 then (1 : ℝ) else 0) ∧
    LCNZ (newtonCoeff ρ) ∧
    deriv (deriv fun x : ℝ => Real.log (1 + x / 2 + x ^ 2 / 2)) 0 = 3 / 4 := by
  intro ρ
  have hnc : ∀ k : ℕ, newtonCoeff ρ k = if k ≤ 2 then (1 : ℝ) else 0 := by
    intro k
    rw [newtonCoeff_congr (d' := fun i : ℕ => (1 : ℝ) * (i : ℝ) + (1 : ℝ) * (i.choose 2 : ℝ) + 1)
      (fun i _ => by simp only [ρ, choose2_real]; ring)]
    have hadd : ∀ f : ℕ → ℝ, newtonCoeff (fun i => f i + 1) k = newtonCoeff f k + newtonCoeff (fun _ => (1 : ℝ)) k :=
      fun f => by unfold newtonCoeff; rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun _ _ => by ring
    have hone : newtonCoeff (fun _ : ℕ => (1 : ℝ)) k = (0 : ℝ) ^ k := by
      have := newtonCoeff_const_geom 1 0 0 k
      simp only [zero_mul, add_zero, mul_one] at this
      simpa using this
    rw [hadd, newton_examples_quad, hone]
    rcases k with _ | _ | _ | k <;> simp
  refine ⟨hnc, ⟨fun i => by rw [hnc]; split_ifs <;> norm_num, fun i => ?_, fun i j k hij hjk hi hk => ?_⟩, ?_⟩
  · rw [hnc, hnc, hnc]; split_ifs <;> first | omega | norm_num
  · rw [hnc] at hi hk ⊢; split_ifs at hi hk ⊢ <;> first | omega | norm_num | linarith
  have hpos : ∀ x : ℝ, 0 < 1 + x / 2 + x ^ 2 / 2 := fun x => by nlinarith [sq_nonneg (x + 1 / 2)]
  have hd : deriv (fun x : ℝ => Real.log (1 + x / 2 + x ^ 2 / 2)) = fun x => (1 / 2 + x) / (1 + x / 2 + x ^ 2 / 2) := by
    funext x
    have h1 : HasDerivAt (fun x : ℝ => 1 + x / 2 + x ^ 2 / 2) (1 / 2 + x) x := by
      have := (((hasDerivAt_id' x).div_const 2).const_add 1).add ((hasDerivAt_pow 2 x).div_const 2)
      refine this.congr_deriv ?_
      push_cast; ring
    exact (h1.log (hpos x).ne').deriv
  rw [hd]
  have h2 : HasDerivAt (fun x : ℝ => (1 / 2 + x) / (1 + x / 2 + x ^ 2 / 2)) (3 / 4) 0 := by
    have hn : HasDerivAt (fun x : ℝ => 1 / 2 + x) 1 0 := (hasDerivAt_id 0).const_add _
    have hdn : HasDerivAt (fun x : ℝ => 1 + x / 2 + x ^ 2 / 2) (1 / 2) 0 := by
      have := (((hasDerivAt_id' (0 : ℝ)).div_const 2).const_add 1).add ((hasDerivAt_pow 2 (0 : ℝ)).div_const 2)
      refine this.congr_deriv ?_
      norm_num
    refine (hn.div hdn (hpos 0).ne').congr_deriv ?_
    norm_num
  exact h2.deriv

end Szkraw
