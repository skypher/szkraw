import Szkraw.VRAffineMain
import Szkraw.QuadBUnitFails

/-!
# The remarks after Theorem 8.9

With `R = d_{N-1}/(1 - d_{N-1})` the condition of Theorem 8.9 is `κ(N + R) ≤ N(1 - r)`
(`affine_bmono_iff`). For a profile whose Newton coefficients are log-concave without internal zeros:
for the linear profile it reads `κ ≤ N(1-r)/(2N-1)`; in general `d_{N-1} ≤ (N-1)/N`, so every
`κ ∈ [0, N(1-r)/(2N-1)]` is admitted; and for `r < 1` and a nonlinear profile the admitted range is
strictly larger. The example `N = 4`, `d_i = (2^i-1)/15`, `r = 1/2`, `κ = 2/5`.
-/

namespace Szkraw

open Finset

section Profile

variable {N : ℕ} {ν : ℕ → ℝ}

/-- `d(ℓ+a) - d(ℓ) ≤ a f₁(ℓ+a-1)` for a nonnegative sequence `ν` (convexity of the profile). -/
theorem dd_incr_le (hν : LCNZ ν) (ℓ : ℕ) : ∀ a, 1 ≤ a →
    dd ν (ℓ + a) - dd ν ℓ ≤ a * Szkraw.iterShift ν (ℓ + a - 1) 1
  | 0, h => absurd h (by norm_num)
  | 1, _ => by
    have e : dd ν (ℓ + 1) = dd ν ℓ + Szkraw.iterShift ν ℓ 1 := rfl
    rw [e, show ℓ + 1 - 1 = ℓ by omega]; push_cast; linarith
  | a + 2, _ => by
    have ih := dd_incr_le hν ℓ (a + 1) (by omega)
    have e : dd ν (ℓ + (a + 2)) = dd ν (ℓ + (a + 1)) + Szkraw.iterShift ν (ℓ + (a + 1)) 1 := rfl
    have e2 : Szkraw.iterShift ν (ℓ + (a + 1)) 1 = Szkraw.iterShift ν (ℓ + a) 1 + Szkraw.iterShift ν (ℓ + a) 2 := rfl
    have h2 := iterShift_nonneg hν (ℓ + a) 2
    have h1 := iterShift_nonneg hν (ℓ + a) 1
    rw [show ℓ + (a + 1) - 1 = ℓ + a by omega] at ih
    rw [e, show ℓ + (a + 2) - 1 = ℓ + (a + 1) by omega, e2]
    push_cast at ih ⊢
    nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ (a : ℝ) + 1) h2]

theorem f1_mono_of (hν : LCNZ ν) {m m' : ℕ} (h : m ≤ m') :
    Szkraw.iterShift ν m 1 ≤ Szkraw.iterShift ν m' 1 := by
  induction m' with
  | zero => rw [Nat.le_zero.mp h]
  | succ m' ih =>
    rcases Nat.eq_or_lt_of_le h with e | e
    · rw [e]
    · have e2 : Szkraw.iterShift ν (m' + 1) 1 = Szkraw.iterShift ν m' 1 + Szkraw.iterShift ν m' 2 := rfl
      have := iterShift_nonneg hν m' 2
      linarith [ih (by omega)]

end Profile

/-- The profile data of an admissible array with log-concave Newton coefficients: `d_{N-1} ≤ (N-1)/N`,
with equality only for the linear profile. -/
theorem profile_last_le {N : ℕ} (vv : Coefficients N) (hv : Admissible vv)
    (hlc : LogConcaveNoInternalZeros N (newtonCoeff (profile vv))) :
    profile vv (N - 1) ≤ ((N : ℝ) - 1) / N ∧
      (profile vv (N - 1) = ((N : ℝ) - 1) / N → ∀ i, i ≤ N → profile vv i = (i : ℝ) / N) := by
  obtain ⟨hN, _, hb0, hc0, haN, hsum, hapos, hcpos⟩ := hv
  set d := profile vv with hd
  set ν := padNewton N (newtonCoeff d) with hν_def
  have hd0 : d 0 = 0 := by simp [hd, profile, hb0, hc0]
  have hν := padNewton_lcnz hlc
  have hdd : ∀ i, i ≤ N → dd ν i = d i := fun i hi => dd_padNewton d hd0 N i hi
  have hdN : d N = 1 := by have := hsum N le_rfl; rw [haN] at this; simp [hd, profile]; linarith
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hf : 1 - d (N - 1) = Szkraw.iterShift ν (N - 1) 1 := by
    have e1 : dd ν (N - 1 + 1) = dd ν (N - 1) + Szkraw.iterShift ν (N - 1) 1 := rfl
    rw [show N - 1 + 1 = N by omega, hdd N le_rfl, hdd (N - 1) (by omega), hdN] at e1; linarith
  -- `d(ℓ+a) - d(ℓ) ≤ a f₁(N-1)` on `Ω`
  have hinc : ∀ ℓ a, ℓ + a ≤ N → d (ℓ + a) - d ℓ ≤ a * (1 - d (N - 1)) := by
    intro ℓ a h
    rcases Nat.eq_zero_or_pos a with ha | ha
    · subst ha; simp
    · have h1 := dd_incr_le hν ℓ a ha
      have h2 := f1_mono_of hν (show ℓ + a - 1 ≤ N - 1 by omega)
      rw [hdd _ h, hdd _ (by omega)] at h1
      rw [hf]
      have : (a : ℝ) * Szkraw.iterShift ν (ℓ + a - 1) 1 ≤ a * Szkraw.iterShift ν (N - 1) 1 :=
        mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg a)
      linarith
  have hNm : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by push_cast [Nat.cast_sub (show 1 ≤ N by omega)]; ring
  have hle : d (N - 1) ≤ ((N : ℝ) - 1) / N := by
    have := hinc 0 N (by omega)
    rw [zero_add, hdN, hd0] at this
    rw [le_div_iff₀ hNpos]; nlinarith
  refine ⟨hle, fun heq i hi => ?_⟩
  have hP : 1 - d (N - 1) = 1 / N := by rw [heq]; field_simp; ring
  have u := hinc 0 i (by omega)
  have l := hinc i (N - i) (by omega)
  rw [zero_add, hd0, hP] at u
  rw [show i + (N - i) = N by omega, hdN, hP, Nat.cast_sub hi] at l
  have e1 : (i : ℝ) * (1 / N) = i / N := by ring
  have e2 : ((N : ℝ) - i) * (1 / N) = 1 - i / N := by field_simp
  linarith

/-- **The remarks after Theorem 8.9.** For an admissible array whose profile has Newton coefficients
log-concave without internal zeros, with `R = d_{N-1}/(1 - d_{N-1})`:
for the linear profile the condition `κ(N+R) ≤ N(1-r)` reads `κ ≤ N(1-r)/(2N-1)`; for every profile,
every `κ ∈ [0, N(1-r)/(2N-1)]` satisfies it (for `r ≤ 1`); and for `r < 1` and a nonlinear profile,
`κ = N(1-r)/(N+R)` satisfies it although `κ > N(1-r)/(2N-1)`. -/
theorem affine_range_remarks {N : ℕ} (vv : Coefficients N) (hv : Admissible vv)
    (hlc : LogConcaveNoInternalZeros N (newtonCoeff (profile vv))) (r : ℝ) :
    ((∀ i, i ≤ N → profile vv i = (i : ℝ) / N) → ∀ κ : ℝ,
        (κ * (N + profile vv (N - 1) / (1 - profile vv (N - 1))) ≤ N * (1 - r) ↔
          κ ≤ N * (1 - r) / (2 * N - 1))) ∧
      (r ≤ 1 → ∀ κ : ℝ, 0 ≤ κ → κ ≤ N * (1 - r) / (2 * N - 1) →
        κ * (N + profile vv (N - 1) / (1 - profile vv (N - 1))) ≤ N * (1 - r)) ∧
      (r < 1 → (∃ i, i ≤ N ∧ profile vv i ≠ (i : ℝ) / N) →
        N * (1 - r) / (2 * N - 1) < N * (1 - r) / (N + profile vv (N - 1) / (1 - profile vv (N - 1))) ∧
        N * (1 - r) / (N + profile vv (N - 1) / (1 - profile vv (N - 1))) *
          (N + profile vv (N - 1) / (1 - profile vv (N - 1))) ≤ N * (1 - r)) := by
  obtain ⟨hle, hlin⟩ := profile_last_le vv hv hlc
  have hN : 1 ≤ N := hv.1
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  set D := profile vv (N - 1) with hD
  have hD0 : 0 ≤ D := by
    obtain ⟨_, _, hb0, hc0, _, hsum, hapos, hcpos⟩ := hv
    have hd0 : profile vv 0 = 0 := by simp [profile, hb0, hc0]
    have := dd_padNewton (profile vv) hd0 N (N - 1) (by omega)
    rw [hD, ← this]; exact iterShift_nonneg (padNewton_lcnz hlc) _ 0
  have hD1 : D < 1 := by
    have : ((N : ℝ) - 1) / N < 1 := by rw [div_lt_one (by linarith)]; linarith
    linarith
  have hP : 0 < 1 - D := by linarith
  have hR : D / (1 - D) ≤ N - 1 := by
    rw [div_le_iff₀ hP]
    have := hle; rw [le_div_iff₀ (by linarith)] at this; nlinarith
  have hR0 : 0 ≤ D / (1 - D) := div_nonneg hD0 hP.le
  have h2N : (0 : ℝ) < 2 * N - 1 := by linarith
  refine ⟨fun hl κ => ?_, fun hr κ hκ hκ' => ?_, fun hr ⟨i, hi, hne⟩ => ?_⟩
  · have hDv : D = ((N : ℝ) - 1) / N := by
      rw [hD, hl (N - 1) (by omega)]; push_cast [Nat.cast_sub hN]; ring
    have hRv : D / (1 - D) = N - 1 := by
      rw [hDv]; field_simp; ring
    rw [hRv, show (N : ℝ) + (N - 1) = 2 * N - 1 by ring, le_div_iff₀ h2N]
  · have hs : 0 ≤ (N : ℝ) * (1 - r) := mul_nonneg (by linarith) (by linarith)
    rw [le_div_iff₀ h2N] at hκ'
    nlinarith [mul_le_mul_of_nonneg_left hR hκ]
  · have hlt : D < ((N : ℝ) - 1) / N := by
      rcases lt_or_eq_of_le hle with h | h
      · exact h
      · exact absurd (hlin h i hi) hne
    have hRlt : D / (1 - D) < N - 1 := by
      rw [div_lt_iff₀ hP]
      rw [lt_div_iff₀ (by linarith)] at hlt; nlinarith
    have hpos : (0 : ℝ) < N * (1 - r) := mul_pos (by linarith) (by linarith)
    have hNR : (0 : ℝ) < N + D / (1 - D) := by linarith
    refine ⟨div_lt_div_of_pos_left hpos hNR (by linarith), ?_⟩
    rw [div_mul_cancel₀ _ hNR.ne']

/-- The example after Theorem 8.9: `N = 4`, `d_i = (2^i-1)/15`, `r = 1/2`, `κ = 2/5`. -/
noncomputable def affEx : Coefficients 4 where
  a i := 1 - ((2 : ℝ) ^ i - 1) / 15
  b i := (1 - (1 / 2 + 2 / 5 * i / 4)) * (((2 : ℝ) ^ i - 1) / 15)
  c i := (1 / 2 + 2 / 5 * i / 4) * (((2 : ℝ) ^ i - 1) / 15)

theorem affEx_newton (k : ℕ) (hk : 1 ≤ k) : newtonCoeff (profile affEx) k = 1 / 15 := by
  have hp : profile affEx = fun i : ℕ => ((2 : ℝ) ^ i - 1) / 15 := by
    funext i; simp only [profile, affEx]; ring
  have h2 : ((2 : ℝ) + -1) ^ k = ∑ m ∈ range (k + 1), (2 : ℝ) ^ m * (-1) ^ (k - m) * (k.choose m : ℝ) :=
    add_pow _ _ _
  have h1 : ((1 : ℝ) + -1) ^ k = ∑ m ∈ range (k + 1), (1 : ℝ) ^ m * (-1) ^ (k - m) * (k.choose m : ℝ) :=
    add_pow _ _ _
  norm_num at h2
  rw [show (1 : ℝ) + -1 = 0 by norm_num, zero_pow (by omega)] at h1
  simp only [one_pow, one_mul] at h1
  rw [hp]; unfold newtonCoeff
  rw [eq_div_iff (by norm_num : (15 : ℝ) ≠ 0), sum_mul]
  have e : ∀ m ∈ range (k + 1), (-1 : ℝ) ^ (k - m) * (k.choose m : ℝ) * (((2 : ℝ) ^ m - 1) / 15) * 15 =
      (2 : ℝ) ^ m * (-1) ^ (k - m) * (k.choose m : ℝ) - (-1) ^ (k - m) * (k.choose m : ℝ) := by
    intro m _; ring
  rw [sum_congr rfl e, sum_sub_distrib, ← h2, ← h1]; ring

/-- **The example after Theorem 8.9**: the array is admitted by Theorem 8.9 (so it has nonnegative
linearization), `b = (0, 2/75, 3/50, 7/75, 1/10)`, and `(2N-1)κ/N = 7/10 > 1 - r`. -/
theorem affEx_remark :
    Admissible affEx ∧ AffineRatioHyp affEx ∧ MatrixPositivity affEx ∧
      affEx.b 0 = 0 ∧ affEx.b 1 = 2 / 75 ∧ affEx.b 2 = 3 / 50 ∧ affEx.b 3 = 7 / 75 ∧ affEx.b 4 = 1 / 10 ∧
      (2 * 4 - 1) * (2 / 5 : ℝ) / 4 = 7 / 10 ∧ (1 - 1 / 2 : ℝ) < 7 / 10 := by
  have hadm : Admissible affEx := by
    refine ⟨by norm_num, by norm_num [affEx], by norm_num [affEx], by norm_num [affEx], by norm_num [affEx],
      fun i _ => by simp only [affEx]; ring, fun i hi => ?_, fun i hi hi4 => ?_⟩
    · interval_cases i <;> norm_num [affEx]
    · interval_cases i <;> norm_num [affEx]
  have hhyp : AffineRatioHyp affEx := by
    refine ⟨1 / 2, 2 / 5, by norm_num, by norm_num, by norm_num, fun i hi => ?_, fun i hi => ?_, ?_⟩
    · interval_cases i <;> norm_num [affEx]
    · simp only [affEx, profile]; push_cast; ring
    · have hc : (0 : ℝ) < 1 / 15 := by norm_num
      refine ⟨by rw [affEx_newton 1 le_rfl]; exact hc, fun k hk _ => by rw [affEx_newton k hk]; exact hc.le,
        fun k hk _ => by
          rw [affEx_newton (k - 1) (by omega), affEx_newton k (by omega), affEx_newton (k + 1) (by omega)]
          norm_num,
        fun k hk _ h0 => by rw [affEx_newton k hk] at h0; exact absurd h0 hc.ne'⟩
  exact ⟨hadm, hhyp, affine_matrix 4 affEx hadm hhyp, by norm_num [affEx], by norm_num [affEx],
    by norm_num [affEx], by norm_num [affEx], by norm_num [affEx], by norm_num, by norm_num⟩

end Szkraw
