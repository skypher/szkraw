import Szkraw.RaiseTopMass
import Szkraw.RadiusOrder
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Corollary 9.13: exponentially small stability radius

For `0 < r < 1`, if `(1 - r^2)^N ≤ 1/2` and `3 (1 - r^2)^N ≤ (1 - r)/N`, then
`ρ_N(r) ≤ 3 τ_N^* max_n w_n ≤ 3 (1 - r^2)^N`; in particular `ρ_N(r) = O((1 - r^2)^N)` as `N → ∞`
for every fixed `r`.
-/

namespace Szkraw

open Finset Filter Topology

variable {N : ℕ} {r : ℝ}

/-- `τ_N^* = (1 - (1 - r^2)^N)^{-1/2} - 1`. -/
noncomputable def tauStar (N : ℕ) (r : ℝ) : ℝ := (Real.sqrt (1 - (1 - r ^ 2) ^ N))⁻¹ - 1

theorem kw_le_one (hN : 1 ≤ N) (hr : 0 < r) (hr1 : r ≤ 1) : univ.sup' univ_nonempty (kw N r) ≤ 1 := by
  refine sup'_le _ _ fun t _ => ?_
  have hsum : ∑ s, kw N r s = 1 := binomial_mass_sum _ (one_le_inv_r hr hr1) N hN
  rw [← hsum]
  exact single_le_sum (fun s _ => (k_w_pos hr hr1 s).le) (mem_univ t)

/-- For `0 < x ≤ 1/2`: `0 < (1 - x)^{-1/2} - 1 < x`. -/
theorem tauStar_bounds {x : ℝ} (hx0 : 0 < x) (hx : x ≤ 1 / 2) :
    0 < (Real.sqrt (1 - x))⁻¹ - 1 ∧ (Real.sqrt (1 - x))⁻¹ - 1 < x := by
  set s := Real.sqrt (1 - x)
  have hs0 : 0 < s := Real.sqrt_pos.mpr (by linarith)
  have hs2 : s ^ 2 = 1 - x := Real.sq_sqrt (by linarith)
  have hs1 : s < 1 := by nlinarith
  constructor
  · rw [sub_pos, one_lt_inv₀ hs0]; exact hs1
  · rw [sub_lt_iff_lt_add, inv_lt_comm₀ hs0 (by linarith)]
    -- `1 < (1 + x)^2 (1 - x)`, i.e. `(1+x)⁻¹ < s`
    have h3 : 0 < 1 - x - x ^ 2 := by nlinarith
    have key : 1 < (1 + x) ^ 2 * (1 - x) := by nlinarith [mul_pos hx0 h3]
    have h : (1 / (1 + x)) ^ 2 < s ^ 2 := by
      rw [hs2, div_pow, one_pow, div_lt_iff₀ (by positivity)]; linarith
    have := lt_of_pow_lt_pow_left₀ 2 hs0.le h
    rw [one_div] at this
    rwa [add_comm] at this

/-- **Corollary 9.13** (Exponentially small stability radius). -/
theorem radius_exp (hN : 1 ≤ N) (hr : 0 < r) (hr1 : r < 1) (hx : (1 - r ^ 2) ^ N ≤ 1 / 2)
    (hx2 : 3 * (1 - r ^ 2) ^ N ≤ (1 - r) / N) :
    stabilityRadius N r ≤ 3 * tauStar N r * univ.sup' univ_nonempty (kw N r) ∧
      3 * tauStar N r * univ.sup' univ_nonempty (kw N r) ≤ 3 * (1 - r ^ 2) ^ N := by
  have hr1' := hr1.le
  set x := (1 - r ^ 2) ^ N with hxdef
  set W := univ.sup' univ_nonempty (kw N r) with hWdef
  have hx0 : 0 < x := pow_pos (by nlinarith) N
  have hW0 : 0 < W := lt_of_lt_of_le (k_w_pos hr hr1' 0) (le_sup' (kw N r) (mem_univ 0))
  have hW1 : W ≤ 1 := kw_le_one hN hr hr1'
  obtain ⟨hτ0, hτx⟩ := tauStar_bounds hx0 hx
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  -- every `τ ∈ (τ*, x)` gives an array within `3 τ W` of `K_{N,r}` lacking property (P)
  have hbad : ∀ τ, tauStar N r < τ → τ < x → ∀ ρ ∈ stableRadii N r, ρ < 3 * τ * W := by
    intro τ hτs hτx' ρ ⟨_, hρ⟩
    have hτ : 0 < τ := lt_trans hτ0 hτs
    obtain ⟨hadm, -, -⟩ := raise_measure hN hr hr1 hτ
    have hneg := (raise_sign hN hr hr1 hτ).mpr hτs
    have hbd := raise_bound hN hr hr1 hτ
    have hτW : τ * W < x := lt_of_le_of_lt (by nlinarith) hτx'
    by_contra hge
    push Not at hge
    refine absurd (hρ _ hadm (fun i hi => ?_) (fun i hi => ?_) N le_rfl (Fin.last N) (Fin.last N))
      (not_le.mpr hneg)
    · -- `b̃_i ≥ 0`
      rcases Nat.eq_zero_or_pos i with h0 | hpos
      · rw [h0, hadm.2.2.1]
      · have hb := (hbd i hi).2.1
        have hKb : (krawCoefficients N r).b i = (1 - r) * i / N := rfl
        rw [hKb, abs_le] at hb
        have : (1 - r) / N ≤ (1 - r) * i / N := by
          rw [div_le_div_iff_of_pos_right hN0]
          have : (1 : ℝ) ≤ i := by exact_mod_cast hpos
          nlinarith
        linarith
    · obtain ⟨h1, h2, h3⟩ := hbd i hi
      exact ⟨h1.trans hge, h2.trans hge, h3.trans hge⟩
  -- hence every stable radius is at most `3 τ* W`
  have hbound : ∀ ρ ∈ stableRadii N r, ρ ≤ 3 * tauStar N r * W := by
    intro ρ hρ
    by_contra hlt
    push Not at hlt
    set τ := (tauStar N r + min x (ρ / (3 * W))) / 2
    have hm1 : tauStar N r < min x (ρ / (3 * W)) := by
      refine lt_min hτx ?_
      rw [lt_div_iff₀ (by positivity)]; linarith
    have h1 : tauStar N r < τ := by simp only [τ]; linarith
    have h2 : τ < min x (ρ / (3 * W)) := by simp only [τ]; linarith
    have h3 : τ < ρ / (3 * W) := lt_of_lt_of_le h2 (min_le_right _ _)
    have := hbad τ h1 (lt_of_lt_of_le h2 (min_le_left _ _)) ρ hρ
    rw [lt_div_iff₀ (by positivity)] at h3
    linarith
  have hη : perturbationRadius N r ∈ stableRadii N r := by
    refine ⟨by unfold perturbationRadius; positivity, fun v hv hb hw => ?_⟩
    exact perturbation_matrix_positivity N v r hv hr hr1 ⟨hb, hw⟩
  refine ⟨csSup_le ⟨_, hη⟩ hbound, ?_⟩
  have htau : tauStar N r = (Real.sqrt (1 - x))⁻¹ - 1 := rfl
  have : tauStar N r * W ≤ x := by
    rw [htau]
    calc ((Real.sqrt (1 - x))⁻¹ - 1) * W ≤ ((Real.sqrt (1 - x))⁻¹ - 1) * 1 :=
          mul_le_mul_of_nonneg_left hW1 hτ0.le
      _ ≤ x := by rw [mul_one]; exact hτx.le
  linarith

/-- **Corollary 9.13**, asymptotics: for fixed `0 < r < 1`, `ρ_N(r) ≤ 3 (1 - r^2)^N` for all large `N`. -/
theorem radius_exp_asymp (hr : 0 < r) (hr1 : r < 1) :
    ∃ N₀, ∀ N, N₀ ≤ N → stabilityRadius N r ≤ 3 * (1 - r ^ 2) ^ N := by
  have hq0 : 0 ≤ 1 - r ^ 2 := by nlinarith
  have hq1 : 1 - r ^ 2 < 1 := by nlinarith
  have h1 := (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).eventually (ge_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  have h2 := (tendsto_self_mul_const_pow_of_lt_one hq0 hq1).eventually
    (ge_mem_nhds (by linarith : (0 : ℝ) < (1 - r) / 3))
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp (h1.and h2)
  refine ⟨N₀ + 1, fun N hN => ?_⟩
  obtain ⟨ha, hb⟩ := hN₀ N (by omega)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hx2 : 3 * (1 - r ^ 2) ^ N ≤ (1 - r) / N := by
    rw [le_div_iff₀ hN0]; linarith
  obtain ⟨h, h'⟩ := radius_exp (by omega) hr hr1 ha hx2
  exact h.trans h'

end Szkraw
