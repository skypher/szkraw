import Szkraw.CornerIdentity
import Szkraw.KrawtchoukMargin

/-!
# Corollary 9.11: optimal order of the stability radius

`ρ_N(r)` is the supremum of the radii `ρ` such that every array satisfying (2.1) with `b_i ≥ 0`
within distance `ρ` of `K_{N,r}` in the norm (5.2) has property (P). For `N ≥ 2` it is of exact
order `(1 - r)^N` as `r → 1`: the lower bound is Theorem 5.3, and the upper bound comes from
Proposition 9.10 along the terminal direction `δc_N = -sgn(s_N)`, whose first-order change is
`-|s_N|` by Lemma 9.2.
-/

namespace Szkraw

open Finset Filter Topology

/-- `v` is within `ρ` of `K_{N,r}` in the norm (5.2). -/
def WithinKraw {N : ℕ} (v : Coefficients N) (r ρ : ℝ) : Prop :=
  ∀ i, i ≤ N → |v.a i - ((N : ℝ) - i) / N| ≤ ρ ∧ |v.b i - ((1 - r) * i) / N| ≤ ρ ∧ |v.c i - (r * i) / N| ≤ ρ

/-- The radii `ρ ≥ 0` for which every array satisfying (2.1) with `b_i ≥ 0` within `ρ` of
`K_{N,r}` has property (P). -/
def stableRadii (N : ℕ) (r : ℝ) : Set ℝ :=
  {ρ | 0 ≤ ρ ∧ ∀ v : Coefficients N, Admissible v → (∀ i, i ≤ N → 0 ≤ v.b i) → WithinKraw v r ρ →
    MatrixPositivity v}

/-- `ρ_N(r)`, the stability radius of Corollary 9.11. -/
noncomputable def stabilityRadius (N : ℕ) (r : ℝ) : ℝ := sSup (stableRadii N r)

variable {N : ℕ}

/-- The terminal direction `δc_N = -σ`, `δb_N = σ`, all other entries unchanged. -/
def terminalDir (N : ℕ) (σ : ℝ) (n : ℕ) : ℝ := if n = N then -σ else 0

theorem terminal_sum (hN : 2 ≤ N) (σ : ℝ) :
    ∑ n ∈ range (N + 1), (-1 : ℝ) ^ n * (N.choose n : ℝ) * cornerF N (fun _ => 0) (terminalDir N σ) n = -σ := by
  rw [sum_eq_single N]
  · simp only [cornerF, stochDir, terminalDir, Nat.choose_self, Nat.cast_one, mul_one,
      if_neg (show N ≠ 0 by omega)]
    split_ifs with hpar
    · rw [(Even.neg_one_pow ⟨N / 2, by omega⟩ : (-1 : ℝ) ^ N = 1)]; ring
    · rw [(Odd.neg_one_pow ⟨N / 2, by omega⟩ : (-1 : ℝ) ^ N = -1)]; ring
  · intro n hn hnN
    rw [mem_range] at hn
    simp only [cornerF, stochDir, terminalDir, if_neg hnN]
    split_ifs <;> simp
  · intro h; exact absurd (mem_range.mpr (by omega)) h

theorem sN_ne_zero (N : ℕ) : sN N ≠ 0 := by
  rw [sN]
  exact div_ne_zero (pow_ne_zero _ (by norm_num)) (by exact_mod_cast (Nat.choose_pos (by omega)).ne')

/-- The terminal array `K_{N,r} + ε v` lies within `ε` of `K_{N,r}` and has `b_i ≥ 0` when
`ε ≤ 1 - r`, for `|σ| = 1`. -/
theorem terminal_within (hN : 1 ≤ N) {σ r ε : ℝ} (hσ : σ = 1 ∨ σ = -1) (hε : 0 ≤ ε) (hεr : ε ≤ 1 - r) :
    WithinKraw (krawDir N (fun _ => 0) (terminalDir N σ) r ε) r ε ∧
      ∀ i, i ≤ N → 0 ≤ (krawDir N (fun _ => 0) (terminalDir N σ) r ε).b i := by
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  have habs : |σ| = 1 := by rcases hσ with h | h <;> simp [h]
  constructor
  · intro i hi
    simp only [krawDir, stochArray, terminalDir]
    by_cases h0 : i = 0
    · subst h0; simp [hε, hN0]
    by_cases hiN : i = N
    · subst hiN
      simp only [if_neg h0, ↓reduceIte]
      refine ⟨by simp [hε], ?_, ?_⟩
      · rw [show 1 - (r * i / i + ε * -σ) - (1 - r) * i / i = ε * σ by field_simp; ring, abs_mul,
          abs_of_nonneg hε, habs, mul_one]
      · rw [show r * i / i + ε * -σ - r * i / i = -(ε * σ) by ring, abs_neg, abs_mul, abs_of_nonneg hε,
          habs, mul_one]
    · simp only [if_neg h0, if_neg hiN, mul_zero, add_zero]
      refine ⟨?_, by simp [hε], by simp [hε]⟩
      rw [show 1 - (1 - r) * i / N - r * i / N - (N - i) / N = 0 by field_simp; ring]
      simp [hε]
  · intro i hi
    simp only [krawDir, stochArray, terminalDir]
    by_cases h0 : i = 0
    · simp [h0]
    by_cases hiN : i = N
    · subst hiN
      simp only [if_neg h0, ↓reduceIte]
      have : r * i / i = r := by field_simp
      rw [this]
      rcases hσ with h | h <;> subst h <;> nlinarith
    · simp only [if_neg h0, if_neg hiN, mul_zero, add_zero]
      have : (0 : ℝ) ≤ i := Nat.cast_nonneg i
      have h1r : 0 ≤ 1 - r := by linarith
      positivity

/-- **Corollary 9.11** (Optimal order of the stability radius): for `N ≥ 2`, `ρ_N(r)` is of exact
order `(1 - r)^N` as `r → 1`. -/
theorem radius_order (hN : 2 ≤ N) :
    ∃ c₁ > 0, ∃ c₂ > 0, ∃ r₀ < 1, ∀ r, r₀ < r → r < 1 →
      c₁ * (1 - r) ^ N ≤ stabilityRadius N r ∧ stabilityRadius N r ≤ c₂ * (1 - r) ^ N := by
  -- the terminal direction has first-order change `-|s_N| < 0`
  set σ : ℝ := if sN N < 0 then -1 else 1 with hσdef
  have hσ : σ = 1 ∨ σ = -1 := by rw [hσdef]; split_ifs <;> simp
  have hderiv := corner_identity (δb := fun _ => 0) (δc := terminalDir N σ) hN
  rw [terminal_sum hN σ] at hderiv
  have hneg : deriv (fun ε => productMatrix (krawDir N (fun _ => 0) (terminalDir N σ) 1 ε) N (Fin.last N)
      (Fin.last N)) 0 < 0 := by
    rw [hderiv.deriv, hσdef]
    have := sN_ne_zero N
    split_ifs with h
    · linarith
    · have : 0 < sN N := lt_of_le_of_ne (not_lt.mp h) (Ne.symm this)
      linarith
  obtain ⟨rs, hrs, C, hC, c, hc, hthin⟩ := thinness hN hneg
  set δ₀ : ℝ := min (1 / 2) (min (1 / (C + 1)) (c / (C + 1)))
  have hδ₀ : 0 < δ₀ := by positivity
  refine ⟨(1 / 2) * (1 / (32 * N)) ^ N, by positivity, C, hC, max rs (1 - δ₀), max_lt hrs (by linarith), ?_⟩
  intro r hr0 hr1
  have hrs' : rs < r := lt_of_le_of_lt (le_max_left _ _) hr0
  have ht : 1 - r < δ₀ := by have := le_max_right rs (1 - δ₀); linarith
  set t := 1 - r with htdef
  have ht0 : 0 < t := by linarith
  have ht12 : t ≤ 1 / 2 := le_trans ht.le (min_le_left _ _)
  have htC : t ≤ 1 / (C + 1) := le_trans ht.le (le_trans (min_le_right _ _) (min_le_left _ _))
  have htc : t ≤ c / (C + 1) := le_trans ht.le (le_trans (min_le_right _ _) (min_le_right _ _))
  have hr : 1 / 2 ≤ r := by linarith
  have htN : t ^ N ≤ t * t := by
    calc t ^ N = t ^ 2 * t ^ (N - 2) := by rw [← pow_add]; congr 1; omega
      _ ≤ t ^ 2 * 1 := mul_le_mul_of_nonneg_left (pow_le_one₀ ht0.le (by linarith)) (by positivity)
      _ = t * t := by ring
  set ε := C * t ^ N with hεdef
  have hε0 : 0 ≤ ε := by positivity
  have hεt : ε ≤ t := by
    have h1 : C * t ≤ 1 := by
      rw [le_div_iff₀ (by linarith)] at htC; nlinarith
    calc ε ≤ C * (t * t) := mul_le_mul_of_nonneg_left htN hC.le
      _ = (C * t) * t := by ring
      _ ≤ 1 * t := mul_le_mul_of_nonneg_right h1 ht0.le
      _ = t := one_mul t
  have hεc : ε ≤ c := by
    have h1 : C * t ≤ c := by
      rw [le_div_iff₀ (by linarith)] at htc; nlinarith
    calc ε ≤ C * (t * t) := mul_le_mul_of_nonneg_left htN hC.le
      _ = (C * t) * t := by ring
      _ ≤ c * 1 := mul_le_mul h1 (by linarith) ht0.le hc.le
      _ = c := mul_one c
  obtain ⟨hadm, hnotP, -⟩ := hthin r ε hrs' hr1 le_rfl hεc
  obtain ⟨hwithin, hbnn⟩ := terminal_within (N := N) (by omega) hσ hε0 hεt
  -- every stable radius is below `ε`
  have hbound : ∀ ρ ∈ stableRadii N r, ρ ≤ ε := by
    intro ρ ⟨_, hρ⟩
    by_contra hlt
    push Not at hlt
    exact hnotP (hρ _ hadm hbnn fun i hi => by
      obtain ⟨h1, h2, h3⟩ := hwithin i hi
      exact ⟨h1.trans hlt.le, h2.trans hlt.le, h3.trans hlt.le⟩)
  -- the radius of Theorem 5.3 is stable
  have hη : perturbationRadius N r ∈ stableRadii N r := by
    refine ⟨by unfold perturbationRadius; positivity, fun v hv hb hw => ?_⟩
    exact perturbation_matrix_positivity N v r hv (by linarith) hr1 ⟨hb, hw⟩
  have hmin : min r (1 - r) = t := min_eq_right (by linarith)
  refine ⟨?_, csSup_le ⟨_, hη⟩ hbound⟩
  calc (1 / 2) * (1 / (32 * N)) ^ N * (1 - r) ^ N = perturbationRadius N r := by
        rw [perturbationRadius, hmin, div_pow, div_pow, one_pow]; ring
    _ ≤ stabilityRadius N r := le_csSup ⟨ε, hbound⟩ hη

end Szkraw
