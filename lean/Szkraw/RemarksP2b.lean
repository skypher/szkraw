import Szkraw.RemarksP2
import Szkraw.CubicB

/-!
# P2: non-comparability of Theorem 5.3 and Corollary 4.4; the geometric family after Theorem 5.6

* `quad_lowdeg_incomparable`: an array satisfying the hypotheses of Theorem 5.3 but not those of Corollary 4.4
  (geometric profile, `N = 3`), and one satisfying those of Corollary 4.4 but not those of Theorem 5.3 (linear
  profile, cubic ratio, `N = 4`).
* `geometric_kappa`: on the geometric Newton sequence `u_0 = 0`, `u_k = q^(k-1)`, the coefficients of `tτ` and `rσ` in
  (eq:cubic-B) at `(ℓ, n) = (0, 3)` are `20(q+1)(8q³+33q²+30q+6)` and `-20q(4q³+11q²+9q+1)`; their ratio tends to `2`,
  so the coefficientwise test `κ_tτ + u κ_rσ ≥ 0` fails for every `u > 2`.
-/

namespace Szkraw

open Finset Filter Topology

/-! ### Non-comparability -/

/-- Theorem 5.3 and Corollary 4.4 are not comparable. -/
theorem quad_lowdeg_incomparable :
    (∃ v : Coefficients 3, Admissible v ∧ QuadRatioHyp v ∧ ¬ LowDegRatioHyp v) ∧
    (∃ v : Coefficients 4, Admissible v ∧ LowDegRatioHyp v ∧ ¬ QuadRatioHyp v) := by
  constructor
  · -- geometric profile `(0, 1/7, 3/7, 1)`, ratio `1/2 + C(i,2)/20`
    let d : ℕ → ℝ := fun i => if i = 0 then 0 else if i = 1 then 1 / 7 else if i = 2 then 3 / 7 else 1
    let ρ : ℕ → ℝ := fun i => 1 / 2 + (i.choose 2 : ℝ) / 20
    let v : Coefficients 3 := ⟨fun i => 1 - d i, fun i => (1 - ρ i) * d i, fun i => ρ i * d i⟩
    have hprof : ∀ i, profile v i = d i := fun i => by simp only [profile, v]; ring
    refine ⟨v, ⟨by norm_num, by simp [v, d], by simp [v, d], by simp [v, d], by simp [v, d],
      fun i _ => by simp only [v]; ring, fun i hi => ?_, fun i hi hi3 => ?_⟩,
      ⟨1 / 2, 0, 1 / 20, by norm_num, le_rfl, by norm_num, fun i hi => ?_, fun i hi => ?_, ?_⟩, ?_⟩
    · interval_cases i <;> simp [v, d] <;> norm_num
    · interval_cases i <;> simp [v, d, ρ, Nat.choose] <;> norm_num
    · interval_cases i <;> simp [v, d, ρ, Nat.choose] <;> norm_num
    · rw [hprof]; simp only [v, ρ]; ring
    · have h : ∀ k, newtonCoeff (profile v) k = newtonCoeff d k := fun k => by rw [show profile v = d from funext hprof]
      have n1 : newtonCoeff d 1 = 1 / 7 := by simp [newtonCoeff, d, sum_range_succ]
      have n2 : newtonCoeff d 2 = 1 / 7 := by simp [newtonCoeff, d, sum_range_succ]; norm_num
      have n3 : newtonCoeff d 3 = 1 / 7 := by simp [newtonCoeff, d, sum_range_succ]; norm_num
      refine ⟨by rw [h, n1]; norm_num, fun k hk1 hk3 => ?_, fun k hk2 hk3 => ?_, fun k hk1 hk3 h0 => ?_⟩
      · rw [h]; interval_cases k <;> simp [n1, n2, n3]
      · have : k ≤ 2 := by omega
        rw [h, h, h]; interval_cases k; simp [n1, n2, n3]; norm_num
      · rw [h] at h0; interval_cases k <;> simp_all
    · rintro ⟨ν1, ν2, ρ', -, -, -, -, hp, -, -⟩
      have h1 := hp 1 (by norm_num); have h2 := hp 2 (by norm_num); have h3 := hp 3 (by norm_num)
      have h0 := hp 0 (by norm_num)
      rw [hprof] at h0 h1 h2 h3
      simp [d, Nat.choose] at h0 h1 h2 h3
      linarith
  · -- linear profile `i/4`, ratio Newton coefficients `(1/2, 1/20, 1/200, 1/2000, 0, …)`
    let ρk : ℕ → ℝ := fun k => if k = 0 then 1 / 2 else if k = 1 then 1 / 20 else if k = 2 then 1 / 200
      else if k = 3 then 1 / 2000 else 0
    let ρ : ℕ → ℝ := fun i => ∑ k ∈ range (i + 1), (i.choose k : ℝ) * ρk k
    have r1 : ρ 1 = 11 / 20 := by simp [ρ, ρk, sum_range_succ]; norm_num
    have r2 : ρ 2 = 121 / 200 := by simp [ρ, ρk, sum_range_succ]; norm_num
    have r3 : ρ 3 = 1331 / 2000 := by simp [ρ, ρk, sum_range_succ, Nat.choose]; norm_num
    have r4 : ρ 4 = 183 / 250 := by simp [ρ, ρk, sum_range_succ, Nat.choose]; norm_num
    let v : Coefficients 4 := ⟨fun i => 1 - (i : ℝ) / 4, fun i => (1 - ρ i) * ((i : ℝ) / 4), fun i => ρ i * ((i : ℝ) / 4)⟩
    have hprof : ∀ i, profile v i = (i : ℝ) / 4 := fun i => by simp only [profile, v]; ring
    refine ⟨v, ⟨by norm_num, by simp [v], by simp [v], by simp [v], by simp [v], fun i _ => by simp only [v]; ring,
      fun i hi => ?_, fun i hi hi4 => ?_⟩, ⟨1 / 4, 0, ρk, by norm_num, le_rfl, ?_, by simp [ρk], fun i _ => ?_,
      fun i hi => ?_, fun i hi => ?_⟩, ?_⟩
    · interval_cases i <;> simp [v] <;> norm_num
    · interval_cases i <;> simp [v, r1, r2, r3, r4] <;> norm_num
    · refine ⟨fun i => by dsimp only [ρk]; split_ifs <;> norm_num, fun i => ?_, fun i j k hij hjk hi hk => ?_⟩
      · rcases i with _ | _ | _ | i <;> simp [ρk] <;> norm_num
      · dsimp only [ρk] at hi hk ⊢
        split_ifs at hi hk ⊢ <;> first | omega | norm_num | linarith
    · rw [hprof]; simp; ring
    · rw [hprof]
    · interval_cases i <;> simp [v, r1, r2, r3, r4] <;> norm_num
    · rintro ⟨r, t, τ, -, -, -, -, hc, -⟩
      have e : ∀ i, 1 ≤ i → i ≤ 4 → ρ i = r + t * i + τ * (i.choose 2 : ℝ) := fun i h1 h4 => by
        have := hc i h4
        rw [hprof] at this
        have h1' : (1 : ℝ) ≤ i := by exact_mod_cast h1
        have hi : (0 : ℝ) < (i : ℝ) / 4 := by positivity
        exact mul_right_cancel₀ hi.ne' this
      have e1 := e 1 le_rfl (by norm_num); have e2 := e 2 (by norm_num) (by norm_num)
      have e3 := e 3 (by norm_num) (by norm_num); have e4 := e 4 (by norm_num) le_rfl
      rw [r1] at e1; rw [r2] at e2; rw [r3] at e3; rw [r4] at e4
      simp [Nat.choose] at e1 e2 e3 e4
      linarith

/-! ### The geometric family after Theorem 5.6 -/

/-- The coefficient of `tτ` in (eq:cubic-B) at `(ℓ, n) = (0, 3)`. -/
noncomputable def kapTTau (v : ℕ → ℝ) : ℝ :=
  (((3 : ℕ) : ℝ) + 1) * (((3 : ℕ) : ℝ) + 2) * (PhiC 0 1 0 0 0 2 v * PhiC 0 0 1 0 (0 + 1) 3 (fun k => v k + v (k + 1)) +
    PhiC 0 0 1 0 0 2 v * PhiC 0 1 0 0 (0 + 1) 3 (fun k => v k + v (k + 1))) -
  8 * (((3 : ℕ) : ℝ) - 1) * (rhoC 0 1 0 0 (0 + 1) * (v 0 + v 1) * PhiC 0 0 1 0 0 (3 + 2) v +
    rhoC 0 0 1 0 (0 + 1) * (v 0 + v 1) * PhiC 0 1 0 0 0 (3 + 2) v)

/-- The coefficient of `rσ` in (eq:cubic-B) at `(ℓ, n) = (0, 3)`. -/
noncomputable def kapRSig (v : ℕ → ℝ) : ℝ :=
  (((3 : ℕ) : ℝ) + 1) * (((3 : ℕ) : ℝ) + 2) * (PhiC 1 0 0 0 0 2 v * PhiC 0 0 0 1 (0 + 1) 3 (fun k => v k + v (k + 1)) +
    PhiC 0 0 0 1 0 2 v * PhiC 1 0 0 0 (0 + 1) 3 (fun k => v k + v (k + 1))) -
  8 * (((3 : ℕ) : ℝ) - 1) * (rhoC 1 0 0 0 (0 + 1) * (v 0 + v 1) * PhiC 0 0 0 1 0 (3 + 2) v +
    rhoC 0 0 0 1 (0 + 1) * (v 0 + v 1) * PhiC 1 0 0 0 0 (3 + 2) v)

/-- The geometric Newton sequence `u_0 = 0`, `u_k = q^(k-1)`. -/
noncomputable def geoSeq (q : ℝ) (k : ℕ) : ℝ := if k = 0 then 0 else q ^ (k - 1)

theorem geometric_kappa_values (q : ℝ) :
    kapRSig (geoSeq q) = -20 * q * (4 * q ^ 3 + 11 * q ^ 2 + 9 * q + 1) ∧
    kapTTau (geoSeq q) = 20 * (q + 1) * (8 * q ^ 3 + 33 * q ^ 2 + 30 * q + 6) := by
  constructor <;> simp only [kapRSig, kapTTau, PhiC, rhoC, drhoC, d2rhoC, choose2_real, choose3_real, geoSeq] <;>
    push_cast <;> simp <;> ring

/-- **P2, after Theorem 5.6**: on geometric profiles `κ_tτ/|κ_rσ| → 2`, and for every `u > 2` some `q > 0` gives
`κ_tτ + u κ_rσ < 0`, so the coefficientwise test fails for `rσ ≤ u tτ` with `u > 2`. -/
theorem geometric_kappa :
    Tendsto (fun q => kapTTau (geoSeq q) / |kapRSig (geoSeq q)|) atTop (𝓝 2) ∧
    ∀ u : ℝ, 2 < u → ∃ q : ℝ, 0 < q ∧ kapTTau (geoSeq q) + u * kapRSig (geoSeq q) < 0 := by
  have hval := geometric_kappa_values
  constructor
  · have hle : ∀ᶠ q in atTop, kapTTau (geoSeq q) / |kapRSig (geoSeq q)| ≤ 2 + 26 / q := by
      filter_upwards [eventually_ge_atTop (1 : ℝ)] with q hq
      rw [(hval q).1, (hval q).2, abs_of_neg (by nlinarith), div_le_iff₀ (by nlinarith)]
      have : 0 < q := by linarith
      field_simp
      nlinarith [pow_pos this 2, pow_pos this 3, pow_pos this 4]
    have hge : ∀ᶠ q in atTop, 2 ≤ kapTTau (geoSeq q) / |kapRSig (geoSeq q)| := by
      filter_upwards [eventually_ge_atTop (1 : ℝ)] with q hq
      rw [(hval q).1, (hval q).2, abs_of_neg (by nlinarith), le_div_iff₀ (by nlinarith)]
      nlinarith [pow_pos (by linarith : (0 : ℝ) < q) 2, pow_pos (by linarith : (0 : ℝ) < q) 3]
    have h0 : Tendsto (fun q : ℝ => 26 / q) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
    have hlim : Tendsto (fun q : ℝ => 2 + 26 / q) atTop (𝓝 2) := by
      simpa using (tendsto_const_nhds (x := (2 : ℝ))).add h0
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim hge hle
  · intro u hu
    set δ := u - 2 with hδ
    have hδ0 : 0 < δ := by linarith
    refine ⟨27 / δ + 1, by positivity, ?_⟩
    rw [(hval _).1, (hval _).2]
    set q := 27 / δ + 1 with hq
    have h27 : 0 < 27 / δ := by positivity
    have hq1 : 1 ≤ q := by linarith
    have hqδ : 27 < δ * q := by
      rw [hq, mul_add, mul_div_cancel₀ _ hδ0.ne']; linarith
    have hu' : u = 2 + δ := by linarith
    rw [hu']
    have h3 : 0 < q ^ 3 := by positivity
    nlinarith [pow_pos (by linarith : (0 : ℝ) < q) 2, mul_pos hδ0 h3, mul_pos (mul_pos hδ0 h3) (by linarith : (0 : ℝ) < q)]

end Szkraw

namespace Szkraw

open Finset

/-- **P2, after Lemma 5.4**: the weight sums are the coefficients of `Q` on geometric sequences,
`Q(1, r, r², …) = Σ_W N_W(Q) r^W`, for `Q(u) = Σ_{i ≤ j ≤ M} q_{ij} u_i u_j` and
`N_W(Q) = Σ_{i ≤ j, i + j = W} q_{ij}`. -/
theorem weight_sums_geometric (M : ℕ) (q : ℕ → ℕ → ℝ) (r : ℝ) :
    ∑ p ∈ (range (M + 1) ×ˢ range (M + 1)).filter (fun p => p.1 ≤ p.2), q p.1 p.2 * (r ^ p.1 * r ^ p.2) =
      ∑ W ∈ range (2 * M + 1),
        (∑ p ∈ (range (M + 1) ×ˢ range (M + 1)).filter (fun p => p.1 ≤ p.2 ∧ p.1 + p.2 = W), q p.1 p.2) * r ^ W := by
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun p : ℕ × ℕ => p.1 + p.2) (t := range (2 * M + 1)) (fun p hp => by
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp ⊢; omega)]
  refine Finset.sum_congr rfl fun W _ => ?_
  rw [Finset.sum_mul, Finset.filter_filter]
  refine Finset.sum_congr rfl fun p hp => ?_
  simp only [Finset.mem_filter] at hp
  rw [← pow_add, hp.2.2]

end Szkraw
