import Szkraw.ProductSmooth
import Szkraw.CornerValue
import Szkraw.Reversal
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Tactic.FunProp

/-!
# Proposition 9.9: thinness near the symmetric endpoint

Section 9 uses the coordinates `b_1, …, b_{N-1}, c_1, …, c_N` of a stochastic array with
`a_0 = 1`, `b_0 = c_0 = 0`, `a_N = 0`, `b_N = 1 - c_N` and `a_n = 1 - b_n - c_n` otherwise
(`stochArray`). A direction `v = (δb, δc)` changes these coordinates; `krawDir N δb δc r ε` is
`K_{N,r} + ε v`. If the first-order change of `g(N,N;N)` along `v` at `K_{N,1}` is negative, then
`K_{N,r} + ε v` is an admissible array with `g(N,N;N) < 0` whenever `r_* < r < 1` and
`C (1 - r)^N ≤ ε ≤ c`.
-/

namespace Szkraw

open Finset Filter Topology

/-- The stochastic array with coordinates `b_1, …, b_{N-1}, c_1, …, c_N`. -/
def stochArray (N : ℕ) (b c : ℕ → ℝ) : Coefficients N where
  a i := if i = 0 then 1 else if i = N then 0 else 1 - b i - c i
  b i := if i = 0 then 0 else if i = N then 1 - c N else b i
  c i := if i = 0 then 0 else c i

/-- `K_{N,r} + ε v` for the direction `v = (δb, δc)` in the coordinates of `stochArray`. -/
noncomputable def krawDir (N : ℕ) (δb δc : ℕ → ℝ) (r ε : ℝ) : Coefficients N :=
  stochArray N (fun n => (1 - r) * n / N + ε * δb n) (fun n => r * n / N + ε * δc n)

variable {N : ℕ} {δb δc : ℕ → ℝ}

theorem krawDir_zero (hN : 1 ≤ N) (r : ℝ) :
    ∀ m, m ≤ N + 1 → productMatrix (krawDir N δb δc r 0) m = productMatrix (krawCoefficients N r) m := by
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  apply product_congr
  · intro i hi
    simp only [krawDir, stochArray, krawCoefficients]
    split_ifs with h0 h1
    · subst h0; simp [hN0]
    · subst h1; simp
    · field_simp; ring
  · intro i hi
    simp only [krawDir, stochArray, krawCoefficients]
    split_ifs with h0 h1
    · subst h0; simp
    · subst h1; field_simp; ring
    · ring
  · intro i hi
    simp only [krawDir, stochArray, krawCoefficients]
    split_ifs with h0
    · subst h0; simp
    · ring

theorem krawDir_admissible_of (hN : 1 ≤ N) {r ε : ℝ} (ha : ∀ i, i < N → 0 < (krawDir N δb δc r ε).a i)
    (hc : ∀ i, 0 < i → i ≤ N → 0 < (krawDir N δb δc r ε).c i) : Admissible (krawDir N δb δc r ε) := by
  refine ⟨hN, by simp [krawDir, stochArray], by simp [krawDir, stochArray], by simp [krawDir, stochArray],
    by simp [krawDir, stochArray, show N ≠ 0 by omega], fun i hi => ?_, ha, hc⟩
  simp only [krawDir, stochArray]
  split_ifs with h0 h1
  · ring
  · rw [h1]; ring
  · ring

/-- `G(r, ε) = g(N, N; N)` at `K_{N,r} + ε v`. -/
noncomputable def cornerG (N : ℕ) (δb δc : ℕ → ℝ) (p : ℝ × ℝ) : ℝ :=
  productMatrix (krawDir N δb δc p.1 p.2) N (Fin.last N) (Fin.last N)

theorem krawDir_a_contDiff (i : ℕ) :
    ContDiff ℝ 1 (fun p : ℝ × ℝ => (krawDir N δb δc p.1 p.2).a i) := by
  simp only [krawDir, stochArray]
  split_ifs <;> fun_prop

theorem krawDir_b_contDiff (i : ℕ) :
    ContDiff ℝ 1 (fun p : ℝ × ℝ => (krawDir N δb δc p.1 p.2).b i) := by
  simp only [krawDir, stochArray]
  split_ifs <;> fun_prop

theorem krawDir_c_contDiff (i : ℕ) :
    ContDiff ℝ 1 (fun p : ℝ × ℝ => (krawDir N δb δc p.1 p.2).c i) := by
  simp only [krawDir, stochArray]
  split_ifs <;> fun_prop

/-- The set where `a_0, …, a_{N-1}` do not vanish. -/
def upwardNonzero (N : ℕ) (δb δc : ℕ → ℝ) : Set (ℝ × ℝ) :=
  {p | ∀ i ∈ range N, (krawDir N δb δc p.1 p.2).a i ≠ 0}

theorem upwardNonzero_open : IsOpen (upwardNonzero N δb δc) := by
  have : upwardNonzero N δb δc = ⋂ i ∈ range N, {p | (krawDir N δb δc p.1 p.2).a i ≠ 0} := by
    ext p; simp [upwardNonzero]
  rw [this]
  exact isOpen_biInter_finset fun i _ =>
    isOpen_ne_fun (krawDir_a_contDiff i).continuous continuous_const

theorem cornerG_contDiffOn : ContDiffOn ℝ 1 (cornerG N δb δc) (upwardNonzero N δb δc) := by
  intro p hp
  apply ContDiffAt.contDiffWithinAt
  exact productMatrix_contDiffAt (fun q : ℝ × ℝ => krawDir N δb δc q.1 q.2) p
    (fun i => (krawDir_a_contDiff i).contDiffAt) (fun i => (krawDir_b_contDiff i).contDiffAt)
    (fun i => (krawDir_c_contDiff i).contDiffAt) N (fun i hi => hp i (mem_range.mpr hi)) _ _

theorem cornerG_hasDerivAt_snd {r t : ℝ} (hp : (r, t) ∈ upwardNonzero N δb δc) :
    HasDerivAt (fun s => cornerG N δb δc (r, s)) (fderiv ℝ (cornerG N δb δc) (r, t) (0, 1)) t := by
  have hd : DifferentiableAt ℝ (cornerG N δb δc) (r, t) :=
    ((cornerG_contDiffOn (r, t) hp).contDiffAt (upwardNonzero_open.mem_nhds hp)).differentiableAt
      one_ne_zero
  have hl : HasDerivAt (fun s : ℝ => (r, s)) ((0 : ℝ), (1 : ℝ)) t :=
    (hasDerivAt_const t r).prodMk (hasDerivAt_id t)
  exact hd.hasFDerivAt.comp_hasDerivAt t hl

/-- **Proposition 9.9** (Thinness near the symmetric endpoint): if the first-order change of
`g(N,N;N)` along `v` at `K_{N,1}` is negative, there are `r_* < 1` and `C, c > 0` such that
`K_{N,r} + ε v` is an admissible array lacking property (P), with `g(N,N;N) < 0`, whenever
`r_* < r < 1` and `C (1 - r)^N ≤ ε ≤ c`. -/
theorem thinness (hN : 2 ≤ N)
    (hneg : deriv (fun ε => productMatrix (krawDir N δb δc 1 ε) N (Fin.last N) (Fin.last N)) 0 < 0) :
    ∃ rstar < 1, ∃ C > 0, ∃ c > 0, ∀ r ε : ℝ, rstar < r → r < 1 → C * (1 - r) ^ N ≤ ε → ε ≤ c →
      Admissible (krawDir N δb δc r ε) ∧ ¬ MatrixPositivity (krawDir N δb δc r ε) ∧
        productMatrix (krawDir N δb δc r ε) N (Fin.last N) (Fin.last N) < 0 := by
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  set G := cornerG N δb δc
  set D := deriv (fun ε => productMatrix (krawDir N δb δc 1 ε) N (Fin.last N) (Fin.last N)) 0
  set φ : ℝ × ℝ → ℝ := fun p => fderiv ℝ G p (0, 1)
  -- positivity of the upward and downward coefficients at `(1, 0)`
  have ha1 : ∀ i ∈ range N, 0 < (krawDir N δb δc (1, (0 : ℝ)).1 (1, (0 : ℝ)).2).a i := by
    intro i hi
    rw [mem_range] at hi
    simp only [krawDir, stochArray]
    split_ifs with h0 h1
    · norm_num
    · omega
    · have : (i : ℝ) < N := by exact_mod_cast hi
      rw [show 1 - ((1 - 1) * (i : ℝ) / N + 0 * δb i) - (1 * i / N + 0 * δc i) = (N - i) / N by
        field_simp; ring]
      exact div_pos (by linarith) hNpos
  have hc1 : ∀ i ∈ Finset.Icc 1 N, 0 < (krawDir N δb δc (1, (0 : ℝ)).1 (1, (0 : ℝ)).2).c i := by
    intro i hi
    rw [Finset.mem_Icc] at hi
    simp only [krawDir, stochArray]
    rw [if_neg (by omega)]
    have : (0 : ℝ) < i := by exact_mod_cast (by omega : 0 < i)
    simp only [one_mul, zero_mul, add_zero]
    exact div_pos this hNpos
  have hU1 : ((1 : ℝ), (0 : ℝ)) ∈ upwardNonzero N δb δc := fun i hi => (ha1 i hi).ne'
  -- `φ (1, 0) = D`
  have hφ1 : φ (1, 0) = D := ((cornerG_hasDerivAt_snd hU1).deriv).symm
  have hφc : ContinuousAt φ (1, 0) := by
    have h := (cornerG_contDiffOn.continuousOn_fderiv_of_isOpen upwardNonzero_open le_rfl).continuousAt
      (upwardNonzero_open.mem_nhds hU1)
    exact h.clm_apply continuousAt_const
  -- everything holds near `(1, 0)`
  have hev : ∀ᶠ p in 𝓝 ((1 : ℝ), (0 : ℝ)), (∀ i ∈ range N, 0 < (krawDir N δb δc p.1 p.2).a i) ∧
      (∀ i ∈ Finset.Icc 1 N, 0 < (krawDir N δb δc p.1 p.2).c i) ∧ φ p < D / 2 ∧ 0 < p.1 := by
    have e1 : ∀ᶠ p in 𝓝 ((1 : ℝ), (0 : ℝ)), ∀ i ∈ range N, 0 < (krawDir N δb δc p.1 p.2).a i :=
      (eventually_all_finset _).mpr fun i hi =>
        continuousAt_const.eventually_lt (krawDir_a_contDiff i).continuous.continuousAt (ha1 i hi)
    have e2 : ∀ᶠ p in 𝓝 ((1 : ℝ), (0 : ℝ)), ∀ i ∈ Finset.Icc 1 N, 0 < (krawDir N δb δc p.1 p.2).c i :=
      (eventually_all_finset _).mpr fun i hi =>
        continuousAt_const.eventually_lt (krawDir_c_contDiff i).continuous.continuousAt (hc1 i hi)
    have e3 : ∀ᶠ p in 𝓝 ((1 : ℝ), (0 : ℝ)), φ p < D / 2 :=
      hφc.eventually_lt continuousAt_const (by rw [hφ1]; linarith)
    have e4 : ∀ᶠ p in 𝓝 ((1 : ℝ), (0 : ℝ)), 0 < p.1 :=
      continuousAt_const.eventually_lt continuous_fst.continuousAt (by norm_num)
    exact e1.and (e2.and (e3.and e4))
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp hev
  refine ⟨1 - δ / 2, by linarith, 4 / (-D), div_pos (by norm_num) (by linarith), δ / 2, by linarith, ?_⟩
  intro r ε hr hr1 hεC hεc
  have h1r : 0 < 1 - r := by linarith
  have hpow : 0 < (1 - r) ^ N := pow_pos h1r N
  have hε : 0 < ε := lt_of_lt_of_le (mul_pos (div_pos (by norm_num) (by linarith)) hpow) hεC
  have hin : ∀ t, 0 ≤ t → t ≤ ε → dist (r, t) ((1 : ℝ), (0 : ℝ)) < δ := by
    intro t ht0 ht
    rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq, max_lt_iff]
    constructor
    · rw [abs_lt]; constructor <;> linarith
    · rw [sub_zero, abs_of_nonneg ht0]; linarith
  have hP : ∀ t, 0 ≤ t → t ≤ ε → _ := fun t ht0 ht => hball (hin t ht0 ht)
  have hU : ∀ t, 0 ≤ t → t ≤ ε → (r, t) ∈ upwardNonzero N δb δc :=
    fun t ht0 ht i hi => ((hP t ht0 ht).1 i hi).ne'
  -- mean value inequality in `ε`
  have hmvt : G (r, ε) - G (r, 0) ≤ D / 2 * (ε - 0) := by
    apply (convex_Icc 0 ε).image_sub_le_mul_sub_of_deriv_le (f := fun s => G (r, s))
    · intro t ht
      exact (cornerG_hasDerivAt_snd (hU t ht.1 ht.2)).continuousAt.continuousWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      exact (cornerG_hasDerivAt_snd (hU t ht.1.le ht.2.le)).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      rw [(cornerG_hasDerivAt_snd (hU t ht.1.le ht.2.le)).deriv]
      exact ((hP t ht.1.le ht.2.le).2.2.1).le
    · exact ⟨le_rfl, hε.le⟩
    · exact ⟨hε.le, le_rfl⟩
    · exact hε.le
  have hG0 : G (r, 0) = (1 - r) ^ N := by
    show productMatrix (krawDir N δb δc r 0) N (Fin.last N) (Fin.last N) = _
    rw [krawDir_zero (by omega) r N (by omega)]
    exact corner_value N (by omega) r (hball (hin 0 le_rfl hε.le)).2.2.2 hr1.le
  have hneg' : G (r, ε) < 0 := by
    have hDε : D / 2 * ε ≤ D / 2 * (4 / (-D) * (1 - r) ^ N) :=
      mul_le_mul_of_nonpos_left hεC (by linarith)
    have e : D / 2 * (4 / (-D) * (1 - r) ^ N) = -2 * (1 - r) ^ N := by
      have hD : D ≠ 0 := hneg.ne
      field_simp
      ring
    linarith
  have hPε := hP ε hε.le le_rfl
  have hadm : Admissible (krawDir N δb δc r ε) :=
    krawDir_admissible_of (by omega) (fun i hi => hPε.1 i (mem_range.mpr hi))
      (fun i hi1 hi2 => hPε.2.1 i (Finset.mem_Icc.mpr ⟨hi1, hi2⟩))
  exact ⟨hadm, fun hpos => absurd (hpos N le_rfl (Fin.last N) (Fin.last N)) (not_le.mpr hneg'), hneg'⟩

end Szkraw
