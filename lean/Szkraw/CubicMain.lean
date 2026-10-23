import Szkraw.CubicKey

/-!
# Theorem 8.17 (cubic ratio)

The kernel of the cubic setting `CubicSetting` is nonnegative (`cubic_kernel_nonneg`), by the
resummation lemma `gkernel_resum2` applied to the weights `H = cubicH`, `V = cubicV`, `W = cubicE`
and the key inequality `CubicSetting.key`. The matrix-positivity conclusion follows as for
Theorem 8.11 (`quadratic_ratio_matrix`).
-/

set_option linter.unusedSectionVars false

namespace Szkraw

open Finset

/-- The kernel nonnegativity in the setting of Theorem 8.17. -/
theorem cubic_kernel_nonneg {N : ℕ} {r t τ σ : ℝ} {ν u : ℕ → ℝ} (S : CubicSetting N r t τ σ ν u)
    (hd1 : ∀ m, m ≤ N → dd ν m ≤ 1) (hT : dd (quadW ν u) N + dd u N = 1)
    {k : ℕ} (hk : k ≤ N) : ∀ ℓ a, 0 ≤ kerFnV u (quadW ν u) k ℓ a := by
  have hw : ResumWeights2 (dd u) (wA (quadW ν u)) (wB u) (wC u (quadW ν u)) (cubicH r t τ σ ν)
      (cubicV t τ σ ν) (cubicE τ σ ν) (wSV u (quadW ν u)) N := by
    refine ⟨fun n hn => dd_pos_of S.hu_nn S.hu1 hn, fun j ℓ a hj h => S.A_split h, fun ℓ a h => ?_,
      fun j ℓ a _ => Wt_nonneg_of S.hu_nn _ _ _ _, fun j ℓ a _ => ?_, fun j ℓ a h => S.H_nn h,
      fun j ℓ a _ => S.V_nn j ℓ a, fun j ℓ a _ => S.E_nn j ℓ a, fun ℓ a h => ?_,
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
    · have := S.domE (ℓ := ℓ) (a := a) hj h
      unfold wB; simpa using this
    · have := S.key h ha
      unfold wA wB; simpa using this
  exact gkernel_resum2 S.hN hw (genRec_of S.hu_nn S.hu1)
    (fun a => by rw [kerFnV_zero]; split_ifs <;> norm_num) (kerFnV_supp S.hu_nn S.hu1 N hk hT)

/-- Hypotheses of Theorem 8.17: `c_i = (r + t i + τ C(i,2) + σ C(i,3)) d_i` with `r > 0`,
`t, τ, σ ≥ 0` and `r σ ≤ t τ`, the diagonal coefficients `b_0 ≤ b_1 ≤ ⋯ ≤ b_N` nondecreasing, and a
profile `d = b + c` whose Newton coefficients are log-concave without internal zeros. -/
def CubicRatioHyp {N : ℕ} (vv : Coefficients N) : Prop :=
  ∃ r t τ σ : ℝ, 0 < r ∧ 0 ≤ t ∧ 0 ≤ τ ∧ 0 ≤ σ ∧ r * σ ≤ t * τ ∧
    (∀ i, i < N → vv.b i ≤ vv.b (i + 1)) ∧
    (∀ i, i ≤ N → vv.c i = (r + t * i + τ * (i.choose 2 : ℝ) + σ * (i.choose 3 : ℝ)) * profile vv i) ∧
    LogConcaveNoInternalZeros N (newtonCoeff (profile vv))

/-- Theorem 8.17 (cubic ratio), matrix-positivity conclusion. -/
def Stmt_cubic_ratio : Prop :=
  ∀ (N : ℕ) (vv : Coefficients N), Admissible vv → CubicRatioHyp vv → MatrixPositivity vv

/-- **Theorem 8.17** (cubic ratio). -/
theorem cubic_ratio_matrix : Stmt_cubic_ratio := by
  intro N vv hv hyp
  obtain ⟨r, t, τ, σ, hr, ht, hτ, hσ, hrs, hbmono, hc, hlc⟩ := hyp
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
  have hcN : ∀ i, i ≤ N → vv.c i = rhoC r t τ σ i * dd ν i := fun i hi => by
    rw [hc i hi, hdd i hi]; rfl
  have hφ : ∀ ℓ n, ℓ + n ≤ N → Szkraw.iterShift u ℓ n = PhiC r t τ σ ℓ n (Szkraw.iterShift ν ℓ) := by
    intro ℓ n h
    rw [hu_def, iterShift_padNewton vv.c hc0 N ℓ n h, ← leibniz_cubic]
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
      exact PhiC_nonneg hr.le ht hτ hσ (fun k => iterShift_nonneg hν 0 k) 0 i
    · rw [hu_def]; unfold padNewton; rw [if_neg (by omega)]
  have hddc : ∀ i, i ≤ N → dd u i = vv.c i := fun i hi => dd_padNewton vv.c hc0 N i hi
  have hddb : ∀ i, i ≤ N → dd (quadW ν u) i = vv.b i := fun i hi => by
    rw [← hw_eq]; exact dd_padNewton vv.b hb0 N i hi
  have S : CubicSetting N r t τ σ ν u := by
    refine ⟨hN, hr, ht, hτ, hσ, hrs, hν, hν0, hν1, hu_nn, hφ, fun m hm => ?_⟩
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
    (fun k hk => cubic_kernel_nonneg S hd1 hT hk)

end Szkraw
