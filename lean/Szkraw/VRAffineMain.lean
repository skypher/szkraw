import Szkraw.VRAffineKey
import Szkraw.VRAssembly

/-!
# Theorem 8.9 (linearly increasing ratio)

Statement and assembly: the Newton sequences of `c` and `b` are `affU` and `affW`; the weights of
the recurrence of Theorem 8.6 satisfy `ResumWeights`, so the kernels are nonnegative
(`gkernel_resum`) and the array has property (P) (`matrixPositivity_of_kernel`).
-/

set_option linter.unusedSectionVars false

namespace Szkraw

open Finset

/-- Hypotheses of Theorem 8.9: `c_i = (r + κ i / N) d_i` with `0 < r ≤ 1` and
`0 ≤ κ ≤ N(1-r)/(2N-1)` (written `(2N-1)κ ≤ N(1-r)`), and a profile `d = b + c` whose Newton
coefficients are log-concave without internal zeros. -/
def AffineRatioHyp {N : ℕ} (vv : Coefficients N) : Prop :=
  ∃ r κ : ℝ, 0 < r ∧ r ≤ 1 ∧ 0 ≤ κ ∧ (2 * (N : ℝ) - 1) * κ ≤ N * (1 - r) ∧
    (∀ i, i ≤ N → vv.c i = (r + κ * i / N) * profile vv i) ∧
    LogConcaveNoInternalZeros N (newtonCoeff (profile vv))

/-- Theorem 8.9 (linearly increasing ratio), matrix-positivity conclusion. -/
def Stmt_affine : Prop :=
  ∀ (N : ℕ) (vv : Coefficients N), Admissible vv → AffineRatioHyp vv → MatrixPositivity vv

theorem newtonCoeff_sub (f g : ℕ → ℝ) (k : ℕ) :
    newtonCoeff (fun i => f i - g i) k = newtonCoeff f k - newtonCoeff g k := by
  unfold newtonCoeff
  rw [← sum_sub_distrib]
  exact sum_congr rfl fun i _ => by ring

/-- The kernel nonnegativity in the setting of Theorem 8.9. -/
theorem affine_kernel_nonneg {N : ℕ} {r t : ℝ} {ν : ℕ → ℝ} (S : AffSetting N r t ν)
    (hd1 : ∀ m, m ≤ N → dd ν m ≤ 1) (hT : dd (affW N r t ν) N + dd (affU N r t ν) N = 1)
    {k : ℕ} (hk : k ≤ N) : ∀ ℓ a, 0 ≤ kerFnV (affU N r t ν) (affW N r t ν) k ℓ a := by
  have hU := S.U_lcnz
  have hU1 := S.U_one
  have hw : ResumWeights (dd (affU N r t ν)) (wA (affW N r t ν)) (wB (affU N r t ν))
      (wC (affU N r t ν) (affW N r t ν)) (affH r t ν) (affV t ν) (wSV (affU N r t ν) (affW N r t ν)) N := by
    refine ⟨fun n hn => dd_pos hU hU1 hn, fun j ℓ a hj h => S.A_split h, fun ℓ a h => ?_,
      fun j ℓ a _ => Wt_nonneg hU _ _ _ _, fun j ℓ a _ => ?_, fun j ℓ a h => S.H_nn h,
      fun j ℓ a _ => S.V_nn j ℓ a, fun ℓ a h => ?_, fun j ℓ a hj _ => S.domB hj,
      fun j ℓ a hj h => ?_, fun j ℓ a hj h => ?_, fun j ℓ a hj h => ?_, fun ℓ a h ha => ?_⟩
    · unfold wA; simpa using S.A0_nn h
    · rw [S.wC_eq]; exact Wt_nonneg S.hν _ _ _ _
    · unfold wSV
      have e : dd (affW N r t ν) (ℓ + a) + dd (affU N r t ν) (ℓ + a) = dd ν (ℓ + a) := by
        unfold dd affW; rw [iterShift_sub]; ring
      linarith [hd1 (ℓ + a) h]
    · rw [S.wC_eq, S.wC_eq, show 2 * (j - 1) + 2 = 2 * j by omega, show j - 1 + 1 = j by omega]
      have := S.domC (ℓ := ℓ) (a := a) hj h
      unfold wB; simpa using this
    · have := S.domH (ℓ := ℓ) (a := a) hj h
      unfold wB; simpa using this
    · have := S.domV (ℓ := ℓ) (a := a) hj h
      unfold wB; simpa using this
    · have := S.key h ha
      unfold wA wB; simpa using this
  exact gkernel_resum S.hN hw (genRec_of hU.1 hU1)
    (fun a => by rw [kerFnV_zero]; split_ifs <;> norm_num) (kerFnV_supp hU.1 hU1 N hk hT)

/-- **Theorem 8.9** (linearly increasing ratio). -/
theorem affine_matrix : Stmt_affine := by
  intro N vv hv hyp
  obtain ⟨r, κ, hr, hr1, hκ, hκN, hc, hlc⟩ := hyp
  have hv' := hv
  obtain ⟨hN, _, hb0, hc0, haN, hsum, hapos, hcpos⟩ := hv'
  set d := profile vv with hd
  set ν := padNewton N (newtonCoeff d) with hν_def
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  set t := κ / N with ht_def
  have ht : 0 ≤ t := div_nonneg hκ hNpos.le
  have hts : (2 * (N : ℝ) - 1) * t ≤ 1 - r := by
    rw [ht_def, ← mul_div_assoc, div_le_iff₀ hNpos]; linarith
  have hd0 : d 0 = 0 := by simp [hd, profile, hb0, hc0]
  have S : AffSetting N r t ν := by
    refine ⟨hN, hr, ht, hts, padNewton_lcnz hlc, padNewton_zero _ _, ?_⟩
    rw [hν_def]; unfold padNewton; rw [if_pos ⟨le_rfl, hN⟩]; exact hlc.1
  have hcd : ∀ i, i ≤ N → vv.c i = (r + t * i) * d i := fun i hi => by
    rw [hc i hi, ht_def]; ring
  -- the Newton sequences of `c` and `b`
  have hu_eq : padNewton N (newtonCoeff vv.c) = affU N r t ν := by
    funext i
    unfold padNewton affU kapHat
    by_cases hi : 1 ≤ i ∧ i ≤ N
    · rw [if_pos hi, if_pos hi.2,
        newtonCoeff_congr (d' := fun j : ℕ => (r + t * j) * d j) (fun j hj => hcd j (by omega)),
        newtonCoeff_lin_mul r t d i hi.1]
      have e1 : ν i = newtonCoeff d i := by rw [hν_def]; unfold padNewton; rw [if_pos hi]
      have e2 : ν (i - 1) = newtonCoeff d (i - 1) := by
        rw [hν_def]; unfold padNewton
        by_cases h1 : 1 ≤ i - 1
        · rw [if_pos ⟨h1, by omega⟩]
        · rw [if_neg (by omega), show i - 1 = 0 by omega]
          unfold newtonCoeff; simp [hd0]
      rw [e1, e2]
    · rw [if_neg hi]
      by_cases hiN : i ≤ N
      · rw [if_pos hiN, show i = 0 by omega, S.hν0]; simp
      · rw [if_neg hiN]
  have hw_eq : padNewton N (newtonCoeff vv.b) = affW N r t ν := by
    funext i
    unfold affW
    rw [← hu_eq, hν_def]
    unfold padNewton
    split_ifs
    · rw [← newtonCoeff_sub]
      exact newtonCoeff_congr fun j _ => by simp [hd, profile]
    · ring
  have hddc : ∀ i, i ≤ N → dd (affU N r t ν) i = vv.c i := fun i hi => by
    rw [← hu_eq]; exact dd_padNewton vv.c hc0 N i hi
  have hddb : ∀ i, i ≤ N → dd (affW N r t ν) i = vv.b i := fun i hi => by
    rw [← hw_eq]; exact dd_padNewton vv.b hb0 N i hi
  have hdd : ∀ m, m ≤ N → dd ν m ≤ 1 := fun m hm => by
    rw [hν_def, dd_padNewton d hd0 N m hm, hd]
    unfold profile
    have := hsum m hm
    rcases Nat.lt_or_ge m N with h | h
    · linarith [hapos m h]
    · rw [show m = N by omega] at this ⊢; rw [haN] at this; linarith
  have hT : dd (affW N r t ν) N + dd (affU N r t ν) N = 1 := by
    rw [hddb N le_rfl, hddc N le_rfl]; have := hsum N le_rfl; rw [haN] at this; linarith
  refine matrixPositivity_of_kernel vv hv S.U_lcnz.1 S.U_one (affU_zero S.hν0) hddc hddb
    (fun k' hk' => affine_kernel_nonneg S hdd hT hk')

end Szkraw
