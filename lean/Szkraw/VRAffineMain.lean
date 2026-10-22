import Szkraw.VRAffineKey2
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

/-- Hypotheses of Theorem 8.9: `c_i = (r + κ i / N) d_i` with `0 < r ≤ 1` and `κ ≥ 0`, the diagonal
coefficients `b_0 ≤ b_1 ≤ ⋯ ≤ b_N` nondecreasing, and a profile `d = b + c` whose Newton coefficients
are log-concave without internal zeros. -/
def AffineRatioHyp {N : ℕ} (vv : Coefficients N) : Prop :=
  ∃ r κ : ℝ, 0 < r ∧ r ≤ 1 ∧ 0 ≤ κ ∧ (∀ i, i < N → vv.b i ≤ vv.b (i + 1)) ∧
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
  obtain ⟨r, κ, hr, hr1, hκ, hbmono, hc, hlc⟩ := hyp
  have hv' := hv
  obtain ⟨hN, _, hb0, hc0, haN, hsum, hapos, hcpos⟩ := hv'
  set d := profile vv with hd
  set ν := padNewton N (newtonCoeff d) with hν_def
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  set t := κ / N with ht_def
  have ht : 0 ≤ t := div_nonneg hκ hNpos.le
  have hd0 : d 0 = 0 := by simp [hd, profile, hb0, hc0]
  have hν0 : ν 0 = 0 := padNewton_zero _ _
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
      · rw [if_pos hiN, show i = 0 by omega, hν0]; simp
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
  have S : AffSetting N r t ν := by
    refine ⟨hN, hr, ht, fun m hm => ?_, padNewton_lcnz hlc, hν0, ?_⟩
    · rw [hddb m hm.le, hddb (m + 1) hm]; exact hbmono m hm
    · rw [hν_def]; unfold padNewton; rw [if_pos ⟨le_rfl, hN⟩]; exact hlc.1
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

/-- `d_i/f_1(i)` is nondecreasing (cross-multiplied, from `ℓ` to `ℓ + k`), for `ν` log-concave
without internal zeros with `ν 1 > 0`. -/
theorem R_chain_of {ν : ℕ → ℝ} (hν : LCNZ ν) (hν1 : 0 < ν 1) (ℓ k : ℕ) :
    dd ν ℓ * Szkraw.iterShift ν (ℓ + k) 1 ≤ dd ν (ℓ + k) * Szkraw.iterShift ν ℓ 1 := by
  have f1pos : ∀ i, 0 < Szkraw.iterShift ν i 1 := iterShift_one_pos hν hν1
  have step : ∀ i, dd ν i * Szkraw.iterShift ν (i + 1) 1 ≤ dd ν (i + 1) * Szkraw.iterShift ν i 1 := by
    intro i
    have hlc := (hν.iterShift i).2.1 0
    have e1 : dd ν (i + 1) = dd ν i + Szkraw.iterShift ν i 1 := rfl
    have e2 : Szkraw.iterShift ν (i + 1) 1 = Szkraw.iterShift ν i 1 + Szkraw.iterShift ν i 2 := rfl
    have e0 : dd ν i = Szkraw.iterShift ν i 0 := rfl
    rw [e1, e2, e0]
    simp only [zero_add] at hlc
    nlinarith [hlc]
  induction k with
  | zero => simp
  | succ k ih =>
    have hs := step (ℓ + k)
    have hp := f1pos (ℓ + k)
    have hp1 := f1pos (ℓ + k + 1)
    have hpl := f1pos ℓ
    rw [show ℓ + (k + 1) = ℓ + k + 1 by ring]
    have a1 := mul_le_mul_of_nonneg_right ih hp1.le
    have a2 := mul_le_mul_of_nonneg_left hs hpl.le
    have : dd ν ℓ * Szkraw.iterShift ν (ℓ + k + 1) 1 * Szkraw.iterShift ν (ℓ + k) 1 ≤
        dd ν (ℓ + k + 1) * Szkraw.iterShift ν ℓ 1 * Szkraw.iterShift ν (ℓ + k) 1 := by nlinarith
    exact le_of_mul_le_mul_right this hp

/-- **Theorem 8.9, the condition on `κ`**: `b` is nondecreasing exactly when
`κ (N + d_{N-1}/(1 - d_{N-1})) ≤ N(1-r)`. -/
theorem affine_bmono_iff {N : ℕ} (vv : Coefficients N) (hv : Admissible vv) {r κ : ℝ} (hr : 0 < r)
    (hκ : 0 ≤ κ) (hc : ∀ i, i ≤ N → vv.c i = (r + κ * i / N) * profile vv i)
    (hlc : LogConcaveNoInternalZeros N (newtonCoeff (profile vv))) :
    (∀ i, i < N → vv.b i ≤ vv.b (i + 1)) ↔
      κ * (N + profile vv (N - 1) / (1 - profile vv (N - 1))) ≤ N * (1 - r) := by
  obtain ⟨hN, _, hb0, hc0, haN, hsum, hapos, hcpos⟩ := hv
  set d := profile vv with hd
  set ν := padNewton N (newtonCoeff d) with hν_def
  have hd0 : d 0 = 0 := by simp [hd, profile, hb0, hc0]
  have hν := padNewton_lcnz hlc
  have hν1 : 0 < ν 1 := by rw [hν_def]; unfold padNewton; rw [if_pos ⟨le_rfl, hN⟩]; exact hlc.1
  have hdd : ∀ i, i ≤ N → dd ν i = d i := fun i hi => dd_padNewton d hd0 N i hi
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  set t := κ / N with ht_def
  have ht : 0 ≤ t := div_nonneg hκ hNpos.le
  have hbval : ∀ i, i ≤ N → vv.b i = (1 - r - t * i) * d i := fun i hi => by
    have h1 : vv.b i = d i - vv.c i := by simp [hd, profile]
    rw [h1, hc i hi, ht_def]; ring
  -- `b_{i+1} - b_i = (s - t(i+1)) f_1(i) - t d_i`, with `f_1(i) = d_{i+1} - d_i`
  have hinc : ∀ i, i < N → vv.b (i + 1) - vv.b i =
      (1 - r - t * ((i : ℝ) + 1)) * Szkraw.iterShift ν i 1 - t * d i := fun i hi => by
    have e1 : dd ν (i + 1) = dd ν i + Szkraw.iterShift ν i 1 := rfl
    have hf : Szkraw.iterShift ν i 1 = d (i + 1) - d i := by
      rw [← hdd (i + 1) hi, ← hdd i hi.le, e1]; ring
    rw [hbval (i + 1) hi, hbval i hi.le, hf]; push_cast; ring
  have hfN : Szkraw.iterShift ν (N - 1) 1 = 1 - d (N - 1) := by
    have e1 : dd ν (N - 1 + 1) = dd ν (N - 1) + Szkraw.iterShift ν (N - 1) 1 := rfl
    rw [show N - 1 + 1 = N by omega] at e1
    have hdN : d N = 1 := by
      have := hsum N le_rfl; rw [haN] at this; simp [hd, profile]; linarith
    rw [hdd N le_rfl, hdd (N - 1) (by omega), hdN] at e1; linarith
  have hf1pos : ∀ i, 0 < Szkraw.iterShift ν i 1 := iterShift_one_pos hν hν1
  have hpos : 0 < 1 - d (N - 1) := by rw [← hfN]; exact hf1pos _
  have hNm : ((N - 1 : ℕ) : ℝ) + 1 = N := by push_cast [Nat.cast_sub (show 1 ≤ N by omega)]; ring
  -- the last increment is nonnegative exactly when `t (N + R) ≤ s`
  set P := 1 - d (N - 1) with hP
  set D := d (N - 1) with hDdef
  have hlast : (0 ≤ vv.b N - vv.b (N - 1)) ↔ κ * (N + D / P) ≤ N * (1 - r) := by
    have hi := hinc (N - 1) (by omega)
    rw [show N - 1 + 1 = N by omega, hNm, hfN] at hi
    rw [hi]
    have key1 : (N : ℝ) * ((1 - r - t * N) * P - t * D) = N * (1 - r) * P - κ * (N * P + D) := by
      rw [ht_def]; field_simp; ring
    have key2 : κ * (N + D / P) = κ * (N * P + D) / P := by field_simp
    rw [key2, div_le_iff₀ hpos]
    constructor
    · intro h
      have := mul_nonneg hNpos.le h
      rw [key1] at this; linarith
    · intro h
      have h' : 0 ≤ (N : ℝ) * ((1 - r - t * N) * P - t * D) := by rw [key1]; linarith
      by_contra hneg; push Not at hneg
      have := mul_neg_of_pos_of_neg hNpos hneg; linarith
  constructor
  · intro hb
    have h1 := hb (N - 1) (by omega)
    rw [show N - 1 + 1 = N by omega] at h1
    exact hlast.mp (by linarith)
  · intro hk i hi
    have hl := hlast.mpr hk
    have hl' := hinc (N - 1) (by omega)
    rw [show N - 1 + 1 = N by omega, hNm] at hl'
    -- `(s - tN) f_1(N-1) ≥ t d_{N-1}`, then the chain of `d_i/f_1(i)`
    have hA : t * d (N - 1) ≤ (1 - r - t * N) * Szkraw.iterShift ν (N - 1) 1 := by linarith
    have hdN1 : 0 ≤ d (N - 1) := by rw [← hdd (N - 1) (by omega)]; exact iterShift_nonneg hν _ 0
    have hsN : 0 ≤ 1 - r - t * N := by
      by_contra hneg; push Not at hneg
      have := mul_neg_of_neg_of_pos hneg (hf1pos (N - 1))
      nlinarith [mul_nonneg ht hdN1]
    have hch := R_chain_of hν hν1 i (N - 1 - i)
    rw [show i + (N - 1 - i) = N - 1 by omega, hdd i hi.le, hdd (N - 1) (by omega)] at hch
    have hdi : 0 ≤ d i := by rw [← hdd i hi.le]; exact iterShift_nonneg hν _ 0
    have hi1 : (i : ℝ) + 1 ≤ N := by exact_mod_cast (show i + 1 ≤ N by omega)
    -- `(s - tN) f_1(i) f_1(N-1) ≥ t d_{N-1} f_1(i) ≥ t d_i f_1(N-1)`
    have k1 : t * d (N - 1) * Szkraw.iterShift ν i 1 ≤ (1 - r - t * N) * Szkraw.iterShift ν (N - 1) 1 * Szkraw.iterShift ν i 1 :=
      mul_le_mul_of_nonneg_right hA (hf1pos i).le
    have k2 : t * (d i * Szkraw.iterShift ν (N - 1) 1) ≤ t * (d (N - 1) * Szkraw.iterShift ν i 1) :=
      mul_le_mul_of_nonneg_left hch ht
    have k3 : t * d i ≤ (1 - r - t * N) * Szkraw.iterShift ν i 1 := by
      have : t * d i * Szkraw.iterShift ν (N - 1) 1 ≤ (1 - r - t * N) * Szkraw.iterShift ν i 1 * Szkraw.iterShift ν (N - 1) 1 := by
        nlinarith
      exact le_of_mul_le_mul_right this (hf1pos _)
    have k4 : (1 - r - t * N) * Szkraw.iterShift ν i 1 ≤ (1 - r - t * ((i : ℝ) + 1)) * Szkraw.iterShift ν i 1 :=
      mul_le_mul_of_nonneg_right (by nlinarith) (hf1pos i).le
    have := hinc i hi
    linarith

end Szkraw
