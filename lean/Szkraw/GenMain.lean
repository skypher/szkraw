import Szkraw.VRGenSetting
import Szkraw.VRAssembly
import Szkraw.VRQuadLeib
import Szkraw.VRQuadProfile
import Szkraw.VRAffineMain
import Szkraw.NewtonProduct
import Szkraw.LCConvolution

/-!
# Theorem 8.16: the main assembly, with the key inequality as an explicit input

For a setting `GenSetting N ρc ν u` the weights of the recurrence of Theorem 8.6 satisfy
`ResumWeights3`, provided the key inequality (G-key) holds in that setting. Then the kernels are
nonnegative (`gkernel_resum3`) and the array has property (P) (`matrixPositivity_of_kernel`).

The statement `Stmt_lc_general` is Theorem 8.16 (matrix-positivity conclusion). It is proved here
from the single explicit input `GenKeyStmt`, the key inequality (G-key) of the paper, which is
not yet formalized (see `GenKeyStmt`).
-/

set_option linter.unusedSectionVars false

namespace Szkraw

open Finset

/-- The key inequality (G-key) of Theorem 8.16, in every setting `GenSetting`. -/
def GenKeyStmt : Prop :=
  ∀ (N : ℕ) (ρc ν u : ℕ → ℝ), GenSetting N ρc ν u → ∀ ℓ a : ℕ, ℓ + a ≤ N → 3 ≤ a →
    4 * dd u (ℓ + 1) * genH ρc ν 1 ℓ a ≤
      wA (quadW ν u) 0 ℓ a * wB u 0 (ℓ + 1) (a - 1) + wB u 0 ℓ a * wA (quadW ν u) 0 (ℓ + 1) (a - 2) +
        2 * dd u (ℓ + 1) * genV ρc ν 1 ℓ a

section Weights

variable {N : ℕ} {ρc ν u : ℕ → ℝ} (S : GenSetting N ρc ν u)
include S

/-- The weights of Theorem 8.16 satisfy `ResumWeights3`, given the key inequality and `d ≤ 1`. -/
theorem GenSetting.resumW (hd1 : ∀ m, m ≤ N → dd ν m ≤ 1)
    (hk : ∀ ℓ a : ℕ, ℓ + a ≤ N → 3 ≤ a →
      4 * dd u (ℓ + 1) * genH ρc ν 1 ℓ a ≤
        wA (quadW ν u) 0 ℓ a * wB u 0 (ℓ + 1) (a - 1) + wB u 0 ℓ a * wA (quadW ν u) 0 (ℓ + 1) (a - 2) +
          2 * dd u (ℓ + 1) * genV ρc ν 1 ℓ a) :
    ResumWeights3 (dd u) (wA (quadW ν u)) (wB u) (wC u (quadW ν u)) (genH ρc ν) (genV ρc ν)
      (genW ρc ν) (wSV u (quadW ν u)) N := by
  refine ⟨fun n hn => dd_pos S.hu S.hu1 hn, fun j ℓ a hj h => S.A_split h, fun ℓ a h => ?_,
    fun j ℓ a _ => Wt_nonneg_of S.hu_nn _ _ _ _, fun j ℓ a _ => ?_, fun j ℓ a h => S.H_nn h,
    fun j ℓ a _ => S.V_nn j ℓ a, fun j ℓ a _ => S.W_nn j ℓ a, fun ℓ a h => ?_,
    fun j ℓ a hj h => ?_, fun j ℓ a hj h => ?_, fun j ℓ a hj h => ?_, fun j ℓ a hj h => ?_,
    fun j ℓ a hj h => ?_, fun ℓ a h ha => ?_⟩
  · unfold wA; simpa using S.A0_nn h
  · rw [S.wC_eq]; exact Wt_nonneg S.hν _ _ _ _
  · unfold wSV
    have e : dd (quadW ν u) (ℓ + a) + dd u (ℓ + a) = dd ν (ℓ + a) := by
      unfold dd quadW; rw [iterShift_sub]; ring
    linarith [hd1 (ℓ + a) h]
  · have := S.domB (ℓ := ℓ) (a := a) hj
    unfold wB; rw [show 2 * (j - 1) + 2 = 2 * j by omega]; simpa using this
  · rw [S.wC_eq, S.wC_eq, show 2 * (j - 1) + 2 = 2 * j by omega, show j - 1 + 1 = j by omega]
    have := S.domC (ℓ := ℓ) (a := a) hj h
    unfold wB; simpa using this
  · have := S.domH (ℓ := ℓ) (a := a) hj h
    unfold wB; simpa using this
  · have := S.domV (ℓ := ℓ) (a := a) hj h
    unfold wB; simpa using this
  · have := S.domW (ℓ := ℓ) (a := a) hj h
    unfold wB; simpa using this
  · exact hk ℓ a h ha

/-- Kernel nonnegativity of Theorem 8.16 from the key inequality. -/
theorem GenSetting.kernel_nonneg (hd1 : ∀ m, m ≤ N → dd ν m ≤ 1)
    (hk : ∀ ℓ a : ℕ, ℓ + a ≤ N → 3 ≤ a →
      4 * dd u (ℓ + 1) * genH ρc ν 1 ℓ a ≤
        wA (quadW ν u) 0 ℓ a * wB u 0 (ℓ + 1) (a - 1) + wB u 0 ℓ a * wA (quadW ν u) 0 (ℓ + 1) (a - 2) +
          2 * dd u (ℓ + 1) * genV ρc ν 1 ℓ a)
    (hT : dd (quadW ν u) N + dd u N = 1) {k : ℕ} (hk' : k ≤ N) :
    ∀ ℓ a, 0 ≤ kerFnV u (quadW ν u) k ℓ a :=
  gkernel_resum3 S.hN (S.resumW hd1 hk) (genRec_of S.hu_nn S.hu1)
    (fun a => by rw [kerFnV_zero]; split_ifs <;> norm_num) (kerFnV_supp S.hu_nn S.hu1 N hk' hT)

end Weights

/-- Newton coefficients of a sequence agreeing, up to `N`, in their Newton series. -/
theorem nval_inj_le {e κ : ℕ → ℝ} {N : ℕ} (h : ∀ x, x ≤ N → nval e x = nval κ x) :
    ∀ m, m ≤ N → e m = κ m := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hm
    have hx := h m hm
    unfold nval at hx
    rw [sum_range_succ, sum_range_succ, Nat.choose_self, Nat.cast_one, one_mul, one_mul] at hx
    have hs : ∑ i ∈ range m, (m.choose i : ℝ) * e i = ∑ i ∈ range m, (m.choose i : ℝ) * κ i :=
      sum_congr rfl (fun i hi => by
        rw [ih i (Finset.mem_range.mp hi) (by have := Finset.mem_range.mp hi; omega)])
    linarith

/-- `dd u n` is the Newton series of `u` at `n`. -/
theorem dd_eq_nval (u : ℕ → ℝ) (n : ℕ) : dd u n = nval u n := by
  unfold dd nval
  rw [iterShift_eq]
  simp

/-- The hypotheses of Theorem 8.16 (matrix form): `c_i = ρ(i) d_i`, `ρ(x) = Σ_k ρ_k C(x,k)`, with
`(ρ_k)` nonnegative, log-concave without internal zeros and `ρ_0 > 0`; `d` has log-concave Newton
coefficients; `b` is nondecreasing on `0..N`. -/
def GenRatioHyp {N : ℕ} (vv : Coefficients N) : Prop :=
  ∃ ρc : ℕ → ℝ, LCNZ ρc ∧ 0 < ρc 0 ∧ (∀ i, i < N → vv.b i ≤ vv.b (i + 1)) ∧
    (∀ i, i ≤ N → vv.c i = dd ρc i * profile vv i) ∧
    LogConcaveNoInternalZeros N (newtonCoeff (profile vv))

/-- Theorem 8.16 (log-concave ratio), matrix-positivity conclusion. -/
def Stmt_lc_general : Prop :=
  ∀ (N : ℕ) (vv : Coefficients N), Admissible vv → GenRatioHyp vv → MatrixPositivity vv

/-- **Theorem 8.16, assembly.** Theorem 8.16 follows from the key inequality `GenKeyStmt`. -/
theorem lcgeneral_matrix_of_key (hkey : GenKeyStmt) : Stmt_lc_general := by
  intro N vv hv hyp
  obtain ⟨ρc, hρc, hρ0, hbmono, hc, hlc⟩ := hyp
  have hv' := hv
  obtain ⟨hN, _, hb0, hc0, haN, hsum, hapos, hcpos⟩ := hv'
  set d := profile vv with hd
  set ν := padNewton N (newtonCoeff d) with hν_def
  have hd0 : d 0 = 0 := by simp [hd, profile, hb0, hc0]
  have hν0 : ν 0 = 0 := padNewton_zero _ _
  have hν := padNewton_lcnz hlc
  have hν1 : 0 < ν 1 := by rw [hν_def]; unfold padNewton; rw [if_pos ⟨le_rfl, hN⟩]; exact hlc.1
  have hdd : ∀ i, i ≤ N → dd ν i = d i := fun i hi => dd_padNewton d hd0 N i hi
  -- the product sequence `κ = kap ρc ν` is LCNZ and has the Newton coefficients of `c` up to `N`
  set κ := kap ρc ν with hκ_def
  have hκ : LCNZ κ := kap_LCNZ hρc hν
  have hκc : ∀ m, m ≤ N → newtonCoeff vv.c m = κ m := by
    apply nval_inj_le
    intro x hx
    rw [← nval_mul ρc ν x]
    have h1 : nval (newtonCoeff vv.c) x = vv.c x := (newton_forward vv.c x).symm
    rw [h1, hc x hx, dd_eq_nval ρc x, ← dd_eq_nval ν x, hdd x hx]
  set u := padNewton N (newtonCoeff vv.c) with hu_def
  have hu_eq : u = fun x => if 1 ≤ x ∧ x ≤ N then κ x else 0 := by
    funext x
    rw [hu_def]; unfold padNewton
    by_cases hx : 1 ≤ x ∧ x ≤ N
    · rw [if_pos hx, if_pos hx, hκc x hx.2]
    · rw [if_neg hx, if_neg hx]
  have hu : LCNZ u := by rw [hu_eq]; exact LCNZ.restrict hκ 1 N
  have hu_nn : ∀ i, 0 ≤ u i := hu.1
  have hu0 : u 0 = 0 := padNewton_zero _ _
  have hφ : ∀ ℓ n, ℓ + n ≤ N → Szkraw.iterShift u ℓ n = PhiG ρc ℓ n (Szkraw.iterShift ν ℓ) := by
    intro ℓ n h
    rw [hu_def, iterShift_padNewton vv.c hc0 N ℓ n h]
    have hc' : (fwdDiff 1)^[n] vv.c ℓ = (fwdDiff 1)^[n] (fun i => dd ρc i * dd ν i) ℓ :=
      fwdDiff_iter_congr n ℓ (fun i _ hi => by
        rw [hc i (by omega), hdd i (by omega)])
    rw [hc']
    refine (leibniz_general (fun i => dd ρc i) (fun i => dd ν i) n ℓ).trans ?_
    unfold PhiG
    refine sum_congr rfl (fun j _ => ?_)
    have e1 : Dn j (fun i => dd ρc i) (ℓ + (n - j)) = Szkraw.iterShift ρc (ℓ + (n - j)) j :=
      fwdDiff_dd ρc j _
    have e2 : Dn (n - j) (fun i => dd ν i) ℓ = Szkraw.iterShift ν ℓ (n - j) := fwdDiff_dd ν _ _
    rw [e1, e2]
    ring
  have hw_eq : padNewton N (newtonCoeff vv.b) = quadW ν u := by
    funext i
    unfold quadW
    rw [hν_def, hu_def]
    unfold padNewton
    split_ifs
    · rw [← newtonCoeff_sub]
      exact newtonCoeff_congr fun j _ => by simp [hd, profile]
    · ring
  have hddc : ∀ i, i ≤ N → dd u i = vv.c i := fun i hi => dd_padNewton vv.c hc0 N i hi
  have hddb : ∀ i, i ≤ N → dd (quadW ν u) i = vv.b i := fun i hi => by
    rw [← hw_eq]; exact dd_padNewton vv.b hb0 N i hi
  have S : GenSetting N ρc ν u := by
    refine ⟨hN, hρc, hρ0, hν, hν0, hν1, hu, hφ, fun m hm => ?_⟩
    rw [hddb m (by omega), hddb (m + 1) hm]
    exact hbmono m hm
  have hd1 : ∀ m, m ≤ N → dd ν m ≤ 1 := fun m hm => by
    rw [hdd m hm, hd]
    unfold profile
    have := hsum m hm
    rcases Nat.lt_or_ge m N with h | h
    · linarith [hapos m h]
    · rw [show m = N by omega] at this ⊢; rw [haN] at this; linarith
  have hT : dd (quadW ν u) N + dd u N = 1 := by
    rw [hddb N le_rfl, hddc N le_rfl]; have := hsum N le_rfl; rw [haN] at this; linarith
  exact matrixPositivity_of_kernel vv hv hu_nn S.hu1 hu0 hddc hddb
    (fun k hk => S.kernel_nonneg hd1 (fun ℓ a h ha => hkey N ρc ν u S ℓ a h ha) hT hk)

end Szkraw
