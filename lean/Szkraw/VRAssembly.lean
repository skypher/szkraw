import Szkraw.VRKernel
import Szkraw.VRInduction
import Szkraw.VRDetours
import Szkraw.LCAssembly

/-!
# Theorem 8.6 (varying ratio), Corollary 8.7 and Proposition 8.8 (quadratic arrays)

The kernel `ω` is defined by the recurrence of Theorem 8.6 with `ω(0,a) = [a = k]`. It has the
support property; under the hypotheses it is nonnegative (generic induction of `VRInduction.lean`);
its coefficient array satisfies `ℒ_z L = ℒ_w L` (`VRKernel.lean`). With `e_{i+1}/e_i = a_i/c_{i+1}`
the array `e_k L/(e_m e_n)` satisfies the recurrence of `productMatrix`, so `g(m,n;k) ≥ 0`.
-/

namespace Szkraw

open Finset

/-! ### The kernel -/

noncomputable def kerLevelsV (u v : ℕ → ℝ) (k : ℕ) : ℕ → (ℕ → ℕ → ℝ)
  | 0 => fun ℓ a => if ℓ = 0 ∧ a = k then 1 else 0
  | L + 1 => fun ℓ a =>
      if ℓ ≤ L then kerLevelsV u v k L ℓ a
      else ((1 - dd v (L + a) - dd u (L + a)) * kerLevelsV u v k L L a +
        ∑ j ∈ range (L + 1), (-1 : ℝ) ^ j * grpV u v (kerLevelsV u v k L) j L a) / dd u (L + 1)

noncomputable def kerFnV (u v : ℕ → ℝ) (k ℓ a : ℕ) : ℝ := kerLevelsV u v k ℓ ℓ a

variable {u v : ℕ → ℝ} {k : ℕ}

theorem kerLevelsV_eq (L : ℕ) : ∀ ℓ a, ℓ ≤ L → kerLevelsV u v k L ℓ a = kerFnV u v k ℓ a := by
  induction L with
  | zero => intro ℓ a h; rw [Nat.le_zero.mp h]; rfl
  | succ L ih =>
    intro ℓ a h
    by_cases hl : ℓ ≤ L
    · show (if ℓ ≤ L then kerLevelsV u v k L ℓ a else _) = _
      rw [if_pos hl, ih ℓ a hl]
    · have : ℓ = L + 1 := by omega
      subst this; rfl

theorem grpV_congr {ω₁ ω₂ : ℕ → ℕ → ℝ} {ℓ : ℕ} (h : ∀ ℓ' a, ℓ' ≤ ℓ → ω₁ ℓ' a = ω₂ ℓ' a) (j a : ℕ) :
    grpV u v ω₁ j ℓ a = grpV u v ω₂ j ℓ a := by
  unfold grpV moveAV moveBV moveCV
  rw [h _ _ (Nat.sub_le _ _), h _ _ (Nat.sub_le _ _)]
  split_ifs
  · rw [h _ _ (by omega)]
  · rfl

theorem dd_pos_of (hu : ∀ i, 0 ≤ u i) (hu1 : 0 < u 1) {n : ℕ} (hn : 1 ≤ n) : 0 < dd u n := by
  unfold dd
  rw [iterShift_eq]
  have hmem : 1 ∈ range (n + 1) := mem_range.mpr (by omega)
  have := single_le_sum (f := fun h => (n.choose h : ℝ) * u (0 + h))
    (fun i _ => mul_nonneg (Nat.cast_nonneg _) (hu _)) hmem
  have h1 : (0 : ℝ) < (n.choose 1 : ℝ) * u (0 + 1) := by
    rw [Nat.choose_one_right]; simp only [zero_add]; exact mul_pos (by exact_mod_cast hn) hu1
  linarith

theorem kerFnV_rec (hu : ∀ i, 0 ≤ u i) (hu1 : 0 < u 1) : KernelRecV u v (kerFnV u v k) := by
  intro ℓ a
  have hd : dd u (ℓ + 1) ≠ 0 := ne_of_gt (dd_pos_of hu hu1 (by omega))
  have e : kerFnV u v k (ℓ + 1) a =
      ((1 - dd v (ℓ + a) - dd u (ℓ + a)) * kerLevelsV u v k ℓ ℓ a +
        ∑ j ∈ range (ℓ + 1), (-1 : ℝ) ^ j * grpV u v (kerLevelsV u v k ℓ) j ℓ a) / dd u (ℓ + 1) := by
    show (if ℓ + 1 ≤ ℓ then _ else _) = _
    rw [if_neg (by omega)]
  rw [e, mul_div_cancel₀ _ hd]
  have hg : ∀ j, grpV u v (kerLevelsV u v k ℓ) j ℓ a = grpV u v (kerFnV u v k) j ℓ a :=
    fun j => grpV_congr (fun ℓ' a' h => kerLevelsV_eq ℓ ℓ' a' h) j a
  simp only [hg]
  rfl

theorem kerFnV_zero (a : ℕ) : kerFnV u v k 0 a = if a = k then 1 else 0 := by
  show (if 0 = 0 ∧ a = k then (1 : ℝ) else 0) = _
  simp

theorem kerFnV_supp (hu : ∀ i, 0 ≤ u i) (hu1 : 0 < u 1) (N : ℕ) (hk : k ≤ N)
    (hT : dd v N + dd u N = 1) : ∀ ℓ a, N < ℓ + a → kerFnV u v k ℓ a = 0 := by
  intro ℓ
  induction ℓ using Nat.strong_induction_on with
  | _ ℓ ih =>
    intro a ha
    rcases ℓ with _ | ℓ
    · rw [kerFnV_zero, if_neg (by omega)]
    · have hrec := kerFnV_rec (v := v) (k := k) hu hu1 ℓ a
      have hd : dd u (ℓ + 1) ≠ 0 := ne_of_gt (dd_pos_of hu hu1 (by omega))
      have h1 : (1 - dd v (ℓ + a) - dd u (ℓ + a)) * kerFnV u v k ℓ a = 0 := by
        by_cases h : ℓ + a = N
        · rw [h, show 1 - dd v N - dd u N = 0 by linarith, zero_mul]
        · rw [ih ℓ (by omega) a (by omega), mul_zero]
      have h2 : ∀ j ∈ range (ℓ + 1), (-1 : ℝ) ^ j * grpV u v (kerFnV u v k) j ℓ a = 0 := by
        intro j hj
        rw [Finset.mem_range] at hj
        unfold grpV moveAV moveBV moveCV
        rw [ih (ℓ - j) (by omega) _ (by omega), ih (ℓ - j) (by omega) _ (by omega)]
        split_ifs
        · rw [ih (ℓ - j - 1) (by omega) _ (by omega)]; ring
        · ring
      rw [h1, sum_eq_zero h2, add_zero] at hrec
      exact (mul_eq_zero.mp hrec).resolve_left hd

/-- The weights of the recurrence of Theorem 8.6, in the generic form. -/
noncomputable def wA (v : ℕ → ℝ) (j ℓ a : ℕ) : ℝ := Wt v (2 * j + 1) j ℓ a
noncomputable def wB (u : ℕ → ℝ) (j ℓ a : ℕ) : ℝ := Wt u (2 * j + 2) j ℓ a
noncomputable def wC (u v : ℕ → ℝ) (j ℓ a : ℕ) : ℝ := Wt u (2 * j + 2) (j + 1) ℓ a + Wt v (2 * j + 2) (j + 1) ℓ a
noncomputable def wSV (u v : ℕ → ℝ) (ℓ a : ℕ) : ℝ := 1 - dd v (ℓ + a) - dd u (ℓ + a)

theorem genRec_of (hu : ∀ i, 0 ≤ u i) (hu1 : 0 < u 1) :
    GenRec (dd u) (wA v) (wB u) (wC u v) (wSV u v) (kerFnV u v k) := by
  intro ℓ a
  have h := kerFnV_rec (v := v) (k := k) hu hu1 ℓ a
  rw [h]
  rfl

/-! ### From the kernel to the product coefficients -/

/-- If the kernels are nonnegative for every `k ≤ N`, the array has property (P). -/
theorem matrixPositivity_of_kernel {N : ℕ} (vv : Coefficients N) (hv : Admissible vv)
    (hu : ∀ i, 0 ≤ u i) (hu1 : 0 < u 1) (hu0 : u 0 = 0)
    (hddc : ∀ i, i ≤ N → dd u i = vv.c i) (hddb : ∀ i, i ≤ N → dd v i = vv.b i)
    (hnn : ∀ k', k' ≤ N → ∀ ℓ a, 0 ≤ kerFnV u v k' ℓ a) : MatrixPositivity vv := by
  obtain ⟨hN, _, hb0, hc0, haN, hsum, hapos, hcpos⟩ := hv
  have hT : dd v N + dd u N = 1 := by
    rw [hddb N le_rfl, hddc N le_rfl]; have := hsum N le_rfl; rw [haN] at this; linarith
  have hsupp : ∀ k', k' ≤ N → ∀ ℓ a, N < ℓ + a → kerFnV u v k' ℓ a = 0 :=
    fun k' hk' => kerFnV_supp hu hu1 N hk' hT
  set e : ℕ → ℝ := fun i => ∏ j ∈ range i, (vv.a j / vv.c (j + 1)) with he_def
  have he_succ : ∀ i, e (i + 1) = e i * (vv.a i / vv.c (i + 1)) := fun i => prod_range_succ _ _
  have he_pos : ∀ i, i ≤ N → 0 < e i := fun i hi => by
    apply prod_pos; intro j hj; rw [Finset.mem_range] at hj
    exact div_pos (hapos j (by omega)) (hcpos (j + 1) (by omega) (by omega))
  have he0 : e 0 = 1 := prod_range_zero _
  set G : ℕ → ℕ → ℕ → ℝ := fun m n k' => e k' / (e m * e n) * Lker N (kerFnV u v k') m n with hG
  have h0 : ∀ n k' : ℕ, n ≤ N → k' ≤ N → G 0 n k' = if n = k' then 1 else 0 := by
    intro n k' hn hk'
    simp only [hG]
    rw [Lker_zero_left N _ n hn, kerFnV_zero, he0, one_mul]
    split_ifs with h
    · subst h; rw [div_self (he_pos n hn).ne', one_mul]
    · rw [mul_zero]
  have ha_eq : ∀ i, i ≤ N → vv.a i = 1 - vv.b i - vv.c i := fun i hi => by
    have := hsum i hi; linarith
  have hrecG : ∀ m n k', m + 1 ≤ N → n ≤ N → k' ≤ N →
      vv.a m * G (m + 1) n k' =
        (if n + 1 ≤ N then vv.a n * G m (n + 1) k' else 0) + vv.b n * G m n k' +
        (if 1 ≤ n then vv.c n * G m (n - 1) k' else 0) - vv.b m * G m n k' -
        (if 1 ≤ m then vv.c m * G (m - 1) n k' else 0) := by
    intro m n k' hm hn hk'
    set L := Lker N (kerFnV u v k') with hL
    have star := kernel_starV hu0 N (kerFnV_rec (v := v) (k := k') hu hu1) (hsupp k' hk') m n
    unfold LzV LwV at star
    rw [← hL] at star
    have em : e m ≠ 0 := (he_pos m (by omega)).ne'
    have en : e n ≠ 0 := (he_pos n hn).ne'
    set E := e k' / (e m * e n) with hE
    have hcm1 : vv.c (m + 1) ≠ 0 := (hcpos (m + 1) (by omega) hm).ne'
    have ham : vv.a m ≠ 0 := (hapos m (by omega)).ne'
    -- rewrite the star relation in the array's coefficients
    have sm : dd u (m + 1) * L (m + 1) n + dd v m * L m n +
        (if 1 ≤ m then (1 - dd v (m - 1) - dd u (m - 1)) * L (m - 1) n else 0) =
        vv.c (m + 1) * L (m + 1) n + vv.b m * L m n +
        (if 1 ≤ m then vv.a (m - 1) * L (m - 1) n else 0) := by
      rw [hddc (m + 1) hm, hddb m (by omega)]
      split_ifs
      · rw [hddb (m - 1) (by omega), hddc (m - 1) (by omega), ha_eq (m - 1) (by omega)]
      · rfl
    have sn : dd u (n + 1) * L m (n + 1) + dd v n * L m n +
        (if 1 ≤ n then (1 - dd v (n - 1) - dd u (n - 1)) * L m (n - 1) else 0) =
        (if n + 1 ≤ N then vv.c (n + 1) * L m (n + 1) else 0) + vv.b n * L m n +
        (if 1 ≤ n then vv.a (n - 1) * L m (n - 1) else 0) := by
      rw [hddb n hn]
      have e1 : dd u (n + 1) * L m (n + 1) = if n + 1 ≤ N then vv.c (n + 1) * L m (n + 1) else 0 := by
        split_ifs with h
        · rw [hddc (n + 1) h]
        · rw [show n = N by omega, hL, Lker_top N _ (hsupp k' hk') m, mul_zero]
      rw [e1]
      split_ifs
      · rw [hddb (n - 1) (by omega), hddc (n - 1) (by omega), ha_eq (n - 1) (by omega)]
      · rfl
      · rw [hddb (n - 1) (by omega), hddc (n - 1) (by omega), ha_eq (n - 1) (by omega)]
      · rfl
    rw [sm, sn] at star
    -- conversions
    have c1 : vv.a m * G (m + 1) n k' = E * (vv.c (m + 1) * L (m + 1) n) := by
      simp only [hG]; rw [← hL, he_succ m, hE]; field_simp
    have c2m : vv.b m * G m n k' = E * (vv.b m * L m n) := by simp only [hG]; rw [← hL]; ring
    have c2n : vv.b n * G m n k' = E * (vv.b n * L m n) := by simp only [hG]; rw [← hL]; ring
    have c3m : (if 1 ≤ m then vv.c m * G (m - 1) n k' else 0) =
        E * (if 1 ≤ m then vv.a (m - 1) * L (m - 1) n else 0) := by
      split_ifs with h
      · simp only [hG]; rw [← hL, hE]
        have hs := he_succ (m - 1)
        rw [show m - 1 + 1 = m by omega] at hs
        have hcm : vv.c m ≠ 0 := (hcpos m (by omega) (by omega)).ne'
        have ham1 : vv.a (m - 1) ≠ 0 := (hapos (m - 1) (by omega)).ne'
        have em1 : e (m - 1) ≠ 0 := (he_pos (m - 1) (by omega)).ne'
        rw [hs]; field_simp
      · ring
    have c1n : (if n + 1 ≤ N then vv.a n * G m (n + 1) k' else 0) =
        E * (if n + 1 ≤ N then vv.c (n + 1) * L m (n + 1) else 0) := by
      split_ifs with h
      · simp only [hG]; rw [← hL, hE, he_succ n]
        have hcn1 : vv.c (n + 1) ≠ 0 := (hcpos (n + 1) (by omega) h).ne'
        have han : vv.a n ≠ 0 := (hapos n (by omega)).ne'
        field_simp
      · ring
    have c3n : (if 1 ≤ n then vv.c n * G m (n - 1) k' else 0) =
        E * (if 1 ≤ n then vv.a (n - 1) * L m (n - 1) else 0) := by
      split_ifs with h
      · simp only [hG]; rw [← hL, hE]
        have hs := he_succ (n - 1)
        rw [show n - 1 + 1 = n by omega] at hs
        have hcn : vv.c n ≠ 0 := (hcpos n (by omega) hn).ne'
        have han1 : vv.a (n - 1) ≠ 0 := (hapos (n - 1) (by omega)).ne'
        have en1 : e (n - 1) ≠ 0 := (he_pos (n - 1) (by omega)).ne'
        rw [hs]; field_simp
      · ring
    rw [c1, c1n, c2n, c3n, c2m, c3m]
    linear_combination E * star
  intro m hm n k'
  rw [product_eq_of_rec vv G (fun i hi => (hapos i hi).ne') h0 hrecG m hm n k']
  simp only [hG]
  exact mul_nonneg (div_nonneg (he_pos k' (by omega)).le
    (mul_pos (he_pos m hm) (he_pos n (by omega))).le)
    (Lker_nonneg N _ (hnn k' (by omega)) m n)

/-! ### Theorem 8.6 -/

/-- Hypotheses of Theorem 8.6: the Newton coefficients `κ` of `c` are log-concave without internal
zeros, those `β` of `b` are nonnegative, and the two mixed inequalities hold for `0 ≤ ℓ ≤ N-1`,
with `φ_n(ℓ) = Σ_h C(ℓ,h) κ_{n+h}` and `ψ_n(ℓ) = Σ_h C(ℓ,h) β_{n+h}` (`κ_0 = β_0 = 0`, zero
beyond `N`); here `iterShift (padNewton N κ) ℓ n = φ_n(ℓ)` (`iterShift_eq`). -/
def VaryRatioHyp {N : ℕ} (vv : Coefficients N) : Prop :=
  LogConcaveNoInternalZeros N (newtonCoeff vv.c) ∧
  (∀ k, 1 ≤ k → k ≤ N → 0 ≤ newtonCoeff vv.b k) ∧
  MixedIneq (padNewton N (newtonCoeff vv.c)) (padNewton N (newtonCoeff vv.b)) N

/-- Theorem 8.6 (varying ratio), matrix-positivity conclusion. -/
def Stmt_varyratio : Prop :=
  ∀ (N : ℕ) (vv : Coefficients N), Admissible vv → VaryRatioHyp vv → MatrixPositivity vv

theorem padNewton_nonneg {N : ℕ} {β : ℕ → ℝ} (h : ∀ k, 1 ≤ k → k ≤ N → 0 ≤ β k) (i : ℕ) :
    0 ≤ padNewton N β i := by
  unfold padNewton; split_ifs with hi
  · exact h i hi.1 hi.2
  · exact le_rfl

theorem padNewton_zero (N : ℕ) (β : ℕ → ℝ) : padNewton N β 0 = 0 := by
  unfold padNewton; rw [if_neg (by omega)]

/-- **Theorem 8.6** (varying ratio). -/
theorem varyratio_matrix : Stmt_varyratio := by
  intro N vv hv hyp
  obtain ⟨hlc, hβ, hMI⟩ := hyp
  have hv' := hv
  obtain ⟨hN, _, hb0, hc0, _, _, _, _⟩ := hv'
  set u := padNewton N (newtonCoeff vv.c) with hu_def
  set w := padNewton N (newtonCoeff vv.b) with hw_def
  have hu : LCNZ u := padNewton_lcnz hlc
  have hu1 : 0 < u 1 := by rw [hu_def]; unfold padNewton; rw [if_pos ⟨le_rfl, hN⟩]; exact hlc.1
  have hu0 : u 0 = 0 := padNewton_zero _ _
  have hw : ∀ i, 0 ≤ w i := padNewton_nonneg hβ
  have hddc : ∀ i, i ≤ N → dd u i = vv.c i := fun i hi => dd_padNewton vv.c hc0 N i hi
  have hddb : ∀ i, i ≤ N → dd w i = vv.b i := fun i hi => dd_padNewton vv.b hb0 N i hi
  refine matrixPositivity_of_kernel vv hv hu.1 hu1 hu0 hddc hddb (fun k' hk' => ?_)
  -- the generic induction
  have hsum := hv.2.2.2.2.2.1
  have hapos := hv.2.2.2.2.2.2.1
  have haN := hv.2.2.2.2.1
  have hT : dd w N + dd u N = 1 := by
    rw [hddb N le_rfl, hddc N le_rfl]; have := hsum N le_rfl; rw [haN] at this; linarith
  have hgw : GenWeights (dd u) (wA w) (wB u) (wC u w) (wSV u w) N := by
    refine ⟨fun n hn => dd_pos hu hu1 hn, fun j ℓ a _ => Wt_nonneg_of hw _ _ _ _,
      fun j ℓ a _ => Wt_nonneg hu _ _ _ _,
      fun j ℓ a _ => add_nonneg (Wt_nonneg hu _ _ _ _) (Wt_nonneg_of hw _ _ _ _), fun ℓ a hla => ?_,
      fun j ℓ a hj hla => ?_, fun j ℓ a hj hla => ?_, fun j ℓ a hj hla => ?_⟩
    · unfold wSV
      rcases Nat.lt_or_ge (ℓ + a) N with h | h
      · rw [hddb _ h.le, hddc _ h.le]; have := hsum (ℓ + a) h.le; linarith [hapos (ℓ + a) h]
      · rw [show ℓ + a = N by omega]; linarith
    · unfold wA wB
      have := lemma_8_4_AV hu hw hMI j ℓ a hj hla
      have e1 : 2 * (j - 1) + 2 = 2 * j := by omega
      have e2 : 2 * (j - 1) + 1 = 2 * j - 1 := by omega
      simp only [Nat.mul_zero, zero_add, e1, e2]
      have hdd : Szkraw.iterShift u (ℓ + 1) 0 = dd u (ℓ + 1) := rfl
      rw [hdd] at this; exact this
    · unfold wB
      have := lemma_8_4_B hu j ℓ a hj
      have e1 : 2 * (j - 1) + 2 = 2 * j := by omega
      simp only [Nat.mul_zero, zero_add, e1]
      exact this
    · unfold wB wC
      have h1 := lemma_8_4_C hu j ℓ a hj
      have h2 := lemma_8_4_CV hu hw hMI j ℓ a hj hla
      have e1 : 2 * (j - 1) + 2 = 2 * j := by omega
      have e2 : j - 1 + 1 = j := by omega
      simp only [Nat.mul_zero, zero_add, e1, e2]
      have hdd : Szkraw.iterShift u (ℓ + 1) 0 = dd u (ℓ + 1) := rfl
      rw [hdd] at h1 h2
      nlinarith
  exact gkernel_nonneg hgw (genRec_of hu.1 hu1)
    (fun a => by rw [kerFnV_zero]; split_ifs <;> norm_num) (kerFnV_supp hu.1 hu1 N hk' hT)

end Szkraw
