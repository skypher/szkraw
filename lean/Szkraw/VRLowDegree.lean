import Szkraw.VRQuadProfile

/-!
# Theorem 8.12 (profiles of Newton degree at most two)

`d_i = ν₁ i + ν₂ C(i,2)` with `ν₁ > 0`, `ν₂ ≥ 0`; the Newton coefficients of `c` are log-concave
without internal zeros; `b = d - c` is nondecreasing. Since `Δ³d = 0`, every move `A_j` with
`j ≥ 1` of the recurrence of Theorem 8.6 is `-W^c_{2j+1,j}`, the `C`-moves of positive index
vanish, and the resummation (`gkernel_resum`) applies with `H = 0` and `V_j = W^c_{2j+1,j}`:
its detours come from the log-concavity of the Newton coefficients of `c`, and the key
inequality is trivial.
-/

set_option linter.unusedSectionVars false

namespace Szkraw

open Finset

/-- Hypotheses of Theorem 8.12. -/
def LowDegHyp {N : ℕ} (vv : Coefficients N) : Prop :=
  ∃ ν1 ν2 : ℝ, 0 < ν1 ∧ 0 ≤ ν2 ∧
    (∀ i, i ≤ N → profile vv i = ν1 * i + ν2 * (i.choose 2 : ℝ)) ∧
    LogConcaveNoInternalZeros N (newtonCoeff vv.c) ∧
    (∀ i, i < N → vv.b i ≤ vv.b (i + 1))

/-- Theorem 8.12, matrix-positivity conclusion. -/
def Stmt_lowdeg : Prop :=
  ∀ (N : ℕ) (vv : Coefficients N), Admissible vv → LowDegHyp vv → MatrixPositivity vv

/-- `V`-family coefficients: `4 C(m-j-1, j) ≤ C(m,2) C(m-j-2, j-1)` for `j ≥ 2`, `m ≥ 2j+1`. -/
theorem coeffV (j m : ℕ) (hj : 2 ≤ j) (hm : 2 * j + 1 ≤ m) :
    4 * (m - j - 1).choose j ≤ m.choose 2 * (m - j - 2).choose (j - 1) := by
  have key := Nat.add_one_mul_choose_eq (m - j - 2) (j - 1)
  have e1 : m - j - 2 + 1 = m - j - 1 := by omega
  have e2 : j - 1 + 1 = j := by omega
  rw [e1, e2] at key
  have hc2 := choose_two_mul m
  set X := (m - j - 2).choose (j - 1)
  set Y := (m - j - 1).choose j
  have h8 : 8 * (m - j - 1) ≤ j * (m * (m - 1)) := by
    have h2 : 8 * m ≤ 2 * (m * (m - 1)) := by
      have h5 : 5 ≤ m := by omega
      zify [h5, (by omega : 1 ≤ m)]
      nlinarith
    calc 8 * (m - j - 1) ≤ 8 * m := by omega
      _ ≤ 2 * (m * (m - 1)) := h2
      _ ≤ j * (m * (m - 1)) := Nat.mul_le_mul_right _ hj
  have : 2 * j * (4 * Y) ≤ 2 * j * (m.choose 2 * X) := by
    have lhs : 2 * j * (4 * Y) = 8 * (Y * j) := by ring
    have rhs : 2 * j * (m.choose 2 * X) = j * (m.choose 2 * 2) * X := by ring
    rw [lhs, rhs, ← key, hc2]
    calc 8 * ((m - j - 1) * X) = (8 * (m - j - 1)) * X := by ring
      _ ≤ (j * (m * (m - 1))) * X := Nat.mul_le_mul_right _ h8
  exact Nat.le_of_mul_le_mul_left this (by omega)

/-- Detour of the moves `W^c_{2j+1,j}` (`j ≥ 2`) through `B₀`, from log-concavity. -/
theorem detour_selfV {u : ℕ → ℝ} (hu : LCNZ u) (j ℓ a : ℕ) (hj : 2 ≤ j) :
    4 * Szkraw.iterShift u (ℓ + 1) 0 * Wt u (2 * j + 1) j ℓ a ≤
      Wt u 2 0 ℓ a * Wt u (2 * j - 1) (j - 1) (ℓ + 1) (a - 2) := by
  have hF0 := iterShift_nonneg hu (ℓ + 1) 0
  by_cases ha : a < 2 * j + 1
  · rw [Wt_eq_zero _ _ _ _ ha, mul_zero]
    exact mul_nonneg (Wt_nonneg hu _ _ _ _) (Wt_nonneg hu _ _ _ _)
  push Not at ha
  refine le_trans ?_ (detour_second hu (2 * j - 1) (j - 1) ℓ a (by omega) (by omega))
  rw [Wt, mul_sum]
  refine sum_le_sum (fun m _ => ?_)
  by_cases hm : 2 * j + 1 ≤ m
  · rw [if_pos hm, if_pos (by omega)]
    have e1 : m - (2 * j + 1) + j = m - j - 1 := by omega
    have e2 : m - 2 - (2 * j - 1) + (j - 1) = m - j - 2 := by omega
    rw [e1, e2]
    have hco' : (4 : ℝ) * ((m - j - 1).choose j : ℝ) ≤ (m.choose 2 : ℝ) * ((m - j - 2).choose (j - 1) : ℝ) := by
      exact_mod_cast coeffV j m hj hm
    have hf := iterShift_nonneg hu ℓ m
    have hc : (0 : ℝ) ≤ (a.choose m : ℝ) := Nat.cast_nonneg _
    calc 4 * Szkraw.iterShift u (ℓ + 1) 0 * (((m - j - 1).choose j : ℝ) * (a.choose m : ℝ) * Szkraw.iterShift u ℓ m)
        = (4 * ((m - j - 1).choose j : ℝ)) * ((a.choose m : ℝ) * (Szkraw.iterShift u (ℓ + 1) 0 * Szkraw.iterShift u ℓ m)) := by ring
      _ ≤ ((m.choose 2 : ℝ) * ((m - j - 2).choose (j - 1) : ℝ)) * ((a.choose m : ℝ) * (Szkraw.iterShift u (ℓ + 1) 0 * Szkraw.iterShift u ℓ m)) :=
          mul_le_mul_of_nonneg_right hco' (mul_nonneg hc (mul_nonneg hF0 hf))
      _ = _ := by ring
  · rw [if_neg hm, if_neg (by omega)]; simp

/-- **Theorem 8.12** (profiles of Newton degree at most two). -/
theorem lowdeg_matrix : Stmt_lowdeg := by
  intro N vv hv hyp
  obtain ⟨ν1, ν2, h1, h2, hd, hlc, hbmono⟩ := hyp
  have hv' := hv
  obtain ⟨hN, _, hb0, hc0, haN, hsum, hapos, hcpos⟩ := hv'
  set u := padNewton N (newtonCoeff vv.c) with hu_def
  set w := padNewton N (newtonCoeff vv.b) with hw_def
  set ν := padNewton N (newtonCoeff (profile vv)) with hν_def
  set FD : ℕ → ℕ → ℝ := fun ℓ n => (fwdDiff 1)^[n] (dQ ν1 ν2) ℓ with hFD
  have hd0 : profile vv 0 = 0 := by simp [profile, hb0, hc0]
  have hdQ : ∀ i, i ≤ N → profile vv i = dQ ν1 ν2 i := hd
  have hu : LCNZ u := padNewton_lcnz hlc
  have hu_nn : ∀ i, 0 ≤ u i := hu.1
  have fdef : ∀ ℓ n, ℓ + n ≤ N → Szkraw.iterShift ν ℓ n = FD ℓ n := fun ℓ n h => by
    rw [hν_def, iterShift_padNewton (profile vv) hd0 N ℓ n h]
    exact fwdDiff_iter_congr n ℓ fun i _ hi => hdQ i (by omega)
  have hw_eq : w = fun i => ν i - u i := by
    funext i
    rw [hw_def, hν_def, hu_def]
    unfold padNewton
    split_ifs
    · rw [← newtonCoeff_sub]
      exact newtonCoeff_congr fun j _ => by simp [profile]
    · ring
  have FD_z : ∀ ℓ n, 3 ≤ n → FD ℓ n = 0 := fun ℓ n hn => by
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
    exact dQ_diff_high' ν1 ν2 k ℓ
  have FD_nn : ∀ ℓ n, 0 ≤ FD ℓ n := fun ℓ n => by
    rcases Nat.lt_or_ge n 3 with h | h
    · interval_cases n
      · exact dQ_nonneg h1 h2 ℓ
      · simp only [hFD]; rw [dQ_diff1']; positivity
      · simp only [hFD]; rw [dQ_diff2']; exact h2
    · rw [FD_z ℓ n h]
  have WN : ∀ p q ℓ a, ℓ + a ≤ N → Wt ν p q ℓ a = WtF FD p q ℓ a := fun p q ℓ a h => by
    rw [Wt_eq_WtF]; exact WtF_congr fun n hn => fdef ℓ n (by omega)
  have hWw : ∀ p q ℓ a, Wt w p q ℓ a = Wt ν p q ℓ a - Wt u p q ℓ a := fun p q ℓ a => by
    unfold Wt; rw [← sum_sub_distrib]
    refine sum_congr rfl fun n _ => ?_
    rw [hw_eq, iterShift_sub]; ring
  have hWν0 : ∀ p q ℓ a, 3 ≤ p → ℓ + a ≤ N → Wt ν p q ℓ a = 0 := fun p q ℓ a hp h => by
    rw [WN _ _ _ _ h]; exact WtF_zero_of fun n hn _ => FD_z ℓ n (by omega)
  have hwC : ∀ j ℓ a, wC u w j ℓ a = Wt ν (2 * j + 2) (j + 1) ℓ a := fun j ℓ a => by
    unfold wC; rw [Wt_add]; congr 1; funext i; rw [hw_eq]; ring
  have hu1 : 0 < u 1 := by
    rw [hu_def]; unfold padNewton; rw [if_pos ⟨le_rfl, hN⟩]; exact hlc.1
  have hu0 : u 0 = 0 := padNewton_zero _ _
  have hddc : ∀ i, i ≤ N → dd u i = vv.c i := fun i hi => dd_padNewton vv.c hc0 N i hi
  have hddb : ∀ i, i ≤ N → dd w i = vv.b i := fun i hi => dd_padNewton vv.b hb0 N i hi
  refine matrixPositivity_of_kernel vv hv hu_nn hu1 hu0 hddc hddb (fun k' hk' => ?_)
  have hT : dd w N + dd u N = 1 := by
    rw [hddb N le_rfl, hddc N le_rfl]; have := hsum N le_rfl; rw [haN] at this; linarith
  have bchain : ∀ ℓ k, ℓ + k ≤ N → vv.b ℓ ≤ vv.b (ℓ + k) := by
    intro ℓ k hk
    induction k with
    | zero => simp
    | succ k ih => exact le_trans (ih (by omega)) (hbmono (ℓ + k) (by omega))
  have hA0 : ∀ ℓ a, ℓ + a ≤ N → 0 ≤ wA w 0 ℓ a := fun ℓ a h => by
    unfold wA; rw [show 2 * 0 + 1 = 1 by ring, Wt_one_zero, hddb _ h, hddb _ (by omega)]
    linarith [bchain ℓ a h]
  have hBnn : ∀ j ℓ a, 0 ≤ wB u j ℓ a := fun j ℓ a => Wt_nonneg hu _ _ _ _
  have hCnn : ∀ j ℓ a, ℓ + a ≤ N → 0 ≤ wC u w j ℓ a := fun j ℓ a h => by
    rw [hwC, WN _ _ _ _ h]; exact WtF_nonneg fun n _ _ => FD_nn ℓ n
  have hCz : ∀ j ℓ a, 1 ≤ j → ℓ + a ≤ N → wC u w j ℓ a = 0 := fun j ℓ a hj h => by
    rw [hwC]; exact hWν0 _ _ _ _ (by omega) h
  set V0 : ℕ → ℕ → ℕ → ℝ := fun j ℓ a => if j = 0 then 0 else Wt u (2 * j + 1) j ℓ a with hV0
  have hV0nn : ∀ j ℓ a, 0 ≤ V0 j ℓ a := fun j ℓ a => by
    simp only [hV0]; split_ifs
    · exact le_rfl
    · exact Wt_nonneg hu _ _ _ _
  have hcc : ∀ n, 1 ≤ n → 0 < dd u n := fun n hn => dd_pos_of hu_nn hu1 hn
  have hw : ResumWeights (dd u) (wA w) (wB u) (wC u w) (fun _ _ _ => 0) V0 (wSV u w) N := by
    refine ⟨hcc, fun j ℓ a hj h => ?_, hA0, fun j ℓ a _ => hBnn j ℓ a, hCnn, fun _ _ _ _ => le_rfl,
      fun j ℓ a _ => hV0nn j ℓ a, fun ℓ a h => ?_, fun j ℓ a hj h => ?_, fun j ℓ a hj h => ?_,
      fun j ℓ a hj h => ?_, fun j ℓ a hj h => ?_, fun ℓ a h ha => ?_⟩
    · -- split: `A_j = -W^c_{2j+1,j}` for `j ≥ 1`
      simp only [hV0]; rw [if_neg (by omega)]
      unfold wA; rw [hWw, hWν0 _ _ _ _ (by omega) h]
    · -- straight weights
      unfold wSV
      rcases Nat.lt_or_ge (ℓ + a) N with hl | hl
      · rw [hddb _ hl.le, hddc _ hl.le]; have := hsum (ℓ + a) hl.le; linarith [hapos (ℓ + a) hl]
      · rw [show ℓ + a = N by omega]; linarith
    · -- domB
      have := lemma_8_4_B hu j ℓ a hj
      unfold wB
      rw [show 2 * (j - 1) + 2 = 2 * j by omega, show 2 * 0 + 2 = 2 by ring]
      exact this
    · -- domC
      rw [hCz j ℓ a hj h, mul_zero]
      rcases Nat.lt_or_ge a 2 with ha | ha
      · unfold wB; rw [Wt_eq_zero _ _ _ _ (by omega), zero_mul]
      · exact mul_nonneg (hBnn 0 ℓ a) (hCnn _ _ _ (by omega))
    · -- domH
      simp
    · -- domV
      simp only [hV0]
      rw [if_neg (by omega), if_neg (by omega)]
      have := detour_selfV hu j ℓ a hj
      unfold wB
      rw [show 2 * (j - 1) + 1 = 2 * j - 1 by omega, show 2 * 0 + 2 = 2 by ring]
      exact this
    · -- key: `H = 0`
      simp only [mul_zero]
      have := hcc (ℓ + 1) (by omega)
      have hv1 := hV0nn 1 ℓ a
      refine add_nonneg (add_nonneg (mul_nonneg (hA0 ℓ a h) (hBnn _ _ _))
        (mul_nonneg (hBnn 0 ℓ a) (hA0 _ _ (by omega)))) (by positivity)
  exact gkernel_resum hN hw (genRec_of hu_nn hu1)
    (fun a => by rw [kerFnV_zero]; split_ifs <;> norm_num) (kerFnV_supp hu_nn hu1 N hk' hT)

end Szkraw

/-! ### Corollary: ratios with log-concave Newton coefficients -/

namespace Szkraw

open Finset

/-- Differences of `ℓ ↦ iterShift u ℓ n`: `Δ^m` gives `iterShift u ℓ (n+m)`. -/
theorem fwdDiff_iter_iterShift (u : ℕ → ℝ) : ∀ m n x : ℕ,
    (fwdDiff 1)^[m] (fun ℓ => Szkraw.iterShift u ℓ n) x = Szkraw.iterShift u x (n + m)
  | 0, n, x => by simp
  | m + 1, n, x => by
    rw [fwdDiff_iter_succ, fwdDiff_iter_iterShift u m n (x + 1), fwdDiff_iter_iterShift u m n x]
    show Szkraw.iterShift u x (n + m) + Szkraw.iterShift u x (n + m + 1) - Szkraw.iterShift u x (n + m) = _
    rw [show n + (m + 1) = n + m + 1 by ring]; ring

/-- Hypotheses of Corollary 8.13: a profile of Newton degree at most two and a ratio
`ρ(i) = Σ_k ρ_k C(i,k)` whose Newton coefficients `ρ_k` are nonnegative, log-concave and
without internal zeros, with `ρ_0 > 0`; `b` nondecreasing. -/
def LowDegRatioHyp {N : ℕ} (vv : Coefficients N) : Prop :=
  ∃ (ν1 ν2 : ℝ) (ρ : ℕ → ℝ), 0 < ν1 ∧ 0 ≤ ν2 ∧ LCNZ ρ ∧ 0 < ρ 0 ∧
    (∀ i, i ≤ N → profile vv i = ν1 * i + ν2 * (i.choose 2 : ℝ)) ∧
    (∀ i, i ≤ N → vv.c i = (∑ k ∈ range (i + 1), (i.choose k : ℝ) * ρ k) * profile vv i) ∧
    (∀ i, i < N → vv.b i ≤ vv.b (i + 1))

/-- Corollary 8.13, matrix-positivity conclusion. -/
def Stmt_lowdeg_ratio : Prop :=
  ∀ (N : ℕ) (vv : Coefficients N), Admissible vv → LowDegRatioHyp vv → MatrixPositivity vv

/-- The log-concavity identity behind Lemma (NP) for profiles of degree two. -/
theorem lowdeg_lc_identity (α β h x0 x1 x2 x3 : ℝ) :
    (α * x2 + β * x1) ^ 2 - ((α - h) * x1 + (β - h) * x0) * ((α + h) * x3 + (β + h) * x2) =
      α ^ 2 * (x2 ^ 2 - x1 * x3) + h ^ 2 * (x1 * x3) + β ^ 2 * (x1 ^ 2 - x0 * x2) + h ^ 2 * (x0 * x2) +
        2 * h ^ 2 * (x1 * x2) + (β - h) * (α + h) * (x1 * x2 - x0 * x3) := by ring

/-- **Lemma (NP), profiles of Newton degree at most two**: the Newton coefficients of `c` are
log-concave without internal zeros. -/
theorem lowdeg_newton_lc {N : ℕ} (vv : Coefficients N) (hv : Admissible vv) {ν1 ν2 : ℝ} {ρ : ℕ → ℝ}
    (h1 : 0 < ν1) (h2 : 0 ≤ ν2) (hρ : LCNZ ρ) (hρ0 : 0 < ρ 0)
    (hd : ∀ i, i ≤ N → profile vv i = ν1 * i + ν2 * (i.choose 2 : ℝ))
    (hc : ∀ i, i ≤ N → vv.c i = (∑ k ∈ range (i + 1), (i.choose k : ℝ) * ρ k) * profile vv i) :
    LogConcaveNoInternalZeros N (newtonCoeff vv.c) := by
  obtain ⟨hN, _, _, hc0, _, _, _, hcpos⟩ := hv
  set R : ℕ → ℝ := fun i => Szkraw.iterShift ρ i 0 with hR
  have hRi : ∀ i, R i = ∑ k ∈ range (i + 1), (i.choose k : ℝ) * ρ k := fun i => by
    simp only [hR]; rw [iterShift_eq]; exact sum_congr rfl fun k _ => by rw [zero_add]
  have hDR : ∀ m, (fwdDiff 1)^[m] R 0 = ρ m := fun m => by
    rw [hR, fwdDiff_iter_iterShift, zero_add]; rfl
  -- `x_K = ρ_{K-1} + ρ_K`, the shift sum of `ρ` with a zero prepended
  set ρ' : ℕ → ℝ := fun i => if i = 0 then 0 else ρ (i - 1) with hρ'
  have hρ'lc : LCNZ ρ' := by
    obtain ⟨hnn, hlc, hint⟩ := hρ
    refine ⟨fun i => ?_, fun i => ?_, fun i j k hij hjk hi hk => ?_⟩
    · simp only [hρ']; split_ifs
      · exact le_rfl
      · exact hnn _
    · simp only [hρ']
      rcases Nat.eq_zero_or_pos i with h0 | hpos
      · subst h0; simp; positivity
      · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
        have := hlc (i - 1)
        rw [show i - 1 + 2 = i + 2 - 1 by omega, show i - 1 + 1 = i + 1 - 1 by omega] at this
        exact this
    · simp only [hρ'] at hi hk ⊢
      have hi0 : i ≠ 0 := by rintro rfl; simp at hi
      rw [if_neg hi0] at hi
      rw [if_neg (by omega)] at hk ⊢
      exact hint (i - 1) (j - 1) (k - 1) (by omega) (by omega) hi hk
  set x : ℕ → ℝ := Szkraw.shiftSum ρ' with hx
  have hxlc : LCNZ x := hρ'lc.shiftSum
  have hxK : ∀ K, 1 ≤ K → x K = ρ (K - 1) + ρ K := fun K hK => by
    simp only [hx, Szkraw.shiftSum, hρ']; rw [if_neg (by omega), if_neg (by omega)]; congr 1
  have hx0 : x 0 = ρ 0 := by simp [hx, Szkraw.shiftSum, hρ']
  set hh := ν2 / 2 with hhh
  set e : ℕ → ℝ := fun K => (ν1 + hh * ((K : ℝ) - 1)) * x K + hh * ((K : ℝ) - 1) * x (K - 1) with he
  -- the formula `κ_K = K e_K`
  have hκ : ∀ K, 1 ≤ K → K ≤ N → newtonCoeff vv.c K = K * e K := by
    intro K hK hKN
    rw [newtonCoeff_eq_iter]
    have hcongr : (fwdDiff 1)^[K] vv.c 0 =
        (fwdDiff 1)^[K] (fun i : ℕ => (0 + ν1 * i + ν2 * (i.choose 2 : ℝ)) * R i) 0 :=
      fwdDiff_iter_congr K 0 fun i _ hi => by rw [hc i (by omega), hd i (by omega), hRi]; ring
    rw [hcongr]
    rcases Nat.lt_or_ge K 2 with hK2 | hK2
    · have hK1 : K = 1 := by omega
      subst hK1
      simp only [Function.iterate_one, fwdDiff, he, hR]
      rw [hxK 1 le_rfl]
      simp [Szkraw.iterShift, Szkraw.shiftSum, Nat.choose]
    · obtain ⟨k, rfl⟩ : ∃ k, K = k + 2 := ⟨K - 2, by omega⟩
      rw [fwdDiff_quad_mul 0 ν1 ν2 R k 0, hDR, hDR, hDR]
      have ex2 : x (k + 2) = ρ (k + 1) + ρ (k + 2) := by
        have := hxK (k + 2) (by omega); simpa using this
      have ex1 : x (k + 1) = ρ k + ρ (k + 1) := by
        have := hxK (k + 1) (by omega); simpa using this
      have hc2n := choose_two_mul (k + 2)
      have hc2 : (((0 + k + 2).choose 2 : ℕ) : ℝ) = ((k : ℝ) + 2) * ((k : ℝ) + 1) / 2 := by
        rw [zero_add]
        have : (((k + 2).choose 2 : ℕ) : ℝ) * 2 = ((k : ℝ) + 2) * ((k : ℝ) + 1) := by
          rw [show k + 2 - 1 = k + 1 by omega] at hc2n; exact_mod_cast hc2n
        linarith
      simp only [he, show k + 2 - 1 = k + 1 by omega, ex2, ex1, hc2]
      push_cast; ring
  have he_nn : ∀ K, 1 ≤ K → 0 ≤ e K := fun K hK => by
    simp only [he]
    have hK1 : (0 : ℝ) ≤ (K : ℝ) - 1 := by
      have : (1 : ℝ) ≤ K := by exact_mod_cast hK
      linarith
    have := hxlc.1 K; have := hxlc.1 (K - 1)
    positivity
  refine ⟨?_, fun k hk hkN => ?_, fun k hk hkN => ?_, fun k hk hkN h0 => ?_⟩
  · -- `κ_1 = c_1 > 0`
    have : newtonCoeff vv.c 1 = vv.c 1 - vv.c 0 := by simp [newtonCoeff, Finset.sum_range_succ]; ring
    rw [this, hc0, sub_zero]; exact hcpos 1 (by norm_num) hN
  · rw [hκ k hk hkN]; exact mul_nonneg (Nat.cast_nonneg _) (he_nn k hk)
  · -- log-concavity
    rw [hκ (k - 1) (by omega) (by omega), hκ (k + 1) (by omega) hkN, hκ k (by omega) (by omega)]
    have hKr : (2 : ℝ) ≤ k := by exact_mod_cast hk
    have heLC : e (k - 1) * e (k + 1) ≤ e k ^ 2 := by
      simp only [he]
      rw [show k - 1 - 1 = k - 2 by omega, show k + 1 - 1 = k by omega]
      have c1 : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by rw [Nat.cast_sub (by omega)]; norm_num
      rw [c1]; push_cast
      set α := ν1 + hh * ((k : ℝ) - 1); set β := hh * ((k : ℝ) - 1)
      have eA : ν1 + hh * ((k : ℝ) - 1 - 1) = α - hh := by simp only [α]; ring
      have eB : hh * ((k : ℝ) - 1 - 1) = β - hh := by simp only [β]; ring
      have eA' : ν1 + hh * ((k : ℝ) + 1 - 1) = α + hh := by simp only [α]; ring
      have eB' : hh * ((k : ℝ) + 1 - 1) = β + hh := by simp only [β]; ring
      rw [eA, eB, eA', eB']
      have hid := lowdeg_lc_identity α β hh (x (k - 2)) (x (k - 1)) (x k) (x (k + 1))
      have s1 : x (k - 1) * x (k + 1) ≤ x k ^ 2 := by
        have := hxlc.2.1 (k - 1); rwa [show k - 1 + 2 = k + 1 by omega, show k - 1 + 1 = k by omega] at this
      have s2 : x (k - 2) * x k ≤ x (k - 1) ^ 2 := by
        have := hxlc.2.1 (k - 2); rwa [show k - 2 + 2 = k by omega, show k - 2 + 1 = k - 1 by omega] at this
      have s3 : x (k - 2) * x (k + 1) ≤ x (k - 1) * x k := by
        have := hxlc.step (x := k - 2) (y := k - 1) (by omega)
        rwa [show k - 1 + 2 = k + 1 by omega, show k - 2 + 1 = k - 1 by omega, show k - 1 + 1 = k by omega] at this
      have n0 := hxlc.1 (k - 2); have n1 := hxlc.1 (k - 1); have n2 := hxlc.1 k; have n3 := hxlc.1 (k + 1)
      have hβh : 0 ≤ β - hh := by simp only [β, hhh]; nlinarith
      have hαh : 0 ≤ α + hh := by simp only [α, hhh]; nlinarith
      have t1 : 0 ≤ α ^ 2 * (x k ^ 2 - x (k - 1) * x (k + 1)) := mul_nonneg (sq_nonneg _) (by linarith)
      have t2 : 0 ≤ β ^ 2 * (x (k - 1) ^ 2 - x (k - 2) * x k) := mul_nonneg (sq_nonneg _) (by linarith)
      have t3 : 0 ≤ (β - hh) * (α + hh) * (x (k - 1) * x k - x (k - 2) * x (k + 1)) :=
        mul_nonneg (mul_nonneg hβh hαh) (by linarith)
      have t4 : 0 ≤ hh ^ 2 * (x (k - 1) * x (k + 1)) + hh ^ 2 * (x (k - 2) * x k) + 2 * hh ^ 2 * (x (k - 1) * x k) := by
        positivity
      linarith [hid, t1, t2, t3, t4]
    have hek := he_nn k (by omega); have hem := he_nn (k - 1) (by omega); have hep := he_nn (k + 1) (by omega)
    have c1 : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by rw [Nat.cast_sub (by omega)]; norm_num
    rw [c1]; push_cast
    have hP := mul_nonneg hem hep
    have hk2 : ((k : ℝ) - 1) * ((k : ℝ) + 1) ≤ (k : ℝ) ^ 2 := by nlinarith
    have step1 : ((k : ℝ) - 1) * ((k : ℝ) + 1) * (e (k - 1) * e (k + 1)) ≤ (k : ℝ) ^ 2 * (e (k - 1) * e (k + 1)) :=
      mul_le_mul_of_nonneg_right hk2 hP
    have step2 : (k : ℝ) ^ 2 * (e (k - 1) * e (k + 1)) ≤ (k : ℝ) ^ 2 * e k ^ 2 :=
      mul_le_mul_of_nonneg_left heLC (sq_nonneg _)
    calc ((k : ℝ) - 1) * e (k - 1) * (((k : ℝ) + 1) * e (k + 1))
        = ((k : ℝ) - 1) * ((k : ℝ) + 1) * (e (k - 1) * e (k + 1)) := by ring
      _ ≤ (k : ℝ) ^ 2 * e k ^ 2 := step1.trans step2
      _ = ((k : ℝ) * e k) ^ 2 := by ring
  · -- no internal zeros
    rw [hκ k hk (by omega)] at h0
    have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
    have hek0 : e k = 0 := by
      rcases mul_eq_zero.mp h0 with h | h
      · linarith
      · exact h
    simp only [he] at hek0
    have hK1 : (0 : ℝ) ≤ (k : ℝ) - 1 := by
      have : (1 : ℝ) ≤ k := by exact_mod_cast hk
      linarith
    have hα : 0 < ν1 + hh * ((k : ℝ) - 1) := by simp only [hhh]; positivity
    have hxk0 : x k = 0 := by
      have a1 := hxlc.1 k; have a2 := hxlc.1 (k - 1)
      have : 0 ≤ hh * ((k : ℝ) - 1) * x (k - 1) := by simp only [hhh]; positivity
      have : (ν1 + hh * ((k : ℝ) - 1)) * x k = 0 := by nlinarith [mul_nonneg hα.le a1]
      rcases mul_eq_zero.mp this with h | h
      · linarith
      · exact h
    rw [hxK k hk] at hxk0
    have hρk : ρ k = 0 := by linarith [hρ.1 (k - 1), hρ.1 k]
    have hρk1 : ρ (k + 1) = 0 := by
      by_contra hne
      have hpos : 0 < ρ (k + 1) := lt_of_le_of_ne (hρ.1 _) (Ne.symm hne)
      have := hρ.2.2 0 k (k + 1) (by omega) (by omega) hρ0 hpos
      linarith
    rw [hκ (k + 1) (by omega) hkN]
    simp only [he]
    rw [hxK (k + 1) (by omega), show k + 1 - 1 = k by omega, hxK k hk, hρk, hρk1]
    have : ρ (k - 1) + 0 = 0 := by linarith [hρ.1 (k - 1), hρ.1 k]
    rw [this]; ring

/-- **Corollary 8.13**: on profiles of Newton degree at most two, every ratio whose Newton
coefficients are nonnegative, log-concave and without internal zeros, with nondecreasing `b`. -/
theorem lowdeg_ratio_matrix : Stmt_lowdeg_ratio := by
  intro N vv hv hyp
  obtain ⟨ν1, ν2, ρ, h1, h2, hρ, hρ0, hd, hc, hb⟩ := hyp
  exact lowdeg_matrix N vv hv ⟨ν1, ν2, h1, h2, hd, lowdeg_newton_lc vv hv h1 h2 hρ hρ0 hd hc, hb⟩

end Szkraw
