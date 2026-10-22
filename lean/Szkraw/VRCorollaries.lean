import Szkraw.VRAssembly

/-!
# Corollary 8.7 (nonincreasing weights) and Proposition 8.8 (quadratic arrays)

Corollary 8.7: if the Newton coefficients of `c` are log-concave without internal zeros and those of
`b` are `β_k = w_k κ_k` with `w` nonnegative and nonincreasing, the array has property (P); the ratio
`c_i/(b_i + c_i)` is nondecreasing; and if `w` is constant on the support of `κ`, then `b` is a
constant multiple of `c` (the arrays of Theorem 8.1).

Proposition 8.8: if `b` and `c` are quadratic in the index, `c` and `b + c` are convex and `b` is
nondecreasing, the array has property (P).
-/

namespace Szkraw

open Finset

/-! ### Corollary 8.7 -/

/-- Hypotheses of Corollary 8.7. -/
def WeightHyp {N : ℕ} (vv : Coefficients N) (w : ℕ → ℝ) : Prop :=
  LogConcaveNoInternalZeros N (newtonCoeff vv.c) ∧
  (∀ k, 1 ≤ k → k ≤ N → 0 ≤ w k) ∧
  (∀ i k, 1 ≤ i → i ≤ k → k ≤ N → w k ≤ w i) ∧
  (∀ k, 1 ≤ k → k ≤ N → newtonCoeff vv.b k = w k * newtonCoeff vv.c k)

/-- Corollary 8.7: property (P), the nondecreasing ratio `c_i/(b_i + c_i)`, and the constant-weight
case `b = w₀ c`. -/
def Stmt_varyratio_weights : Prop :=
  ∀ (N : ℕ) (vv : Coefficients N) (w : ℕ → ℝ), Admissible vv → WeightHyp vv w →
    MatrixPositivity vv ∧
    (∀ i, 1 ≤ i → i < N → vv.c i / (vv.b i + vv.c i) ≤ vv.c (i + 1) / (vv.b (i + 1) + vv.c (i + 1))) ∧
    (∀ w₀ : ℝ, (∀ k, 1 ≤ k → k ≤ N → newtonCoeff vv.c k ≠ 0 → w k = w₀) → ∀ i, i ≤ N → vv.b i = w₀ * vv.c i)

theorem varyratio_weights : Stmt_varyratio_weights := by
  intro N vv w hv hyp
  obtain ⟨hlc, hw0, hwmono, hbw⟩ := hyp
  obtain ⟨hN, _, hb0, hc0, _, hsum, hapos, hcpos⟩ := hv
  set u := padNewton N (newtonCoeff vv.c) with hu_def
  set v := padNewton N (newtonCoeff vv.b) with hv_def
  have hu : LCNZ u := padNewton_lcnz hlc
  have hu1 : 0 < u 1 := by rw [hu_def]; unfold padNewton; rw [if_pos ⟨le_rfl, hN⟩]; exact hlc.1
  have hβ : ∀ k, 1 ≤ k → k ≤ N → 0 ≤ newtonCoeff vv.b k := fun k h1 h2 => by
    rw [hbw k h1 h2]; exact mul_nonneg (hw0 k h1 h2) (hlc.2.1 k h1 h2)
  have hvnn : ∀ i, 0 ≤ v i := padNewton_nonneg hβ
  have hvw : ∀ i, v i = w i * u i := by
    intro i; rw [hv_def, hu_def]; unfold padNewton
    split_ifs with h
    · exact hbw i h.1 h.2
    · ring
  have hco : CrossOrder u v := crossOrder_of_weights hu.1 hvw (fun i k hik hi hk => by
    have hi' : 1 ≤ i ∧ i ≤ N := by
      by_contra hc; apply hi; rw [hu_def]; unfold padNewton; rw [if_neg hc]
    have hk' : 1 ≤ k ∧ k ≤ N := by
      by_contra hc; apply hk; rw [hu_def]; unfold padNewton; rw [if_neg hc]
    exact hwmono i k hi'.1 hik hk'.2)
  have hMI := mixedIneq_of_crossOrder hu hu1 hvnn hco N
  have hddc : ∀ i, i ≤ N → dd u i = vv.c i := fun i hi => dd_padNewton vv.c hc0 N i hi
  have hddb : ∀ i, i ≤ N → dd v i = vv.b i := fun i hi => dd_padNewton vv.b hb0 N i hi
  refine ⟨varyratio_matrix N vv ⟨hN, by assumption, hb0, hc0, by assumption, hsum, hapos, hcpos⟩
    ⟨hlc, hβ, hMI⟩, fun i hi1 hiN => ?_, fun w₀ hconst i hi => ?_⟩
  · -- the ratio: `b_{i+1} c_i ≤ b_i c_{i+1}` from the cross order at level `i`
    have hc := (hco.iterShift i) 0 1 (by omega)
    have hG0 : Szkraw.iterShift u i 0 = vv.c i := hddc i hiN.le
    have hH0 : Szkraw.iterShift v i 0 = vv.b i := hddb i hiN.le
    have hG1 : Szkraw.iterShift u i 1 = vv.c (i + 1) - vv.c i := by
      have : dd u (i + 1) = Szkraw.iterShift u i 0 + Szkraw.iterShift u i 1 := rfl
      rw [hddc (i + 1) hiN, hG0] at this; linarith
    have hH1 : Szkraw.iterShift v i 1 = vv.b (i + 1) - vv.b i := by
      have : dd v (i + 1) = Szkraw.iterShift v i 0 + Szkraw.iterShift v i 1 := rfl
      rw [hddb (i + 1) hiN, hH0] at this; linarith
    rw [hG0, hH0, hG1, hH1] at hc
    have hbi : 0 ≤ vv.b i := by rw [← hddb i hiN.le]; unfold dd; exact iterShift_nonneg_of hvnn i 0
    have hbi1 : 0 ≤ vv.b (i + 1) := by rw [← hddb (i + 1) hiN]; unfold dd; exact iterShift_nonneg_of hvnn (i + 1) 0
    have hci := hcpos i (by omega) hiN.le
    have hci1 := hcpos (i + 1) (by omega) hiN
    rw [div_le_div_iff₀ (by linarith) (by linarith)]
    nlinarith
  · -- constant weights: `b = w₀ c`
    have hk : ∀ k, newtonCoeff vv.b k * (if 1 ≤ k ∧ k ≤ N then 1 else 0) =
        w₀ * (newtonCoeff vv.c k * (if 1 ≤ k ∧ k ≤ N then 1 else 0)) := by
      intro k
      split_ifs with h
      · rw [hbw k h.1 h.2]
        by_cases hz : newtonCoeff vv.c k = 0
        · rw [hz]; ring
        · rw [hconst k h.1 h.2 hz]; ring
      · ring
    rw [← hddb i hi, ← hddc i hi]
    unfold dd
    rw [iterShift_eq, iterShift_eq, mul_sum]
    refine sum_congr rfl (fun h _ => ?_)
    rw [hv_def, hu_def]; unfold padNewton
    have := hk (0 + h)
    split_ifs at this ⊢ <;> [skip; ring]
    rw [mul_one, mul_one] at this; rw [this]; ring

/-! ### Proposition 8.8 -/

/-- Hypotheses of Proposition 8.8 (quadratic arrays). -/
def QuadHyp {N : ℕ} (vv : Coefficients N) : Prop :=
  ∃ β₁ β₂ κ₁ κ₂ : ℝ,
    (∀ n, n ≤ N → vv.b n = β₁ * n + β₂ * (n.choose 2 : ℝ) ∧ vv.c n = κ₁ * n + κ₂ * (n.choose 2 : ℝ)) ∧
    0 ≤ κ₂ ∧ 0 ≤ κ₂ + β₂ ∧ (∀ n, n < N → vv.b n ≤ vv.b (n + 1))

/-- Proposition 8.8 (quadratic arrays). -/
def Stmt_quadratic : Prop :=
  ∀ (N : ℕ) (vv : Coefficients N), Admissible vv → QuadHyp vv → MatrixPositivity vv

open fwdDiff in
theorem newtonCoeff_eq_iter (d : ℕ → ℝ) (k : ℕ) : newtonCoeff d k = (fwdDiff 1)^[k] d 0 := by
  rw [fwdDiff_iter_eq_sum_shift]
  unfold newtonCoeff
  apply sum_congr rfl
  intro j _
  simp [zsmul_eq_mul]

theorem newtonCoeff_congr {d d' : ℕ → ℝ} {k : ℕ} (h : ∀ i, i ≤ k → d i = d' i) :
    newtonCoeff d k = newtonCoeff d' k := by
  unfold newtonCoeff
  exact sum_congr rfl (fun i hi => by rw [h i (by have := mem_range.mp hi; omega)])

theorem newtonCoeff_quad (β₁ β₂ : ℝ) (k : ℕ) :
    newtonCoeff (fun n : ℕ => β₁ * n + β₂ * (n.choose 2 : ℝ)) k =
      if k = 1 then β₁ else if k = 2 then β₂ else if k = 0 then 0 else 0 := by
  rw [newtonCoeff_eq_iter]
  have d1 : fwdDiff 1 (fun n : ℕ => β₁ * n + β₂ * (n.choose 2 : ℝ)) = fun n : ℕ => β₁ + β₂ * n := by
    funext n
    have hc : (((n + 1).choose 2 : ℕ) : ℝ) = (n : ℝ) + (n.choose 2 : ℝ) := by
      rw [show (2 : ℕ) = 1 + 1 from rfl, Nat.choose_succ_succ, Nat.choose_one_right]; push_cast; ring
    show β₁ * ((n + 1 : ℕ) : ℝ) + β₂ * (((n + 1).choose 2 : ℕ) : ℝ) - (β₁ * (n : ℝ) + β₂ * (n.choose 2 : ℝ)) =
      β₁ + β₂ * (n : ℝ)
    rw [hc]; push_cast; ring
  have d2 : fwdDiff 1 (fun n : ℕ => β₁ + β₂ * (n : ℝ)) = fun _ : ℕ => β₂ := by
    funext n; unfold fwdDiff; push_cast; ring
  have d3 : fwdDiff 1 (fun _ : ℕ => β₂) = fun _ : ℕ => (0 : ℝ) := by
    funext n; unfold fwdDiff; ring
  have d4 : fwdDiff 1 (fun _ : ℕ => (0 : ℝ)) = fun _ : ℕ => (0 : ℝ) := by
    funext n; unfold fwdDiff; ring
  have hz : ∀ m, (fwdDiff 1)^[m] (fun _ : ℕ => (0 : ℝ)) = fun _ => 0 := by
    intro m; induction m with
    | zero => rfl
    | succ m ih => rw [Function.iterate_succ_apply', ih, d4]
  rcases k with _ | _ | _ | k
  · simp
  · simp [d1]
  · simp [Function.iterate_succ_apply', d1, d2]
  · rw [show k + 1 + 1 + 1 = k + 3 by ring, Function.iterate_add_apply]
    simp only [Function.iterate_succ_apply', Function.iterate_zero_apply, d1, d2, d3, hz]
    simp

theorem iterShift_high {w : ℕ → ℝ} (h : ∀ i, 3 ≤ i → w i = 0) (ℓ n : ℕ) (hn : 3 ≤ n) :
    Szkraw.iterShift w ℓ n = 0 := by
  rw [iterShift_eq]; exact sum_eq_zero fun j _ => by rw [h (n + j) (by omega), mul_zero]

theorem Wt_high {w : ℕ → ℝ} {p : ℕ} (h : ∀ ℓ n, p ≤ n → Szkraw.iterShift w ℓ n = 0) (q ℓ a : ℕ) :
    Wt w p q ℓ a = 0 := by
  unfold Wt
  refine sum_eq_zero fun n _ => ?_
  by_cases hn : p ≤ n
  · rw [h ℓ n hn, mul_zero]
  · rw [if_neg hn]; ring

theorem Wt_nonneg_high {w : ℕ → ℝ} {p : ℕ} (h : ∀ ℓ n, p ≤ n → 0 ≤ Szkraw.iterShift w ℓ n) (q ℓ a : ℕ) :
    0 ≤ Wt w p q ℓ a := by
  unfold Wt
  refine sum_nonneg fun n _ => ?_
  by_cases hn : p ≤ n
  · rw [if_pos hn]; exact mul_nonneg (by positivity) (h ℓ n hn)
  · rw [if_neg hn]; ring_nf; exact le_refl _

theorem Wt_one_zero (w : ℕ → ℝ) (ℓ a : ℕ) : Wt w 1 0 ℓ a = dd w (ℓ + a) - dd w ℓ := by
  rw [dd_split]
  unfold Wt
  rw [sum_range_succ', sum_range_succ' (fun i => (a.choose i : ℝ) * Szkraw.iterShift w ℓ i)]
  simp only [Nat.choose_zero_right, Nat.cast_one, one_mul, show ¬ (1 ≤ 0) by omega, if_false, zero_mul,
    add_zero]
  have : dd w ℓ = Szkraw.iterShift w ℓ 0 := rfl
  rw [this, add_sub_cancel_right]
  refine sum_congr rfl fun i _ => ?_
  simp

theorem iterShift_add (w w' : ℕ → ℝ) (ℓ n : ℕ) :
    Szkraw.iterShift w ℓ n + Szkraw.iterShift w' ℓ n = Szkraw.iterShift (fun i => w i + w' i) ℓ n := by
  rw [iterShift_eq, iterShift_eq, iterShift_eq, ← sum_add_distrib]
  exact sum_congr rfl fun h _ => by ring

theorem Wt_add (w w' : ℕ → ℝ) (p q ℓ a : ℕ) : Wt w p q ℓ a + Wt w' p q ℓ a = Wt (fun i => w i + w' i) p q ℓ a := by
  unfold Wt
  rw [← sum_add_distrib]
  exact sum_congr rfl fun n _ => by rw [← iterShift_add]; ring

/-- **Proposition 8.8** (quadratic arrays). -/
theorem quadratic_matrix : Stmt_quadratic := by
  intro N vv hv hq
  obtain ⟨β₁, β₂, κ₁, κ₂, hform, hκ2, hd2, hbmono⟩ := hq
  have hv' := hv
  obtain ⟨hN, _, hb0, hc0, haN, hsum, hapos, hcpos⟩ := hv'
  set u := padNewton N (newtonCoeff vv.c) with hu_def
  set v := padNewton N (newtonCoeff vv.b) with hv_def
  have hcN : ∀ k, k ≤ N → newtonCoeff vv.c k = if k = 1 then κ₁ else if k = 2 then κ₂ else if k = 0 then 0 else 0 := by
    intro k hk
    rw [newtonCoeff_congr (d' := fun n : ℕ => κ₁ * n + κ₂ * (n.choose 2 : ℝ)) (fun i hi => (hform i (by omega)).2),
      newtonCoeff_quad]
  have hbN : ∀ k, k ≤ N → newtonCoeff vv.b k = if k = 1 then β₁ else if k = 2 then β₂ else if k = 0 then 0 else 0 := by
    intro k hk
    rw [newtonCoeff_congr (d' := fun n : ℕ => β₁ * n + β₂ * (n.choose 2 : ℝ)) (fun i hi => (hform i (by omega)).1),
      newtonCoeff_quad]
  have hκ1 : 0 < κ₁ := by
    have := hcpos 1 (by omega) hN; rw [(hform 1 hN).2] at this; simpa using this
  have pad_val : ∀ (x : ℕ → ℝ) (p q : ℝ), (∀ k, k ≤ N → newtonCoeff x k =
      if k = 1 then p else if k = 2 then q else if k = 0 then 0 else 0) →
      ∀ i, padNewton N (newtonCoeff x) i = if i = 1 then p else if i = 2 ∧ 2 ≤ N then q else 0 := by
    intro x p q hx i
    unfold padNewton
    by_cases hi : 1 ≤ i ∧ i ≤ N
    · rw [if_pos hi, hx i hi.2]
      by_cases h1 : i = 1
      · subst h1; simp
      by_cases h2 : i = 2
      · subst h2; simp [hi.2]
      rw [if_neg h1, if_neg h2, if_neg (by omega), if_neg h1, if_neg (fun h => h2 h.1)]
    · rw [if_neg hi, if_neg (by omega), if_neg (by omega)]
  have hu_val : ∀ i, u i = if i = 1 then κ₁ else if i = 2 ∧ 2 ≤ N then κ₂ else 0 := pad_val vv.c κ₁ κ₂ hcN
  have hv_val : ∀ i, v i = if i = 1 then β₁ else if i = 2 ∧ 2 ≤ N then β₂ else 0 := pad_val vv.b β₁ β₂ hbN
  have hu_nn : ∀ i, 0 ≤ u i := fun i => by rw [hu_val]; split_ifs <;> linarith
  have hu1 : 0 < u 1 := by rw [hu_val]; simp [hκ1]
  have hu0 : u 0 = 0 := padNewton_zero _ _
  have hu_high : ∀ i, 3 ≤ i → u i = 0 := fun i hi => by rw [hu_val]; rw [if_neg (by omega), if_neg (by omega)]
  have hv_high : ∀ i, 3 ≤ i → v i = 0 := fun i hi => by rw [hv_val]; rw [if_neg (by omega), if_neg (by omega)]
  have huv_nn : ∀ i, 2 ≤ i → 0 ≤ u i + v i := fun i hi => by
    rw [hu_val, hv_val]
    by_cases h2 : i = 2 ∧ 2 ≤ N
    · rw [if_neg (by omega), if_pos h2, if_neg (by omega), if_pos h2]; exact hd2
    · rw [if_neg (by omega), if_neg h2, if_neg (by omega), if_neg h2]; norm_num
  have hddc : ∀ i, i ≤ N → dd u i = vv.c i := fun i hi => dd_padNewton vv.c hc0 N i hi
  have hddb : ∀ i, i ≤ N → dd v i = vv.b i := fun i hi => dd_padNewton vv.b hb0 N i hi
  refine matrixPositivity_of_kernel vv hv hu_nn hu1 hu0 hddc hddb (fun k' hk' => ?_)
  have hT : dd v N + dd u N = 1 := by
    rw [hddb N le_rfl, hddc N le_rfl]; have := hsum N le_rfl; rw [haN] at this; linarith
  -- weights
  have hAhigh : ∀ j ℓ a, 1 ≤ j → wA v j ℓ a = 0 := fun j ℓ a hj =>
    Wt_high (fun ℓ n hn => iterShift_high hv_high ℓ n (by omega)) _ _ _
  have hBhigh : ∀ j ℓ a, 1 ≤ j → wB u j ℓ a = 0 := fun j ℓ a hj =>
    Wt_high (fun ℓ n hn => iterShift_high hu_high ℓ n (by omega)) _ _ _
  have hChigh : ∀ j ℓ a, 1 ≤ j → wC u v j ℓ a = 0 := fun j ℓ a hj => by
    unfold wC
    rw [Wt_high (fun ℓ n hn => iterShift_high hu_high ℓ n (by omega)),
      Wt_high (fun ℓ n hn => iterShift_high hv_high ℓ n (by omega)), add_zero]
  have hB_nn : ∀ j ℓ a, 0 ≤ wB u j ℓ a := fun j ℓ a => Wt_nonneg_of hu_nn _ _ _ _
  have hC_nn : ∀ j ℓ a, 0 ≤ wC u v j ℓ a := fun j ℓ a => by
    unfold wC
    rw [Wt_add]
    refine Wt_nonneg_high (fun ℓ n hn => ?_) _ _ _
    rw [iterShift_eq]
    exact sum_nonneg fun h _ => mul_nonneg (Nat.cast_nonneg _) (huv_nn _ (by omega))
  have hA0 : ∀ ℓ a, ℓ + a ≤ N → 0 ≤ wA v 0 ℓ a := fun ℓ a hla => by
    unfold wA
    rw [show 2 * 0 + 1 = 1 by ring, Wt_one_zero, hddb _ hla, hddb _ (by omega)]
    have : ∀ m, ℓ + m ≤ N → vv.b ℓ ≤ vv.b (ℓ + m) := by
      intro m; induction m with
      | zero => intro _; simp
      | succ m ih => intro h; exact le_trans (ih (by omega)) (hbmono (ℓ + m) (by omega))
    linarith [this a hla]
  have hA_nn : ∀ j ℓ a, ℓ + a ≤ N → 0 ≤ wA v j ℓ a := fun j ℓ a hla => by
    rcases Nat.eq_zero_or_pos j with h | h
    · subst h; exact hA0 ℓ a hla
    · rw [hAhigh j ℓ a h]
  have hgw : GenWeights (dd u) (wA v) (wB u) (wC u v) (wSV u v) N := by
    refine ⟨fun n hn => dd_pos_of hu_nn hu1 hn, hA_nn, fun j ℓ a _ => hB_nn j ℓ a,
      fun j ℓ a _ => hC_nn j ℓ a, fun ℓ a hla => ?_, fun j ℓ a hj hla => ?_,
      fun j ℓ a hj hla => ?_, fun j ℓ a hj hla => ?_⟩
    · unfold wSV
      rcases Nat.lt_or_ge (ℓ + a) N with h | h
      · rw [hddb _ h.le, hddc _ h.le]; have := hsum (ℓ + a) h.le; linarith [hapos (ℓ + a) h]
      · rw [show ℓ + a = N by omega]; linarith
    · rw [hAhigh j ℓ a hj, mul_zero]
      refine add_nonneg (mul_nonneg (hA0 ℓ a hla) (hB_nn _ _ _)) (mul_nonneg (hB_nn _ _ _) ?_)
      rcases Nat.eq_or_lt_of_le hj with e | hj2
      · subst e
        rcases Nat.lt_or_ge a 2 with ha | ha
        · unfold wA; rw [Wt_eq_zero _ _ _ _ (by omega)]
        · exact hA0 (ℓ + 1) (a - 2) (by omega)
      · rw [hAhigh (j - 1) _ _ (by omega)]
    · rw [hBhigh j ℓ a hj, mul_zero]; exact mul_nonneg (hB_nn _ _ _) (hB_nn _ _ _)
    · rw [hChigh j ℓ a hj, mul_zero]; exact mul_nonneg (hB_nn _ _ _) (hC_nn _ _ _)
  exact gkernel_nonneg hgw (genRec_of hu_nn hu1)
    (fun a => by rw [kerFnV_zero]; split_ifs <;> norm_num) (kerFnV_supp hu_nn hu1 N hk' hT)

end Szkraw
