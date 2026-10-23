import Szkraw.CubicE

/-!
# Theorem 8.17: the detours of `B` and `E`

A form of `detour_gen` whose local inequality may use `φ₂ + (n/3) φ₃`, since
`B₀(ℓ,a) ≥ C(a,2) φ₂ + C(a,3) φ₃` and `C(a,3) = C(a,2)(a-2)/3 ≥ C(a,2) n/3` for `n ≤ a - 2`. With it the `B`
detour (constant `4`, from eq. `cubic-B` and, at `(ℓ,n) = (0,2)`, eq. `cubic-corner`) and the `E` detour
(constant `3`, from eq. `cubic-E`) follow.
-/

set_option linter.unusedSectionVars false

namespace Szkraw

open Finset

/-- Detour factor of `E`: `3(n-1)/((n+1)(n+2))`. -/
noncomputable def kapE (n : ℕ) : ℝ := 3 * ((n : ℝ) - 1) / (((n : ℝ) + 1) * ((n : ℝ) + 2))

theorem detour_gen3 {F : ℕ → ℕ → ℝ} {p q Q ℓ a : ℕ} {B0 c φ2 φ3 κ0 : ℝ} {κ : ℕ → ℝ} (hc : 0 ≤ c)
    (hB0nn : 0 ≤ B0) (hB0 : (a.choose 2 : ℝ) * φ2 + (a.choose 3 : ℝ) * φ3 ≤ B0) (hφ3 : 0 ≤ φ3)
    (hF0 : ∀ m, m ≤ a → 0 ≤ F ℓ m) (hF1 : ∀ n, 0 ≤ F (ℓ + 1) n)
    (hloc : ∀ n, p ≤ n → n + 2 ≤ a → κ n * (c * F ℓ (n + 2)) ≤ (φ2 + (n : ℝ) / 3 * φ3) * F (ℓ + 1) n)
    (hcoef : ∀ m, p + 2 ≤ m → m ≤ a → κ0 * ((m - (p + 2) + Q).choose Q : ℝ) ≤
      ((m - 2 - p + q).choose q : ℝ) * (m.choose 2 : ℝ) * κ (m - 2)) :
    κ0 * c * WtF F (p + 2) Q ℓ a ≤ B0 * WtF F p q (ℓ + 1) (a - 2) := by
  have hWnn : 0 ≤ WtF F p q (ℓ + 1) (a - 2) := WtF_nonneg fun n _ _ => hF1 n
  by_cases ha : a < p + 2
  · rw [WtF_eq_zero ha, mul_zero]; exact mul_nonneg hB0nn hWnn
  push Not at ha
  set G : ℕ → ℝ := fun m => (if p + 2 ≤ m then ((m - 2 - p + q).choose q : ℝ) * (m.choose 2 : ℝ) * κ (m - 2)
    else 0) * (a.choose m : ℝ) * (c * F ℓ m) with hG
  have step1 : κ0 * c * WtF F (p + 2) Q ℓ a ≤ ∑ m ∈ range (a + 1), G m := by
    rw [WtF, mul_sum]
    refine sum_le_sum fun m hm => ?_
    rw [mem_range] at hm
    simp only [hG]
    by_cases h : p + 2 ≤ m
    · rw [if_pos h, if_pos h]
      have hco := hcoef m h (by omega)
      have hcF : 0 ≤ (a.choose m : ℝ) * (c * F ℓ m) :=
        mul_nonneg (Nat.cast_nonneg _) (mul_nonneg hc (hF0 m (by omega)))
      calc κ0 * c * (((m - (p + 2) + Q).choose Q : ℝ) * (a.choose m : ℝ) * F ℓ m)
          = (κ0 * ((m - (p + 2) + Q).choose Q : ℝ)) * ((a.choose m : ℝ) * (c * F ℓ m)) := by ring
        _ ≤ (((m - 2 - p + q).choose q : ℝ) * (m.choose 2 : ℝ) * κ (m - 2)) * ((a.choose m : ℝ) * (c * F ℓ m)) :=
            mul_le_mul_of_nonneg_right hco hcF
        _ = _ := by ring
    · rw [if_neg h, if_neg h]; simp
  have hre : ∑ m ∈ range (a + 1), G m = ∑ n ∈ range (a - 1), G (n + 2) := by
    rw [reindex2 G (a - 1) (by simp [hG]) (by simp [hG]), show a - 1 + 2 = a + 1 by omega]
  have step2 : ∑ n ∈ range (a - 1), G (n + 2) ≤ ∑ n ∈ range (a - 1),
      (if p ≤ n then ((n - p + q).choose q : ℝ) else 0) * ((a - 2).choose n : ℝ) * F (ℓ + 1) n * B0 := by
    refine sum_le_sum fun n hn => ?_
    rw [mem_range] at hn
    simp only [hG]
    by_cases hpn : p ≤ n
    · rw [if_pos (by omega), if_pos hpn, show n + 2 - 2 = n by omega]
      have hc' : ((n + 2).choose 2 : ℝ) * (a.choose (n + 2) : ℝ) = (a.choose 2 : ℝ) * ((a - 2).choose n : ℝ) := by
        have hc2 := Nat.choose_mul (n := a) (k := n + 2) (s := 2) (by omega)
        rw [show n + 2 - 2 = n by omega] at hc2
        have : ((a.choose (n + 2) * (n + 2).choose 2 : ℕ) : ℝ) = ((a.choose 2 * (a - 2).choose n : ℕ) : ℝ) := by
          rw [hc2]
        push_cast at this; linarith
      have key := hloc n hpn (by omega)
      have hC : (0 : ℝ) ≤ ((n - p + q).choose q : ℝ) * ((a.choose 2 : ℝ) * ((a - 2).choose n : ℝ)) := by
        positivity
      have h23 : (a.choose 2 : ℝ) * ((n : ℝ) / 3) ≤ (a.choose 3 : ℝ) := by
        rw [choose2_real, choose3_real]
        have hna : (n : ℝ) ≤ (a : ℝ) - 2 := by
          have : n + 2 ≤ a := by omega
          have : ((n + 2 : ℕ) : ℝ) ≤ a := by exact_mod_cast this
          push_cast at this; linarith
        have ha2 : (0 : ℝ) ≤ (a : ℝ) * ((a : ℝ) - 1) := by
          have : (2 : ℝ) ≤ a := by have := (Nat.cast_nonneg n : (0 : ℝ) ≤ n); linarith
          nlinarith
        nlinarith [mul_le_mul_of_nonneg_left hna ha2]
      have hB : (a.choose 2 : ℝ) * (φ2 + (n : ℝ) / 3 * φ3) ≤ B0 := by
        have := mul_le_mul_of_nonneg_right h23 hφ3
        nlinarith [this, hB0]
      have hW : (0 : ℝ) ≤ ((n - p + q).choose q : ℝ) * ((a - 2).choose n : ℝ) * F (ℓ + 1) n :=
        mul_nonneg (by positivity) (hF1 n)
      calc ((n - p + q).choose q : ℝ) * ((n + 2).choose 2 : ℝ) * κ n * (a.choose (n + 2) : ℝ) * (c * F ℓ (n + 2))
          = ((n - p + q).choose q : ℝ) * (((n + 2).choose 2 : ℝ) * (a.choose (n + 2) : ℝ)) *
              (κ n * (c * F ℓ (n + 2))) := by ring
        _ = ((n - p + q).choose q : ℝ) * ((a.choose 2 : ℝ) * ((a - 2).choose n : ℝ)) *
              (κ n * (c * F ℓ (n + 2))) := by rw [hc']
        _ ≤ ((n - p + q).choose q : ℝ) * ((a.choose 2 : ℝ) * ((a - 2).choose n : ℝ)) *
              ((φ2 + (n : ℝ) / 3 * φ3) * F (ℓ + 1) n) := mul_le_mul_of_nonneg_left key hC
        _ = (((n - p + q).choose q : ℝ) * ((a - 2).choose n : ℝ) * F (ℓ + 1) n) *
              ((a.choose 2 : ℝ) * (φ2 + (n : ℝ) / 3 * φ3)) := by ring
        _ ≤ (((n - p + q).choose q : ℝ) * ((a - 2).choose n : ℝ) * F (ℓ + 1) n) * B0 :=
            mul_le_mul_of_nonneg_left hB hW
    · rw [if_neg (by omega), if_neg hpn]; simp
  have step3 : ∑ n ∈ range (a - 1), (if p ≤ n then ((n - p + q).choose q : ℝ) else 0) *
      ((a - 2).choose n : ℝ) * F (ℓ + 1) n * B0 = B0 * WtF F p q (ℓ + 1) (a - 2) := by
    rw [WtF, show a - 2 + 1 = a - 1 by omega, mul_sum]; exact sum_congr rfl fun n _ => by ring
  linarith [step1, hre, step2, step3]

/-- Coefficients of the `E` detour: `2C(m-j-1, j) ≤ (m-3) C(m-j-2, j-1)`, i.e. `(j-2)(m-1) ≥ 0`. -/
theorem coefE {j m : ℕ} (hj : 2 ≤ j) (hm : 2 * j + 1 ≤ m) :
    3 * ((m - (2 * j - 1 + 2) + j).choose j : ℝ) ≤
      ((m - 2 - (2 * j - 1) + (j - 1)).choose (j - 1) : ℝ) * (m.choose 2 : ℝ) * kapE (m - 2) := by
  obtain ⟨M, hM⟩ : ∃ M, M + j + 1 = m := ⟨m - j - 1, by omega⟩
  rw [show m - (2 * j - 1 + 2) + j = M by omega, show m - 2 - (2 * j - 1) + (j - 1) = M - 1 by omega]
  have hrel := choose_pred_rel (M := M) (j := j) (by omega) (by omega)
  have hMm : (M : ℝ) + j + 1 = m := by exact_mod_cast hM
  have hm5 : (5 : ℝ) ≤ m := by exact_mod_cast (show 5 ≤ m by omega)
  have hk : (m.choose 2 : ℝ) * kapE (m - 2) = 3 * ((m : ℝ) - 3) / 2 := by
    unfold kapE
    rw [choose2_real, Nat.cast_sub (by omega : 2 ≤ m), Nat.cast_ofNat, show (m : ℝ) - 2 + 1 = (m : ℝ) - 1 by ring,
      show (m : ℝ) - 2 + 2 = (m : ℝ) by ring]
    have h1 : (m : ℝ) - 1 ≠ 0 := by linarith
    have h2 : (m : ℝ) ≠ 0 := by linarith
    field_simp
    ring
  rw [mul_assoc, hk]
  have hX : (0 : ℝ) ≤ ((M - 1).choose (j - 1) : ℝ) := Nat.cast_nonneg _
  have hj' : (2 : ℝ) ≤ j := by exact_mod_cast hj
  have hle : 2 * (M : ℝ) ≤ j * ((m : ℝ) - 3) := by
    nlinarith [mul_nonneg (sub_nonneg.2 hj') (by linarith : (0 : ℝ) ≤ (m : ℝ) - 1)]
  have h1 : (j : ℝ) * (3 * (M.choose j : ℝ)) ≤ (j : ℝ) * (((M - 1).choose (j - 1) : ℝ) * (3 * ((m : ℝ) - 3) / 2)) := by
    have e : (j : ℝ) * (3 * (M.choose j : ℝ)) = 3 * ((M : ℝ) * ((M - 1).choose (j - 1) : ℝ)) := by
      rw [hrel]; ring
    rw [e]
    have := mul_le_mul_of_nonneg_right hle hX
    nlinarith
  exact le_of_mul_le_mul_left h1 (by linarith)

/-! ### The local inequalities for every `n` -/

theorem kap_scale {K L X Y P Q : ℝ} (hK : 0 < K) (hP : 0 ≤ Q) (hY : 0 ≤ Y) (h : L * X ≤ K * P * Y) :
    L / K * X ≤ (P + Q) * Y := by
  rw [div_mul_eq_mul_div, div_le_iff₀ hK]
  nlinarith [mul_nonneg hP hY]

/-- The local `B` inequality (eqs. `cubic-B`, `cubic-corner`) for every `n ≥ 2`. -/
theorem cubicB_all {v : ℕ → ℝ} (hv : LCNZ v) (hv1 : 0 < v 1) {r t τ σ : ℝ} (hr : 0 < r) (ht : 0 ≤ t)
    (hτ : 0 ≤ τ) (hσ : 0 ≤ σ) (hrs : r * σ ≤ t * τ) (ℓ n : ℕ) (hn : 2 ≤ n) (hz : v 0 ≤ (ℓ : ℝ) * v 1)
    (hv0 : ℓ = 0 → v 0 = 0) :
    kapB n * (rhoC r t τ σ (ℓ + 1) * (v 0 + v 1) * PhiC r t τ σ ℓ (n + 2) v) ≤
      (PhiC r t τ σ ℓ 2 v + (n : ℝ) / 3 * PhiC r t τ σ ℓ 3 v) * PhiC r t τ σ (ℓ + 1) n (fun k => v k + v (k + 1)) := by
  have hw : ∀ k, 0 ≤ v k + v (k + 1) := fun k => add_nonneg (hv.1 k) (hv.1 (k + 1))
  have hY := PhiC_nonneg hr.le ht hτ hσ hw (ℓ + 1) n
  have h3 : 0 ≤ (n : ℝ) / 3 * PhiC r t τ σ ℓ 3 v := mul_nonneg (by positivity) (PhiC_nonneg hr.le ht hτ hσ hv.1 ℓ 3)
  have hK : (0 : ℝ) < ((n : ℝ) + 1) * ((n : ℝ) + 2) := by positivity
  unfold kapB
  rcases (show n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ 6 ≤ n by omega) with rfl | rfl | rfl | rfl | h6
  · rcases Nat.eq_zero_or_pos ℓ with rfl | hℓ
    · have hc := cubicB_corner hv hv1 hr ht hτ hσ hrs (hv0 rfl) hz
      rw [div_mul_eq_mul_div, div_le_iff₀ hK]
      push_cast at hc ⊢
      linarith
    · obtain ⟨l, rfl⟩ : ∃ l, ℓ = l + 1 := ⟨ℓ - 1, by omega⟩
      exact kap_scale hK h3 hY (by have := cubicB_two hv hv1 hr ht hτ hσ hrs l hz; push_cast at this ⊢; linarith)
  · exact kap_scale hK h3 hY (by have := cubicB_three hv hv1 hr ht hτ hσ hrs ℓ hz; push_cast at this ⊢; linarith)
  · exact kap_scale hK h3 hY (by have := cubicB_four hv hv1 hr ht hτ hσ hrs ℓ hz; push_cast at this ⊢; linarith)
  · exact kap_scale hK h3 hY (by have := cubicB_five hv hv1 hr ht hτ hσ hrs ℓ hz; push_cast at this ⊢; linarith)
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 6 := ⟨n - 6, by omega⟩
    exact kap_scale hK h3 hY (by have := cubicB_gen hv hv1 hr ht hτ hσ hrs ℓ m hz; push_cast at this ⊢; linarith)

/-- The local `E` inequality (eq. `cubic-E`) for every `n ≥ 3`. -/
theorem cubicE_all {v : ℕ → ℝ} (hv : LCNZ v) {r t τ σ : ℝ} (hr : 0 < r) (ht : 0 ≤ t)
    (hτ : 0 ≤ τ) (hσ : 0 ≤ σ) (hrs : r * σ ≤ t * τ) (ℓ n : ℕ) (hn : 3 ≤ n) :
    kapE n * (rhoC r t τ σ (ℓ + 1) * (v 0 + v 1) * eCv τ σ ℓ (n + 2) v) ≤
      (PhiC r t τ σ ℓ 2 v + (n : ℝ) / 3 * PhiC r t τ σ ℓ 3 v) * eCv τ σ (ℓ + 1) n (fun k => v k + v (k + 1)) := by
  have hK : (0 : ℝ) < ((n : ℝ) + 1) * ((n : ℝ) + 2) := by positivity
  unfold kapE
  rw [div_mul_eq_mul_div, div_le_iff₀ hK]
  rcases (show n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ 7 ≤ n by omega) with rfl | rfl | rfl | rfl | h7
  · have := cubicE_three hv hr ht hτ hσ hrs ℓ; push_cast at this ⊢; linarith
  · have := cubicE_four hv hr ht hτ hσ hrs ℓ; push_cast at this ⊢; linarith
  · have := cubicE_five hv hr ht hτ hσ hrs ℓ; push_cast at this ⊢; linarith
  · have := cubicE_six hv hr ht hτ hσ hrs ℓ; push_cast at this ⊢; linarith
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 7 := ⟨n - 7, by omega⟩
    have := cubicE_gen hv hr ht hτ hσ hrs ℓ m; push_cast at this ⊢; linarith

/-! ### The detours of `B` and `E` in the setting -/

section Setting

variable {N : ℕ} {r t τ σ : ℝ} {ν u : ℕ → ℝ} (S : CubicSetting N r t τ σ ν u)
include S

/-- The `B` detour. -/
theorem CubicSetting.domB {j ℓ a : ℕ} (hj : 1 ≤ j) (h : ℓ + a ≤ N) :
    4 * dd u (ℓ + 1) * Wt u (2 * j + 2) j ℓ a ≤ Wt u 2 0 ℓ a * Wt u (2 * j) (j - 1) (ℓ + 1) (a - 2) := by
  rw [Wt_eq_WtF u (2 * j + 2), Wt_eq_WtF u (2 * j)]
  refine detour_gen3 (κ := kapB) (p := 2 * j) (φ3 := Szkraw.iterShift u ℓ 3) (S.cc_nn ℓ)
    (Wt_nonneg_of S.hu_nn _ _ _ _) (S.B0_ge_phi23 ℓ a) (S.g_nn ℓ 3) (fun m _ => S.g_nn ℓ m)
    (fun n => S.g_nn (ℓ + 1) n) (fun n hn hna => ?_) (fun m hm hma => coefB hj hm)
  have hn2 : 2 ≤ n := by omega
  rw [S.dd_u (by omega), S.hφ ℓ (n + 2) (by omega), S.hφ ℓ 2 (by omega), S.hφ ℓ 3 (by omega),
    S.hφ (ℓ + 1) n (by omega)]
  have hB := cubicB_all (v := Szkraw.iterShift ν ℓ) (S.hν.iterShift ℓ) (S.f1_pos ℓ) S.hr S.ht S.hτ S.hσ S.hrs
    ℓ n hn2 (S.dd_le ℓ) (fun hℓ => by subst hℓ; exact S.hν0)
  have e1 : (fun k => Szkraw.iterShift ν ℓ k + Szkraw.iterShift ν ℓ (k + 1)) = Szkraw.iterShift ν (ℓ + 1) := rfl
  have e3 : Szkraw.iterShift ν ℓ 0 + Szkraw.iterShift ν ℓ 1 = dd ν (ℓ + 1) := rfl
  rw [e1, e3] at hB
  linarith

/-- The `E` detour. -/
theorem CubicSetting.domE {j ℓ a : ℕ} (hj : 2 ≤ j) (h : ℓ + a ≤ N) :
    3 * dd u (ℓ + 1) * cubicE τ σ ν j ℓ a ≤ Wt u 2 0 ℓ a * cubicE τ σ ν (j - 1) (ℓ + 1) (a - 2) := by
  unfold cubicE
  rw [show 2 * (j - 1) + 1 = 2 * j - 1 by omega, show 2 * j + 1 = 2 * j - 1 + 2 by omega]
  refine detour_gen3 (κ := kapE) (φ3 := Szkraw.iterShift u ℓ 3) (S.cc_nn ℓ) (Wt_nonneg_of S.hu_nn _ _ _ _)
    (S.B0_ge_phi23 ℓ a) (S.g_nn ℓ 3) (fun m _ => S.eC_nn ℓ m) (fun n => S.eC_nn (ℓ + 1) n) (fun n hn hna => ?_)
    (fun m hm hma => coefE hj (by omega))
  have hn3 : 3 ≤ n := by omega
  rw [S.dd_u (by omega), S.hφ ℓ 2 (by omega), S.hφ ℓ 3 (by omega), eC_eq, eC_eq]
  have hE := cubicE_all (v := Szkraw.iterShift ν ℓ) (S.hν.iterShift ℓ) S.hr S.ht S.hτ S.hσ S.hrs ℓ n hn3
  have e1 : (fun k => Szkraw.iterShift ν ℓ k + Szkraw.iterShift ν ℓ (k + 1)) = Szkraw.iterShift ν (ℓ + 1) := rfl
  have e3 : Szkraw.iterShift ν ℓ 0 + Szkraw.iterShift ν ℓ 1 = dd ν (ℓ + 1) := rfl
  rw [e1, e3] at hE
  linarith

end Setting

end Szkraw
