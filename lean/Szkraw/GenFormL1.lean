import Szkraw.GenFormK

/-!
# The coefficient `l₁` of the key of Theorem 8.16

`linC f a 1 = X β'₁ + X' β₁ - 4 D H_*` with `β'₁ = aA + (a-2)D - 2(a-1)d₂` and `β₁ = a(A - D)`; both are
nonnegative `u₀`-free linear forms, so the edge bound applies directly (paper (ii): `l₁ ≥ L ≥ 0`).
-/

set_option linter.unusedSectionVars false

namespace Szkraw

open Finset

noncomputable def cfBp1 (a n : ℕ) : ℝ :=
  (a : ℝ) * (a.choose n : ℝ) + ((a : ℝ) - 2) * ((1 : ℕ).choose n : ℝ) - 2 * ((a : ℝ) - 1) * ((2 : ℕ).choose n : ℝ)
noncomputable def cfB1 (a n : ℕ) : ℝ := (a : ℝ) * (a.choose n : ℝ) - (a : ℝ) * ((1 : ℕ).choose n : ℝ)

section Values

variable {a : ℕ}

theorem cfBp1_zero : cfBp1 a 0 = 0 := by simp [cfBp1]; ring
theorem cfBp1_one : cfBp1 a 1 = (a : ℝ) ^ 2 - 3 * a + 2 := by simp [cfBp1]; ring
theorem cfBp1_two : cfBp1 a 2 = (a : ℝ) * (a.choose 2 : ℝ) - 2 * ((a : ℝ) - 1) := by simp [cfBp1]
theorem cfBp1_ge3 {n : ℕ} (hn : 3 ≤ n) : cfBp1 a n = (a : ℝ) * (a.choose n : ℝ) := by
  unfold cfBp1; rw [choose_small_zero (by omega : 1 < n), choose_small_zero (by omega : 2 < n)]; ring
theorem cfB1_zero : cfB1 a 0 = 0 := by simp [cfB1]
theorem cfB1_one : cfB1 a 1 = (a : ℝ) * ((a : ℝ) - 1) := by simp [cfB1]; ring
theorem cfB1_ge2 {n : ℕ} (hn : 2 ≤ n) : cfB1 a n = (a : ℝ) * (a.choose n : ℝ) := by
  unfold cfB1; rw [choose_small_zero (by omega : 1 < n)]; ring

theorem cfBp1_nonneg (ha : 3 ≤ a) (n : ℕ) : 0 ≤ cfBp1 a n := by
  have hA : (3 : ℝ) ≤ a := by exact_mod_cast ha
  rcases (show n = 0 ∨ n = 1 ∨ n = 2 ∨ 3 ≤ n by omega) with rfl | rfl | rfl | hn
  · rw [cfBp1_zero]
  · rw [cfBp1_one]; nlinarith
  · rw [cfBp1_two, cast_choose_two]
    nlinarith [mul_nonneg (show (0:ℝ) ≤ (a:ℝ) - 1 by linarith) (show (0:ℝ) ≤ (a:ℝ) * a - 4 by nlinarith)]
  · rw [cfBp1_ge3 hn]; positivity
theorem cfB1_nonneg (ha : 1 ≤ a) (n : ℕ) : 0 ≤ cfB1 a n := by
  have hA : (1 : ℝ) ≤ a := by exact_mod_cast ha
  rcases (show n = 0 ∨ n = 1 ∨ 2 ≤ n by omega) with rfl | rfl | hn
  · rw [cfB1_zero]
  · rw [cfB1_one]; nlinarith
  · rw [cfB1_ge2 hn]; positivity
theorem cfB_vanish {n : ℕ} (ha : 3 ≤ a) (hn : a + 1 ≤ n) : cfBp1 a n = 0 ∧ cfB1 a n = 0 := by
  have z : ((a.choose n : ℕ) : ℝ) = 0 := choose_small_zero (by omega)
  exact ⟨by rw [cfBp1_ge3 (by omega), z, mul_zero], by rw [cfB1_ge2 (by omega), z, mul_zero]⟩

end Values

theorem linC_one_lf (f : ℕ → ℝ) {a : ℕ} (ha : 3 ≤ a) :
    linC f a 1 = lf (a + 1) (cfX a) f * lf (a + 1) (cfBp1 a) f + lf (a + 1) (cfXp a) f * lf (a + 1) (cfB1 a) f -
      4 * (f 0 + f 1) * lf (a + 1) (cfH a) f := by
  have hA := dd_lf f (m := a) (R := a + 1) (by omega)
  have h0 := dd_lf f (m := 0) (R := a + 1) (by omega)
  have h1 := dd_lf f (m := 1) (R := a + 1) (by omega)
  have h2 := dd_lf f (m := 2) (R := a + 1) (by omega)
  have hB := dd_lf f (m := a - 1) (R := a + 1) (by omega)
  have eX : dd f a - dd f 0 = lf (a + 1) (cfX a) f := by
    rw [hA, h0]; unfold lf cfX; rw [← sum_sub_distrib]; exact sum_congr rfl fun n _ => by ring
  have eXp : dd f (a - 1) - dd f 1 = lf (a + 1) (cfXp a) f := by
    rw [hB, h1]; unfold lf cfXp; rw [← sum_sub_distrib]; exact sum_congr rfl fun n _ => by ring
  have eB : betaC f a 1 = lf (a + 1) (cfB1 a) f := by
    unfold betaC; rw [hA, h0, h1]; unfold lf cfB1
    simp only [Nat.choose_one_right, Nat.cast_zero, zero_mul, sub_zero, Nat.cast_one,
      one_mul, mul_sum, ← sum_sub_distrib]
    exact sum_congr rfl fun n _ => by ring
  have eBp : beta'C f a 1 = lf (a + 1) (cfBp1 a) f := by
    unfold beta'C; rw [hA, h1, h2]; unfold lf cfBp1
    simp only [Nat.choose_one_right, Nat.cast_one, mul_one, mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
    refine sum_congr rfl fun n _ => ?_
    push_cast; ring
  have eH : Hstar f a = lf (a + 1) (cfH a) f := by
    unfold Hstar lf cfH; exact sum_congr rfl fun n _ => by ring
  unfold linC
  rw [eX, eXp, eB, eBp, eH, dd_one_eq, if_pos le_rfl]
  ring

noncomputable def eL1 (a n : ℕ) : ℝ :=
  edgeCoef (cfX a) (cfBp1 a) n + edgeCoef (cfB1 a) (cfXp a) n - 4 * cfH a n - 4 * cfH a (n + 1)

theorem linC_one_ge (f : ℕ → ℝ) (hf : LCNZ f) {a : ℕ} (ha : 3 ≤ a) :
    f 1 * lf (a + 2) (eL1 a) f ≤ linC f a 1 := by
  rw [linC_one_lf f ha]
  have hv := fun n (hn : a + 1 ≤ n) => cf_vanish (a := a) ha hn
  have hw := fun n (hn : a + 1 ≤ n) => cfB_vanish (a := a) ha hn
  have E1 := hf.edge_prod (R := a + 1) (by omega) (x := cfX a) (y := cfBp1 a) cfX_nonneg (cfBp1_nonneg ha)
    cfX_zero cfBp1_zero (fun n hn => (hv n hn).1) (fun n hn => (hw n hn).1)
  have E2 := hf.edge_prod (R := a + 1) (by omega) (x := cfB1 a) (y := cfXp a) (cfB1_nonneg (by omega))
    (cfXp_nonneg (by omega)) cfB1_zero cfXp_zero (fun n hn => (hw n hn).2) (fun n hn => (hv n hn).2.1)
  have N0 := hf.u0_lf a (cfH a) cfH_nonneg (cfH_le2 (by omega))
  have hH : lf (a + 1) (cfH a) f = lf (a + 2) (cfH a) f :=
    lf_extend (by omega) (fun n hn => (hv n hn).2.2.2.2)
  have hH' : lf a (fun m => cfH a (m + 1)) f = lf (a + 2) (fun m => cfH a (m + 1)) f :=
    lf_extend (by omega) (fun n hn => (hv (n + 1) (by omega)).2.2.2.2)
  have hsplit : lf (a + 2) (eL1 a) f = lf (a + 2) (edgeCoef (cfX a) (cfBp1 a)) f +
      lf (a + 2) (edgeCoef (cfB1 a) (cfXp a)) f - 4 * lf (a + 2) (cfH a) f -
        4 * lf (a + 2) (fun m => cfH a (m + 1)) f := by
    unfold lf eL1; simp only [mul_sum, ← sum_add_distrib, ← sum_sub_distrib]
    exact sum_congr rfl fun n _ => by ring
  rw [hsplit, mul_comm (lf (a + 1) (cfXp a) f)]
  rw [← hH, ← hH'] at *
  have hf1 : 0 ≤ f 1 := hf.1 1
  have hHnn : 0 ≤ lf (a + 1) (cfH a) f := lf_nonneg hf (fun n _ => cfH_nonneg n)
  nlinarith [E1, E2, N0, mul_nonneg hf1 hHnn]

theorem eL1_arith (p K c cm cp d e : ℝ) (hp : 0 ≤ p) (hK : 0 ≤ K) (hc : 0 ≤ c)
    (h1 : cm * (K + 1) = c * (p + 4)) (h2 : cp * (p + 5) = c * K) (h3 : d * (p + 4 + K) = c * (p + 4))
    (h4 : e * (p + 4 + K) = c * K) :
    0 ≤ (p + 4 + K) * ((p + 4 + K) * c) + (p + 4 + K) * (p + 4 + K - 1) / 2 * ((p + 4 + K) * cm) +
      ((p + 4 + K) ^ 2 - 3 * (p + 4 + K) + 2) * c +
      ((p + 4 + K) * ((p + 4 + K) * (p + 4 + K - 1) / 2) - 2 * (p + 4 + K - 1)) * cm +
      ((p + 4 + K) * (p + 4 + K - 1) * e + (p + 4 + K) * ((p + 4 + K) * (p + 4 + K - 1) / 2) * d +
        (p + 4 + K - 2) * ((p + 4 + K) * c) + (p + 4 + K - 1) * (p + 4 + K - 2) / 2 * ((p + 4 + K) * cm)) -
      4 * ((p + 4) - 2) * c - 4 * ((p + 4) - 1) * cp := by
  have hK1 : 0 < K + 1 := by linarith
  have hp5 : 0 < p + 5 := by linarith
  have ha : 0 < p + 4 + K := by linarith
  have ecm : cm = c * (p + 4) / (K + 1) := by field_simp; linarith
  have ecp : cp = c * K / (p + 5) := by field_simp; linarith
  have ed : d = c * (p + 4) / (p + 4 + K) := by field_simp; linarith
  have ee : e = c * K / (p + 4 + K) := by field_simp; linarith
  rw [ecm, ecp, ed, ee]
  have key : (p + 4 + K) * ((p + 4 + K) * c) + (p + 4 + K) * (p + 4 + K - 1) / 2 * ((p + 4 + K) * (c * (p + 4) / (K + 1))) +
      ((p + 4 + K) ^ 2 - 3 * (p + 4 + K) + 2) * c +
      ((p + 4 + K) * ((p + 4 + K) * (p + 4 + K - 1) / 2) - 2 * (p + 4 + K - 1)) * (c * (p + 4) / (K + 1)) +
      ((p + 4 + K) * (p + 4 + K - 1) * (c * K / (p + 4 + K)) +
        (p + 4 + K) * ((p + 4 + K) * (p + 4 + K - 1) / 2) * (c * (p + 4) / (p + 4 + K)) +
        (p + 4 + K - 2) * ((p + 4 + K) * c) + (p + 4 + K - 1) * (p + 4 + K - 2) / 2 * ((p + 4 + K) * (c * (p + 4) / (K + 1)))) -
      4 * ((p + 4) - 2) * c - 4 * ((p + 4) - 1) * (c * K / (p + 5)) =
      c * (4 * K ^ 3 * p ^ 2 + 44 * K ^ 3 * p + 120 * K ^ 3 + 11 * K ^ 2 * p ^ 3 + 152 * K ^ 2 * p ^ 2 +
        685 * K ^ 2 * p + 1016 * K ^ 2 + 10 * K * p ^ 4 + 167 * K * p ^ 3 + 1034 * K * p ^ 2 + 2809 * K * p +
        2836 * K + 3 * p ^ 5 + 59 * p ^ 4 + 463 * p ^ 3 + 1801 * p ^ 2 + 3454 * p + 2620) / (2 * (K + 1) * (p + 5)) := by
    field_simp; ring
  rw [key]; positivity

theorem eL1_nonneg {a : ℕ} (ha : 3 ≤ a) (n : ℕ) : 0 ≤ eL1 a n := by
  have hA3 : (3 : ℝ) ≤ a := by exact_mod_cast ha
  have t : (0:ℝ) ≤ a - 3 := by linarith
  have c1 : ((a.choose 1 : ℕ) : ℝ) = a := by rw [Nat.choose_one_right]
  have c2 := cast_choose_two a
  have c3 := cast_choose_three a (by omega)
  have c4 := cast_choose_four a ha
  have c2' : (((a - 1).choose 2 : ℕ) : ℝ) = ((a : ℝ) - 1) * ((a : ℝ) - 2) / 2 := by
    rw [cast_choose_two, cast_pred (by omega)]; ring
  have c3' : (((a - 1).choose 3 : ℕ) : ℝ) = ((a : ℝ) - 1) * ((a : ℝ) - 2) * ((a : ℝ) - 3) / 6 := by
    rw [cast_choose_three (a - 1) (by omega), cast_pred (by omega)]; ring
  rcases (show n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ (4 ≤ n ∧ n ≤ a) ∨ n = a + 1 ∨ a + 2 ≤ n by omega) with
    rfl | rfl | rfl | rfl | ⟨h4, hna⟩ | rfl | hbig
  · unfold eL1; rw [edgeCoef_zero, edgeCoef_zero, cfBp1_zero, cfXp_zero, cfH_le2 (by norm_num),
      cfH_le2 (by norm_num)]; norm_num
  · unfold eL1
    rw [edgeCoef_one, edgeCoef_one, cfBp1_one, cfBp1_zero, cfB1_one, cfXp_zero, cfXp_one (by omega),
      cfX_pos (a := a) (n := 1) le_rfl, cfH_le2 (by norm_num), cfH_le2 (by norm_num), c1]
    nlinarith [mul_nonneg t t, mul_nonneg (mul_nonneg t t) t]
  · unfold eL1
    rw [edgeCoef_two, edgeCoef_two, cfX_pos (a := a) (n := 1) le_rfl, cfX_pos (a := a) (n := 2) (by norm_num),
      cfBp1_two, cfBp1_one, cfB1_one, cfB1_ge2 (a := a) (n := 2) le_rfl, cfXp_one (by omega),
      cfXp_ge2 (a := a) (n := 2) le_rfl, cfH_le2 (a := a) (n := 2) le_rfl, cfH_ge3 (a := a) (n := 2 + 1) (by norm_num),
      c1, c2, c3, c2']
    push_cast
    nlinarith [mul_nonneg t t, mul_nonneg (mul_nonneg t t) t, mul_nonneg (mul_nonneg (mul_nonneg t t) t) t]
  · unfold eL1
    rw [edgeCoef_three, edgeCoef_three, cfX_pos (a := a) (n := 1) le_rfl, cfX_pos (a := a) (n := 2) (by norm_num),
      cfX_pos (a := a) (n := 3) (by norm_num), cfBp1_ge3 (a := a) (n := 3) le_rfl, cfBp1_two, cfBp1_one, cfB1_one,
      cfB1_ge2 (a := a) (n := 2) le_rfl, cfB1_ge2 (a := a) (n := 3) (by norm_num), cfXp_one (by omega),
      cfXp_ge2 (a := a) (n := 2) le_rfl, cfXp_ge2 (a := a) (n := 3) (by norm_num),
      cfH_ge3 (a := a) (n := 3) le_rfl, cfH_ge3 (a := a) (n := 3 + 1) (by norm_num), c1, c2, c3, c4, c2', c3']
    push_cast
    nlinarith [mul_nonneg t t, mul_nonneg (mul_nonneg t t) t, mul_nonneg (mul_nonneg (mul_nonneg t t) t) t,
      mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg t t) t) t) t]
  · obtain ⟨p, rfl⟩ : ∃ p, n = p + 4 := ⟨n - 4, by omega⟩
    obtain ⟨K, rfl⟩ : ∃ K, a = p + 4 + K := ⟨a - (p + 4), by omega⟩
    set A := p + 4 + K with hAdef
    unfold eL1
    rw [edgeCoef_ge4 _ _ h4, edgeCoef_ge4 _ _ h4]
    simp only [show p + 4 - 1 = p + 3 by omega]
    rw [cfX_pos (a := A) (n := 1) le_rfl, cfX_pos (a := A) (n := 2) (by norm_num),
      cfX_pos (a := A) (n := p + 4) (by omega), cfX_pos (a := A) (n := p + 3) (by omega),
      cfBp1_ge3 (a := A) (n := p + 4) (by omega), cfBp1_ge3 (a := A) (n := p + 3) (by omega), cfBp1_two, cfBp1_one,
      cfB1_one, cfB1_ge2 (a := A) (n := 2) le_rfl, cfB1_ge2 (a := A) (n := p + 4) (by omega),
      cfB1_ge2 (a := A) (n := p + 3) (by omega), cfXp_one (a := A) (by omega),
      cfXp_ge2 (a := A) (n := 2) le_rfl, cfXp_ge2 (a := A) (n := p + 4) (by omega),
      cfXp_ge2 (a := A) (n := p + 3) (by omega),
      cfH_ge3 (a := A) (n := p + 4) (by omega), cfH_ge3 (a := A) (n := p + 4 + 1) (by omega), c1, c2, c2']
    set c : ℝ := (A.choose (p + 4) : ℝ) with hc
    set cm : ℝ := (A.choose (p + 3) : ℝ) with hcm
    set cp : ℝ := (A.choose (p + 4 + 1) : ℝ) with hcp
    set d : ℝ := ((A - 1).choose (p + 3) : ℝ) with hd
    set e : ℝ := ((A - 1).choose (p + 4) : ℝ) with he
    have h1 : cm * (K + 1) = c * (p + 4) := by
      have := choose_succ_real A (p + 3) (by omega)
      rw [show p + 3 + 1 = p + 4 by omega] at this
      have e' : ((A : ℕ) : ℝ) - ((p + 3 : ℕ) : ℝ) = (K : ℝ) + 1 := by rw [hAdef]; push_cast; ring
      rw [e'] at this; push_cast at this ⊢; linarith
    have h2 : cp * (p + 5) = c * K := by
      have := choose_succ_real A (p + 4) (by omega)
      have e' : ((A : ℕ) : ℝ) - ((p + 4 : ℕ) : ℝ) = (K : ℝ) := by rw [hAdef]; push_cast; ring
      rw [e'] at this; push_cast at this ⊢; linarith
    have h3 : d * (p + 4 + K) = c * (p + 4) := by
      have := choose_pred_real A (p + 3) (by omega)
      rw [show p + 3 + 1 = p + 4 by omega] at this
      rw [hAdef] at this; push_cast at this ⊢; linarith
    have h4' : e * (p + 4 + K) = c * K := by
      have hp := choose_pred_real A (p + 4) (by omega)
      have := choose_succ_real A (p + 4) (by omega)
      have e' : ((A : ℕ) : ℝ) - ((p + 4 : ℕ) : ℝ) = (K : ℝ) := by rw [hAdef]; push_cast; ring
      rw [e'] at this; rw [hAdef] at hp; push_cast at hp this ⊢; linarith
    have hc0 : 0 ≤ c := by positivity
    have key := eL1_arith (p : ℝ) (K : ℝ) c cm cp d e (by positivity) (by positivity) hc0 h1 h2 h3 h4'
    have eA : ((A : ℕ) : ℝ) = (p : ℝ) + 4 + K := by rw [hAdef]; push_cast; ring
    rw [eA]; push_cast at key ⊢
    linarith
  · unfold eL1
    rw [edgeCoef_ge4 _ _ (by omega), edgeCoef_ge4 _ _ (by omega)]
    simp only [Nat.add_sub_cancel]
    have hv := cf_vanish (a := a) (n := a + 1) ha le_rfl
    have hv2 := cf_vanish (a := a) (n := a + 1 + 1) ha (by omega)
    have hw := cfB_vanish (a := a) (n := a + 1) ha le_rfl
    rw [hv.1, hv.2.1, hv.2.2.2.2, hv2.2.2.2.2, hw.1, hw.2,
      cfX_pos (a := a) (n := 1) le_rfl, cfX_pos (a := a) (n := 2) (by norm_num), cfX_pos (a := a) (n := a) (by omega),
      cfBp1_ge3 (a := a) (n := a) ha, cfBp1_two, cfBp1_one, cfB1_one, cfB1_ge2 (a := a) (n := 2) le_rfl,
      cfB1_ge2 (a := a) (n := a) (by omega), cfXp_one (a := a) (by omega), cfXp_ge2 (a := a) (n := 2) le_rfl,
      cfXp_ge2 (a := a) (n := a) (by omega), Nat.choose_self, choose_small_zero (by omega : a - 1 < a), c1, c2, c2']
    push_cast
    nlinarith [mul_nonneg t t, mul_nonneg (mul_nonneg t t) t]
  · unfold eL1
    rw [edgeCoef_ge4 _ _ (by omega), edgeCoef_ge4 _ _ (by omega)]
    have hv := cf_vanish (a := a) (n := n) ha (by omega)
    have hv1 := cf_vanish (a := a) (n := n - 1) ha (by omega)
    have hv2 := cf_vanish (a := a) (n := n + 1) ha (by omega)
    have hw := cfB_vanish (a := a) (n := n) ha (by omega)
    have hw1 := cfB_vanish (a := a) (n := n - 1) ha (by omega)
    rw [hv.1, hv.2.1, hv.2.2.2.2, hv1.1, hv1.2.1, hv2.2.2.2.2, hw.1, hw.2, hw1.1, hw1.2]
    norm_num

/-- **`l₁ ≥ 0`** for `a ≥ 3`. -/
theorem linC_one_nonneg (f : ℕ → ℝ) (hf : LCNZ f) {a : ℕ} (ha : 3 ≤ a) : 0 ≤ linC f a 1 :=
  le_trans (mul_nonneg (hf.1 1) (lf_nonneg hf (fun n _ => eL1_nonneg ha n))) (linC_one_ge f hf ha)

/-- **All linear coefficients of the key are nonnegative** (paper (ii)): `LinCoefStmt` holds. -/
theorem linCoef_holds : LinCoefStmt := by
  intro f hf hf1 a ha k hk
  rcases (show k = 0 ∨ k = 1 ∨ 2 ≤ k by omega) with rfl | rfl | hk2
  · exact linC_zero_nonneg f hf ha
  · exact linC_one_nonneg f hf ha
  · exact linC_ge2 hf hf1 ha hk2 hk

end Szkraw
