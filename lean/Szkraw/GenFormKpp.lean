import Szkraw.GenRel

/-!
# The forms `K''` and `Q*` of the key of Theorem 8.16 (paper step (iv))

`K'' = Y'X'' + YX' - 4 D H_*` and `3Q* = 3(Y'X'' + YX') - 12 u₀ H_* - 4a u₁ H_* - (a-3) u₁ (Y + Y')`,
where `Q*` is the `s`-free lower bound of `Q_s / C(a-1,s-1)`. Both are `≥ u₁ Σ_n e_n u_n` with `e_n ≥ 0`.
-/

set_option linter.unusedSectionVars false

namespace Szkraw

open Finset

noncomputable def cfXpp (a n : ℕ) : ℝ := ((a - 1).choose n : ℝ) - ((0 : ℕ).choose n : ℝ)

section Values

variable {a : ℕ}

theorem cfXpp_zero : cfXpp a 0 = 0 := by simp [cfXpp]
theorem cfXpp_pos {n : ℕ} (hn : 1 ≤ n) : cfXpp a n = (a - 1).choose n := by
  unfold cfXpp; rw [choose_small_zero (by omega : 0 < n)]; ring
theorem cfXpp_one (ha : 1 ≤ a) : cfXpp a 1 = (a : ℝ) - 1 := by
  rw [cfXpp_pos le_rfl, Nat.choose_one_right, cast_pred ha]
theorem cfXpp_nonneg (n : ℕ) : 0 ≤ cfXpp a n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [cfXpp_zero]
  · rw [cfXpp_pos hn]; positivity
theorem cfXpp_vanish {n : ℕ} (hn : a ≤ n) (ha : 1 ≤ a) : cfXpp a n = 0 := by
  rw [cfXpp_pos (by omega), choose_small_zero (by omega)]

end Values

theorem Xpp_lf (f : ℕ → ℝ) {a : ℕ} (ha : 3 ≤ a) : dd f (a - 1) - dd f 0 = lf (a + 1) (cfXpp a) f := by
  rw [dd_lf f (m := a - 1) (R := a + 1) (by omega), dd_lf f (m := 0) (R := a + 1) (by omega)]
  unfold lf cfXpp; rw [← sum_sub_distrib]; exact sum_congr rfl fun n _ => by ring

/-- The common positive part `Y'X'' + YX'` and its edge coefficients. -/
noncomputable def ePos (a n : ℕ) : ℝ := edgeCoef (cfYp a) (cfXpp a) n + edgeCoef (cfY a) (cfXp a) n

noncomputable def eKpp (a n : ℕ) : ℝ := ePos a n - 4 * cfH a n - 4 * cfH a (n + 1)

noncomputable def eQs (a n : ℕ) : ℝ :=
  3 * ePos a n - 12 * cfH a (n + 1) - 4 * (a : ℝ) * cfH a n - ((a : ℝ) - 3) * (cfY a n + cfYp a n)

theorem pos_edge (f : ℕ → ℝ) (hf : LCNZ f) {a : ℕ} (ha : 3 ≤ a) :
    f 1 * lf (a + 2) (ePos a) f ≤
      lf (a + 1) (cfYp a) f * lf (a + 1) (cfXpp a) f + lf (a + 1) (cfY a) f * lf (a + 1) (cfXp a) f := by
  have hv := fun n (hn : a + 1 ≤ n) => cf_vanish (a := a) ha hn
  have E1 := hf.edge_prod (R := a + 1) (by omega) (x := cfYp a) (y := cfXpp a) (cfYp_nonneg (by omega))
    cfXpp_nonneg cfYp_zero cfXpp_zero (fun n hn => (hv n hn).2.2.2.1) (fun n hn => cfXpp_vanish (by omega) (by omega))
  have E2 := hf.edge_prod (R := a + 1) (by omega) (x := cfY a) (y := cfXp a) cfY_nonneg (cfXp_nonneg (by omega))
    cfY_zero cfXp_zero (fun n hn => (hv n hn).2.2.1) (fun n hn => (hv n hn).2.1)
  have hs : lf (a + 2) (ePos a) f = lf (a + 2) (edgeCoef (cfYp a) (cfXpp a)) f +
      lf (a + 2) (edgeCoef (cfY a) (cfXp a)) f := by
    unfold lf ePos; rw [← sum_add_distrib]; exact sum_congr rfl fun n _ => by ring
  rw [hs, mul_add]; linarith

/-- `K'' ≥ u₁ Σ e_n u_n`. -/
theorem Kpp_ge (f : ℕ → ℝ) (hf : LCNZ f) {a : ℕ} (ha : 3 ≤ a) :
    f 1 * lf (a + 2) (eKpp a) f ≤
      lf (a + 1) (cfYp a) f * lf (a + 1) (cfXpp a) f + lf (a + 1) (cfY a) f * lf (a + 1) (cfXp a) f -
        4 * (f 0 + f 1) * lf (a + 1) (cfH a) f := by
  have hv := fun n (hn : a + 1 ≤ n) => cf_vanish (a := a) ha hn
  have P := pos_edge f hf ha
  have N0 := hf.u0_lf a (cfH a) cfH_nonneg (cfH_le2 (by omega))
  have hH : lf (a + 1) (cfH a) f = lf (a + 2) (cfH a) f := lf_extend (by omega) (fun n hn => (hv n hn).2.2.2.2)
  have hH' : lf a (fun m => cfH a (m + 1)) f = lf (a + 2) (fun m => cfH a (m + 1)) f :=
    lf_extend (by omega) (fun n hn => (hv (n + 1) (by omega)).2.2.2.2)
  have hs : lf (a + 2) (eKpp a) f = lf (a + 2) (ePos a) f - 4 * lf (a + 2) (cfH a) f -
      4 * lf (a + 2) (fun m => cfH a (m + 1)) f := by
    unfold lf eKpp; simp only [mul_sum, ← sum_sub_distrib]; exact sum_congr rfl fun n _ => by ring
  rw [hs, ← hH, ← hH']
  have hf1 : 0 ≤ f 1 := hf.1 1
  have hHnn : 0 ≤ lf (a + 1) (cfH a) f := lf_nonneg hf (fun n _ => cfH_nonneg n)
  nlinarith [mul_nonneg hf1 hHnn]

/-- `3Q* ≥ u₁ Σ e_n u_n`. -/
theorem Qs_ge (f : ℕ → ℝ) (hf : LCNZ f) {a : ℕ} (ha : 3 ≤ a) :
    f 1 * lf (a + 2) (eQs a) f ≤
      3 * (lf (a + 1) (cfYp a) f * lf (a + 1) (cfXpp a) f + lf (a + 1) (cfY a) f * lf (a + 1) (cfXp a) f) -
        12 * f 0 * lf (a + 1) (cfH a) f - 4 * (a : ℝ) * f 1 * lf (a + 1) (cfH a) f -
        ((a : ℝ) - 3) * f 1 * (lf (a + 1) (cfY a) f + lf (a + 1) (cfYp a) f) := by
  have hv := fun n (hn : a + 1 ≤ n) => cf_vanish (a := a) ha hn
  have P := pos_edge f hf ha
  have N0 := hf.u0_lf a (cfH a) cfH_nonneg (cfH_le2 (by omega))
  have hH : lf (a + 1) (cfH a) f = lf (a + 2) (cfH a) f := lf_extend (by omega) (fun n hn => (hv n hn).2.2.2.2)
  have hH' : lf a (fun m => cfH a (m + 1)) f = lf (a + 2) (fun m => cfH a (m + 1)) f :=
    lf_extend (by omega) (fun n hn => (hv (n + 1) (by omega)).2.2.2.2)
  have hY : lf (a + 1) (cfY a) f = lf (a + 2) (cfY a) f := lf_extend (by omega) (fun n hn => (hv n hn).2.2.1)
  have hYp : lf (a + 1) (cfYp a) f = lf (a + 2) (cfYp a) f := lf_extend (by omega) (fun n hn => (hv n hn).2.2.2.1)
  have hs : lf (a + 2) (eQs a) f = 3 * lf (a + 2) (ePos a) f - 12 * lf (a + 2) (fun m => cfH a (m + 1)) f -
      4 * (a : ℝ) * lf (a + 2) (cfH a) f - ((a : ℝ) - 3) * (lf (a + 2) (cfY a) f + lf (a + 2) (cfYp a) f) := by
    unfold lf eQs; simp only [mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
    exact sum_congr rfl fun n _ => by ring
  rw [hs, ← hH, ← hH', ← hY, ← hYp]
  have hf0 : 0 ≤ f 0 := hf.1 0
  nlinarith [N0, P]

/-! ### `e_n ≥ 0` -/

theorem Kpp_arith (p K c cm cp d e : ℝ) (hp : 0 ≤ p) (hK : 0 ≤ K) (hc : 0 ≤ c)
    (h1 : cm * (K + 1) = c * (p + 4)) (h2 : cp * (p + 5) = c * K) (h3 : d * (p + 4 + K) = c * (p + 4))
    (h4 : e * (p + 4 + K) = c * K) :
    0 ≤ 0 * e + ((p + 4 + K) * (p + 4 + K - 1) / 2 - (p + 4 + K - 1)) * d + (p + 4 + K - 1) * c +
        (p + 4 + K - 1) * (p + 4 + K - 2) / 2 * cm +
      (0 * e + (p + 4 + K) * (p + 4 + K - 1) / 2 * d + (p + 4 + K - 2) * c + (p + 4 + K - 1) * (p + 4 + K - 2) / 2 * cm) -
      4 * ((p + 4 - 2) * c) - 4 * ((p + 4 + 1 - 2) * cp) := by
  have hK1 : 0 < K + 1 := by linarith
  have hp5 : 0 < p + 5 := by linarith
  have ha : 0 < p + 4 + K := by linarith
  have ecm : cm = c * (p + 4) / (K + 1) := by field_simp; linarith
  have ecp : cp = c * K / (p + 5) := by field_simp; linarith
  have ed : d = c * (p + 4) / (p + 4 + K) := by field_simp; linarith
  rw [ecm, ecp, ed]
  have key : 0 * e + ((p + 4 + K) * (p + 4 + K - 1) / 2 - (p + 4 + K - 1)) * (c * (p + 4) / (p + 4 + K)) +
        (p + 4 + K - 1) * c + (p + 4 + K - 1) * (p + 4 + K - 2) / 2 * (c * (p + 4) / (K + 1)) +
      (0 * e + (p + 4 + K) * (p + 4 + K - 1) / 2 * (c * (p + 4) / (p + 4 + K)) + (p + 4 + K - 2) * c +
        (p + 4 + K - 1) * (p + 4 + K - 2) / 2 * (c * (p + 4) / (K + 1))) -
      4 * ((p + 4 - 2) * c) - 4 * ((p + 4 + 1 - 2) * (c * K / (p + 5))) =
      c * (4 * K ^ 3 * p ^ 2 + 32 * K ^ 3 * p + 76 * K ^ 3 + 10 * K ^ 2 * p ^ 3 + 114 * K ^ 2 * p ^ 2 +
        438 * K ^ 2 * p + 590 * K ^ 2 + 8 * K * p ^ 4 + 120 * K * p ^ 3 + 660 * K * p ^ 2 + 1598 * K * p +
        1474 * K + 2 * p ^ 5 + 38 * p ^ 4 + 280 * p ^ 3 + 1000 * p ^ 2 + 1740 * p + 1200) /
        (2 * (K + 1) * (p + 4 + K) * (p + 5)) := by
    field_simp; ring
  rw [key]; positivity

theorem Qs_arith (p K c cm cp d e : ℝ) (hp : 0 ≤ p) (hK : 0 ≤ K) (hc : 0 ≤ c)
    (h1 : cm * (K + 1) = c * (p + 4)) (h2 : cp * (p + 5) = c * K) (h3 : d * (p + 4 + K) = c * (p + 4))
    (h4 : e * (p + 4 + K) = c * K) :
    0 ≤ 3 * (0 * e + ((p + 4 + K) * (p + 4 + K - 1) / 2 - (p + 4 + K - 1)) * d + (p + 4 + K - 1) * c +
        (p + 4 + K - 1) * (p + 4 + K - 2) / 2 * cm +
      (0 * e + (p + 4 + K) * (p + 4 + K - 1) / 2 * d + (p + 4 + K - 2) * c +
        (p + 4 + K - 1) * (p + 4 + K - 2) / 2 * cm)) -
      12 * ((p + 4 + 1 - 2) * cp) - 4 * (p + 4 + K) * ((p + 4 - 2) * c) - (p + 4 + K - 3) * (c + c) := by
  have hK1 : 0 < K + 1 := by linarith
  have hp5 : 0 < p + 5 := by linarith
  have ha : 0 < p + 4 + K := by linarith
  have ecm : cm = c * (p + 4) / (K + 1) := by field_simp; linarith
  have ecp : cp = c * K / (p + 5) := by field_simp; linarith
  have ed : d = c * (p + 4) / (p + 4 + K) := by field_simp; linarith
  rw [ecm, ecp, ed]
  have key : 3 * (0 * e + ((p + 4 + K) * (p + 4 + K - 1) / 2 - (p + 4 + K - 1)) * (c * (p + 4) / (p + 4 + K)) +
        (p + 4 + K - 1) * c + (p + 4 + K - 1) * (p + 4 + K - 2) / 2 * (c * (p + 4) / (K + 1)) +
      (0 * e + (p + 4 + K) * (p + 4 + K - 1) / 2 * (c * (p + 4) / (p + 4 + K)) + (p + 4 + K - 2) * c +
        (p + 4 + K - 1) * (p + 4 + K - 2) / 2 * (c * (p + 4) / (K + 1)))) -
      12 * ((p + 4 + 1 - 2) * (c * K / (p + 5))) - 4 * (p + 4 + K) * ((p + 4 - 2) * c) - (p + 4 + K - 3) * (c + c) =
      c * (4 * K ^ 3 * p ^ 2 + 36 * K ^ 3 * p + 128 * K ^ 3 + 14 * K ^ 2 * p ^ 3 + 174 * K ^ 2 * p ^ 2 +
        754 * K ^ 2 * p + 1170 * K ^ 2 + 16 * K * p ^ 4 + 244 * K * p ^ 3 + 1388 * K * p ^ 2 + 3554 * K * p +
        3522 * K + 6 * p ^ 5 + 106 * p ^ 4 + 740 * p ^ 3 + 2568 * p ^ 2 + 4480 * p + 3200) /
        (2 * (K + 1) * (p + 4 + K) * (p + 5)) := by
    field_simp; ring
  rw [key]; positivity

/-- Evaluation of `ePos` at the generic index. -/
theorem ePos_generic (p K : ℕ) :
    ePos (p + 4 + K) (p + 4) =
      0 * (((p + 4 + K - 1).choose (p + 4) : ℕ) : ℝ) +
        (((p : ℝ) + 4 + K) * ((p : ℝ) + 4 + K - 1) / 2 - ((p : ℝ) + 4 + K - 1)) *
          (((p + 4 + K - 1).choose (p + 3) : ℕ) : ℝ) + ((p : ℝ) + 4 + K - 1) * ((p + 4 + K).choose (p + 4) : ℝ) +
        ((p : ℝ) + 4 + K - 1) * ((p : ℝ) + 4 + K - 2) / 2 * ((p + 4 + K).choose (p + 3) : ℝ) +
      (0 * (((p + 4 + K - 1).choose (p + 4) : ℕ) : ℝ) +
        ((p : ℝ) + 4 + K) * ((p : ℝ) + 4 + K - 1) / 2 * (((p + 4 + K - 1).choose (p + 3) : ℕ) : ℝ) +
        ((p : ℝ) + 4 + K - 2) * ((p + 4 + K).choose (p + 4) : ℝ) +
        ((p : ℝ) + 4 + K - 1) * ((p : ℝ) + 4 + K - 2) / 2 * ((p + 4 + K).choose (p + 3) : ℝ)) := by
  set A := p + 4 + K with hAdef
  have hA : 3 ≤ A := by omega
  have eA : ((A : ℕ) : ℝ) = (p : ℝ) + 4 + K := by rw [hAdef]; push_cast; ring
  unfold ePos
  rw [edgeCoef_ge4 _ _ (by omega : 4 ≤ p + 4), edgeCoef_ge4 _ _ (by omega : 4 ≤ p + 4)]
  simp only [show p + 4 - 1 = p + 3 by omega]
  rw [cfYp_one, cfYp_two, cfYp_ge3 (a := A) (n := p + 4) (by omega), cfYp_ge3 (a := A) (n := p + 3) (by omega),
    cfXpp_pos (a := A) (n := p + 4) (by omega), cfXpp_pos (a := A) (n := p + 3) (by omega), cfXpp_one (by omega),
    cfXpp_pos (a := A) (n := 2) (by norm_num), cfY_one, cfY_ge2 (a := A) (n := 2) le_rfl,
    cfY_ge2 (a := A) (n := p + 4) (by omega), cfY_ge2 (a := A) (n := p + 3) (by omega), cfXp_one (a := A) (by omega),
    cfXp_ge2 (a := A) (n := 2) le_rfl, cfXp_ge2 (a := A) (n := p + 4) (by omega),
    cfXp_ge2 (a := A) (n := p + 3) (by omega), cast_choose_two, cast_choose_two (A - 1), cast_pred (by omega), eA]
  ring

theorem eKpp_nonneg {a : ℕ} (ha : 3 ≤ a) (n : ℕ) : 0 ≤ eKpp a n := by
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
    rfl | rfl | rfl | rfl | ⟨_h4, hna⟩ | rfl | hbig
  · unfold eKpp ePos; rw [edgeCoef_zero, edgeCoef_zero, cfXpp_zero, cfXp_zero, cfH_le2 (by norm_num),
      cfH_le2 (by norm_num)]; norm_num
  · unfold eKpp ePos
    rw [edgeCoef_one, edgeCoef_one, cfYp_one, cfXpp_zero, cfY_one, cfXp_zero, cfH_le2 (by norm_num),
      cfH_le2 (by norm_num)]; norm_num
  · unfold eKpp ePos
    rw [edgeCoef_two, edgeCoef_two, cfYp_one, cfYp_two, cfXpp_one (by omega), cfXpp_pos (a := a) (n := 2) (by norm_num),
      cfY_one, cfY_ge2 (a := a) (n := 2) le_rfl, cfXp_one (by omega), cfXp_ge2 (a := a) (n := 2) le_rfl,
      cfH_le2 (a := a) (n := 2) le_rfl, cfH_ge3 (a := a) (n := 2 + 1) (by norm_num), c2, c3, c2']
    push_cast
    nlinarith [mul_nonneg t t, mul_nonneg (mul_nonneg t t) t]
  · unfold eKpp ePos
    rw [edgeCoef_three, edgeCoef_three, cfYp_one, cfYp_two, cfYp_ge3 (a := a) (n := 3) le_rfl,
      cfXpp_one (by omega), cfXpp_pos (a := a) (n := 2) (by norm_num), cfXpp_pos (a := a) (n := 3) (by norm_num),
      cfY_one, cfY_ge2 (a := a) (n := 2) le_rfl, cfY_ge2 (a := a) (n := 3) (by norm_num), cfXp_one (by omega),
      cfXp_ge2 (a := a) (n := 2) le_rfl, cfXp_ge2 (a := a) (n := 3) (by norm_num),
      cfH_ge3 (a := a) (n := 3) le_rfl, cfH_ge3 (a := a) (n := 3 + 1) (by norm_num), c2, c3, c4, c2', c3']
    push_cast
    nlinarith [mul_nonneg t t, mul_nonneg (mul_nonneg t t) t, mul_nonneg (mul_nonneg (mul_nonneg t t) t) t]
  · obtain ⟨p, rfl⟩ : ∃ p, n = p + 4 := ⟨n - 4, by omega⟩
    obtain ⟨K, rfl⟩ : ∃ K, a = p + 4 + K := ⟨a - (p + 4), by omega⟩
    unfold eKpp
    rw [ePos_generic, cfH_ge3 (a := p + 4 + K) (n := p + 4) (by omega),
      cfH_ge3 (a := p + 4 + K) (n := p + 4 + 1) (by omega)]
    have := Kpp_arith (p : ℝ) (K : ℝ) _ _ _ _ _ (by positivity) (by positivity) (by positivity)
      (rel_cm p K) (rel_cp p K) (rel_d p K) (rel_e p K)
    push_cast at this ⊢; linarith
  · unfold eKpp ePos
    rw [edgeCoef_ge4 _ _ (by omega), edgeCoef_ge4 _ _ (by omega)]
    simp only [Nat.add_sub_cancel]
    have hv := cf_vanish (a := a) (n := a + 1) ha le_rfl
    have hv2 := cf_vanish (a := a) (n := a + 1 + 1) ha (by omega)
    rw [hv.2.1, hv.2.2.1, hv.2.2.2.1, hv.2.2.2.2, hv2.2.2.2.2, cfXpp_vanish (n := a + 1) (by omega) (by omega),
      cfXpp_vanish (n := a) le_rfl (by omega), cfYp_one, cfYp_two, cfYp_ge3 (a := a) (n := a) ha,
      cfXpp_one (by omega), cfXpp_pos (a := a) (n := 2) (by norm_num), cfY_one, cfY_ge2 (a := a) (n := 2) le_rfl,
      cfY_ge2 (a := a) (n := a) (by omega), cfXp_one (by omega), cfXp_ge2 (a := a) (n := 2) le_rfl,
      cfXp_ge2 (a := a) (n := a) (by omega), Nat.choose_self, choose_small_zero (by omega : a - 1 < a), c2, c2']
    push_cast
    nlinarith [mul_nonneg t t]
  · unfold eKpp ePos
    rw [edgeCoef_ge4 _ _ (by omega), edgeCoef_ge4 _ _ (by omega)]
    have hv := cf_vanish (a := a) (n := n) ha (by omega)
    have hv1 := cf_vanish (a := a) (n := n - 1) ha (by omega)
    have hv2 := cf_vanish (a := a) (n := n + 1) ha (by omega)
    rw [hv.2.1, hv.2.2.1, hv.2.2.2.1, hv.2.2.2.2, hv1.2.1, hv1.2.2.1, hv1.2.2.2.1, hv2.2.2.2.2,
      cfXpp_vanish (n := n) (by omega) (by omega), cfXpp_vanish (n := n - 1) (by omega) (by omega)]
    norm_num

theorem eQs_nonneg {a : ℕ} (ha : 3 ≤ a) (n : ℕ) : 0 ≤ eQs a n := by
  have hA3 : (3 : ℝ) ≤ a := by exact_mod_cast ha
  have t : (0:ℝ) ≤ a - 3 := by linarith
  have c2 := cast_choose_two a
  have c3 := cast_choose_three a (by omega)
  have c4 := cast_choose_four a ha
  have c2' : (((a - 1).choose 2 : ℕ) : ℝ) = ((a : ℝ) - 1) * ((a : ℝ) - 2) / 2 := by
    rw [cast_choose_two, cast_pred (by omega)]; ring
  have c3' : (((a - 1).choose 3 : ℕ) : ℝ) = ((a : ℝ) - 1) * ((a : ℝ) - 2) * ((a : ℝ) - 3) / 6 := by
    rw [cast_choose_three (a - 1) (by omega), cast_pred (by omega)]; ring
  rcases (show n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ (4 ≤ n ∧ n ≤ a) ∨ n = a + 1 ∨ a + 2 ≤ n by omega) with
    rfl | rfl | rfl | rfl | ⟨_h4, hna⟩ | rfl | hbig
  · unfold eQs ePos; rw [edgeCoef_zero, edgeCoef_zero, cfXpp_zero, cfXp_zero, cfH_le2 (by norm_num),
      cfH_le2 (by norm_num), cfY_zero, cfYp_zero]; norm_num
  · unfold eQs ePos
    rw [edgeCoef_one, edgeCoef_one, cfYp_one, cfXpp_zero, cfY_one, cfXp_zero, cfH_le2 (by norm_num),
      cfH_le2 (by norm_num)]; norm_num
  · unfold eQs ePos
    rw [edgeCoef_two, edgeCoef_two, cfYp_one, cfYp_two, cfXpp_one (by omega), cfXpp_pos (a := a) (n := 2) (by norm_num),
      cfY_one, cfY_ge2 (a := a) (n := 2) le_rfl, cfXp_one (by omega), cfXp_ge2 (a := a) (n := 2) le_rfl,
      cfH_le2 (a := a) (n := 2) le_rfl, cfH_ge3 (a := a) (n := 2 + 1) (by norm_num), c2, c3, c2']
    push_cast
    nlinarith [mul_nonneg t t, mul_nonneg (mul_nonneg t t) t]
  · unfold eQs ePos
    rw [edgeCoef_three, edgeCoef_three, cfYp_one, cfYp_two, cfYp_ge3 (a := a) (n := 3) le_rfl,
      cfXpp_one (by omega), cfXpp_pos (a := a) (n := 2) (by norm_num), cfXpp_pos (a := a) (n := 3) (by norm_num),
      cfY_one, cfY_ge2 (a := a) (n := 2) le_rfl, cfY_ge2 (a := a) (n := 3) (by norm_num), cfXp_one (by omega),
      cfXp_ge2 (a := a) (n := 2) le_rfl, cfXp_ge2 (a := a) (n := 3) (by norm_num),
      cfH_ge3 (a := a) (n := 3) le_rfl, cfH_ge3 (a := a) (n := 3 + 1) (by norm_num), c2, c3, c4, c2', c3']
    push_cast
    nlinarith [mul_nonneg t t, mul_nonneg (mul_nonneg t t) t, mul_nonneg (mul_nonneg (mul_nonneg t t) t) t]
  · obtain ⟨p, rfl⟩ : ∃ p, n = p + 4 := ⟨n - 4, by omega⟩
    obtain ⟨K, rfl⟩ : ∃ K, a = p + 4 + K := ⟨a - (p + 4), by omega⟩
    unfold eQs
    rw [ePos_generic, cfH_ge3 (a := p + 4 + K) (n := p + 4) (by omega),
      cfH_ge3 (a := p + 4 + K) (n := p + 4 + 1) (by omega), cfY_ge2 (a := p + 4 + K) (n := p + 4) (by omega),
      cfYp_ge3 (a := p + 4 + K) (n := p + 4) (by omega)]
    have := Qs_arith (p : ℝ) (K : ℝ) _ _ _ _ _ (by positivity) (by positivity) (by positivity)
      (rel_cm p K) (rel_cp p K) (rel_d p K) (rel_e p K)
    push_cast at this ⊢; linarith
  · unfold eQs ePos
    rw [edgeCoef_ge4 _ _ (by omega), edgeCoef_ge4 _ _ (by omega)]
    simp only [Nat.add_sub_cancel]
    have hv := cf_vanish (a := a) (n := a + 1) ha le_rfl
    have hv2 := cf_vanish (a := a) (n := a + 1 + 1) ha (by omega)
    rw [hv.2.1, hv.2.2.1, hv.2.2.2.1, hv.2.2.2.2, hv2.2.2.2.2, cfXpp_vanish (n := a + 1) (by omega) (by omega),
      cfXpp_vanish (n := a) le_rfl (by omega), cfYp_one, cfYp_two, cfYp_ge3 (a := a) (n := a) ha,
      cfXpp_one (by omega), cfXpp_pos (a := a) (n := 2) (by norm_num), cfY_one, cfY_ge2 (a := a) (n := 2) le_rfl,
      cfY_ge2 (a := a) (n := a) (by omega), cfXp_one (by omega), cfXp_ge2 (a := a) (n := 2) le_rfl,
      cfXp_ge2 (a := a) (n := a) (by omega), Nat.choose_self, choose_small_zero (by omega : a - 1 < a), c2, c2']
    push_cast
    nlinarith [mul_nonneg t t]
  · unfold eQs ePos
    rw [edgeCoef_ge4 _ _ (by omega), edgeCoef_ge4 _ _ (by omega)]
    have hv := cf_vanish (a := a) (n := n) ha (by omega)
    have hv1 := cf_vanish (a := a) (n := n - 1) ha (by omega)
    have hv2 := cf_vanish (a := a) (n := n + 1) ha (by omega)
    rw [hv.2.1, hv.2.2.1, hv.2.2.2.1, hv.2.2.2.2, hv1.2.1, hv1.2.2.1, hv1.2.2.2.1, hv2.2.2.2.2,
      cfXpp_vanish (n := n) (by omega) (by omega), cfXpp_vanish (n := n - 1) (by omega) (by omega)]
    norm_num

end Szkraw
