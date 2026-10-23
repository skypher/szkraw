import Szkraw.GenEdge
import Szkraw.GenPhaseA

/-!
# The coefficient `l₀ = K` of the key of Theorem 8.16

`linC f a 0 = X Y' + X' Y - 4 D H_*` (paper (ii), `l₀ = K`). With the edge linearization of `GenEdge`,
`K ≥ u₁ Σ_n e_n u_n` with explicit `e_n ≥ 0`.
-/

set_option linter.unusedSectionVars false

namespace Szkraw

open Finset

/-- `d_{ℓ+m}` as a linear form in `u = f`. -/
theorem dd_lf (f : ℕ → ℝ) {m R : ℕ} (hm : m < R) : dd f m = lf R (fun n => (m.choose n : ℝ)) f := by
  have h1 : dd f m = lf (m + 1) (fun n => (m.choose n : ℝ)) f := by
    show iterShift f m 0 = _
    rw [iterShift_eq]; unfold lf
    exact sum_congr rfl fun h _ => by rw [zero_add]
  rw [h1]
  exact lf_extend (by omega) (fun n hn => by rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero])

/-! ### Coefficient sequences -/

noncomputable def cfX (a n : ℕ) : ℝ := (a.choose n : ℝ) - ((0 : ℕ).choose n : ℝ)
noncomputable def cfXp (a n : ℕ) : ℝ := ((a - 1).choose n : ℝ) - ((1 : ℕ).choose n : ℝ)
noncomputable def cfY (a n : ℕ) : ℝ :=
  (a.choose n : ℝ) - ((0 : ℕ).choose n : ℝ) - (a : ℝ) * (((1 : ℕ).choose n : ℝ) - ((0 : ℕ).choose n : ℝ))
noncomputable def cfYp (a n : ℕ) : ℝ :=
  (a.choose n : ℝ) + ((a : ℝ) - 2) * ((1 : ℕ).choose n : ℝ) - ((a : ℝ) - 1) * ((2 : ℕ).choose n : ℝ)
noncomputable def cfH (a n : ℕ) : ℝ := wgtH n * (a.choose n : ℝ)

section Values

variable {a : ℕ}

theorem choose_small_zero {m n : ℕ} (h : m < n) : ((m.choose n : ℕ) : ℝ) = 0 := by
  rw [Nat.choose_eq_zero_of_lt h, Nat.cast_zero]

theorem cast_pred (ha : 1 ≤ a) : (((a - 1 : ℕ) : ℝ)) = (a : ℝ) - 1 := by
  rw [Nat.cast_sub ha, Nat.cast_one]

theorem cast_choose_two (n : ℕ) : ((n.choose 2 : ℕ) : ℝ) = (n : ℝ) * ((n : ℝ) - 1) / 2 :=
  Nat.cast_choose_two ℝ n

theorem cfX_zero : cfX a 0 = 0 := by simp [cfX]
theorem cfX_pos {n : ℕ} (hn : 1 ≤ n) : cfX a n = a.choose n := by
  unfold cfX; rw [choose_small_zero (by omega : 0 < n)]; ring
theorem cfXp_zero : cfXp a 0 = 0 := by simp [cfXp]
theorem cfXp_one (ha : 1 ≤ a) : cfXp a 1 = (a : ℝ) - 2 := by
  unfold cfXp; simp only [Nat.choose_one_right, Nat.cast_one]; rw [cast_pred ha]; ring
theorem cfXp_ge2 {n : ℕ} (hn : 2 ≤ n) : cfXp a n = (a - 1).choose n := by
  unfold cfXp; rw [choose_small_zero (by omega : 1 < n)]; ring
theorem cfY_zero : cfY a 0 = 0 := by simp [cfY]
theorem cfY_one : cfY a 1 = 0 := by simp [cfY]
theorem cfY_ge2 {n : ℕ} (hn : 2 ≤ n) : cfY a n = a.choose n := by
  unfold cfY; rw [choose_small_zero (by omega : 0 < n), choose_small_zero (by omega : 1 < n)]; ring
theorem cfYp_zero : cfYp a 0 = 0 := by simp [cfYp]; ring
theorem cfYp_one : cfYp a 1 = 0 := by simp [cfYp]; ring
theorem cfYp_two : cfYp a 2 = (a.choose 2 : ℝ) - ((a : ℝ) - 1) := by
  simp [cfYp]
theorem cfYp_ge3 {n : ℕ} (hn : 3 ≤ n) : cfYp a n = a.choose n := by
  unfold cfYp; rw [choose_small_zero (by omega : 1 < n), choose_small_zero (by omega : 2 < n)]; ring
theorem cfH_le2 {n : ℕ} (hn : n ≤ 2) : cfH a n = 0 := by
  unfold cfH wgtH; rw [if_neg (by omega), zero_mul]
theorem cfH_ge3 {n : ℕ} (hn : 3 ≤ n) : cfH a n = ((n : ℝ) - 2) * a.choose n := by
  unfold cfH wgtH; rw [if_pos hn, Nat.choose_one_right]
  have : ((n - 3 + 1 : ℕ) : ℝ) = (n : ℝ) - 2 := by rw [Nat.cast_add, Nat.cast_sub hn]; push_cast; ring
  rw [this]

theorem choose_two_ge (ha : 2 ≤ a) : (a : ℝ) - 1 ≤ (a.choose 2 : ℝ) := by
  rw [cast_choose_two]
  have : (2 : ℝ) ≤ a := by exact_mod_cast ha
  nlinarith

theorem cfX_nonneg (n : ℕ) : 0 ≤ cfX a n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [cfX_zero]
  · rw [cfX_pos hn]; positivity
theorem cfXp_nonneg (ha : 2 ≤ a) (n : ℕ) : 0 ≤ cfXp a n := by
  rcases (show n = 0 ∨ n = 1 ∨ 2 ≤ n by omega) with rfl | rfl | hn
  · rw [cfXp_zero]
  · rw [cfXp_one (by omega)]; have : (2 : ℝ) ≤ a := by exact_mod_cast ha
    linarith
  · rw [cfXp_ge2 hn]; positivity
theorem cfY_nonneg (n : ℕ) : 0 ≤ cfY a n := by
  rcases (show n = 0 ∨ n = 1 ∨ 2 ≤ n by omega) with rfl | rfl | hn
  · rw [cfY_zero]
  · rw [cfY_one]
  · rw [cfY_ge2 hn]; positivity
theorem cfYp_nonneg (ha : 2 ≤ a) (n : ℕ) : 0 ≤ cfYp a n := by
  rcases (show n = 0 ∨ n = 1 ∨ n = 2 ∨ 3 ≤ n by omega) with rfl | rfl | rfl | hn
  · rw [cfYp_zero]
  · rw [cfYp_one]
  · rw [cfYp_two]; linarith [choose_two_ge ha]
  · rw [cfYp_ge3 hn]; positivity
theorem cfH_nonneg (n : ℕ) : 0 ≤ cfH a n := by
  rcases Nat.lt_or_ge n 3 with h | h
  · rw [cfH_le2 (by omega)]
  · rw [cfH_ge3 h]; have : (3 : ℝ) ≤ n := by exact_mod_cast h
    have : (0 : ℝ) ≤ a.choose n := by positivity
    nlinarith

theorem cf_vanish {n : ℕ} (ha : 3 ≤ a) (hn : a + 1 ≤ n) :
    cfX a n = 0 ∧ cfXp a n = 0 ∧ cfY a n = 0 ∧ cfYp a n = 0 ∧ cfH a n = 0 := by
  have z : ((a.choose n : ℕ) : ℝ) = 0 := choose_small_zero (by omega)
  have z' : (((a - 1).choose n : ℕ) : ℝ) = 0 := choose_small_zero (by omega)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [cfX_pos (by omega), z]
  · rw [cfXp_ge2 (by omega), z']
  · rw [cfY_ge2 (by omega), z]
  · rw [cfYp_ge3 (by omega), z]
  · unfold cfH; rw [z, mul_zero]

end Values

/-! ### `K` as linear forms and its edge bound -/

theorem linC_zero_lf (f : ℕ → ℝ) {a : ℕ} (ha : 3 ≤ a) :
    linC f a 0 = lf (a + 1) (cfX a) f * lf (a + 1) (cfYp a) f + lf (a + 1) (cfXp a) f * lf (a + 1) (cfY a) f -
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
  have eY : betaC f a 0 = lf (a + 1) (cfY a) f := by
    unfold betaC; rw [hA, h0, h1]; unfold lf cfY
    simp only [Nat.choose_zero_right, Nat.cast_one, one_mul, mul_sum, ← sum_sub_distrib]
    exact sum_congr rfl fun n _ => by ring
  have eYp : beta'C f a 0 = lf (a + 1) (cfYp a) f := by
    unfold beta'C; rw [hA, h1, h2]; unfold lf cfYp
    simp only [Nat.choose_zero_right, Nat.cast_one, one_mul, mul_one, mul_sum, ← sum_sub_distrib,
      ← sum_add_distrib]
    exact sum_congr rfl fun n _ => by ring
  have eH : Hstar f a = lf (a + 1) (cfH a) f := by
    unfold Hstar lf cfH; exact sum_congr rfl fun n _ => by ring
  have eD : dd f 1 = f 0 + f 1 := dd_one_eq f
  unfold linC
  rw [eX, eXp, eY, eYp, eH, eD, if_pos (by omega)]
  ring

/-- The coefficients of the edge bound of `K`. -/
noncomputable def eK (a n : ℕ) : ℝ :=
  edgeCoef (cfX a) (cfYp a) n + edgeCoef (cfY a) (cfXp a) n - 4 * cfH a n - 4 * cfH a (n + 1)

theorem linC_zero_ge (f : ℕ → ℝ) (hf : LCNZ f) {a : ℕ} (ha : 3 ≤ a) :
    f 1 * lf (a + 2) (eK a) f ≤ linC f a 0 := by
  rw [linC_zero_lf f ha]
  have hv := fun n (hn : a + 1 ≤ n) => cf_vanish (a := a) ha hn
  have E1 := hf.edge_prod (R := a + 1) (by omega) (x := cfX a) (y := cfYp a) cfX_nonneg (cfYp_nonneg (by omega))
    cfX_zero cfYp_zero (fun n hn => (hv n hn).1) (fun n hn => (hv n hn).2.2.2.1)
  have E2 := hf.edge_prod (R := a + 1) (by omega) (x := cfY a) (y := cfXp a) cfY_nonneg (cfXp_nonneg (by omega))
    cfY_zero cfXp_zero (fun n hn => (hv n hn).2.2.1) (fun n hn => (hv n hn).2.1)
  have N0 := hf.u0_lf a (cfH a) cfH_nonneg (cfH_le2 (by omega))
  have hH : lf (a + 1) (cfH a) f = lf (a + 2) (cfH a) f :=
    lf_extend (by omega) (fun n hn => (hv n hn).2.2.2.2)
  have hH' : lf a (fun m => cfH a (m + 1)) f = lf (a + 2) (fun m => cfH a (m + 1)) f :=
    lf_extend (by omega) (fun n hn => (hv (n + 1) (by omega)).2.2.2.2)
  have hsplit : lf (a + 2) (eK a) f = lf (a + 2) (edgeCoef (cfX a) (cfYp a)) f +
      lf (a + 2) (edgeCoef (cfY a) (cfXp a)) f - 4 * lf (a + 2) (cfH a) f -
        4 * lf (a + 2) (fun m => cfH a (m + 1)) f := by
    unfold lf eK; simp only [mul_sum, ← sum_add_distrib, ← sum_sub_distrib]
    exact sum_congr rfl fun n _ => by ring
  have hprodcomm : lf (a + 1) (cfXp a) f * lf (a + 1) (cfY a) f = lf (a + 1) (cfY a) f * lf (a + 1) (cfXp a) f :=
    mul_comm _ _
  rw [hsplit, hprodcomm]
  rw [← hH, ← hH'] at *
  have hf1 : 0 ≤ f 1 := hf.1 1
  have hHnn : 0 ≤ lf (a + 1) (cfH a) f := lf_nonneg hf (fun n _ => cfH_nonneg n)
  nlinarith [E1, E2, N0, mul_nonneg hf1 hHnn]

/-! ### `e_n ≥ 0` -/

/-- The generic case `4 ≤ n ≤ a`, with `n = p + 4`, `a = n + K`. -/
theorem eK_arith (p K c cm cp d : ℝ) (hp : 0 ≤ p) (hK : 0 ≤ K) (hc : 0 ≤ c)
    (h1 : cm * (K + 1) = c * (p + 4)) (h2 : cp * (p + 5) = c * K) (h3 : d * (p + 4 + K) = c * (p + 4)) :
    0 ≤ (p + 4 + K) * c + (p + 4 + K) * (p + 4 + K - 1) / 2 * cm +
      ((p + 4 + K) * (p + 4 + K - 1) / 2 - (p + 4 + K - 1)) * cm +
      ((p + 4 + K) * (p + 4 + K - 1) / 2 * d + (p + 4 + K - 2) * c + (p + 4 + K - 1) * (p + 4 + K - 2) / 2 * cm) -
      4 * ((p + 4) - 2) * c - 4 * ((p + 4) - 1) * cp := by
  have hK1 : 0 < K + 1 := by linarith
  have hp5 : 0 < p + 5 := by linarith
  have ha : 0 < p + 4 + K := by linarith
  have ecm : cm = c * (p + 4) / (K + 1) := by field_simp; linarith
  have ecp : cp = c * K / (p + 5) := by field_simp; linarith
  have ed : d = c * (p + 4) / (p + 4 + K) := by field_simp; linarith
  rw [ecm, ecp, ed]
  have key : (p + 4 + K) * c + (p + 4 + K) * (p + 4 + K - 1) / 2 * (c * (p + 4) / (K + 1)) +
      ((p + 4 + K) * (p + 4 + K - 1) / 2 - (p + 4 + K - 1)) * (c * (p + 4) / (K + 1)) +
      ((p + 4 + K) * (p + 4 + K - 1) / 2 * (c * (p + 4) / (p + 4 + K)) + (p + 4 + K - 2) * c +
        (p + 4 + K - 1) * (p + 4 + K - 2) / 2 * (c * (p + 4) / (K + 1))) -
      4 * ((p + 4) - 2) * c - 4 * ((p + 4) - 1) * (c * K / (p + 5)) =
      c * (4 * K ^ 2 * p ^ 2 + 32 * K ^ 2 * p + 76 * K ^ 2 + 7 * K * p ^ 3 + 80 * K * p ^ 2 + 301 * K * p +
        396 * K + 3 * p ^ 4 + 45 * p ^ 3 + 245 * p ^ 2 + 579 * p + 520) / (2 * (K + 1) * (p + 5)) := by
    field_simp; ring
  rw [key]; positivity

/-- Closed forms of `C(a,3)` and `C(a,4)`. -/
theorem cast_choose_three (a : ℕ) (ha : 2 ≤ a) :
    ((a.choose 3 : ℕ) : ℝ) = (a : ℝ) * ((a : ℝ) - 1) * ((a : ℝ) - 2) / 6 := by
  have h := choose_succ_real a 2 ha
  rw [cast_choose_two] at h; push_cast at h; linarith

theorem cast_choose_four (a : ℕ) (ha : 3 ≤ a) :
    ((a.choose 4 : ℕ) : ℝ) = (a : ℝ) * ((a : ℝ) - 1) * ((a : ℝ) - 2) * ((a : ℝ) - 3) / 24 := by
  have h := choose_succ_real a 3 ha
  rw [cast_choose_three a (by omega)] at h; push_cast at h; linarith

theorem eK_nonneg {a : ℕ} (ha : 3 ≤ a) (n : ℕ) : 0 ≤ eK a n := by
  have hA3 : (3 : ℝ) ≤ a := by exact_mod_cast ha
  have c1 : ((a.choose 1 : ℕ) : ℝ) = a := by rw [Nat.choose_one_right]
  have c2 := cast_choose_two a
  have c3 := cast_choose_three a (by omega)
  have c4 := cast_choose_four a ha
  have c2' : (((a - 1).choose 2 : ℕ) : ℝ) = ((a : ℝ) - 1) * ((a : ℝ) - 2) / 2 := by
    rw [cast_choose_two, cast_pred (by omega)]; ring
  rcases (show n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ (4 ≤ n ∧ n ≤ a) ∨ n = a + 1 ∨ a + 2 ≤ n by omega) with
    rfl | rfl | rfl | rfl | ⟨h4, hna⟩ | rfl | hbig
  · unfold eK; rw [edgeCoef_zero, edgeCoef_zero, cfYp_zero, cfXp_zero, cfH_le2 (by norm_num),
      cfH_le2 (by norm_num)]; norm_num
  · unfold eK; rw [edgeCoef_one, edgeCoef_one, cfYp_one, cfYp_zero, cfY_one, cfXp_zero,
      cfH_le2 (by norm_num), cfH_le2 (by norm_num)]; norm_num
  · unfold eK
    rw [edgeCoef_two, edgeCoef_two, cfX_pos (by norm_num), cfYp_two, cfYp_one, cfY_one, cfY_ge2 le_rfl,
      cfXp_one (by omega), cfH_le2 le_rfl, cfH_ge3 (by norm_num), c1, c2, c3]
    nlinarith [mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ a - 3) (by linarith : (0:ℝ) ≤ a - 3))
      (by linarith : (0:ℝ) ≤ a - 3), mul_nonneg (by linarith : (0:ℝ) ≤ a - 3) (by linarith : (0:ℝ) ≤ a - 3)]
  · unfold eK
    rw [edgeCoef_three, edgeCoef_three, cfX_pos (by norm_num), cfX_pos (by norm_num), cfYp_ge3 le_rfl,
      cfYp_two, cfYp_one, cfY_one, cfY_ge2 (by norm_num), cfY_ge2 (by norm_num), cfXp_one (by omega),
      cfXp_ge2 le_rfl, cfXp_ge2 (by norm_num), cfH_ge3 le_rfl, cfH_ge3 (by norm_num), c1, c2, c3, c4, c2']
    have t : (0:ℝ) ≤ a - 3 := by linarith
    nlinarith [mul_nonneg t t, mul_nonneg (mul_nonneg t t) t, mul_nonneg (mul_nonneg (mul_nonneg t t) t) t]
  · -- generic case
    obtain ⟨p, rfl⟩ : ∃ p, n = p + 4 := ⟨n - 4, by omega⟩
    obtain ⟨K, rfl⟩ : ∃ K, a = p + 4 + K := ⟨a - (p + 4), by omega⟩
    set A := p + 4 + K with hAdef
    unfold eK
    rw [edgeCoef_ge4 _ _ h4, edgeCoef_ge4 _ _ h4]
    simp only [show p + 4 - 1 = p + 3 by omega]
    rw [cfX_pos (a := A) (n := 1) le_rfl, cfX_pos (a := A) (n := 2) (by norm_num),
      cfX_pos (a := A) (n := p + 4) (by omega), cfX_pos (a := A) (n := p + 3) (by omega),
      cfYp_ge3 (a := A) (n := p + 4) (by omega), cfYp_ge3 (a := A) (n := p + 3) (by omega), cfYp_two, cfYp_one,
      cfY_one, cfY_ge2 (a := A) (n := 2) le_rfl, cfY_ge2 (a := A) (n := p + 4) (by omega),
      cfY_ge2 (a := A) (n := p + 3) (by omega), cfXp_one (a := A) (by omega),
      cfXp_ge2 (a := A) (n := 2) le_rfl, cfXp_ge2 (a := A) (n := p + 3) (by omega),
      cfH_ge3 (a := A) (n := p + 4) (by omega), cfH_ge3 (a := A) (n := p + 4 + 1) (by omega), c1, c2, c2']
    set c : ℝ := (A.choose (p + 4) : ℝ) with hc
    set cm : ℝ := (A.choose (p + 3) : ℝ) with hcm
    set cp : ℝ := (A.choose (p + 4 + 1) : ℝ) with hcp
    set d : ℝ := ((A - 1).choose (p + 3) : ℝ) with hd
    have h1 : cm * (K + 1) = c * (p + 4) := by
      have := choose_succ_real A (p + 3) (by omega)
      rw [show p + 3 + 1 = p + 4 by omega] at this
      have e : ((A : ℕ) : ℝ) - ((p + 3 : ℕ) : ℝ) = (K : ℝ) + 1 := by rw [hAdef]; push_cast; ring
      rw [e] at this; push_cast at this ⊢; linarith
    have h2 : cp * (p + 5) = c * K := by
      have := choose_succ_real A (p + 4) (by omega)
      have e : ((A : ℕ) : ℝ) - ((p + 4 : ℕ) : ℝ) = (K : ℝ) := by rw [hAdef]; push_cast; ring
      rw [e] at this; push_cast at this ⊢; linarith
    have h3 : d * (p + 4 + K) = c * (p + 4) := by
      have := choose_pred_real A (p + 3) (by omega)
      rw [show p + 3 + 1 = p + 4 by omega] at this
      rw [hAdef] at this; push_cast at this ⊢; linarith
    have hc0 : 0 ≤ c := by positivity
    have key := eK_arith (p : ℝ) (K : ℝ) c cm cp d (by positivity) (by positivity) hc0 h1 h2 h3
    have eA : ((A : ℕ) : ℝ) = (p : ℝ) + 4 + K := by rw [hAdef]; push_cast; ring
    rw [eA]; push_cast at key ⊢
    linarith
  · unfold eK
    rw [edgeCoef_ge4 _ _ (by omega), edgeCoef_ge4 _ _ (by omega)]
    simp only [Nat.add_sub_cancel]
    have hv := cf_vanish (a := a) (n := a + 1) ha le_rfl
    have hv2 := cf_vanish (a := a) (n := a + 1 + 1) ha (by omega)
    rw [hv.1, hv.2.1, hv.2.2.1, hv.2.2.2.1, hv.2.2.2.2, hv2.2.2.2.2,
      cfX_pos (a := a) (n := 1) le_rfl, cfX_pos (a := a) (n := 2) (by norm_num), cfX_pos (a := a) (n := a) (by omega),
      cfYp_ge3 (a := a) (n := a) ha, cfYp_two, cfYp_one, cfY_one, cfY_ge2 (a := a) (n := 2) le_rfl,
      cfY_ge2 (a := a) (n := a) (by omega), cfXp_one (a := a) (by omega), cfXp_ge2 (a := a) (n := 2) le_rfl,
      cfXp_ge2 (a := a) (n := a) (by omega), Nat.choose_self, choose_small_zero (by omega : a - 1 < a), c1, c2, c2']
    have t : (0:ℝ) ≤ a - 3 := by linarith
    push_cast
    nlinarith [mul_nonneg t t]
  · unfold eK
    rw [edgeCoef_ge4 _ _ (by omega), edgeCoef_ge4 _ _ (by omega)]
    have hv := cf_vanish (a := a) (n := n) ha (by omega)
    have hv1 := cf_vanish (a := a) (n := n - 1) ha (by omega)
    have hv2 := cf_vanish (a := a) (n := n + 1) ha (by omega)
    rw [hv.1, hv.2.1, hv.2.2.1, hv.2.2.2.1, hv.2.2.2.2, hv1.1, hv1.2.1, hv1.2.2.1, hv1.2.2.2.1, hv2.2.2.2.2]
    norm_num

/-- **`l₀ = K ≥ 0`** for `a ≥ 3`. -/
theorem linC_zero_nonneg (f : ℕ → ℝ) (hf : LCNZ f) {a : ℕ} (ha : 3 ≤ a) : 0 ≤ linC f a 0 :=
  le_trans (mul_nonneg (hf.1 1) (lf_nonneg hf (fun n _ => eK_nonneg ha n))) (linC_zero_ge f hf ha)

end Szkraw
