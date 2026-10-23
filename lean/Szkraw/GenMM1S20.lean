import Szkraw.GenFormR
import Szkraw.GenWindows

/-!
# `M_{1,m} + M_{m,1} ≥ 0` (paper step (iii′)) and `S_{2,0} ≥ 0` (paper step (v)); Theorem 8.16 unconditional

For `a ≥ 6`, `M_{1,m} + M_{m,1} ≥ ½ c' B R + ½ c' A R₂ + β'_m E¹₁ + β_m E²₁`; for `a ≥ 5`,
`u₁ S_{2,0} ≥ u₁ β'₁ E¹₁ + u₁ A Ψ + F D Q̂`. The windows `3 ≤ a ≤ 5` are in `GenWindows`.
-/

set_option linter.unusedSectionVars false

namespace Szkraw

open Finset

/-- The scalar core of step (iii′). -/
theorem mm1_scalar (A B f0 f1 H cs c1 c2 z v bp1 bm bpm a m : ℝ) (hf0 : 0 ≤ f0) (hf1 : 0 ≤ f1)
    (hB0 : 0 ≤ B) (hAB : B ≤ A) (hX' : f0 + f1 ≤ B) (hH : 0 ≤ H) (hz : 0 ≤ z) (hv : 0 ≤ v)
    (hc1 : 0 ≤ c1) (hc2 : 0 ≤ c2) (hpas : cs = c1 + c2) (he1 : c1 * a = cs * m) (he2 : c2 * m = c1 * (a - m))
    (hm : 2 ≤ m) (ha : 3 ≤ a)
    (hE1 : (a - 1) * f0 * (A - B) ≤ A * (B - f0)) (hE2 : (a - 2) * (f0 + f1) * (A - B) ≤ A * (B - (f0 + f1)))
    (hbp1 : (a - 2) * (A - (f0 + f1)) ≤ bp1) (hbm : 0 ≤ bm) (hbpm : 0 ≤ bpm)
    (hR : 0 ≤ a * ((A - (f0 + f1)) * (B - (f0 + f1))) - 8 * ((f0 + f1) * H))
    (hR2 : 0 ≤ (a - 2) * ((A - (f0 + f1)) * (B - f0)) - 4 * a * ((f0 + f1) * H)) :
    0 ≤ bp1 * ((A - f0) * (cs * A - c2 * B) - (A - B) * (cs * A)) +
        a * (A - (f0 + f1)) * ((B - (f0 + f1)) * (cs * A - c2 * B) - (A - B) * (c2 * B)) +
        (f0 + f1) * (2 * (A - B) * v - 4 * (H * (cs * A - c2 * B) - (A - B) * z)) +
      (bpm * ((A - f0) * (a * A - (a - 1) * B) - (A - B) * (a * A)) +
        bm * ((B - (f0 + f1)) * (a * A - (a - 1) * B) - (A - B) * ((a - 1) * B - (f0 + f1)))) := by
  subst hpas
  set D := f0 + f1 with hD
  set F := A - B with hF
  have hD0 : 0 ≤ D := by linarith
  have hF0 : 0 ≤ F := by linarith
  have hA0 : 0 ≤ A := by linarith
  have hX'0 : 0 ≤ B - D := by linarith
  have hX''0 : 0 ≤ B - f0 := by linarith
  have hAD : 0 ≤ A - D := by linarith
  have hm0 : 0 ≤ m := by linarith
  set E1m := c1 * A * (B - f0) - c2 * f0 * F with hE1m
  set E2m := c1 * A * (B - D) - c2 * D * F with hE2m
  -- `2 E²_m ≥ c' A X'` and `2 E¹_m ≥ c' A X''`
  have k2 : c1 * A * (B - D) ≤ 2 * E2m := by
    have k1 : 2 * m * c2 * ((a - 2) * D * F) ≤ 2 * m * c2 * (A * (B - D)) :=
      mul_le_mul_of_nonneg_left hE2 (mul_nonneg (mul_nonneg (by norm_num) hm0) hc2)
    have k3 : 0 ≤ c1 * (A * (B - D)) * (a * (m - 2)) :=
      mul_nonneg (mul_nonneg hc1 (mul_nonneg hA0 hX'0)) (mul_nonneg (by linarith) (by linarith))
    have he2' : c2 * m * (A * (B - D)) = c1 * (a - m) * (A * (B - D)) := by rw [he2]
    have k4 : 0 ≤ (a - 2) * m * (2 * E2m - c1 * A * (B - D)) := by
      simp only [hE2m]; linarith [k1, k3, he2']
    exact sub_nonneg.1 ((mul_nonneg_iff_of_pos_left (mul_pos (by linarith) (by linarith))).1 k4)
  have k5 : c1 * A * (B - f0) ≤ 2 * E1m := by
    have k1 : 2 * m * c2 * ((a - 1) * f0 * F) ≤ 2 * m * c2 * (A * (B - f0)) :=
      mul_le_mul_of_nonneg_left hE1 (mul_nonneg (mul_nonneg (by norm_num) hm0) hc2)
    have k3 : 0 ≤ c1 * (A * (B - f0)) * ((a + 1) * m - 2 * a) :=
      mul_nonneg (mul_nonneg hc1 (mul_nonneg hA0 hX''0))
        (by nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ a + 1) (sub_nonneg.2 hm)])
    have he2' : c2 * m * (A * (B - f0)) = c1 * (a - m) * (A * (B - f0)) := by rw [he2]
    have k4 : 0 ≤ (a - 1) * m * (2 * E1m - c1 * A * (B - f0)) := by
      simp only [hE1m]; linarith [k1, k3, he2']
    exact sub_nonneg.1 ((mul_nonneg_iff_of_pos_left (mul_pos (by linarith) (by linarith))).1 k4)
  have hcs : 2 * (c1 + c2) ≤ a * c1 := by linarith [mul_nonneg (add_nonneg hc1 hc2) (sub_nonneg.2 hm)]
  have hE1m0 : 0 ≤ E1m := by linarith [mul_nonneg hc1 (mul_nonneg hA0 hX''0)]
  have hb1 : 0 ≤ a * (A - D) := mul_nonneg (by linarith) hAD
  -- first bracket `≥ ½ c' B R`
  have t1 : 0 ≤ a * (A - D) * E2m - 4 * c1 * D * B * H := by
    have t1a := mul_le_mul_of_nonneg_left k2 hb1
    have t1b : a * (A - D) * c1 * (B - D) * B ≤ a * (A - D) * c1 * (B - D) * A :=
      mul_le_mul_of_nonneg_left hAB (mul_nonneg (mul_nonneg hb1 hc1) hX'0)
    have t1c : 0 ≤ c1 * B * (a * ((A - D) * (B - D)) - 8 * (D * H)) := mul_nonneg (mul_nonneg hc1 hB0) hR
    linarith [t1a, t1b, t1c]
  -- second bracket `≥ ½ c' A R₂`
  have t2 : 0 ≤ bp1 * E1m - D * F * (4 * ((c1 + c2) * H - z) - 2 * v) := by
    have u1 := mul_le_mul_of_nonneg_right hbp1 hE1m0
    have u2 := mul_le_mul_of_nonneg_left k5 (mul_nonneg (by linarith : (0 : ℝ) ≤ a - 2) hAD)
    have u3 := mul_nonneg (mul_nonneg hD0 hF0) hz
    have u4 := mul_nonneg (mul_nonneg hD0 hF0) hv
    have u5 : D * F * ((c1 + c2) * H) ≤ D * A * ((c1 + c2) * H) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith) hD0)
        (mul_nonneg (add_nonneg hc1 hc2) hH)
    have u6 := mul_le_mul_of_nonneg_left hcs (mul_nonneg (mul_nonneg hD0 hA0) hH)
    have u7 : 0 ≤ c1 * A * ((a - 2) * ((A - D) * (B - f0)) - 4 * a * (D * H)) := mul_nonneg (mul_nonneg hc1 hA0) hR2
    linarith [u1, u2, u3, u4, u5, u6, u7]
  have t3 : 0 ≤ bpm * (A * (B - f0) - (a - 1) * f0 * F) := mul_nonneg hbpm (by linarith)
  have t4 : 0 ≤ bm * (A * (B - D) - (a - 2) * D * F) := mul_nonneg hbm (by linarith)
  have hid : bp1 * ((A - f0) * ((c1 + c2) * A - c2 * B) - F * ((c1 + c2) * A)) +
        a * (A - D) * ((B - D) * ((c1 + c2) * A - c2 * B) - F * (c2 * B)) +
        D * (2 * F * v - 4 * (H * ((c1 + c2) * A - c2 * B) - F * z)) +
      (bpm * ((A - f0) * (a * A - (a - 1) * B) - F * (a * A)) +
        bm * ((B - D) * (a * A - (a - 1) * B) - F * ((a - 1) * B - D))) =
      (a * (A - D) * E2m - 4 * c1 * D * B * H) + (bp1 * E1m - D * F * (4 * ((c1 + c2) * H - z) - 2 * v)) +
        bpm * (A * (B - f0) - (a - 1) * f0 * F) + bm * (A * (B - D) - (a - 2) * D * F) := by
    simp only [hE1m, hE2m, hF, hD]; ring
  linarith [hid, t1, t2, t3, t4]

/-- The scalar core of step (v). -/
theorem s20_scalar (A B f0 f1 H z1 z2 v1 v2 Y Y' bp1 a : ℝ) (hf0 : 0 ≤ f0) (hf1 : 0 < f1)
    (hAB : B ≤ A) (hX' : f0 + f1 ≤ B) (hY : 0 ≤ Y) (hY' : 0 ≤ Y') (ha : 3 ≤ a)
    (hE1 : (a - 1) * f0 * (A - B) ≤ A * (B - f0)) (hbp1 : 0 ≤ bp1) (huB : f0 * (A - B) ≤ f1 * B)
    (hKa : 0 ≤ (a - 1) * (Y' * (B - f0) + Y * (B - (f0 + f1))) - 4 * a * ((f0 + f1) * H))
    (hPsi : 0 ≤ a * ((A - (f0 + f1)) * (B - (f0 + f1) - (a - 2) * f1)) -
      (a - 1) * (a - 2) / 2 * (f1 * (Y + Y')))
    (hQ : 0 ≤ (a - 1) * (Y' * (B - f0) + Y * (B - (f0 + f1))) - 4 * a * (f0 * H) +
      f1 * (2 * v1 + 2 * v2 - 4 * (a * H - z1) - 4 * (a * (a - 1) / 2 * H - z2))) :
    0 ≤ Y' * ((A - f0) * (a * (a - 1) / 2 * A - (a - 1) * (a - 2) / 2 * B) - (A - B) * (a * (a - 1) / 2 * A)) +
        Y * ((B - (f0 + f1)) * (a * (a - 1) / 2 * A - (a - 1) * (a - 2) / 2 * B) -
          (A - B) * ((a - 1) * (a - 2) / 2 * B)) +
        (f0 + f1) * (2 * (A - B) * v2 - 4 * (H * (a * (a - 1) / 2 * A - (a - 1) * (a - 2) / 2 * B) - (A - B) * z2)) +
      (bp1 * ((A - f0) * (a * A - (a - 1) * B) - (A - B) * (a * A)) +
        a * (A - (f0 + f1)) * ((B - (f0 + f1)) * (a * A - (a - 1) * B) - (A - B) * ((a - 1) * B - (f0 + f1))) +
        (f0 + f1) * (2 * (A - B) * v1 - 4 * (H * (a * A - (a - 1) * B) - (A - B) * z1))) := by
  set D := f0 + f1 with hD
  set F := A - B with hF
  set c2 := (a - 1) * (a - 2) / 2 with hc2
  have hc20 : 0 ≤ c2 := by rw [hc2]; nlinarith
  have hD0 : 0 ≤ D := by linarith
  have hF0 : 0 ≤ F := by linarith
  have hA0 : 0 ≤ A := by linarith
  have hAD : 0 ≤ A - D := by linarith
  have hb1' : 0 ≤ a * (A - D) := mul_nonneg (by linarith) hAD
  set Ka := (a - 1) * (Y' * (B - f0) + Y * (B - D)) - 4 * a * (D * H) with hKadef
  set W := (a - 1) * (Y' * (B - f0) + Y * (B - D)) +
    D * (2 * v1 + 2 * v2 - 4 * (a * H - z1) - 4 * (a * (a - 1) / 2 * H - z2)) with hW
  set E11 := A * (B - f0) - (a - 1) * f0 * F with hE11
  set E21 := A * (B - D) - (a - 2) * D * F with hE21
  have hid : Y' * ((A - f0) * (a * (a - 1) / 2 * A - c2 * B) - F * (a * (a - 1) / 2 * A)) +
        Y * ((B - D) * (a * (a - 1) / 2 * A - c2 * B) - F * (c2 * B)) +
        D * (2 * F * v2 - 4 * (H * (a * (a - 1) / 2 * A - c2 * B) - F * z2)) +
      (bp1 * ((A - f0) * (a * A - (a - 1) * B) - F * (a * A)) +
        a * (A - D) * ((B - D) * (a * A - (a - 1) * B) - F * ((a - 1) * B - D)) +
        D * (2 * F * v1 - 4 * (H * (a * A - (a - 1) * B) - F * z1))) =
      bp1 * E11 + (a * (A - D) * E21 - c2 * F * (f0 * Y' + D * Y)) + B * Ka + F * W := by
    simp only [hD, hF, hc2, hKadef, hW, hE11, hE21]; ring
  have hDF : D * F ≤ f1 * A := by
    have e1 : f1 * A = f1 * B + f1 * F := by rw [hF]; ring
    have e2 : D * F = f0 * F + f1 * F := by rw [hD]; ring
    linarith
  -- the bracket is at least `A Ψ`
  have hbr : A * (a * ((A - D) * (B - D - (a - 2) * f1)) - c2 * (f1 * (Y + Y'))) ≤
      a * (A - D) * E21 - c2 * F * (f0 * Y' + D * Y) := by
    have k1 := mul_le_mul_of_nonneg_left hDF (mul_nonneg hb1' (by linarith : (0 : ℝ) ≤ a - 2))
    have k2 : c2 * F * Y' * f0 ≤ c2 * F * Y' * D :=
      mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg (mul_nonneg hc20 hF0) hY')
    have k3 := mul_le_mul_of_nonneg_left hDF (mul_nonneg hc20 (add_nonneg hY hY'))
    simp only [hE21]; linarith [k1, k2, k3]
  -- `u₁ (B K_a + F W) ≥ F (u₀ K_a + u₁ W) = F D Q̂`
  have hK3 : F * (f0 * Ka + f1 * W) ≤ f1 * (B * Ka + F * W) := by
    have := mul_le_mul_of_nonneg_right huB hKa
    linarith [this]
  have hQid : f0 * Ka + f1 * W = D * ((a - 1) * (Y' * (B - f0) + Y * (B - D)) - 4 * a * (f0 * H) +
      f1 * (2 * v1 + 2 * v2 - 4 * (a * H - z1) - 4 * (a * (a - 1) / 2 * H - z2))) := by
    simp only [hKadef, hW, hD]; ring
  have hE110 : 0 ≤ E11 := by simp only [hE11]; linarith
  have h1 : 0 ≤ f1 * (bp1 * E11) := mul_nonneg hf1.le (mul_nonneg hbp1 hE110)
  have h2 : 0 ≤ f1 * (A * (a * ((A - D) * (B - D - (a - 2) * f1)) - c2 * (f1 * (Y + Y')))) :=
    mul_nonneg hf1.le (mul_nonneg hA0 hPsi)
  have h3 : 0 ≤ F * (f0 * Ka + f1 * W) := by rw [hQid]; exact mul_nonneg hF0 (mul_nonneg hD0 hQ)
  have h4 : 0 ≤ f1 * (bp1 * E11 + (a * (A - D) * E21 - c2 * F * (f0 * Y' + D * Y)) + B * Ka + F * W) := by
    linarith [mul_le_mul_of_nonneg_left hbr hf1.le, hK3]
  linarith [hid, (mul_nonneg_iff_of_pos_left hf1).1 h4]

/-! ### Glue: the Lean coefficients, the windows, and the assembly -/

section Glue

variable {f : ℕ → ℝ}

theorem basic_E1 (hf : LCNZ f) (hf1 : 0 < f 1) {a : ℕ} (ha : 3 ≤ a) :
    ((a : ℝ) - 1) * f 0 * (dd f a - dd f (a - 1)) ≤ dd f a * (dd f (a - 1) - f 0) := by
  have h := A2a hf hf1 (a - 1)
  rwa [Nat.sub_add_cancel (by omega : 1 ≤ a), cast_pred (by omega), dd_zero_eq] at h

theorem basic_E2 (hf : LCNZ f) (hf1 : 0 < f 1) {a : ℕ} (ha : 3 ≤ a) :
    ((a : ℝ) - 2) * (f 0 + f 1) * (dd f a - dd f (a - 1)) ≤ dd f a * (dd f (a - 1) - (f 0 + f 1)) := by
  have h := A2b hf hf1 (b := a - 1) (by omega)
  rw [Nat.sub_add_cancel (by omega : 1 ≤ a), cast_pred (by omega), dd_one_eq] at h
  linarith

theorem beta'_one_ge (hf : LCNZ f) {a : ℕ} (ha : 3 ≤ a) :
    ((a : ℝ) - 2) * (dd f a - (f 0 + f 1)) ≤ beta'C f a 1 := by
  have h1 := beta'C_one f (a := a)
  have h0 := beta'C_zero_eq f (a := a)
  have hY' : 0 ≤ beta'C f a 0 := by
    rw [beta'C_zero_lf f ha]; exact lf_nonneg hf fun n _ => cfYp_nonneg (by omega) n
  rw [dd_one_eq] at h1
  linarith

theorem MM1_generic (hf : LCNZ f) (hf1 : 0 < f 1) {a : ℕ} (ha : 6 ≤ a) (m : ℕ) (hm : 2 ≤ m) :
    0 ≤ MC f a 1 m + MC f a m 1 := by
  have ha3 : 3 ≤ a := by omega
  rcases lt_or_ge a m with h | h
  · rw [MC_zero ha3 1 m (Or.inr h), MC_zero ha3 m 1 (Or.inl h), add_zero]
  have pascal : ((a.choose m : ℕ) : ℝ) = ((a - 1).choose (m - 1) : ℝ) + ((a - 1).choose m : ℝ) := by
    obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
    obtain ⟨t, rfl⟩ : ∃ t, m = t + 1 := ⟨m - 1, by omega⟩
    simp only [Nat.add_sub_cancel]; rw [Nat.choose_succ_succ]; push_cast; ring
  have e1 : ((a - 1).choose (m - 1) : ℝ) * a = (a.choose m : ℝ) * m := by
    obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
    obtain ⟨t, rfl⟩ : ∃ t, m = t + 1 := ⟨m - 1, by omega⟩
    have := choose_pred_real (b + 1) t (by omega)
    simp only [Nat.add_sub_cancel] at this ⊢; push_cast at this ⊢; linear_combination this
  have e2 : ((a - 1).choose m : ℝ) * m = ((a - 1).choose (m - 1) : ℝ) * ((a : ℝ) - m) := by
    obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
    obtain ⟨t, rfl⟩ : ∃ t, m = t + 1 := ⟨m - 1, by omega⟩
    have := choose_succ_real b t (by omega)
    simp only [Nat.add_sub_cancel] at this ⊢; push_cast at this ⊢; linear_combination this
  have hA : (3 : ℝ) ≤ a := by exact_mod_cast ha3
  have hm2 : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hX' : f 0 + f 1 ≤ dd f (a - 1) := by rw [← dd_one_eq]; exact dd_mono_of hf (by omega)
  have hH : 0 ≤ Hstar f a := by rw [Hstar_lf]; exact lf_nonneg hf fun n _ => cfH_nonneg n
  have hR : 0 ≤ (a : ℝ) * ((dd f a - (f 0 + f 1)) * (dd f (a - 1) - (f 0 + f 1))) -
      8 * ((f 0 + f 1) * Hstar f a) := by
    have h := R_ge f hf ha3
    have h0 : 0 ≤ f 1 * lf (a + 2) (eR a) f := mul_nonneg hf1.le (lf_nonneg hf fun n _ => eR_nonneg ha3 n)
    rw [← AD_lf f ha3, ← Xp_lf f ha3, ← Hstar_lf, dd_one_eq] at h
    linarith
  have hR2 : 0 ≤ ((a : ℝ) - 2) * ((dd f a - (f 0 + f 1)) * (dd f (a - 1) - f 0)) -
      4 * (a : ℝ) * ((f 0 + f 1) * Hstar f a) := by
    have h := R2_ge f hf ha3
    have h0 : 0 ≤ f 1 * lf (a + 2) (eR2 a) f := mul_nonneg hf1.le (lf_nonneg hf fun n _ => eR2_nonneg ha n)
    rw [← AD_lf f ha3, ← Xpp_lf f ha3, ← Hstar_lf, dd_one_eq, dd_zero_eq] at h
    linarith
  refine le_of_le_of_eq (mm1_scalar (dd f a) (dd f (a - 1)) (f 0) (f 1) (Hstar f a) (a.choose m)
    ((a - 1).choose (m - 1)) ((a - 1).choose m) (zetaC f a m) (nuC f a m) (beta'C f a 1) (betaC f a m)
    (beta'C f a m) a m (hf.1 0) (hf.1 1) (dd_nonneg_of hf _) (dd_mono_of hf (by omega)) hX' hH
    (zetaC_nonneg hf a m) (nuC_nonneg hf a m) (Nat.cast_nonneg _) (Nat.cast_nonneg _) pascal e1 e2 hm2 hA
    (basic_E1 hf hf1 ha3) (basic_E2 hf hf1 ha3) (beta'_one_ge hf ha3) (beta_ge2 hf a m hm)
    (beta'_ge2 hf ha3 hm) hR hR2) ?_
  have hchi : chiC f a m = (a.choose m : ℝ) * dd f a := by
    unfold chiC; rw [choose_small_zero (by omega : 0 < m)]; ring
  have hchi' : chi'C f a m = ((a - 1).choose m : ℝ) * dd f (a - 1) := by
    unfold chi'C; rw [choose_small_zero (by omega : 1 < m)]; ring
  unfold MC
  rw [hchi, hchi', if_pos (le_refl (1 : ℕ)), if_neg (by omega : ¬ m ≤ 1), deltaC_one f (by omega), chiC_one f,
    chi'C_one f (by omega), betaC_one f, dd_zero_eq, dd_one_eq]
  unfold deltaC
  ring

theorem S20_generic (hf : LCNZ f) (hf1 : 0 < f 1) {a : ℕ} (ha : 5 ≤ a) : 0 ≤ MC f a 0 2 + MC f a 1 1 := by
  have ha3 : 3 ≤ a := by omega
  have hA : (3 : ℝ) ≤ a := by exact_mod_cast ha3
  have hX' : f 0 + f 1 ≤ dd f (a - 1) := by rw [← dd_one_eq]; exact dd_mono_of hf (by omega)
  have hY : 0 ≤ betaC f a 0 := by rw [betaC_zero_lf f ha3]; exact lf_nonneg hf fun n _ => cfY_nonneg n
  have hY' : 0 ≤ beta'C f a 0 := by
    rw [beta'C_zero_lf f ha3]; exact lf_nonneg hf fun n _ => cfYp_nonneg (by omega) n
  have hKa : 0 ≤ ((a : ℝ) - 1) * (beta'C f a 0 * (dd f (a - 1) - f 0) +
      betaC f a 0 * (dd f (a - 1) - (f 0 + f 1))) - 4 * (a : ℝ) * ((f 0 + f 1) * Hstar f a) := by
    have h := Ka_ge f hf ha3
    have h0 : 0 ≤ f 1 * lf (a + 2) (eKa a) f := mul_nonneg hf1.le (lf_nonneg hf fun n _ => eKa_nonneg ha n)
    rw [← beta'C_zero_lf f ha3, ← Xpp_lf f ha3, ← betaC_zero_lf f ha3, ← Xp_lf f ha3, ← Hstar_lf, dd_zero_eq,
      dd_one_eq] at h
    linarith
  have hPsi : 0 ≤ (a : ℝ) * ((dd f a - (f 0 + f 1)) * (dd f (a - 1) - (f 0 + f 1) - ((a : ℝ) - 2) * f 1)) -
      ((a : ℝ) - 1) * ((a : ℝ) - 2) / 2 * (f 1 * (betaC f a 0 + beta'C f a 0)) := by
    have h := Psi_ge f hf ha3
    have h0 : 0 ≤ f 1 * lf (a + 2) (ePsi a) f := mul_nonneg hf1.le (lf_nonneg hf fun n _ => ePsi_nonneg ha3 n)
    rw [← AD_lf f ha3, ← J_lf f ha3, ← betaC_zero_lf f ha3, ← beta'C_zero_lf f ha3, dd_one_eq] at h
    linarith
  have hQ : 0 ≤ ((a : ℝ) - 1) * (beta'C f a 0 * (dd f (a - 1) - f 0) +
      betaC f a 0 * (dd f (a - 1) - (f 0 + f 1))) - 4 * (a : ℝ) * (f 0 * Hstar f a) +
      f 1 * (2 * nuC f a 1 + 2 * nuC f a 2 - 4 * ((a : ℝ) * Hstar f a - zetaC f a 1) -
        4 * ((a : ℝ) * ((a : ℝ) - 1) / 2 * Hstar f a - zetaC f a 2)) := by
    have h := Qhat_ge f hf ha3
    have h0 : 0 ≤ f 1 * lf (a + 2) (eQhat a) f :=
      mul_nonneg hf1.le (lf_nonneg hf fun n _ => eQhat_nonneg ha3 n)
    rw [← beta'C_zero_lf f ha3, ← Xpp_lf f ha3, ← betaC_zero_lf f ha3, ← Xp_lf f ha3, dd_zero_eq, dd_one_eq] at h
    linarith
  have huB : f 0 * (dd f a - dd f (a - 1)) ≤ f 1 * dd f (a - 1) := by
    have := u0F_le_u1B (hf := hf) (b := a - 1); rwa [Nat.sub_add_cancel (by omega : 1 ≤ a)] at this
  have hbp1 : 0 ≤ beta'C f a 1 := by
    have h := beta'_one_ge hf ha3
    have : f 0 + f 1 ≤ dd f a := by rw [← dd_one_eq]; exact dd_mono_of hf (by omega)
    nlinarith
  refine le_of_le_of_eq (s20_scalar (dd f a) (dd f (a - 1)) (f 0) (f 1) (Hstar f a) (zetaC f a 1)
    (zetaC f a 2) (nuC f a 1) (nuC f a 2) (betaC f a 0) (beta'C f a 0) (beta'C f a 1) a (hf.1 0) hf1
    (dd_mono_of hf (by omega)) hX' hY hY' hA (basic_E1 hf hf1 ha3) hbp1 huB hKa hPsi hQ) ?_
  have hchi : chiC f a 2 = (a.choose 2 : ℝ) * dd f a := by
    unfold chiC; rw [choose_small_zero (by omega : 0 < 2)]; ring
  have hchi' : chi'C f a 2 = ((a - 1).choose 2 : ℝ) * dd f (a - 1) := by
    unfold chi'C; rw [choose_small_zero (by omega : 1 < 2)]; ring
  unfold MC
  rw [hchi, hchi', if_pos (by norm_num : (0 : ℕ) ≤ 1), if_pos (le_refl (1 : ℕ)), deltaC_one f (by omega),
    chiC_one f, chi'C_one f (by omega), betaC_one f, dd_zero_eq, dd_one_eq]
  unfold deltaC
  rw [pred_two (a := a) (by omega), cast_choose_two a]
  ring

end Glue

theorem MM1_holds : MM1Stmt := by
  intro f hf hf1 a ha m hm
  rcases (show a = 3 ∨ a = 4 ∨ a = 5 ∨ 6 ≤ a by omega) with rfl | rfl | rfl | h6
  · rcases (show m = 2 ∨ m = 3 ∨ 3 < m by omega) with rfl | rfl | hm'
    · exact win_MM1_3_2 hf
    · exact win_MM1_3_3 hf
    · rw [MC_zero le_rfl 1 m (Or.inr hm'), MC_zero le_rfl m 1 (Or.inl hm'), add_zero]
  · rcases (show m = 2 ∨ m = 3 ∨ m = 4 ∨ 4 < m by omega) with rfl | rfl | rfl | hm'
    · exact win_MM1_4_2 hf
    · exact win_MM1_4_3 hf
    · exact win_MM1_4_4 hf
    · rw [MC_zero (by norm_num) 1 m (Or.inr hm'), MC_zero (by norm_num) m 1 (Or.inl hm'), add_zero]
  · rcases (show m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 5 ∨ 5 < m by omega) with rfl | rfl | rfl | rfl | hm'
    · exact win_MM1_5_2 hf
    · exact win_MM1_5_3 hf
    · exact win_MM1_5_4 hf
    · exact win_MM1_5_5 hf
    · rw [MC_zero (by norm_num) 1 m (Or.inr hm'), MC_zero (by norm_num) m 1 (Or.inl hm'), add_zero]
  · exact MM1_generic hf hf1 h6 m hm

theorem S20_holds : S20Stmt := by
  intro f hf hf1 a ha
  rcases (show a = 3 ∨ a = 4 ∨ 5 ≤ a by omega) with rfl | rfl | h5
  · exact win_S20_3 hf
  · exact win_S20_4 hf
  · exact S20_generic hf hf1 h5

/-- The central sums of `MC` are nonnegative (paper steps (iii)–(vii)). -/
theorem central_holds : CentralStmt :=
  central_of_pieces M0s_holds MM1_holds S20_holds (fun f hf hf1 _ ha => (M01_M11_nonneg f hf hf1 ha).1)
    (fun f hf hf1 _ ha => (M01_M11_nonneg f hf hf1 ha).2)

/-- The key inequality (G-key) of Theorem 8.16. -/
theorem genKey_holds : GenKeyStmt := genKey_of_props linCoef_holds central_holds

/-- **Theorem 8.16** (log-concave Newton coefficients and log-concave ratio coefficients), unconditional. -/
theorem lc_general : Stmt_lc_general := lcgeneral_matrix_of_key genKey_holds

end Szkraw
