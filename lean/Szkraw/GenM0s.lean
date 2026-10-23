import Szkraw.GenFormKpp
import Szkraw.GenM01
import Szkraw.GenCentral

/-!
# `M_{0,s} ≥ 0` for `s ≥ 3` (paper step (iv))

`M_{0,s} = c' B K'' + F G_s` and `c' u₀ K'' + u₁ G_s = D Q_s + c'' u₁² Y'`, with `c' = C(a-1,s-1)`,
`c'' = C(a-1,s)`; `3 Q_s ≥ c' · 3Q*` by `ν_s, ζ_s ≥ 0`, `3 C(a,s) ≤ a c'` and `3 c'' ≤ (a-3) c'`.
-/

set_option linter.unusedSectionVars false

namespace Szkraw

open Finset

theorem wgtH_nonneg (n : ℕ) : 0 ≤ wgtH n := by
  unfold wgtH; split_ifs <;> positivity

theorem zetaC_nonneg {f : ℕ → ℝ} (hf : LCNZ f) (a k : ℕ) : 0 ≤ zetaC f a k := by
  unfold zetaC
  exact sum_nonneg fun n _ =>
    mul_nonneg (mul_nonneg (mul_nonneg (wgtH_nonneg n) (Nat.cast_nonneg _)) (hf.1 n)) (Nat.cast_nonneg _)

theorem nuC_nonneg {f : ℕ → ℝ} (hf : LCNZ f) (a k : ℕ) : 0 ≤ nuC f a k := by
  unfold nuC
  refine sum_nonneg fun n _ => mul_nonneg (mul_nonneg (mul_nonneg (wgtH_nonneg n) (Nat.cast_nonneg _))
    (mul_nonneg (Nat.cast_nonneg _) (hf.1 _))) ?_
  split_ifs <;> positivity

/-- The scalar core of step (iv). -/
theorem m0s_scalar (A B f0 f1 Y Y' H z v cs c1 c2 a : ℝ) (hf0 : 0 ≤ f0) (hf1 : 0 < f1) (hF : 0 ≤ A - B)
    (hY : 0 ≤ Y) (hY' : 0 ≤ Y') (hH : 0 ≤ H) (hz : 0 ≤ z) (hv : 0 ≤ v) (hc1 : 0 ≤ c1) (hc2 : 0 ≤ c2)
    (hpas : cs = c1 + c2) (hcs : 3 * cs ≤ a * c1) (hc2b : 3 * c2 ≤ (a - 3) * c1)
    (huB : f0 * (A - B) ≤ f1 * B)
    (hK : 0 ≤ Y' * (B - f0) + Y * (B - (f0 + f1)) - 4 * (f0 + f1) * H)
    (hQ : 0 ≤ 3 * (Y' * (B - f0) + Y * (B - (f0 + f1))) - 12 * f0 * H - 4 * a * f1 * H -
      (a - 3) * f1 * (Y + Y')) :
    0 ≤ Y' * ((A - f0) * (cs * A - c2 * B) - (A - B) * (cs * A)) +
      Y * ((B - (f0 + f1)) * (cs * A - c2 * B) - (A - B) * (c2 * B)) +
      1 * (f0 + f1) * (2 * (A - B) * v - 4 * (H * (cs * A - c2 * B) - (A - B) * z)) := by
  subst hpas
  set F := A - B with hFdef
  set D := f0 + f1 with hD
  set Kpp := Y' * (B - f0) + Y * (B - D) - 4 * D * H with hKpp
  set G := c1 * (Y' * (B - f0) + Y * (B - D)) - c2 * (f0 * Y' + D * Y) + D * (2 * v - 4 * ((c1 + c2) * H - z))
  set Qs := c1 * (Y' * (B - f0) + Y * (B - D)) - 4 * c1 * f0 * H + f1 * (2 * v - 4 * ((c1 + c2) * H - z)) -
    c2 * f1 * (Y + Y') with hQs
  have h1 : f1 * (Y' * ((A - f0) * ((c1 + c2) * A - c2 * B) - F * ((c1 + c2) * A)) +
      Y * ((B - D) * ((c1 + c2) * A - c2 * B) - F * (c2 * B)) +
      1 * D * (2 * F * v - 4 * (H * ((c1 + c2) * A - c2 * B) - F * z))) =
      c1 * Kpp * (f1 * B) + F * (f1 * G) := by
    simp only [hFdef, hD, hKpp]; ring
  have h3 : c1 * Kpp * (f0 * F) ≤ c1 * Kpp * (f1 * B) := mul_le_mul_of_nonneg_left huB (mul_nonneg hc1 hK)
  have h4 : c1 * Kpp * (f0 * F) + F * (f1 * G) = F * (D * Qs + c2 * f1 ^ 2 * Y') := by
    simp only [hD, hKpp, hQs]; ring
  have h5 : c1 * (3 * (Y' * (B - f0) + Y * (B - D)) - 12 * f0 * H - 4 * a * f1 * H - (a - 3) * f1 * (Y + Y')) ≤
      3 * Qs := by
    nlinarith [mul_nonneg hf1.le hv, mul_nonneg hf1.le hz, mul_nonneg (mul_nonneg hf1.le hH) (sub_nonneg.2 hcs),
      mul_nonneg (mul_nonneg hf1.le (add_nonneg hY hY')) (sub_nonneg.2 hc2b)]
  have h6 : 0 ≤ Qs := by nlinarith [mul_nonneg hc1 hQ]
  have h7 : 0 ≤ F * (D * Qs + c2 * f1 ^ 2 * Y') :=
    mul_nonneg hF (add_nonneg (mul_nonneg (by positivity) h6) (mul_nonneg (mul_nonneg hc2 (by positivity)) hY'))
  have h8 : 0 ≤ f1 * (Y' * ((A - f0) * ((c1 + c2) * A - c2 * B) - F * ((c1 + c2) * A)) +
      Y * ((B - D) * ((c1 + c2) * A - c2 * B) - F * (c2 * B)) +
      1 * D * (2 * F * v - 4 * (H * ((c1 + c2) * A - c2 * B) - F * z))) := by
    rw [h1]; linarith
  exact le_of_mul_le_mul_left (by rw [mul_zero]; exact h8) hf1

theorem M0s_holds : M0Stmt := by
  intro f hf hf1 a ha s hs
  rcases lt_or_ge a s with has | has
  · rw [MC_zero ha 0 s (Or.inr has)]
  have pascal : ((a.choose s : ℕ) : ℝ) = ((a - 1).choose (s - 1) : ℝ) + ((a - 1).choose s : ℝ) := by
    obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
    obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := ⟨s - 1, by omega⟩
    simp only [Nat.add_sub_cancel]; rw [Nat.choose_succ_succ]; push_cast; ring
  have e1 : ((a - 1).choose (s - 1) : ℝ) * a = (a.choose s : ℝ) * s := by
    obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
    obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := ⟨s - 1, by omega⟩
    have := choose_pred_real (b + 1) t (by omega)
    simp only [Nat.add_sub_cancel] at this ⊢; push_cast at this ⊢; linear_combination this
  have e2 : ((a - 1).choose s : ℝ) * s = ((a - 1).choose (s - 1) : ℝ) * ((a : ℝ) - s) := by
    obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
    obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := ⟨s - 1, by omega⟩
    have := choose_succ_real b t (by omega)
    simp only [Nat.add_sub_cancel] at this ⊢; push_cast at this ⊢; linear_combination this
  have hs3 : (3 : ℝ) ≤ s := by exact_mod_cast hs
  have hcs0 : (0 : ℝ) ≤ (a.choose s : ℝ) := Nat.cast_nonneg _
  have hc10 : (0 : ℝ) ≤ ((a - 1).choose (s - 1) : ℝ) := Nat.cast_nonneg _
  have hc20 : (0 : ℝ) ≤ ((a - 1).choose s : ℝ) := Nat.cast_nonneg _
  have hcs : 3 * (a.choose s : ℝ) ≤ a * ((a - 1).choose (s - 1) : ℝ) := by
    nlinarith [mul_nonneg hcs0 (sub_nonneg.2 hs3)]
  have hc2b : 3 * ((a - 1).choose s : ℝ) ≤ ((a : ℝ) - 3) * ((a - 1).choose (s - 1) : ℝ) := by
    nlinarith [mul_nonneg hc20 (sub_nonneg.2 hs3), mul_nonneg hc10 (sub_nonneg.2 hs3)]
  have huB : f 0 * (dd f a - dd f (a - 1)) ≤ f 1 * dd f (a - 1) := by
    have := u0F_le_u1B (hf := hf) (b := a - 1); rwa [Nat.sub_add_cancel (by omega : 1 ≤ a)] at this
  have hY : 0 ≤ betaC f a 0 := by rw [betaC_zero_lf f ha]; exact lf_nonneg hf fun n _ => cfY_nonneg n
  have hY' : 0 ≤ beta'C f a 0 := by
    rw [beta'C_zero_lf f ha]; exact lf_nonneg hf fun n _ => cfYp_nonneg (by omega) n
  have hH : 0 ≤ Hstar f a := by rw [Hstar_lf]; exact lf_nonneg hf fun n _ => cfH_nonneg n
  have hK : 0 ≤ beta'C f a 0 * (dd f (a - 1) - f 0) + betaC f a 0 * (dd f (a - 1) - (f 0 + f 1)) -
      4 * (f 0 + f 1) * Hstar f a := by
    have h := Kpp_ge f hf ha
    have h0 : 0 ≤ f 1 * lf (a + 2) (eKpp a) f := mul_nonneg hf1.le (lf_nonneg hf fun n _ => eKpp_nonneg ha n)
    rw [← beta'C_zero_lf f ha, ← Xpp_lf f ha, ← betaC_zero_lf f ha, ← Xp_lf f ha, ← Hstar_lf, dd_zero_eq,
      dd_one_eq] at h
    linarith
  have hQ : 0 ≤ 3 * (beta'C f a 0 * (dd f (a - 1) - f 0) + betaC f a 0 * (dd f (a - 1) - (f 0 + f 1))) -
      12 * f 0 * Hstar f a - 4 * (a : ℝ) * f 1 * Hstar f a - ((a : ℝ) - 3) * f 1 * (betaC f a 0 + beta'C f a 0) := by
    have h := Qs_ge f hf ha
    have h0 : 0 ≤ f 1 * lf (a + 2) (eQs a) f := mul_nonneg hf1.le (lf_nonneg hf fun n _ => eQs_nonneg ha n)
    rw [← beta'C_zero_lf f ha, ← Xpp_lf f ha, ← betaC_zero_lf f ha, ← Xp_lf f ha, ← Hstar_lf, dd_zero_eq,
      dd_one_eq] at h
    linarith
  refine le_of_le_of_eq (m0s_scalar (dd f a) (dd f (a - 1)) (f 0) (f 1) (betaC f a 0) (beta'C f a 0) (Hstar f a)
    (zetaC f a s) (nuC f a s) (a.choose s) ((a - 1).choose (s - 1)) ((a - 1).choose s) a (hf.1 0) hf1
    (sub_nonneg.2 (dd_mono_of hf (by omega))) hY hY' hH (zetaC_nonneg hf a s) (nuC_nonneg hf a s) hc10 hc20
    pascal hcs hc2b huB hK hQ) ?_
  have hchi : chiC f a s = (a.choose s : ℝ) * dd f a := by
    unfold chiC; rw [choose_small_zero (by omega : 0 < s)]; ring
  have hchi' : chi'C f a s = ((a - 1).choose s : ℝ) * dd f (a - 1) := by
    unfold chi'C; rw [choose_small_zero (by omega : 1 < s)]; ring
  unfold MC deltaC
  rw [hchi, hchi', if_pos (by norm_num : (0 : ℕ) ≤ 1), dd_zero_eq, dd_one_eq]

end Szkraw
