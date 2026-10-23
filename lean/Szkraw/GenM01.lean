import Szkraw.GenFormL1
import Szkraw.VRAffineKey2

/-!
# Theorem 8.16, paper step (iii): `M_{0,1} ≥ 0` and `M_{1,1} ≥ 0`

For `P = (P₀, P₁, 0, …)`, `Φ(P) = P₁ (M_{0,1} P₀ + M_{1,1} P₁)` and, with `λ = F/Δc(P)`,
`F Φ(P) = Δc(P)² Key(λP)`. The key at the two-term ratio `λP` is bounded below by Theorem 8.9's affine
inequality, `u₁ aff(α,t) = (u₁α - t u₀) K + t G` with `K = l₀ ≥ 0` and `G ≥ 0` (`G_nonneg`).
-/

set_option linter.unusedSectionVars false

namespace Szkraw

open Finset

section Bridge

variable (f : ℕ → ℝ) {a : ℕ}

/-- `sY = β₀ = Y`. -/
theorem sY_eq_beta (ha : 3 ≤ a) : sY f a = betaC f a 0 := by
  rw [betaC_zero_lf f ha]
  unfold sY lf
  refine sum_congr rfl fun n _ => ?_
  rcases Nat.lt_or_ge n 2 with h | h
  · rw [if_neg (by omega)]
    rcases (show n = 0 ∨ n = 1 by omega) with rfl | rfl
    · rw [cfY_zero]
    · rw [cfY_one]
  · rw [if_pos h, cfY_ge2 h]

/-- `sJ = X' - (a-2) u₁`. -/
theorem sJ_eq (ha : 3 ≤ a) : sJ f a = (dd f (a - 1) - dd f 1) - ((a : ℝ) - 2) * f 1 := by
  rw [Xp_lf f ha]
  set g : ℕ → ℝ := fun n => if 2 ≤ n then ((a - 1).choose n : ℝ) else 0 with hg
  have hpt : ∀ n, cfXp a n = g n + (if n = 1 then (a : ℝ) - 2 else 0) := by
    intro n
    rcases (show n = 0 ∨ n = 1 ∨ 2 ≤ n by omega) with rfl | rfl | h
    · rw [cfXp_zero]; simp [hg]
    · rw [cfXp_one (by omega)]; simp [hg]
    · rw [cfXp_ge2 h]; simp [hg, h, show n ≠ 1 by omega]
  have e1 : lf (a + 1) (cfXp a) f = lf (a + 1) g f + ((a : ℝ) - 2) * f 1 := by
    unfold lf
    rw [sum_congr rfl (fun n _ => by rw [hpt n, add_mul]), sum_add_distrib]
    congr 1
    simp only [ite_mul, zero_mul]
    rw [sum_ite_eq']; simp only [mem_range, show 1 < a + 1 by omega, if_true]
  have e2 : lf (a + 1) g f = lf a g f :=
    (lf_extend (by omega) (fun n hn => by simp [hg, choose_small_zero (by omega : a - 1 < n)])).symm
  rw [e1, e2]; unfold sJ lf; simp [hg]

/-- `sH = H_*`. -/
theorem sH_eq : sH f a = Hstar f a := by
  unfold sH Hstar
  refine sum_congr rfl fun n _ => ?_
  rcases Nat.lt_or_ge n 3 with h | h
  · rw [if_neg (by omega)]; unfold wgtH; rw [if_neg (by omega)]; ring
  · rw [if_pos h]; have := cfH_ge3 (a := a) h; unfold cfH at this; rw [mul_assoc, this]; ring

/-- `sYp = β'₀ = Y'`. -/
theorem sYp_eq_beta' (ha : 3 ≤ a) : sYp f a = beta'C f a 0 := by
  rw [beta'C_zero_lf f ha]
  set g : ℕ → ℝ := fun j => if 2 ≤ j then ((a - 1).choose j : ℝ) else 0 with hg
  have e1 : sYp f a = lf a g f + ∑ j ∈ range a, g j * f (j + 1) := by
    unfold sYp lf; rw [← sum_add_distrib]; exact sum_congr rfl fun j _ => by rw [hg]; ring
  rw [e1, lf_shift a g]
  have e2 : lf a g f = lf (a + 1) g f :=
    lf_extend (by omega) (fun n hn => by simp [hg, choose_small_zero (by omega : a - 1 < n)])
  rw [e2]
  unfold lf; rw [← sum_add_distrib]
  refine sum_congr rfl fun n hn => ?_
  simp only [mem_range] at hn
  have pas : ∀ m, 1 ≤ m → ((a.choose m : ℕ) : ℝ) = ((a - 1).choose (m - 1) : ℝ) + ((a - 1).choose m : ℝ) := by
    intro m hm
    have := Nat.choose_succ_succ' (a - 1) (m - 1)
    rw [show a - 1 + 1 = a by omega, show m - 1 + 1 = m by omega] at this
    exact_mod_cast this
  rcases (show n = 0 ∨ n = 1 ∨ n = 2 ∨ 3 ≤ n by omega) with rfl | rfl | rfl | h
  · rw [cfYp_zero]; simp [hg]
  · rw [cfYp_one]; simp [hg]
  · rw [cfYp_two, pas 2 (by norm_num)]; simp [hg, cast_pred (show 1 ≤ a by omega)]
  · rw [cfYp_ge3 h, pas n (by omega)]; simp [hg, show 2 ≤ n by omega, show 2 ≤ n - 1 by omega,
      show 1 ≤ n by omega]; ring

/-- `T = 2a H_* - 2 ζ₁ - ν₁`. -/
theorem sT_eq (ha : 3 ≤ a) : sT f a = 2 * (a : ℝ) * Hstar f a - 2 * zetaC f a 1 - nuC f a 1 := by
  -- reindex `ν₁ = Σ_m [m ≥ 2] (m-1)(a-m) C(a,m) f_m`
  have hnu : nuC f a 1 = ∑ m ∈ range (a + 1),
      (if 2 ≤ m then ((m : ℝ) - 1) * ((a : ℝ) - m) * (a.choose m : ℝ) else 0) * f m := by
    unfold nuC
    rw [sum_range_succ']
    simp only [show wgtH 0 = 0 by unfold wgtH; simp, zero_mul, add_zero, Nat.cast_zero, zero_mul, mul_zero,
      if_pos (le_refl 1), Nat.sub_self, Nat.choose_zero_right, Nat.cast_one, mul_one]
    rw [sum_range_succ (fun m => (if 2 ≤ m then ((m : ℝ) - 1) * ((a : ℝ) - m) * (a.choose m : ℝ) else 0) * f m) a]
    have hlast : (if 2 ≤ a then ((a : ℝ) - 1) * ((a : ℝ) - a) * (a.choose a : ℝ) else 0) * f a = 0 := by
      rw [if_pos (by omega)]; ring
    rw [hlast, add_zero]
    refine sum_congr rfl fun m hm => ?_
    simp only [mem_range] at hm
    rw [Nat.add_sub_cancel]
    unfold wgtH
    rcases Nat.lt_or_ge m 2 with h | h
    · rw [if_neg (by omega), if_neg (by omega)]; ring
    · rw [if_pos (by omega), if_pos h, Nat.choose_one_right]
      have hc := choose_succ_real a m (by omega)
      have e : ((m + 1 - 3 + 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
        rw [show m + 1 - 3 + 1 = m - 1 by omega, Nat.cast_sub (by omega : 1 ≤ m)]; norm_num
      rw [e]; push_cast at hc ⊢
      have : ((a.choose (m + 1) : ℕ) : ℝ) * ((m : ℝ) + 1) = (a.choose m : ℝ) * ((a : ℝ) - m) := hc
      linear_combination ((m : ℝ) - 1) * f m * this
  rw [hnu]; unfold sT Hstar zetaC
  rw [mul_sum, mul_sum, ← sum_sub_distrib, ← sum_sub_distrib]
  refine sum_congr rfl fun n _ => ?_
  unfold wgtH
  rcases (show n < 2 ∨ n = 2 ∨ 3 ≤ n by omega) with h | rfl | h
  · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]; ring
  · rw [if_pos le_rfl, if_neg (by omega), if_pos le_rfl]; push_cast; ring
  · rw [if_pos (by omega), if_pos h, if_pos (by omega),
      show n - 3 + 1 = n - 2 by omega]
    simp only [Nat.choose_one_right, Nat.cast_sub (by omega : 2 ≤ n)]
    push_cast; ring

/-! ### Coefficients at `k, m ∈ {0, 1}` -/

theorem chiC_zero : chiC f a 0 = dd f a - dd f 0 := by simp [chiC]
theorem chiC_one : chiC f a 1 = (a : ℝ) * dd f a := by simp [chiC]
theorem chi'C_zero : chi'C f a 0 = dd f (a - 1) - dd f 1 := by simp [chi'C]
theorem chi'C_one (ha : 1 ≤ a) : chi'C f a 1 = ((a : ℝ) - 1) * dd f (a - 1) - dd f 1 := by
  simp [chi'C, cast_pred ha]
theorem deltaC_zero : deltaC f a 0 = dd f a - dd f (a - 1) := by simp [deltaC]
theorem deltaC_one (ha : 1 ≤ a) : deltaC f a 1 = (a : ℝ) * dd f a - ((a : ℝ) - 1) * dd f (a - 1) := by
  simp [deltaC, cast_pred ha]
theorem betaC_one : betaC f a 1 = (a : ℝ) * dd f a - (a : ℝ) * dd f 1 := by simp [betaC]
theorem beta'C_one : beta'C f a 1 = (a : ℝ) * dd f a + ((a : ℝ) - 2) * dd f 1 - 2 * ((a : ℝ) - 1) * dd f 2 := by
  unfold beta'C; simp only [Nat.choose_one_right]; push_cast; ring
theorem zetaC_zero : zetaC f a 0 = Hstar f a := by
  unfold zetaC Hstar; exact sum_congr rfl fun n _ => by simp
theorem nuC_zero : nuC f a 0 = 0 := by
  unfold nuC; exact sum_eq_zero fun n _ => by simp

end Bridge

/-! ### The scalar argument -/

section Scalar

variable (A B d2 u0 u1 H z1 n1 a : ℝ)

/-- `M_{0,1}` in scalar variables (`D = u₀+u₁`, `F = A-B`, `X = A-u₀`, `X' = B-D`). -/
noncomputable def sM01 : ℝ :=
  (A + (a - 2) * (u0 + u1) - (a - 1) * d2) * ((A - u0) * (a * A - (a - 1) * B) - (A - B) * (a * A)) +
    (A - u0 - a * u1) * ((B - (u0 + u1)) * (a * A - (a - 1) * B) - (A - B) * ((a - 1) * B - (u0 + u1))) +
    (u0 + u1) * (2 * (A - B) * n1 - 4 * (H * (a * A - (a - 1) * B) - (A - B) * z1))

/-- `M_{1,1}` in scalar variables. -/
noncomputable def sM11 : ℝ :=
  (a * A + (a - 2) * (u0 + u1) - 2 * (a - 1) * d2) * ((A - u0) * (a * A - (a - 1) * B) - (A - B) * (a * A)) +
    (a * A - a * (u0 + u1)) * ((B - (u0 + u1)) * (a * A - (a - 1) * B) - (A - B) * ((a - 1) * B - (u0 + u1))) +
    (u0 + u1) * (2 * (A - B) * n1 - 4 * (H * (a * A - (a - 1) * B) - (A - B) * z1))

/-- The key at the two-term ratio `(s, t)`. -/
noncomputable def sKey (s t : ℝ) : ℝ :=
  ((A - u0) - ((A - u0) * s + a * A * t)) * ((A + (a - 2) * (u0 + u1) - (a - 1) * d2) * s +
      (a * A + (a - 2) * (u0 + u1) - 2 * (a - 1) * d2) * t) +
    ((A - u0 - a * u1) * s + (a * A - a * (u0 + u1)) * t) *
      ((B - (u0 + u1)) - ((B - (u0 + u1)) * s + ((a - 1) * B - (u0 + u1)) * t)) +
    2 * ((u0 + u1) * (s + t)) * (n1 * t) - 4 * ((u0 + u1) * (s + t)) * (H - (H * s + z1 * t))

/-- Linear and quadratic parts of the key at `(s, t)`. -/
noncomputable def sLin (s t : ℝ) : ℝ :=
  (A - u0) * ((A + (a - 2) * (u0 + u1) - (a - 1) * d2) * s + (a * A + (a - 2) * (u0 + u1) - 2 * (a - 1) * d2) * t) +
    ((A - u0 - a * u1) * s + (a * A - a * (u0 + u1)) * t) * (B - (u0 + u1)) - 4 * ((u0 + u1) * (s + t)) * H

noncomputable def sQuad (s t : ℝ) : ℝ :=
  ((A - u0) * s + a * A * t) * ((A + (a - 2) * (u0 + u1) - (a - 1) * d2) * s +
      (a * A + (a - 2) * (u0 + u1) - 2 * (a - 1) * d2) * t) +
    ((A - u0 - a * u1) * s + (a * A - a * (u0 + u1)) * t) * ((B - (u0 + u1)) * s + ((a - 1) * B - (u0 + u1)) * t) -
    2 * ((u0 + u1) * (s + t)) * (n1 * t) - 4 * ((u0 + u1) * (s + t)) * (H * s + z1 * t)

theorem sKey_split (s t : ℝ) :
    sKey A B d2 u0 u1 H z1 n1 a s t = sLin A B d2 u0 u1 H a s t - sQuad A B d2 u0 u1 H z1 n1 a s t := by
  unfold sKey sLin sQuad; ring

theorem sLin_scale (l s t : ℝ) : sLin A B d2 u0 u1 H a (l * s) (l * t) = l * sLin A B d2 u0 u1 H a s t := by
  unfold sLin; ring

theorem sQuad_scale (l s t : ℝ) :
    sQuad A B d2 u0 u1 H z1 n1 a (l * s) (l * t) = l ^ 2 * sQuad A B d2 u0 u1 H z1 n1 a s t := by
  unfold sQuad; ring

/-- `F (M_{0,1} P₀ + M_{1,1}) = Δc F Lin(P₀,1) - F² Quad(P₀,1)`, `Δc = F P₀ + δ₁`. -/
theorem phi_lin_quad (P0 : ℝ) :
    (A - B) * (sM01 A B d2 u0 u1 H z1 n1 a * P0 + sM11 A B d2 u0 u1 H z1 n1 a) =
      ((A - B) * P0 + (a * A - (a - 1) * B)) * (A - B) * sLin A B d2 u0 u1 H a P0 1 -
        (A - B) ^ 2 * sQuad A B d2 u0 u1 H z1 n1 a P0 1 := by
  unfold sM01 sM11 sLin sQuad; ring

theorem scaling_identity (P0 : ℝ) (hDc : (A - B) * P0 + (a * A - (a - 1) * B) ≠ 0) :
    (A - B) * (sM01 A B d2 u0 u1 H z1 n1 a * P0 + sM11 A B d2 u0 u1 H z1 n1 a) =
      ((A - B) * P0 + (a * A - (a - 1) * B)) ^ 2 *
        sKey A B d2 u0 u1 H z1 n1 a ((A - B) / ((A - B) * P0 + (a * A - (a - 1) * B)) * P0)
          ((A - B) / ((A - B) * P0 + (a * A - (a - 1) * B))) := by
  set Dc := (A - B) * P0 + (a * A - (a - 1) * B) with hDcdef
  set l := (A - B) / Dc with hl
  have hlD : Dc * l = A - B := by rw [hl]; field_simp
  have e1 := sLin_scale A B d2 u0 u1 H a l P0 1
  have e2 := sQuad_scale A B d2 u0 u1 H z1 n1 a l P0 1
  rw [mul_one] at e1 e2
  rw [phi_lin_quad, sKey_split, e1, e2]
  have : Dc ^ 2 * (l * sLin A B d2 u0 u1 H a P0 1 - l ^ 2 * sQuad A B d2 u0 u1 H z1 n1 a P0 1) =
      (Dc * l) * Dc * sLin A B d2 u0 u1 H a P0 1 - (Dc * l) ^ 2 * sQuad A B d2 u0 u1 H z1 n1 a P0 1 := by ring
  rw [this, hlD]; ring

theorem sKey_nonneg (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) (hu0 : 0 ≤ u0) (hu1 : 0 < u1)
    (hal : t * u0 ≤ u1 * (1 - s - a * t)) (ha : 1 ≤ a)
    (hX : 0 ≤ A - u0) (hXp : 0 ≤ B - (u0 + u1)) (hY : 0 ≤ A - u0 - a * u1)
    (hJ : 0 ≤ (B - (u0 + u1)) - (a - 2) * u1)
    (hAd2 : d2 ≤ A)
    (hK : 0 ≤ (A - u0) * (A + (a - 2) * (u0 + u1) - (a - 1) * d2) + (B - (u0 + u1)) * (A - u0 - a * u1) -
      4 * (u0 + u1) * H)
    (hG : 0 ≤ u0 * (A - u0 - a * u1) * (A + (a - 2) * (u0 + u1) - (a - 1) * d2) +
      (u0 + u1) * (A - u0 - a * u1) * ((B - (u0 + u1)) - (a - 2) * u1) -
      (u0 + u1) * (4 * u0 * H + 2 * u1 * (2 * a * H - 2 * z1 - n1))) :
    0 ≤ sKey A B d2 u0 u1 H z1 n1 a s t := by
  set al := 1 - s - a * t with hal_def
  set K := (A - u0) * (A + (a - 2) * (u0 + u1) - (a - 1) * d2) + (B - (u0 + u1)) * (A - u0 - a * u1) -
      4 * (u0 + u1) * H with hKdef
  set G := u0 * (A - u0 - a * u1) * (A + (a - 2) * (u0 + u1) - (a - 1) * d2) +
      (u0 + u1) * (A - u0 - a * u1) * ((B - (u0 + u1)) - (a - 2) * u1) -
      (u0 + u1) * (4 * u0 * H + 2 * u1 * (2 * a * H - 2 * z1 - n1)) with hGdef
  have hw : 0 ≤ u1 * al - t * u0 := by linarith
  -- the two weights `A₀`, `A₀'`
  set A0 := al * (A - u0) - t * a * u0 with hA0def
  set A0' := al * (B - (u0 + u1)) + t * (B - (a - 1) * (u0 + u1)) with hA0'def
  have hA0 : 0 ≤ A0 := by
    have e : u1 * A0 = (u1 * al - t * u0) * (A - u0) + t * u0 * (A - u0 - a * u1) := by rw [hA0def]; ring
    have : 0 ≤ u1 * A0 := by rw [e]; exact add_nonneg (mul_nonneg hw hX) (mul_nonneg (mul_nonneg ht hu0) hY)
    exact le_of_mul_le_mul_left (by rw [mul_zero]; exact this) hu1
  have hA0' : 0 ≤ A0' := by
    have e : u1 * A0' = (u1 * al - t * u0) * (B - (u0 + u1)) +
        t * (u0 + u1) * ((B - (u0 + u1)) - (a - 2) * u1) := by rw [hA0'def]; ring
    have : 0 ≤ u1 * A0' := by
      rw [e]; exact add_nonneg (mul_nonneg hw hXp) (mul_nonneg (mul_nonneg ht (by linarith)) hJ)
    exact le_of_mul_le_mul_left (by rw [mul_zero]; exact this) hu1
  -- the affine inequality
  set aff := A0 * (A + (a - 2) * (u0 + u1) - (a - 1) * d2) + (A - u0 - a * u1) * A0' -
      (u0 + u1) * (4 * al * H + 2 * t * (2 * a * H - 2 * z1 - n1)) with haffdef
  have haff : 0 ≤ aff := by
    have e : u1 * aff = (u1 * al - t * u0) * K + t * G := by rw [haffdef, hA0def, hA0'def, hKdef, hGdef]; ring
    have : 0 ≤ u1 * aff := by rw [e]; exact add_nonneg (mul_nonneg hw hK) (mul_nonneg ht hG)
    exact le_of_mul_le_mul_left (by rw [mul_zero]; exact this) hu1
  have e : sKey A B d2 u0 u1 H z1 n1 a s t = (s + t) * aff + t * A0 * ((a - 1) * (A - d2)) +
      t * A0' * ((a - 1) * (A - u0)) := by
    unfold sKey; rw [haffdef, hA0def, hA0'def, hal_def]; ring
  rw [e]
  have h1 : 0 ≤ (a - 1) * (A - d2) := mul_nonneg (by linarith) (by linarith)
  have h2 : 0 ≤ (a - 1) * (A - u0) := mul_nonneg (by linarith) hX
  have := mul_nonneg (add_nonneg hs ht) haff
  have := mul_nonneg (mul_nonneg ht hA0) h1
  have := mul_nonneg (mul_nonneg ht hA0') h2
  linarith

end Scalar

/-! ### `M_{0,1} ≥ 0` and `M_{1,1} ≥ 0` -/

section Glue

variable (f : ℕ → ℝ) {a : ℕ}

theorem betaC_zero_eq : betaC f a 0 = dd f a - f 0 - (a : ℝ) * f 1 := by
  unfold betaC; rw [dd_zero_eq, dd_one_eq]; simp

theorem beta'C_zero_eq : beta'C f a 0 = dd f a + ((a : ℝ) - 2) * (f 0 + f 1) - ((a : ℝ) - 1) * dd f 2 := by
  unfold beta'C; rw [dd_one_eq]; simp

theorem MC01_eq (ha : 1 ≤ a) :
    MC f a 0 1 = sM01 (dd f a) (dd f (a - 1)) (dd f 2) (f 0) (f 1) (Hstar f a) (zetaC f a 1) (nuC f a 1) a := by
  unfold MC
  rw [beta'C_zero_eq, betaC_zero_eq, deltaC_one f ha, chiC_one, chi'C_one f ha, dd_zero_eq, dd_one_eq,
    if_pos (by norm_num)]
  unfold sM01; ring

theorem MC11_eq (ha : 1 ≤ a) :
    MC f a 1 1 = sM11 (dd f a) (dd f (a - 1)) (dd f 2) (f 0) (f 1) (Hstar f a) (zetaC f a 1) (nuC f a 1) a := by
  unfold MC
  rw [beta'C_one, betaC_one, deltaC_one f ha, chiC_one, chi'C_one f ha, dd_zero_eq, dd_one_eq,
    if_pos le_rfl]
  unfold sM11; ring

/-- `u₀ F ≤ u₁ B`, termwise from `u₀ u_{m+1} ≤ u₁ u_m`. -/
theorem u0F_le_u1B (hf : LCNZ f) (b : ℕ) : f 0 * (dd f (b + 1) - dd f b) ≤ f 1 * dd f b := by
  rw [dd_succ_eq, add_sub_cancel_left]
  show f 0 * iterShift f b 1 ≤ f 1 * iterShift f b 0
  rw [iterShift_eq, iterShift_eq, mul_sum, mul_sum]
  refine sum_le_sum fun h _ => ?_
  have := hf.zero_shift h
  rw [show 1 + h = h + 1 by ring, zero_add]
  have hc : (0 : ℝ) ≤ (b.choose h : ℝ) := by positivity
  nlinarith [mul_le_mul_of_nonneg_left this hc]

theorem M01_M11_nonneg (hf : LCNZ f) (hf1 : 0 < f 1) (ha : 3 ≤ a) : 0 ≤ MC f a 0 1 ∧ 0 ≤ MC f a 1 1 := by
  set A := dd f a with hAdef
  set B := dd f (a - 1) with hBdef
  set d2 := dd f 2 with hd2
  set u0 := f 0
  set u1 := f 1
  set H := Hstar f a
  set z1 := zetaC f a 1
  set n1 := nuC f a 1
  have haR : (3 : ℝ) ≤ a := by exact_mod_cast ha
  have hab : a = (a - 1) + 1 := by omega
  have hF : 0 < A - B := by
    rw [hAdef, hBdef, hab, dd_succ_eq, show a - 1 + 1 - 1 = a - 1 by omega, add_sub_cancel_left]
    exact iterShift_one_pos hf hf1 (a - 1)
  have hu0 : 0 ≤ u0 := hf.1 0
  have hB0 : 0 ≤ B := dd_nonneg_of hf _
  have hD := dd_one_eq f
  have hFB : u0 * (A - B) ≤ u1 * B := by
    have := u0F_le_u1B f hf (a - 1); rwa [← hab] at this
  have hX : 0 ≤ A - u0 := by have := dd_mono_of hf (Nat.zero_le a); rw [dd_zero_eq] at this; linarith
  have hXp : 0 ≤ B - (u0 + u1) := by have := dd_mono_of hf (show 1 ≤ a - 1 by omega); rw [hD] at this; linarith
  have hY : 0 ≤ A - u0 - (a : ℝ) * u1 := by
    have := sY_nonneg hf a; rw [sY_eq_beta f ha, betaC_zero_eq] at this; exact this
  have hJ : 0 ≤ (B - (u0 + u1)) - ((a : ℝ) - 2) * u1 := by
    have := sJ_nonneg hf a; rw [sJ_eq f ha, hD] at this; exact this
  have hAd2 : d2 ≤ A := dd_mono_of hf (by omega)
  have hK : 0 ≤ (A - u0) * (A + ((a : ℝ) - 2) * (u0 + u1) - ((a : ℝ) - 1) * d2) +
      (B - (u0 + u1)) * (A - u0 - (a : ℝ) * u1) - 4 * (u0 + u1) * H := by
    have := linC_zero_nonneg f hf ha
    unfold linC at this
    rw [beta'C_zero_eq, betaC_zero_eq, dd_zero_eq, hD, if_pos (by norm_num)] at this
    linarith
  have hG : 0 ≤ u0 * (A - u0 - (a : ℝ) * u1) * (A + ((a : ℝ) - 2) * (u0 + u1) - ((a : ℝ) - 1) * d2) +
      (u0 + u1) * (A - u0 - (a : ℝ) * u1) * ((B - (u0 + u1)) - ((a : ℝ) - 2) * u1) -
      (u0 + u1) * (4 * u0 * H + 2 * u1 * (2 * (a : ℝ) * H - 2 * z1 - n1)) := by
    have := G_nonneg hf hf1 ha
    rw [sY_eq_beta f ha, sYp_eq_beta' f ha, sJ_eq f ha, sH_eq, sT_eq f ha, betaC_zero_eq, beta'C_zero_eq, hD] at this
    exact this
  -- `Φ(P₀, 1) ≥ 0` for every `P₀ ≥ 0`
  have key : ∀ P0 : ℝ, 0 ≤ P0 → 0 ≤ sM01 A B d2 u0 u1 H z1 n1 a * P0 + sM11 A B d2 u0 u1 H z1 n1 a := by
    intro P0 hP0
    set Dc := (A - B) * P0 + ((a : ℝ) * A - ((a : ℝ) - 1) * B) with hDcdef
    have hDc : 0 < Dc := by
      have : 0 < (a : ℝ) * A - ((a : ℝ) - 1) * B := by nlinarith
      have : 0 ≤ (A - B) * P0 := mul_nonneg hF.le hP0
      linarith
    set l := (A - B) / Dc with hl
    have hl0 : 0 ≤ l := div_nonneg hF.le hDc.le
    have hlD : l * Dc = A - B := by rw [hl]; field_simp
    have hal : l * u0 ≤ u1 * (1 - l * P0 - (a : ℝ) * l) := by
      have e : 1 - l * P0 - (a : ℝ) * l = B / Dc := by
        rw [hl]; field_simp; rw [hDcdef]; ring
      rw [e, hl, div_mul_eq_mul_div, mul_div_assoc']
      rw [div_le_div_iff_of_pos_right hDc]; linarith
    have hS := sKey_nonneg A B d2 u0 u1 H z1 n1 a (l * P0) l (mul_nonneg hl0 hP0) hl0 hu0 hf1 hal (by linarith)
      hX hXp hY hJ hAd2 hK hG
    have hid := scaling_identity A B d2 u0 u1 H z1 n1 a P0 hDc.ne'
    rw [← hl] at hid
    have : 0 ≤ (A - B) * (sM01 A B d2 u0 u1 H z1 n1 a * P0 + sM11 A B d2 u0 u1 H z1 n1 a) := by
      rw [hid]; exact mul_nonneg (sq_nonneg _) hS
    exact le_of_mul_le_mul_left (by rw [mul_zero]; exact this) hF
  rw [MC01_eq f (by omega), MC11_eq f (by omega)]
  have h11 : 0 ≤ sM11 A B d2 u0 u1 H z1 n1 a := by simpa using key 0 le_rfl
  refine ⟨?_, h11⟩
  by_contra hneg
  push Not at hneg
  have := key ((sM11 A B d2 u0 u1 H z1 n1 a + 1) / -(sM01 A B d2 u0 u1 H z1 n1 a))
    (div_nonneg (by linarith) (by linarith))
  rw [mul_div_assoc', div_add' _ _ _ (by linarith), le_div_iff₀ (by linarith)] at this
  nlinarith

end Glue

end Szkraw
