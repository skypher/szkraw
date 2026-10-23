import Szkraw.CubicKeyE
import Szkraw.CubicKeyHV
import Szkraw.CubicBridges
import Szkraw.CubicAlpha
import Szkraw.CubicKeyRed

/-!
# Theorem 8.17: the key inequality (eq. `cubic-key`)

As for Theorem 8.11 (`QuadSetting.key`): `B₀ ≥ ρ(ℓ+1) Y` reduces the key to `R ≥ 0`, and `R ≥ 0` is
`cubic_key_scalar`, from `quad_key_red` (the `σ`-free part, with the local coefficients `P₁ = Δρ(ℓ)`, `P₂ = τ + σℓ`)
and `Phi3_nonneg` (the `σ`-part).
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Szkraw

theorem drhoC_local (t τ σ : ℝ) (ℓ a : ℕ) (ha : 1 ≤ a) :
    drhoC t τ σ (ℓ + a - 1) = drhoC t τ σ ℓ + ((a : ℝ) - 1) * (τ + σ * ℓ) + (((a - 1).choose 2 : ℕ) : ℝ) * σ := by
  unfold drhoC
  rw [choose2_real (ℓ + a - 1), choose2_real ℓ, choose2_real (a - 1), Nat.cast_sub (by omega), Nat.cast_sub ha]
  push_cast; ring

section Key

variable {N : ℕ} {r t τ σ : ℝ} {ν u : ℕ → ℝ} (S : CubicSetting N r t τ σ ν u)
include S

/-- **The key inequality** (paper, eq. `cubic-key`), on `Ω` with `a ≥ 3`. -/
theorem CubicSetting.key {ℓ a : ℕ} (h : ℓ + a ≤ N) (ha : 3 ≤ a) :
    4 * dd u (ℓ + 1) * cubicH r t τ σ ν 1 ℓ a ≤
      Wt (quadW ν u) 1 0 ℓ a * Wt u 2 0 (ℓ + 1) (a - 1) + Wt u 2 0 ℓ a * Wt (quadW ν u) 1 0 (ℓ + 1) (a - 2) +
      2 * dd u (ℓ + 1) * cubicV t τ σ ν 1 ℓ a + dd u (ℓ + 1) * cubicE τ σ ν 1 ℓ a := by
  have hD : dd ν (ℓ + 1) = dd ν ℓ + Szkraw.iterShift ν ℓ 1 := rfl
  have hf0 : Szkraw.iterShift ν ℓ 0 = dd ν ℓ := rfl
  set τ' : ℝ := τ + σ * (ℓ : ℝ) with hτ'
  set s : ℝ := drhoC t τ σ ℓ + ((a : ℝ) - 1) * τ' with hs_def
  set α : ℝ := 1 - rhoC r t τ σ (ℓ + a) with hα_def
  have hA0 : Wt (quadW ν u) 1 0 ℓ a = α * Wt ν 1 0 ℓ a - s * a * dd ν ℓ + τ' * (a.choose 2 : ℝ) * dd ν ℓ -
      c3 a * σ * dd ν ℓ := by
    rw [Wt_one_zero, Wt_one_zero, S.dd_w h, S.dd_w (by omega)]
    simp only [hα_def, hs_def, hτ']
    unfold rhoC drhoC c3
    rw [choose2_real (ℓ + a), choose3_real (ℓ + a), choose2_real ℓ, choose3_real ℓ, choose2_real a]
    push_cast; ring
  have hA0'' : Wt (quadW ν u) 1 0 (ℓ + 1) (a - 2) =
      (α + s + (((a - 1).choose 2 : ℕ) : ℝ) * σ) * Wt ν 1 0 (ℓ + 1) (a - 2) - s * ((a : ℝ) - 2) * dd ν (ℓ + 1) +
      τ' * (((a - 1).choose 2 : ℕ) : ℝ) * dd ν (ℓ + 1) - c3' a * σ * dd ν (ℓ + 1) := by
    obtain ⟨k, rfl⟩ : ∃ k, a = k + 3 := ⟨a - 3, by omega⟩
    rw [Wt_one_zero, Wt_one_zero, show ℓ + 1 + (k + 3 - 2) = ℓ + (k + 2) by omega, S.dd_w (by omega),
      S.dd_w (by omega)]
    simp only [hα_def, hs_def, hτ']
    unfold rhoC drhoC c3'
    rw [show k + 3 - 1 = k + 2 by omega, choose2_real (ℓ + (k + 2)), choose3_real (ℓ + (k + 2)),
      choose2_real (ℓ + 1), choose3_real (ℓ + 1), choose2_real (ℓ + (k + 3)), choose3_real (ℓ + (k + 3)),
      choose2_real ℓ, choose2_real (k + 2)]
    push_cast; ring
  have hB0 : rhoC r t τ σ (ℓ + 1) * Wt ν 2 0 ℓ a ≤ Wt u 2 0 ℓ a := S.B0_ge h
  have hB0' : rhoC r t τ σ (ℓ + 1) * Wt ν 2 0 (ℓ + 1) (a - 1) ≤ Wt u 2 0 (ℓ + 1) (a - 1) := by
    have h1 := S.B0_ge (ℓ := ℓ + 1) (a := a - 1) (by omega)
    have h2 : rhoC r t τ σ (ℓ + 1) ≤ rhoC r t τ σ (ℓ + 1 + 1) := S.rho_mono (by omega)
    have h3 : 0 ≤ Wt ν 2 0 (ℓ + 1) (a - 1) := Wt_nonneg S.hν _ _ _ _
    nlinarith
  have hcc : dd u (ℓ + 1) = rhoC r t τ σ (ℓ + 1) * dd ν (ℓ + 1) := S.dd_u (by omega)
  have nA0 := S.A0_nn h
  have nA0'' := S.A0_nn (show ℓ + 1 + (a - 2) ≤ N by omega)
  have hτ'0 : 0 ≤ τ' := add_nonneg S.hτ (mul_nonneg S.hσ (Nat.cast_nonneg ℓ))
  have ha1 : (0 : ℝ) ≤ (a : ℝ) - 1 := by have : (3 : ℝ) ≤ a := by exact_mod_cast ha
                                         linarith
  have hs : 0 ≤ s := add_nonneg (S.drho_nn ℓ) (mul_nonneg ha1 hτ'0)
  have hsτ : τ' * ((a : ℝ) - 1) ≤ s := by have := S.drho_nn ℓ; simp only [hs_def]; nlinarith
  have hαge := S.alpha_ge h (by omega)
  rw [drhoC_local t τ σ ℓ a (by omega)] at hαge
  have hq : ∀ α' : ℝ, s * dd ν ℓ ≤ α' * Szkraw.iterShift ν ℓ 1 →
      0 ≤ (α' * Wt ν 1 0 ℓ a - s * a * dd ν ℓ + τ' * (a.choose 2 : ℝ) * dd ν ℓ) * Wt ν 2 0 (ℓ + 1) (a - 1) +
        Wt ν 2 0 ℓ a * ((α' + s) * Wt ν 1 0 (ℓ + 1) (a - 2) - s * ((a : ℝ) - 2) * (dd ν ℓ + Szkraw.iterShift ν ℓ 1) +
          τ' * (((a - 1).choose 2 : ℕ) : ℝ) * (dd ν ℓ + Szkraw.iterShift ν ℓ 1)) -
        (dd ν ℓ + Szkraw.iterShift ν ℓ 1) * (4 * α' * sH (Szkraw.iterShift ν ℓ) a +
          2 * s * sT (Szkraw.iterShift ν ℓ) a + 4 * τ' * sZ (Szkraw.iterShift ν ℓ) a -
          τ' * sWs (Szkraw.iterShift ν ℓ) a) := fun α' h' => by
    have := quad_key_red S.hν S.hν1 ℓ a ha (α := α') (s := s) (τ := τ') hs hτ'0 h' hsτ
    rw [hD] at this; exact this
  have hΦ := Phi3_nonneg (Szkraw.iterShift ν ℓ) (S.hν.iterShift ℓ) ha
  rw [← Wt_one_lf, ← Wt_two_lf, ← Wt_two_succ_lf ν ℓ a ha, ← Wt_one_succ_lf ν ℓ a ha, ← sH_lf, hf0] at hΦ
  have hsA : sC a = (((a - 1).choose 2 : ℕ) : ℝ) := by unfold sC; rw [pred_two (by omega)]
  rw [hsA] at hΦ
  have hred := cubic_key_scalar (X := Wt ν 1 0 ℓ a) (Y := Wt ν 2 0 ℓ a) (Yp := Wt ν 2 0 (ℓ + 1) (a - 1))
    (Xp := Wt ν 1 0 (ℓ + 1) (a - 2)) (d := dd ν ℓ) (f1 := Szkraw.iterShift ν ℓ 1) (H := sH (Szkraw.iterShift ν ℓ) a)
    (T := sT (Szkraw.iterShift ν ℓ) a) (Z := sZ (Szkraw.iterShift ν ℓ) a) (W := sWs (Szkraw.iterShift ν ℓ) a)
    (T3 := lf (a + 1) (cfT3 a) (Szkraw.iterShift ν ℓ)) (E3 := lf (a + 1) (cfE3 a) (Szkraw.iterShift ν ℓ))
    (α := α) (s := s) (τ := τ') (σ := σ) (a := (a : ℝ)) (c2 := (a.choose 2 : ℝ)) (sA := (((a - 1).choose 2 : ℕ) : ℝ))
    (c3A := c3 a) (c3A' := c3' a) (S.f1_pos ℓ) S.hσ hq (by linarith) hΦ
  rw [← hD] at hred
  have hHV := cubicHV_eq r t τ σ ν ℓ a ha
  have hE := cubicE1_eq τ σ ν ℓ a ha
  rw [hf0] at hE
  have hp := (S.rho_pos (ℓ + 1)).le
  have p1 : 0 ≤ Wt (quadW ν u) 1 0 ℓ a * (Wt u 2 0 (ℓ + 1) (a - 1) -
      rhoC r t τ σ (ℓ + 1) * Wt ν 2 0 (ℓ + 1) (a - 1)) := mul_nonneg nA0 (by linarith)
  have p2 : 0 ≤ (Wt u 2 0 ℓ a - rhoC r t τ σ (ℓ + 1) * Wt ν 2 0 ℓ a) * Wt (quadW ν u) 1 0 (ℓ + 1) (a - 2) :=
    mul_nonneg (by linarith) nA0''
  have p3 := mul_nonneg hp hred
  linear_combination p1 + p2 + p3 + (-(rhoC r t τ σ (ℓ + 1) * Wt ν 2 0 (ℓ + 1) (a - 1))) * hA0 +
    (-(rhoC r t τ σ (ℓ + 1) * Wt ν 2 0 ℓ a)) * hA0'' +
    (-(2 * cubicV t τ σ ν 1 ℓ a + cubicE τ σ ν 1 ℓ a - 4 * cubicH r t τ σ ν 1 ℓ a)) * hcc +
    (rhoC r t τ σ (ℓ + 1) * dd ν (ℓ + 1)) * hHV + (-(rhoC r t τ σ (ℓ + 1) * dd ν (ℓ + 1))) * hE

end Key

end Szkraw
