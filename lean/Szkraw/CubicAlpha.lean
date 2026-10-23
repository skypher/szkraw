import Szkraw.CubicDetours
import Szkraw.CubicKeyForms
set_option linter.unusedSectionVars false
namespace Szkraw
open Finset

/-- `ρ(m+1) = ρ(m) + Δρ(m)` for the cubic ratio. -/
theorem rhoC_succ (r t τ σ : ℝ) (m : ℕ) : rhoC r t τ σ (m + 1) = rhoC r t τ σ m + drhoC t τ σ m := by
  unfold rhoC drhoC
  rw [cast_choose_succ_two, cast_choose_succ_three]
  push_cast; ring

section Alpha
variable {N : ℕ} {r t τ σ : ℝ} {ν u : ℕ → ℝ} (S : CubicSetting N r t τ σ ν u)
include S

/-- `α u₁ ≥ s u₀` with `α = 1 - ρ(ℓ+a)`, `s = Δρ(ℓ+a-1)`, from the monotonicity of `b` at `ℓ+a-1`. -/
theorem CubicSetting.alpha_ge {ℓ a : ℕ} (h : ℓ + a ≤ N) (ha : 1 ≤ a) :
    drhoC t τ σ (ℓ + a - 1) * dd ν ℓ ≤ (1 - rhoC r t τ σ (ℓ + a)) * Szkraw.iterShift ν ℓ 1 := by
  obtain ⟨m, hm⟩ : ∃ m, ℓ + a = m + 1 := ⟨ℓ + a - 1, by omega⟩
  have hstep := S.hb m (by omega)
  rw [S.dd_w (by omega), S.dd_w (by omega)] at hstep
  have e1 : dd ν (m + 1) = dd ν m + Szkraw.iterShift ν m 1 := rfl
  rw [e1] at hstep
  have hm1 : ℓ + a - 1 = m := by omega
  rw [hm1, hm]
  have hr := rhoC_succ r t τ σ m
  have hb' : drhoC t τ σ m * dd ν m ≤ (1 - rhoC r t τ σ (m + 1)) * Szkraw.iterShift ν m 1 := by
    rw [hr] at hstep ⊢
    linear_combination hstep
  have hΔ := S.drho_nn m
  have hch := R_chain_of S.hν S.hν1 ℓ (m - ℓ)
  rw [show ℓ + (m - ℓ) = m by omega] at hch
  have hfm := S.f1_pos m
  have hfl := S.f1_pos ℓ
  have k1 : drhoC t τ σ m * (dd ν ℓ * Szkraw.iterShift ν m 1) ≤
      drhoC t τ σ m * (dd ν m * Szkraw.iterShift ν ℓ 1) := mul_le_mul_of_nonneg_left hch hΔ
  have k2 : drhoC t τ σ m * dd ν m * Szkraw.iterShift ν ℓ 1 ≤
      (1 - rhoC r t τ σ (m + 1)) * Szkraw.iterShift ν m 1 * Szkraw.iterShift ν ℓ 1 :=
    mul_le_mul_of_nonneg_right hb' hfl.le
  have k3 : drhoC t τ σ m * dd ν ℓ * Szkraw.iterShift ν m 1 ≤
      (1 - rhoC r t τ σ (m + 1)) * Szkraw.iterShift ν ℓ 1 * Szkraw.iterShift ν m 1 := by
    linear_combination k1 + k2
  exact le_of_mul_le_mul_right k3 hfm

end Alpha
end Szkraw
