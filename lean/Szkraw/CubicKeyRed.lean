import Szkraw.CubicDetours
import Szkraw.CubicKeyForms

/-!
# Theorem 8.17: the reduced key inequality

With `B₀ ≥ ρ(ℓ+1)Y` the key reduces to `R ≥ 0`, which is affine in `α = 1 - ρ(ℓ+a)` and linear in the local
coefficients `P₁ = Δρ(ℓ)`, `P₂ = Δ²ρ(ℓ)`, `P₃ = σ`. Its `σ`-free part is `quad_key_red` (Theorem 8.11), applied at
`α_q = α - C(a-1,2) σ u₀/u₁`, and `u₁ R = u₁ R_quad(α_q) + σ Φ̃₃` with `Φ̃₃ ≥ 0` (`Phi3_nonneg`).
-/

set_option linter.unusedSectionVars false

namespace Szkraw

/-- The scalar core: `quad_key_red` at `α_q` and `Φ̃₃ ≥ 0` give the cubic reduced key. -/
theorem cubic_key_scalar {X Y Yp Xp d f1 H T Z W T3 E3 α s τ σ a c2 sA c3A c3A' : ℝ} (hf1 : 0 < f1) (hσ : 0 ≤ σ)
    (hq : ∀ α' : ℝ, s * d ≤ α' * f1 → 0 ≤ (α' * X - s * a * d + τ * c2 * d) * Yp +
      Y * ((α' + s) * Xp - s * (a - 2) * (d + f1) + τ * sA * (d + f1)) -
      (d + f1) * (4 * α' * H + 2 * s * T + 4 * τ * Z - τ * W))
    (hα : (s + sA * σ) * d ≤ α * f1)
    (hΦ : 0 ≤ f1 * (-c3A * d * Yp + Y * (sA * Xp - c3A' * (d + f1)) - (d + f1) * (4 * T3 - (c3A * d + E3))) +
      sA * d * (X * Yp + Y * Xp - 4 * (d + f1) * H)) :
    0 ≤ (α * X - s * a * d + τ * c2 * d - c3A * σ * d) * Yp +
      Y * ((α + s + sA * σ) * Xp - s * (a - 2) * (d + f1) + τ * sA * (d + f1) - c3A' * σ * (d + f1)) -
      (d + f1) * (4 * α * H + 2 * s * T + 4 * τ * Z - τ * W + σ * (4 * T3 - (c3A * d + E3))) := by
  obtain ⟨αq, hαq⟩ : ∃ x : ℝ, x = α - sA * σ * d / f1 := ⟨_, rfl⟩
  have hmul : αq * f1 = α * f1 - sA * σ * d := by rw [hαq]; field_simp
  have h1 := hq αq (by rw [hmul]; linarith)
  have key : f1 * ((α * X - s * a * d + τ * c2 * d - c3A * σ * d) * Yp +
      Y * ((α + s + sA * σ) * Xp - s * (a - 2) * (d + f1) + τ * sA * (d + f1) - c3A' * σ * (d + f1)) -
      (d + f1) * (4 * α * H + 2 * s * T + 4 * τ * Z - τ * W + σ * (4 * T3 - (c3A * d + E3)))) =
      f1 * ((αq * X - s * a * d + τ * c2 * d) * Yp +
        Y * ((αq + s) * Xp - s * (a - 2) * (d + f1) + τ * sA * (d + f1)) -
        (d + f1) * (4 * αq * H + 2 * s * T + 4 * τ * Z - τ * W)) +
      σ * (f1 * (-c3A * d * Yp + Y * (sA * Xp - c3A' * (d + f1)) - (d + f1) * (4 * T3 - (c3A * d + E3))) +
        sA * d * (X * Yp + Y * Xp - 4 * (d + f1) * H)) := by
    have e : f1 * αq = α * f1 - sA * σ * d := by rw [mul_comm]; exact hmul
    linear_combination (-(X * Yp + Y * Xp - 4 * (d + f1) * H)) * e
  have h2 : 0 ≤ f1 * ((α * X - s * a * d + τ * c2 * d - c3A * σ * d) * Yp +
      Y * ((α + s + sA * σ) * Xp - s * (a - 2) * (d + f1) + τ * sA * (d + f1) - c3A' * σ * (d + f1)) -
      (d + f1) * (4 * α * H + 2 * s * T + 4 * τ * Z - τ * W + σ * (4 * T3 - (c3A * d + E3)))) := by
    rw [key]; exact add_nonneg (mul_nonneg hf1.le h1) (mul_nonneg hσ hΦ)
  exact (mul_nonneg_iff_of_pos_left hf1).1 h2

end Szkraw
