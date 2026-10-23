import Szkraw.LeibnizGeneral
import Szkraw.NewtonProduct

/-!
# Theorem 8.16, setup: facts about a ratio with log-concave Newton coefficients

`P_k(x) = Σ_h C(x,h) ρ_{k+h}` (`iterShift ρ x k`) is log-concave without internal zeros in `k`,
`n ↦ ρ(n) = P_0(n)` is log-concave, and the two inequalities (8.7) hold.
-/

namespace Szkraw

open Finset

variable {ρ : ℕ → ℝ}

/-- `P_k(x)`. -/
noncomputable abbrev Pk (ρ : ℕ → ℝ) (x k : ℕ) : ℝ := Szkraw.iterShift ρ x k

theorem Pk_succ_x (ρ : ℕ → ℝ) (x k : ℕ) : Pk ρ (x + 1) k = Pk ρ x k + Pk ρ x (k + 1) := rfl

/-- `n ↦ ρ(n) = P_0(n)` is log-concave. -/
theorem rho_lc (hρ : LCNZ ρ) (n : ℕ) : Pk ρ n 0 * Pk ρ (n + 2) 0 ≤ Pk ρ (n + 1) 0 ^ 2 := by
  have h2 : Pk ρ (n + 2) 0 = Pk ρ n 0 + 2 * Pk ρ n 1 + Pk ρ n 2 := by
    show Pk ρ (n + 1 + 1) 0 = _
    rw [Pk_succ_x, Pk_succ_x, Pk_succ_x]; ring
  rw [h2, Pk_succ_x]
  have := (hρ.iterShift n).2.1 0
  simp only [zero_add] at this
  nlinarith [this]

/-- Log-concavity of `x ↦ ρ(x)` across distant arguments: `ρ(x) ρ(y+1) ≤ ρ(x+1) ρ(y)` for `x ≤ y`,
when `ρ` is positive. -/
theorem rho_ratio (hρ : LCNZ ρ) (hpos : ∀ n, 0 < Pk ρ n 0) {x y : ℕ} (hxy : x ≤ y) :
    Pk ρ x 0 * Pk ρ (y + 1) 0 ≤ Pk ρ (x + 1) 0 * Pk ρ y 0 := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hxy
  induction d with
  | zero => simp [mul_comm]
  | succ d ih =>
    have h1 := ih (by omega)
    have h2 := rho_lc hρ (x + d)
    have p1 := hpos (x + d + 1)
    have n2 : 0 ≤ Pk ρ (x + d + 2) 0 := (hpos _).le
    have n3 : 0 ≤ Pk ρ (x + 1) 0 := (hpos _).le
    rw [show x + (d + 1) + 1 = x + d + 2 by omega, show x + (d + 1) = x + d + 1 by omega]
    have A := mul_le_mul_of_nonneg_right h1 n2
    have B := mul_le_mul_of_nonneg_left h2 n3
    have key : Pk ρ x 0 * Pk ρ (x + d + 2) 0 * Pk ρ (x + d + 1) 0 ≤
        Pk ρ (x + 1) 0 * Pk ρ (x + d + 1) 0 * Pk ρ (x + d + 1) 0 := by nlinarith [A, B]
    exact le_of_mul_le_mul_right key p1

/-- Log-concavity in `k`: `P_0 P_{m+1} ≤ P_1 P_m`. -/
theorem Pk_shift_le (hρ : LCNZ ρ) (y m : ℕ) : Pk ρ y 0 * Pk ρ y (m + 1) ≤ Pk ρ y 1 * Pk ρ y m := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · rw [mul_comm]
  · have := (hρ.iterShift y).balanced 1 1 m le_rfl hm
    simpa using this

/-- The first inequality of (8.7): `ρ(x) P_m(y+1) ≤ ρ(x+1) P_m(y)` for `x ≤ y`. -/
theorem ratio_ineq1 (hρ : LCNZ ρ) (hpos : ∀ n, 0 < Pk ρ n 0) {x y : ℕ} (hxy : x ≤ y) (m : ℕ) :
    Pk ρ x 0 * Pk ρ (y + 1) m ≤ Pk ρ (x + 1) 0 * Pk ρ y m := by
  have h1 : Pk ρ y 0 * Pk ρ (y + 1) m ≤ Pk ρ (y + 1) 0 * Pk ρ y m := by
    rw [Pk_succ_x, Pk_succ_x]
    have := Pk_shift_le hρ y m
    nlinarith [this]
  have h2 := rho_ratio hρ hpos hxy
  have py := hpos y
  have nx : 0 ≤ Pk ρ x 0 := (hpos x).le
  have nm : 0 ≤ Pk ρ y m := (hρ.iterShift y).1 m
  have key : Pk ρ x 0 * Pk ρ (y + 1) m * Pk ρ y 0 ≤ Pk ρ (x + 1) 0 * Pk ρ y m * Pk ρ y 0 := by
    nlinarith [mul_le_mul_of_nonneg_left h1 nx, mul_le_mul_of_nonneg_right h2 nm]
  exact le_of_mul_le_mul_right key py

/-- The second inequality of (8.7): `ρ(x) P_{m+1}(y) ≤ Δρ(x) P_m(y)` for `x ≤ y`. -/
theorem ratio_ineq2 (hρ : LCNZ ρ) (hpos : ∀ n, 0 < Pk ρ n 0) {x y : ℕ} (hxy : x ≤ y) (m : ℕ) :
    Pk ρ x 0 * Pk ρ y (m + 1) ≤ Pk ρ x 1 * Pk ρ y m := by
  have h2 := rho_ratio hρ hpos hxy
  rw [Pk_succ_x, Pk_succ_x] at h2
  -- ρ(x) P_1(y) ≤ P_1(x) ρ(y)
  have h3 : Pk ρ x 0 * Pk ρ y 1 ≤ Pk ρ x 1 * Pk ρ y 0 := by nlinarith [h2]
  have h1 := Pk_shift_le hρ y m
  have py := hpos y
  have nx : 0 ≤ Pk ρ x 0 := (hpos x).le
  have nm : 0 ≤ Pk ρ y m := (hρ.iterShift y).1 m
  have key : Pk ρ x 0 * Pk ρ y (m + 1) * Pk ρ y 0 ≤ Pk ρ x 1 * Pk ρ y m * Pk ρ y 0 := by
    nlinarith [mul_le_mul_of_nonneg_left h1 nx, mul_le_mul_of_nonneg_right h3 nm]
  exact le_of_mul_le_mul_right key py

end Szkraw
