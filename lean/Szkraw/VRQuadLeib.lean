import Szkraw.VRQuadB2
import Szkraw.VRQuadProfile

/-!
# Theorem 8.11: finite differences and the quadratic Leibniz rule

`Δ^k (dd ν) ℓ = iterShift ν ℓ k`, and for `c_i = ρ(i) d_i` with `ρ(x) = r + t x + τ C(x,2)`:
`Δ^n c(ℓ) = Φ_n(ℓ, f(ℓ))` for every `n`, where `f(ℓ)_k = iterShift ν ℓ k`.
-/

set_option linter.unusedSectionVars false

namespace Szkraw

open Finset

theorem fwdDiff_dd (ν : ℕ → ℝ) : ∀ k ℓ : ℕ,
    (fwdDiff 1)^[k] (fun i => dd ν i) ℓ = Szkraw.iterShift ν ℓ k
  | 0, ℓ => rfl
  | k + 1, ℓ => by
    rw [fwdDiff_iter_succ, fwdDiff_dd ν k (ℓ + 1), fwdDiff_dd ν k ℓ]
    show Szkraw.iterShift ν ℓ k + Szkraw.iterShift ν ℓ (k + 1) - Szkraw.iterShift ν ℓ k = _
    ring

/-- The ratio as a function on `ℕ`. -/
noncomputable def rhoN (r t τ : ℝ) (i : ℕ) : ℝ := r + t * i + τ * (i.choose 2 : ℝ)

theorem rhoN_eq (r t τ : ℝ) (i : ℕ) : rhoN r t τ i = rhoQ r t τ i := by
  unfold rhoN rhoQ; rw [choose2_real]

/-- The quadratic Leibniz rule for every order. -/
theorem leibniz_quad (r t τ : ℝ) (ν : ℕ → ℝ) (n ℓ : ℕ) :
    (fwdDiff 1)^[n] (fun i => rhoN r t τ i * dd ν i) ℓ = PhiQ r t τ ℓ n (Szkraw.iterShift ν ℓ) := by
  rcases n with _ | _ | k
  · show rhoN r t τ ℓ * dd ν ℓ = _
    unfold PhiQ; rw [rhoN_eq]; simp; left; rfl
  · rw [fwdDiff_iter_succ]
    simp only [Function.iterate_zero, id]
    unfold PhiQ
    rw [rhoN_eq, rhoN_eq]
    have e : dd ν (ℓ + 1) = dd ν ℓ + Szkraw.iterShift ν ℓ 1 := rfl
    rw [e]
    simp only [Nat.cast_add, Nat.cast_one, zero_add, Nat.sub_self]
    have h0 : dd ν ℓ = Szkraw.iterShift ν ℓ 0 := rfl
    rw [← h0]
    unfold rhoQ drhoQ
    ring
  · have h := fwdDiff_quad_mul r t τ (fun i => dd ν i) k ℓ
    have e : (fun i : ℕ => rhoN r t τ i * dd ν i) = fun i : ℕ => (r + t * i + τ * (i.choose 2 : ℝ)) * dd ν i := rfl
    rw [show k + 1 + 1 = k + 2 by ring, e, h, fwdDiff_dd, fwdDiff_dd, fwdDiff_dd]
    unfold PhiQ
    rw [show k + 2 - 1 = k + 1 by omega, show k + 2 - 2 = k by omega, choose2_real]
    unfold rhoQ drhoQ
    push_cast; ring

end Szkraw
