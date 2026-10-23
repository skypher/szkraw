import Szkraw.LeibnizGeneral
import Szkraw.VRQuadMain

/-!
# Theorem 8.17 (cubic ratio): the ratio and its Leibniz rule

`ρ(i) = r + t i + τ C(i,2) + σ C(i,3)`, `Δρ(i) = t + τ i + σ C(i,2)`, `Δ²ρ(i) = τ + σ i`, `Δ³ρ = σ`, and
`φ_n(ℓ) = ρ(ℓ+n) f_n + n Δρ(ℓ+n-1) f_{n-1} + C(n,2) Δ²ρ(ℓ+n-2) f_{n-2} + C(n,3) σ f_{n-3}`.
-/

set_option linter.unusedSectionVars false

namespace Szkraw

open Finset

/-- The cubic ratio on `ℕ`. -/
noncomputable def rhoC (r t τ σ : ℝ) (i : ℕ) : ℝ := r + t * i + τ * (i.choose 2 : ℝ) + σ * (i.choose 3 : ℝ)

/-- `Δρ(i) = t + τ i + σ C(i,2)`. -/
noncomputable def drhoC (t τ σ : ℝ) (i : ℕ) : ℝ := t + τ * i + σ * (i.choose 2 : ℝ)

/-- `Δ²ρ(i) = τ + σ i`. -/
noncomputable def d2rhoC (τ σ : ℝ) (i : ℕ) : ℝ := τ + σ * i

/-- `φ_n(ℓ)` for the cubic ratio, in terms of `v k = f_k(ℓ)`. -/
noncomputable def PhiC (r t τ σ : ℝ) (ℓ n : ℕ) (v : ℕ → ℝ) : ℝ :=
  rhoC r t τ σ (ℓ + n) * v n + (n : ℝ) * drhoC t τ σ (ℓ + (n - 1)) * v (n - 1) +
    (n.choose 2 : ℝ) * d2rhoC τ σ (ℓ + (n - 2)) * v (n - 2) + (n.choose 3 : ℝ) * σ * v (n - 3)

theorem cast_choose_succ_two (x : ℕ) : (((x + 1).choose 2 : ℕ) : ℝ) = (x.choose 2 : ℝ) + x := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, Nat.choose_succ_succ, Nat.choose_one_right]; push_cast; ring

theorem cast_choose_succ_three (x : ℕ) : (((x + 1).choose 3 : ℕ) : ℝ) = (x.choose 3 : ℝ) + (x.choose 2 : ℝ) := by
  rw [show (3 : ℕ) = 2 + 1 from rfl, Nat.choose_succ_succ]; push_cast; ring

/-- `C(n,3) = n(n-1)(n-2)/6` in `ℝ`, for every `n`. -/
theorem choose3_real : ∀ n : ℕ, (n.choose 3 : ℝ) = (n : ℝ) * ((n : ℝ) - 1) * ((n : ℝ) - 2) / 6
  | 0 => by simp
  | n + 1 => by rw [cast_choose_succ_three, choose3_real n, choose2_real]; push_cast; ring

section Diff

variable (r t τ σ : ℝ)

theorem Dn_rhoC_one (x : ℕ) : Dn 1 (rhoC r t τ σ) x = drhoC t τ σ x := by
  rw [Dn_succ]; simp only [Dn, Function.iterate_zero, id]
  unfold rhoC drhoC; rw [cast_choose_succ_two, cast_choose_succ_three]; push_cast; ring

theorem Dn_rhoC_two (x : ℕ) : Dn 2 (rhoC r t τ σ) x = d2rhoC τ σ x := by
  rw [Dn_succ, Dn_rhoC_one, Dn_rhoC_one]
  unfold drhoC d2rhoC; rw [cast_choose_succ_two]; push_cast; ring

theorem Dn_rhoC_three (x : ℕ) : Dn 3 (rhoC r t τ σ) x = σ := by
  rw [Dn_succ, Dn_rhoC_two, Dn_rhoC_two]
  unfold d2rhoC; push_cast; ring

theorem Dn_rhoC_high : ∀ k x : ℕ, Dn (k + 4) (rhoC r t τ σ) x = 0
  | 0, x => by rw [Dn_succ, Dn_rhoC_three, Dn_rhoC_three, sub_self]
  | k + 1, x => by rw [show k + 1 + 4 = k + 4 + 1 by ring, Dn_succ, Dn_rhoC_high k, Dn_rhoC_high k, sub_self]

end Diff

/-- The cubic Leibniz rule for every order. -/
theorem leibniz_cubic (r t τ σ : ℝ) (ν : ℕ → ℝ) (n ℓ : ℕ) :
    Dn n (fun i => rhoC r t τ σ i * dd ν i) ℓ = PhiC r t τ σ ℓ n (Szkraw.iterShift ν ℓ) := by
  rw [leibniz_general (rhoC r t τ σ) (fun i => dd ν i) n ℓ]
  set g : ℕ → ℝ := fun j => (n.choose j : ℝ) * (Dn j (rhoC r t τ σ) (ℓ + (n - j)) * Dn (n - j) (fun i => dd ν i) ℓ)
    with hg
  have h1 : ∑ j ∈ range (n + 1), g j = ∑ j ∈ range (n + 1 + 3), g j := by
    conv_rhs => rw [sum_range_add]
    have : ∑ x ∈ range 3, g (n + 1 + x) = 0 :=
      sum_eq_zero fun i _ => by simp only [hg]; rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, zero_mul]
    rw [this, add_zero]
  have h2 : ∑ j ∈ range (n + 1 + 3), g j = ∑ j ∈ range 4, g j := by
    conv_lhs => rw [show n + 1 + 3 = 4 + n by ring, sum_range_add]
    have : ∑ x ∈ range n, g (4 + x) = 0 :=
      sum_eq_zero fun i _ => by simp only [hg]; rw [show 4 + i = i + 4 by ring, Dn_rhoC_high]; ring
    rw [this, add_zero]
  rw [h1, h2]
  simp only [sum_range_succ, sum_range_zero, zero_add, hg]
  have e0 : Dn 0 (rhoC r t τ σ) (ℓ + (n - 0)) = rhoC r t τ σ (ℓ + n) := by simp [Dn]
  rw [e0, Dn_rhoC_one, Dn_rhoC_two, Dn_rhoC_three]
  simp only [Dn, fwdDiff_dd]
  unfold PhiC
  rw [Nat.choose_zero_right, Nat.choose_one_right, Nat.sub_zero]
  push_cast; ring

end Szkraw
