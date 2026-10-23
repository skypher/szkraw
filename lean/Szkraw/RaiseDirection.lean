import Szkraw.RaiseTopMass
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp

/-!
# P3, Section 9: the raising direction at fixed `r` is not a uniform rule

At fixed `0 < r ≤ 1`, raising the top mass of `K_{N,r}` to `(1 + τ) w_0` gives the normalized array
`raisedKraw N r τ` of P1's Proposition 5.2 (`RaiseTopMass.lean`; Proposition 9.12 of `paper.tex`), with masses
`w_n = C(N,n) r^{N-n} / (1+r)^N`.

* `raise_direction`: at `τ = 0` the coefficients move in the direction
  `δc_n = (r n/N)(w_0 + w_n)`, `δb_n = ((N-n)/N - r n/N) w_n - ((N-n)/N + r n/N) w_0`,
  the binomial profile of the masses.
* `raise_not_uniform`: for every reparametrization `τ = s_N t` with `s_N ≠ 0` (in particular the relative `τ`,
  the additive mass `ε = τ w_0`, and their negatives), the velocity at `t = 0` is not a uniform rule
  `δb_n = β(n/N)`, `δc_n = γ(n/N)` (P3, Definition 9.3) for all `N ≥ N₀`, whatever `N₀`. The test compares the
  ratio `δb_1/δc_1` at size `N` with `δb_2/δc_2` at size `2N` (both at `n/N = 1/N`), which is free of the
  scalings.
-/

namespace Szkraw

open Finset

variable {N : ℕ} {r : ℝ}

/-- The binomial masses `w_n = C(N,n) r^{N-n} / (1+r)^N` of `K_{N,r}`. -/
noncomputable def raiseMass (N : ℕ) (r : ℝ) (n : ℕ) : ℝ := (N.choose n : ℝ) * r ^ (N - n) / (1 + r) ^ N

section general

variable (v : Coefficients N) (x w : Fin (N + 1) → ℝ) (w0 : ℝ)

theorem Aeps_scaled_hasDerivAt (n : ℕ) :
    HasDerivAt (fun τ => Aeps v x w (τ * w0) n) (w0 * Ssum v x w n) 0 := by
  have h := ((hasDerivAt_id (0 : ℝ)).mul_const (w0 * Ssum v x w n)).const_add 1
  simp only [Aeps]
  exact (h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun τ => by simp only [id]; ring)).congr_deriv
    (by ring)

theorem Aeps_scaled_zero (n : ℕ) : Aeps v x w (0 * w0) n = 1 := by simp [Aeps]

/-- First-order change of the affine-normalized array `epsNorm` when the top mass changes by `τ w0`. -/
theorem epsNorm_scaled_hasDerivAt (n : ℕ) :
    HasDerivAt (fun τ => (epsNorm v x w (τ * w0)).b n)
      (w0 * (-(v.a n + v.c n) + (v.a n - v.c n) * piw v x w n)) 0 ∧
    HasDerivAt (fun τ => (epsNorm v x w (τ * w0)).c n) (w0 * v.c n * (1 + piw v x w n)) 0 := by
  have hA := Aeps_scaled_hasDerivAt v x w w0
  have h0 := Aeps_scaled_zero v x w w0
  have hS : Ssum v x w (n + 1) = Ssum v x w n + piw v x w n := by simp only [Ssum, sum_range_succ]
  have hR1 : HasDerivAt (fun τ => Aeps v x w (τ * w0) n / Aeps v x w (τ * w0) (n + 1)) (-(w0 * piw v x w n)) 0 := by
    have h := (hA n).div (hA (n + 1)) (by rw [h0]; norm_num)
    rw [h0, h0, hS] at h
    exact h.congr_deriv (by ring)
  have hR2 : HasDerivAt (fun τ => Aeps v x w (τ * w0) (n + 1) / Aeps v x w (τ * w0) n) (w0 * piw v x w n) 0 := by
    have h := (hA (n + 1)).div (hA n) (by rw [h0]; norm_num)
    rw [h0, h0, hS] at h
    exact h.congr_deriv (by ring)
  have hε : HasDerivAt (fun τ : ℝ => 1 + τ * w0) w0 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const w0).const_add 1
  have hεz : HasDerivAt (fun τ : ℝ => τ * w0) w0 0 := by simpa using (hasDerivAt_id (0 : ℝ)).mul_const w0
  have hR10 : Aeps v x w (0 * w0) n / Aeps v x w (0 * w0) (n + 1) = 1 := by rw [h0, h0]; norm_num
  have hR20 : Aeps v x w (0 * w0) (n + 1) / Aeps v x w (0 * w0) n = 1 := by rw [h0, h0]; norm_num
  constructor
  · have h := (hε.mul (((hasDerivAt_const (0 : ℝ) (1 : ℝ)).sub (hR1.const_mul (v.a n))).sub
      (hR2.const_mul (v.c n)))).sub hεz
    refine (h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun τ => ?_)).congr_deriv ?_
    · simp only [epsNorm, epsRaw, Pi.mul_apply, Pi.sub_apply]; ring
    · simp only [Pi.sub_apply, hR10, hR20]; ring
  · have h := hε.mul (hR2.const_mul (v.c n))
    refine (h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun τ => ?_)).congr_deriv ?_
    · simp only [epsNorm, epsRaw, Pi.mul_apply]; ring
    · simp only [hR20]; ring

end general

/-- **P3, Section 9 (raising at fixed `r`)**: for `0 < r ≤ 1` and `n ≤ N`, raising the top mass of `K_{N,r}` to
`(1 + τ) w_0` (`raisedKraw`, P1 Proposition 5.2) moves the coefficients at `τ = 0` in the direction
`δb_n = ((N-n)/N - r n/N) w_n - ((N-n)/N + r n/N) w_0`, `δc_n = (r n/N)(w_0 + w_n)`, where
`w_n = C(N,n) r^{N-n} / (1+r)^N` are the binomial masses. -/
theorem raise_direction (hN : 1 ≤ N) (hr : 0 < r) (hr1 : r ≤ 1) (n : ℕ) (hn : n ≤ N) :
    HasDerivAt (fun τ => (raisedKraw N r τ).b n)
      ((((N : ℝ) - n) / N - r * n / N) * raiseMass N r n - (((N : ℝ) - n) / N + r * n / N) * raiseMass N r 0) 0 ∧
    HasDerivAt (fun τ => (raisedKraw N r τ).c n) (r * n / N * (raiseMass N r 0 + raiseMass N r n)) 0 := by
  have hr0 := hr.ne'
  have h1r : (1 + r) ≠ 0 := by linarith
  have hwn : kw N r 0 * piw (kv N r) (kx N r) (kw N r) n = raiseMass N r n := by
    rw [k_piw hN hr hr1 n hn, k_w0 hr]
    obtain ⟨k, rfl⟩ : ∃ k, N = n + k := ⟨N - n, by omega⟩
    simp only [raiseMass, Nat.add_sub_cancel_left, div_pow, pow_add]
    field_simp
  have hw0 : kw N r 0 = raiseMass N r 0 := by
    rw [k_w0 hr]; simp only [raiseMass, Nat.choose_zero_right, Nat.cast_one, Nat.sub_zero, one_mul, div_pow]
  have h := epsNorm_scaled_hasDerivAt (kv N r) (kx N r) (kw N r) (kw N r 0) n
  rw [kv_a n hn, kv_c n] at h
  refine ⟨h.1.congr_deriv ?_, h.2.congr_deriv ?_⟩
  · rw [← hwn, ← hw0]; ring
  · rw [← hwn, ← hw0]; ring

/-- Equal pairs `(β, γ) = s₁ (b₁, c₁) = s₂ (b₂, c₂)` force `s₁ s₂ (b₁ c₂ - c₁ b₂) = 0`. -/
theorem det_of_ratio {s₁ s₂ b₁ c₁ b₂ c₂ β γ : ℝ} (h1 : β = s₁ * b₁) (h2 : γ = s₁ * c₁) (h3 : β = s₂ * b₂)
    (h4 : γ = s₂ * c₂) : s₁ * s₂ * (b₁ * c₂ - c₁ * b₂) = 0 := by
  linear_combination (-(s₁ * c₁)) * (h3.symm.trans h1) + (s₁ * b₁) * (h4.symm.trans h2)

/-- **P3, Section 9**: at every fixed `0 < r ≤ 1`, the deformation raising the top mass of `K_{N,r}` is not a
uniform rule, from any starting size `N₀` on and in any parametrization: for every `s_N ≠ 0` (`N ≥ N₀`), the
velocity of `t ↦ raisedKraw N r (s_N t)` at `t = 0` is not of the form `δb_n = β(n/N)` (`1 ≤ n < N`),
`δc_n = γ(n/N)` (`1 ≤ n ≤ N`) for all `N ≥ N₀`. This covers the relative `τ` (`s_N = 1`), the additive mass
`ε = τ w_0` (`s_N = 1/w_0`), and lowering (`s_N < 0`). The ratio `δb_n/δc_n` at `n/N = 1/N` differs between the
sizes `N` and `2N` for every `N ≥ 2`. -/
theorem raise_not_uniform (hr : 0 < r) (hr1 : r ≤ 1) (N₀ : ℕ) (s : ℕ → ℝ) (hs : ∀ N, N₀ ≤ N → s N ≠ 0) :
    ¬ ∃ β γ : ℝ → ℝ, ∀ N : ℕ, N₀ ≤ N →
      (∀ n, 1 ≤ n → n < N → HasDerivAt (fun t => (raisedKraw N r (s N * t)).b n) (β (n / N)) 0) ∧
      (∀ n, 1 ≤ n → n ≤ N → HasDerivAt (fun t => (raisedKraw N r (s N * t)).c n) (γ (n / N)) 0) := by
  rintro ⟨β, γ, h⟩
  have vel : ∀ N n : ℕ, N₀ ≤ N → 1 ≤ N → 1 ≤ n → n < N →
      β (n / N) = s N * ((((N : ℝ) - n) / N - r * n / N) * raiseMass N r n -
        (((N : ℝ) - n) / N + r * n / N) * raiseMass N r 0) ∧
      γ (n / N) = s N * (r * n / N * (raiseMass N r 0 + raiseMass N r n)) := by
    intro N n hN0 hN hn hnN
    have hd := raise_direction hN hr hr1 n hnN.le
    have hs' : HasDerivAt (fun t : ℝ => s N * t) (s N) 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).const_mul (s N)
    have hb := (hd.1.scomp_of_eq 0 hs' (by simp)).congr_deriv (smul_eq_mul _ _)
    have hc := (hd.2.scomp_of_eq 0 hs' (by simp)).congr_deriv (smul_eq_mul _ _)
    exact ⟨((h N hN0).1 n hn hnN).unique (by simpa [Function.comp_def, mul_comm] using hb),
      ((h N hN0).2 n hn hnN.le).unique (by simpa [Function.comp_def, mul_comm] using hc)⟩
  obtain ⟨k, hk⟩ : ∃ k, N₀ + 2 = k + 1 := ⟨N₀ + 1, rfl⟩
  set M := N₀ + 2 with hM
  have e1 := vel M 1 (by omega) (by omega) le_rfl (by omega)
  have e2 := vel (2 * M) 2 (by omega) (by omega) (by norm_num) (by omega)
  have hr0 := hr.ne'
  have h1r : (0 : ℝ) < 1 + r := by linarith
  have hMr : (2 : ℝ) ≤ M := by exact_mod_cast (show 2 ≤ M by omega)
  have hx : ((2 : ℕ) : ℝ) / ((2 * M : ℕ) : ℝ) = ((1 : ℕ) : ℝ) / (M : ℝ) := by
    push_cast; field_simp
  rw [hx] at e2
  have hs1 := hs M (by omega)
  have hs2 := hs (2 * M) (by omega)
  have hw1 : raiseMass M r 1 = raiseMass M r 0 * (M / r) := by
    simp only [raiseMass, Nat.choose_one_right, Nat.choose_zero_right, Nat.cast_one, Nat.sub_zero,
      hk, pow_succ]
    push_cast; field_simp
  have hw2 : raiseMass (2 * M) r 2 = raiseMass (2 * M) r 0 * (M * (2 * M - 1) / r ^ 2) := by
    rw [raiseMass, raiseMass, show 2 * M - 2 = 2 * k by omega, Nat.cast_choose_two, Nat.choose_zero_right,
      Nat.sub_zero, hk]
    push_cast; field_simp; ring
  have hu : 0 < raiseMass M r 0 := by simp only [raiseMass, Nat.choose_zero_right, Nat.cast_one]; positivity
  have hv : 0 < raiseMass (2 * M) r 0 := by simp only [raiseMass, Nat.choose_zero_right, Nat.cast_one]; positivity
  rw [hw1] at e1
  rw [hw2] at e2
  push_cast at e1 e2
  have det := det_of_ratio e1.1 e1.2 e2.1 e2.2
  rcases mul_eq_zero.1 det with h0 | h0
  · exact mul_ne_zero hs1 hs2 h0
  set u := raiseMass M r 0
  set v := raiseMass (2 * M) r 0
  have hM0 : (M : ℝ) ≠ 0 := by linarith
  field_simp at h0
  -- the determinant is `u v · 2 M r (M - 1)(r - 2M + 1)`, and `r - 2M + 1 < 0`
  have hE : u * v * (2 * M * r * ((M : ℝ) - 1) * (2 * M - 1 - r)) = 0 := by linear_combination -h0
  have hpos : 0 < u * v * (2 * M * r * ((M : ℝ) - 1) * (2 * M - 1 - r)) := by
    have h1 : 0 < (M : ℝ) - 1 := by linarith
    have h2 : 0 < 2 * (M : ℝ) - 1 - r := by linarith
    positivity
  exact hpos.ne' hE

end Szkraw
