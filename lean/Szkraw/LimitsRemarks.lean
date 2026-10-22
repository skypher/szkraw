import Szkraw.AnalyticRules
import Szkraw.RadiusExp

/-!
# Consequences stated in the text of Section 9

* After Theorem 9.4: for every `d`, no set of arrays with property (P) admits all rules of a
  nonempty open set of polynomial rules of degree at most `d` (`no_open_rule_set`).
* After Proposition 9.9: the two bulk equalities reduce to `γ(0) + β(1) + γ(1) = 0`, and for
  `k ≥ 1` the boundary-layer contributions satisfy `δb_k = δb_{N-k}` and `δa_k = δc_{N-k}`
  (`boundary_layers_palindromic`).
* After Corollary 9.13: `radius_no_uniform` (in `RadiusExp.lean`).
-/

namespace Szkraw

open Finset Polynomial

/-- The polynomial `Σ_{i ≤ d} c_i X^i` with coefficient vector `c`. -/
noncomputable def coeffPoly {d : ℕ} (c : Fin (d + 1) → ℝ) : ℝ[X] :=
  ∑ i, Polynomial.C (c i) * Polynomial.X ^ (i : ℕ)

theorem coeffPoly_shift {d : ℕ} (c : Fin (d + 1) → ℝ) (t x : ℝ) :
    (coeffPoly (c + Pi.single 0 t)).eval x = (coeffPoly c).eval x + t := by
  simp only [coeffPoly, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X, Pi.add_apply, add_mul,
    sum_add_distrib]
  congr 1
  rw [sum_eq_single (0 : Fin (d + 1)) (fun i _ hi => by rw [Pi.single_eq_of_ne hi, zero_mul])
    (fun h => absurd (mem_univ _) h)]
  simp

/-- Consequence of Theorem 9.4: for every `d`, no set of arrays with property (P) admits all
rules of a nonempty open set of polynomial rules `(β, γ)` of degree at most `d` (rules given by
their coefficient vectors). -/
theorem no_open_rule_set (S : (N : ℕ) → Set (Coefficients N)) (hS : ∀ N, ∀ v ∈ S N, MatrixPositivity v)
    (d : ℕ) (U : Set ((Fin (d + 1) → ℝ) × (Fin (d + 1) → ℝ))) (hU : IsOpen U) (hne : U.Nonempty) :
    ∃ u ∈ U, ¬AdmitsRule S (coeffPoly u.1).eval (coeffPoly u.2).eval := by
  obtain ⟨u, hu⟩ := hne
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU u hu
  by_cases h0 : Leven (coeffPoly u.1).eval (coeffPoly u.2).eval = 0
  · set u' : (Fin (d + 1) → ℝ) × (Fin (d + 1) → ℝ) := (u.1 + Pi.single 0 (ε / 2), u.2)
    have hu' : u' ∈ U := by
      refine hball ?_
      rw [Metric.mem_ball, Prod.dist_eq, dist_self, dist_eq_norm]
      simp only [u', add_sub_cancel_left]
      rw [Pi.norm_single, Real.norm_eq_abs, abs_of_pos (half_pos hε), max_eq_left (half_pos hε).le]
      linarith
    refine ⟨u', hu', fun hadm => ?_⟩
    have h := (forced_equalities _ _ S hS hadm).1
    simp only [Leven, u', coeffPoly_shift] at h h0
    linarith
  · exact ⟨u, hu, fun hadm => h0 (forced_equalities _ _ S hS hadm).1⟩

/-- Consequences of Proposition 9.9 (2): `γ(0) + β(1) + γ(1) = 0`, and for `k ≥ 1` and all large
`N` the boundary-layer contributions `δb^L_n = p_n + q_{N-n}`, `δc^L_n = p'_n + q'_{N-n}`,
`δa^L_n = -δb^L_n - δc^L_n` satisfy `δb^L_k = δb^L_{N-k}` and `δa^L_k = δc^L_{N-k}`. -/
theorem boundary_layers_palindromic (S : (N : ℕ) → Set (Coefficients N))
    (hS : ∀ N, ∀ v ∈ S N, MatrixPositivity v) {β γ : ℝ → ℝ} (hβ : AnalyticOnOmega β)
    (hγ : AnalyticOnOmega γ) {p q p' q' : ℕ → ℝ} {K : ℕ} (hp : ∀ k, K < k → p k = 0)
    (hq : ∀ k, K < k → q k = 0) (hp' : ∀ k, K < k → p' k = 0) (hq' : ∀ k, K < k → q' k = 0)
    {vb vc : ℕ → ℕ → ℝ} (hvb : ∃ N₁, ∀ N, N₁ ≤ N → ∀ n, 1 ≤ n → n < N → vb N n = β (n / N) + p n + q (N - n))
    (hvc : ∃ N₁, ∀ N, N₁ ≤ N → ∀ n, 1 ≤ n → n ≤ N → vc N n = γ (n / N) + p' n + q' (N - n))
    (hfam : ContainsFamily S vb vc) :
    γ 0 + β 1 + γ 1 = 0 ∧ ∀ k, 1 ≤ k → ∀ N, k + K + 1 ≤ N →
      p k + q (N - k) = p (N - k) + q (N - (N - k)) ∧
        -(p k + q (N - k)) - (p' k + q' (N - k)) = p' (N - k) + q' (N - (N - k)) := by
  obtain ⟨he, ho, hpq, hp'q'⟩ := families_boundary_layers S hS hβ hγ hp hq hp' hq' hvb hvc hfam
  refine ⟨by rw [Leven] at he; rw [Lodd] at ho; linarith, fun k hk N hN => ?_⟩
  rw [show N - (N - k) = k by omega, hp (N - k) (by omega), hq (N - k) (by omega), hp' (N - k) (by omega),
    hq' (N - k) (by omega), hpq k hk]
  have := hp'q' k hk
  rw [hpq k hk] at this
  constructor <;> linarith

end Szkraw
