import Szkraw.ProfileCounterexamples
import Szkraw.ComboCounterexamples
import Szkraw.ParitySplit
import Szkraw.Krawtchouk

/-!
# P1: exact remarks outside the numbered results

* Footnote to the introduction: the displayed weights `C(N,n) p^(N-n) (1-p)^n` have mean `N(1-p)`, so the displayed
  `K_1(x) = (x - pN)/((1-p)N)` has `∫ K_1 dμ = (1-2p)/(1-p)` (`szwarc_footnote`).
* After Theorem 3.1: the Newton coefficients of the Krawtchouk and geometric profiles and of every admissible convex
  quadratic profile (`newton_examples`), and the mixed signs of the convex counterexamples of P3
  (`convex_counterexamples_newton_signs`).
* Section 4: the hypotheses of Szwarc's Theorem 3.3 (transcribed from his survey: `β ≡ 0`; `α_{2n}`, `α_{2n+1}`,
  `α_{2n} + γ_{2n}`, `α_{2n+1} + γ_{2n+1}` nondecreasing; `α_n ≤ γ_n`, with upward `γ` and downward `α`) for the
  array (eq:szwarc-q): the monotonicity hypotheses hold, `α_n ≤ γ_n` holds at odd `n` exactly when `p₀ ≤ 1/2` and at
  `n = 2m` exactly when `m ≤ N - m`; and `α_N ≤ γ_N` fails for every admissible finite array (`szwarc_thm33_check`).
-/

namespace Szkraw

open Finset

/-! ### The footnote -/

theorem binomial_mean (N : ℕ) (x y : ℝ) :
    ∑ n ∈ range (N + 1), (N.choose n : ℝ) * y ^ (N - n) * x ^ n * n = N * x * (x + y) ^ (N - 1) := by
  rcases N with _ | M
  · simp
  · rw [Finset.sum_range_succ', show M + 1 - 1 = M by omega, add_pow, Finset.mul_sum]
    simp only [Nat.cast_zero, mul_zero, add_zero]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' : k ≤ M := by simp at hk; omega
    have hc := Nat.add_one_mul_choose_eq M k
    have hc' : ((M + 1 : ℕ) : ℝ) * (M.choose k : ℝ) = ((M + 1).choose (k + 1) : ℝ) * ((k + 1 : ℕ) : ℝ) := by
      exact_mod_cast hc
    rw [show M + 1 - (k + 1) = M - k by omega]
    push_cast at hc' ⊢
    linear_combination (-(x ^ (k + 1) * y ^ (M - k))) * hc'

/-- **P1, footnote**: with the weights `w_n = C(N,n) p^(N-n) (1-p)^n` at the points `n`, `Σ w_n = 1`,
`Σ w_n n = N(1-p)`, and `Σ w_n K_1(n) = (1-2p)/(1-p)` for `K_1(x) = (x - pN)/((1-p)N)`. -/
theorem szwarc_footnote (N : ℕ) (hN : 1 ≤ N) (p : ℝ) (hp1 : p < 1) :
    ∑ n ∈ range (N + 1), (N.choose n : ℝ) * p ^ (N - n) * (1 - p) ^ n = 1 ∧
    ∑ n ∈ range (N + 1), (N.choose n : ℝ) * p ^ (N - n) * (1 - p) ^ n * n = N * (1 - p) ∧
    ∑ n ∈ range (N + 1), (N.choose n : ℝ) * p ^ (N - n) * (1 - p) ^ n * (((n : ℝ) - p * N) / ((1 - p) * N)) =
      (1 - 2 * p) / (1 - p) := by
  have h1 : ∑ n ∈ range (N + 1), (N.choose n : ℝ) * p ^ (N - n) * (1 - p) ^ n = 1 := by
    calc ∑ n ∈ range (N + 1), (N.choose n : ℝ) * p ^ (N - n) * (1 - p) ^ n
        = ∑ n ∈ range (N + 1), (1 - p) ^ n * p ^ (N - n) * (N.choose n : ℝ) :=
          Finset.sum_congr rfl fun n _ => by ring
      _ = (1 - p + p) ^ N := (add_pow (1 - p) p N).symm
      _ = 1 := by rw [show (1 : ℝ) - p + p = 1 by ring, one_pow]
  have h2 : ∑ n ∈ range (N + 1), (N.choose n : ℝ) * p ^ (N - n) * (1 - p) ^ n * n = N * (1 - p) := by
    rw [binomial_mean, show 1 - p + p = 1 by ring, one_pow, mul_one]
  refine ⟨h1, h2, ?_⟩
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hq : (1 : ℝ) - p ≠ 0 := by linarith
  have e : ∀ n ∈ range (N + 1), (N.choose n : ℝ) * p ^ (N - n) * (1 - p) ^ n * (((n : ℝ) - p * N) / ((1 - p) * N)) =
      ((N.choose n : ℝ) * p ^ (N - n) * (1 - p) ^ n * n - p * N * ((N.choose n : ℝ) * p ^ (N - n) * (1 - p) ^ n)) /
        ((1 - p) * N) := fun n _ => by ring
  rw [Finset.sum_congr rfl e, ← Finset.sum_div, Finset.sum_sub_distrib, h2, ← Finset.mul_sum, h1]
  field_simp
  ring

/-! ### Newton coefficients after Theorem 3.1 -/

/-- The Krawtchouk profile `i/N` has `ν = (1/N, 0, …, 0)`; the profile `[i]_q/[N]_q` of `G_{N,q,r}` (`q > 1`) has
`ν_k = (q-1)^(k-1)/[N]_q`, log-concave with equality; an admissible convex quadratic profile `ν₁ i + ν₂ C(i,2)` has
`ν_1 = ν₁`, `ν_2 = ν₂` and `ν_k = 0` for `k ≥ 3`. -/
theorem newton_examples (N : ℕ) (hN : 1 ≤ N) :
    (∀ k, 1 ≤ k → newtonCoeff (fun i => (i : ℝ) / N) k = if k = 1 then (1 : ℝ) / N else (0 : ℝ)) ∧
    (∀ q : ℝ, 1 < q → ∀ k, 1 ≤ k → newtonCoeff (fun i => qInteger q i / qInteger q N) k =
      (q - 1) ^ (k - 1) / qInteger q N) ∧
    (∀ q : ℝ, 1 < q → ∀ k, 2 ≤ k →
      (q - 1) ^ (k - 1 - 1) / qInteger q N * ((q - 1) ^ (k + 1 - 1) / qInteger q N) =
        ((q - 1) ^ (k - 1) / qInteger q N) ^ 2) ∧
    (∀ ν₁ ν₂ : ℝ, ∀ k, newtonCoeff (fun i => ν₁ * i + ν₂ * (i.choose 2 : ℝ)) k =
      if k = 1 then ν₁ else if k = 2 then ν₂ else 0) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  refine ⟨fun k hk => ?_, fun q hq k hk => ?_, fun q hq k hk => ?_, fun ν₁ ν₂ k => ?_⟩
  · rw [newtonCoeff_congr (d' := fun i => (1 / N : ℝ) * (i : ℝ) + 0) (fun i _ => by ring), newtonCoeff_lin_add,
      newtonCoeff_lin]
    have : newtonCoeff (fun _ : ℕ => (0 : ℝ)) k = 0 := by simp [newtonCoeff]
    rw [this]; split_ifs <;> ring
  · have hq1 : (q - 1) ≠ 0 := by linarith
    have hQN : qInteger q N ≠ 0 := (qInteger_pos q hq.le N (by omega)).ne'
    have e : (fun i => qInteger q i / qInteger q N) =
        fun i => (-(1 / ((q - 1) * qInteger q N))) + (1 / ((q - 1) * qInteger q N)) * q ^ i := by
      funext i
      have := qInteger_mul q i
      field_simp
      linear_combination this
    rw [e, newtonCoeff_const_geom, zero_pow (by omega)]
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [show j + 1 - 1 = j by omega, pow_succ]
    field_simp
    ring
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
    have hQN : qInteger q N ≠ 0 := (qInteger_pos q hq.le N (by omega)).ne'
    rw [show j + 2 - 1 - 1 = j by omega, show j + 2 + 1 - 1 = j + 2 by omega, show j + 2 - 1 = j + 1 by omega]
    field_simp
    ring
  · rw [newtonCoeff_congr (d' := fun i => (ν₁ - ν₂ / 2) * (i : ℝ) + (ν₂ / 2) * (i : ℝ) ^ 2)
      (fun i _ => by rw [choose2_real]; ring), newtonCoeff_eq_iter]
    rcases k with _ | _ | _ | k
    · simp
    · simp [fwdDiff]; try ring
    · simp [fwdDiff]; try ring
    · have hq : (fwdDiff 1)^[3] (fun i : ℕ => (ν₁ - ν₂ / 2) * (i : ℝ) + (ν₂ / 2) * (i : ℝ) ^ 2) = 0 := by
        funext x; simp [fwdDiff]; ring
      rw [show k + 1 + 1 + 1 = k + 3 by omega, Function.iterate_add_apply, hq]
      have h0 : ∀ m : ℕ, (fwdDiff 1)^[m] (0 : ℕ → ℝ) = 0 := by
        intro m
        induction m with
        | zero => rfl
        | succ m ih => rw [Function.iterate_succ_apply', ih]; funext x; simp [fwdDiff]
      rw [h0]; simp

/-- The convex counterexamples of P3 have Newton coefficients of both signs: `ν_8 > 0 > ν_9` (`N = 14`),
`ν_13 > 0 > ν_14` (`N = 20`), `ν_15 > 0 > ν_16` (log-convex increments, `N = 18`). -/
theorem convex_counterexamples_newton_signs :
    (0 < newtonCoeff (incProfile (kinkInc 7 (1 / 5)) 14) 8 ∧ newtonCoeff (incProfile (kinkInc 7 (1 / 5)) 14) 9 < 0) ∧
    (0 < newtonCoeff (incProfile (kinkInc 12 (1 / 20)) 20) 13 ∧
      newtonCoeff (incProfile (kinkInc 12 (1 / 20)) 20) 14 < 0) ∧
    (0 < newtonCoeff (incProfile cvxInc 18) 15 ∧ newtonCoeff (incProfile cvxInc 18) 16 < 0) := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;>
    simp only [newtonCoeff, incProfile, kinkInc, cvxInc, Finset.sum_range_succ, Finset.sum_range_zero] <;>
    norm_num [Nat.choose]

/-! ### Szwarc's Theorem 3.3 for the array (eq:szwarc-q) -/

/-- **P1, Section 4**: Szwarc's Theorem 3.3 (`x p_n = γ_n p_{n+1} + β_n p_n + α_n p_{n-1}`; hypotheses `β ≡ 0`,
`α_{2n}`, `α_{2n+1}`, `α_{2n} + γ_{2n}`, `α_{2n+1} + γ_{2n+1}` nondecreasing, `α_n ≤ γ_n`) applied to (eq:szwarc-q)
(`γ = a`, `β = b`, `α = c`, length `2N + 1`): the monotonicity hypotheses hold; `α_n ≤ γ_n` holds at odd `n` exactly
when `p₀ ≤ 1/2`, and at `n = 2m` exactly when `m ≤ N - m`; in every admissible finite array `α_N ≤ γ_N` fails. -/
theorem szwarc_thm33_check (N : ℕ) (hN : 1 ≤ N) (p : ℝ) :
    let v := szwarcCoefficients N p
    (∀ n, v.b n = 0) ∧
    (∀ m, 2 * m + 2 ≤ 2 * N → v.c (2 * m) ≤ v.c (2 * (m + 1))) ∧
    (∀ m, 2 * m + 3 ≤ 2 * N → v.c (2 * m + 1) ≤ v.c (2 * (m + 1) + 1)) ∧
    (∀ m, 2 * m + 2 ≤ 2 * N → v.c (2 * m) + v.a (2 * m) ≤ v.c (2 * (m + 1)) + v.a (2 * (m + 1))) ∧
    (∀ m, 2 * m + 3 ≤ 2 * N → v.c (2 * m + 1) + v.a (2 * m + 1) ≤ v.c (2 * (m + 1) + 1) + v.a (2 * (m + 1) + 1)) ∧
    (∀ m, 2 * m + 1 ≤ 2 * N → (v.c (2 * m + 1) ≤ v.a (2 * m + 1) ↔ p ≤ 1 / 2)) ∧
    (∀ m, m ≤ N → (v.c (2 * m) ≤ v.a (2 * m) ↔ m ≤ N - m)) ∧
    (∀ (M : ℕ) (w : Coefficients M), Admissible w → ¬ w.c M ≤ w.a M) := by
  intro v
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have ce : ∀ m, v.c (2 * m) = (m : ℝ) / N := fun m => by
    simp [v, szwarcCoefficients, Nat.mul_mod_right, Nat.mul_div_cancel_left m (show 0 < 2 by norm_num)]
  have ae : ∀ m, v.a (2 * m) = ((N : ℝ) - m) / N := fun m => by
    simp [v, szwarcCoefficients, Nat.mul_mod_right, Nat.mul_div_cancel_left m (show 0 < 2 by norm_num)]
  have co : ∀ m, v.c (2 * m + 1) = p := fun m => by
    simp [v, szwarcCoefficients, Nat.add_mod]
  have ao : ∀ m, v.a (2 * m + 1) = 1 - p := fun m => by
    simp [v, szwarcCoefficients, Nat.add_mod]
  refine ⟨fun n => rfl, fun m _ => ?_, fun m _ => ?_, fun m _ => ?_, fun m _ => ?_, fun m _ => ?_, fun m hm => ?_,
    fun M w hw => ?_⟩
  · rw [ce, ce]; push_cast; exact div_le_div_of_nonneg_right (by linarith) hN'.le
  · rw [show 2 * (m + 1) + 1 = 2 * (m + 1) + 1 from rfl, co, co]
  · rw [ce, ae, ce, ae]; push_cast; field_simp; linarith
  · rw [co, ao, co, ao]
  · rw [co, ao]; constructor <;> intro h <;> linarith
  · rw [ce, ae, div_le_div_iff_of_pos_right hN']
    constructor <;> intro h
    · have : (m : ℝ) ≤ (N : ℝ) - m := by linarith
      have h' : ((m + m : ℕ) : ℝ) ≤ N := by push_cast; linarith
      have := Nat.cast_le.1 h'
      omega
    · have : m + m ≤ N := by omega
      have h' : ((m + m : ℕ) : ℝ) ≤ N := by exact_mod_cast this
      push_cast at h'; linarith
  · obtain ⟨_, _, _, _, haN, _, _, hcpos⟩ := hw
    rw [haN]
    exact not_le.2 (hcpos M (by omega) le_rfl)

end Szkraw
