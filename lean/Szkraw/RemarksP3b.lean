import Szkraw.UniformRules
import Szkraw.ProfileCounterexamples
import Szkraw.ComboCounterexamples

/-!
# P3: the remark after Theorem 9.4, and the class of convex profiles with log-concave increments

* `known_directions_satisfy`: the Krawtchouk direction, the palindromic deformations and the tangent of the
  geometric family satisfy `L_even = L_odd = 0`; on constant rules `L_even = 2β + 3γ`, `L_odd = -γ`, which are
  independent.
* `no_open_set_of_rules`: for every `d`, no set of arrays with property (P) admits all rules of a nonempty open set of
  polynomial rules of degree at most `d`.
* `logconcave_increment_class`: convex profiles with log-concave increments (step ratios `≥ 1` and nonincreasing)
  contain the Krawtchouk, geometric and normalized quadratic profiles, and exclude the one-kink profiles.
-/

namespace Szkraw

open Finset Polynomial Filter Topology

/-! ### After Theorem 9.4 -/

theorem known_directions_satisfy :
    (Leven (fun x => x) (fun x => -x) = 0 ∧ Lodd (fun x => x) (fun x => -x) = 0) ∧
    (∀ γ : ℝ → ℝ, (∀ x, γ (1 - x) = -γ x) → γ 0 = 0 → γ 1 = 0 →
      Leven (fun _ => 0) γ = 0 ∧ Lodd (fun _ => 0) γ = 0) ∧
    (Leven (fun _ => 0) (fun x => x * (x - 1)) = 0 ∧ Lodd (fun _ => 0) (fun x => x * (x - 1)) = 0) ∧
    (∀ β γ : ℝ, Leven (fun _ => β) (fun _ => γ) = 2 * β + 3 * γ ∧ Lodd (fun _ => β) (fun _ => γ) = -γ) ∧
    (∀ β γ : ℝ, Leven (fun _ => β) (fun _ => γ) = 0 → Lodd (fun _ => β) (fun _ => γ) = 0 → β = 0 ∧ γ = 0) := by
  refine ⟨⟨by simp [Leven], by simp [Lodd]⟩, fun γ _ h0 h1 => ⟨by simp [Leven, h0, h1], by simp [Lodd, h1]⟩,
    ⟨by simp [Leven], by simp [Lodd]⟩, fun β γ => ⟨by simp [Leven]; ring, by simp [Lodd]⟩, fun β γ h1 h2 => ?_⟩
  simp only [Leven, Lodd] at h1 h2
  constructor <;> linarith

/-- The polynomial with coefficient vector `c`. -/
noncomputable def polyOf {d : ℕ} (c : Fin (d + 1) → ℝ) : ℝ[X] := ∑ i, Polynomial.C (c i) * X ^ (i : ℕ)

theorem polyOf_add_const {d : ℕ} (c : Fin (d + 1) → ℝ) (t : ℝ) (x : ℝ) :
    (polyOf (c + Pi.single 0 t)).eval x = (polyOf c).eval x + t := by
  simp only [polyOf, eval_finset_sum, eval_mul, eval_C, eval_pow, eval_X, Pi.add_apply, add_mul,
    Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_eq_single 0 (fun i _ hi => by simp [Pi.single_apply, hi]) (by simp)]
  simp

/-- **P3, after Theorem 9.4**: for every `d`, no set of arrays with property (P) admits all rules of a nonempty open
set of polynomial rules of degree at most `d` (coefficient vectors of `β` and `γ`). -/
theorem no_open_set_of_rules (d : ℕ) (S : (N : ℕ) → Set (Coefficients N))
    (hS : ∀ N, ∀ v ∈ S N, MatrixPositivity v) (U : Set ((Fin (d + 1) → ℝ) × (Fin (d + 1) → ℝ)))
    (hU : IsOpen U) (hne : U.Nonempty) :
    ¬ ∀ c ∈ U, AdmitsRule S (polyOf c.1).eval (polyOf c.2).eval := by
  intro hall
  obtain ⟨c, hc⟩ := hne
  -- the line `t ↦ c + t e₀` (constant coefficient of `β`) stays in `U` for small `t`
  have hcont : Continuous fun t : ℝ => ((c.1 + Pi.single 0 t, c.2) : (Fin (d + 1) → ℝ) × (Fin (d + 1) → ℝ)) := by
    refine Continuous.prodMk (continuous_const.add ?_) continuous_const
    exact continuous_pi fun i => by
      by_cases h : i = 0
      · subst h; simpa using continuous_id'
      · simpa [Pi.single_apply, h] using continuous_const
  have hpre : IsOpen ((fun t : ℝ => ((c.1 + Pi.single 0 t, c.2) : (Fin (d + 1) → ℝ) × (Fin (d + 1) → ℝ))) ⁻¹' U) :=
    hU.preimage hcont
  have h0 : (0 : ℝ) ∈ (fun t : ℝ => ((c.1 + Pi.single 0 t, c.2) : (Fin (d + 1) → ℝ) × (Fin (d + 1) → ℝ))) ⁻¹' U := by
    simpa using hc
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hpre 0 h0
  have ht : ε / 2 ∈ (fun t : ℝ => ((c.1 + Pi.single 0 t, c.2) : (Fin (d + 1) → ℝ) × (Fin (d + 1) → ℝ))) ⁻¹' U :=
    hball (by rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos (by linarith)]; linarith)
  have e1 := (forced_equalities _ _ S hS (hall c hc)).1
  have e2 := (forced_equalities _ _ S hS (hall _ ht)).1
  simp only [Leven, polyOf_add_const] at e1 e2
  linarith

/-! ### Convex profiles with log-concave increments -/

/-- Increments `e_i = d_i - d_{i-1}` (`1 ≤ i ≤ N`) are positive, with step ratios `e_{i+1}/e_i ≥ 1` and
nonincreasing. -/
def LogConcaveIncrements (N : ℕ) (d : ℕ → ℝ) : Prop :=
  (∀ i, 1 ≤ i → i ≤ N → 0 < d i - d (i - 1)) ∧
  (∀ i, 1 ≤ i → i + 1 ≤ N → d i - d (i - 1) ≤ d (i + 1) - d i) ∧
  (∀ i, 1 ≤ i → i + 2 ≤ N → (d (i + 2) - d (i + 1)) * (d i - d (i - 1)) ≤ (d (i + 1) - d i) ^ 2)

/-- **P3, Section 9**: the class contains the Krawtchouk profile `i/N`, the geometric profiles `[i]_q/[N]_q`
(`q > 1`) and the normalized quadratic profiles `d_κ(i/N)`, `d_κ(x) = (x + κx²)/(1 + κ)`, `κ ≥ 0`; it excludes the
one-kink profiles (`m ≥ 2` unit increments, then `1 + δ`, `δ > 0`, `m < N`). -/
theorem logconcave_increment_class (N : ℕ) (hN : 1 ≤ N) :
    LogConcaveIncrements N (fun i => (i : ℝ) / N) ∧
    (∀ q : ℝ, 1 < q → LogConcaveIncrements N (fun i => qInteger q i / qInteger q N)) ∧
    (∀ κ : ℝ, 0 ≤ κ → LogConcaveIncrements N (fun i => ((i : ℝ) / N + κ * ((i : ℝ) / N) ^ 2) / (1 + κ))) ∧
    (∀ m : ℕ, 2 ≤ m → m < N → ∀ δ : ℝ, 0 < δ → ¬ LogConcaveIncrements N (incProfile (kinkInc m δ) N)) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  refine ⟨⟨fun i h1 h2 => ?_, fun i h1 h2 => ?_, fun i h1 h2 => ?_⟩, fun q hq => ⟨fun i h1 h2 => ?_,
    fun i h1 h2 => ?_, fun i h1 h2 => ?_⟩, fun κ hκ => ⟨fun i h1 h2 => ?_, fun i h1 h2 => ?_, fun i h1 h2 => ?_⟩,
    fun m hm hmN δ hδ h => ?_⟩
  -- Krawtchouk
  · obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    simp only [Nat.add_sub_cancel]; push_cast
    rw [show ((j : ℝ) + 1) / N - j / N = 1 / N by ring]; positivity
  · obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    simp only [Nat.add_sub_cancel]; push_cast; ring_nf; exact le_rfl
  · obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    simp only [Nat.add_sub_cancel]; push_cast; ring_nf; exact le_rfl
  -- geometric
  · have hQ := qInteger_pos q hq.le N (by omega)
    obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    simp only [Nat.add_sub_cancel, qInteger]
    rw [← sub_div, show qInteger q j + q ^ j - qInteger q j = q ^ j by ring]
    have : 0 < q ^ j := by positivity
    positivity
  · have hQ := qInteger_pos q hq.le N (by omega)
    obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    simp only [Nat.add_sub_cancel, qInteger]
    rw [← sub_div, ← sub_div, show qInteger q j + q ^ j - qInteger q j = q ^ j by ring,
      show qInteger q j + q ^ j + q ^ (j + 1) - (qInteger q j + q ^ j) = q ^ (j + 1) by ring]
    exact div_le_div_of_nonneg_right (pow_le_pow_right₀ hq.le (by omega)) hQ.le
  · have hQ := qInteger_pos q hq.le N (by omega)
    obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    simp only [Nat.add_sub_cancel, qInteger]
    rw [← sub_div, ← sub_div, ← sub_div, show qInteger q j + q ^ j - qInteger q j = q ^ j by ring,
      show qInteger q j + q ^ j + q ^ (j + 1) - (qInteger q j + q ^ j) = q ^ (j + 1) by ring,
      show qInteger q j + q ^ j + q ^ (j + 1) + q ^ (j + 1 + 1) - (qInteger q j + q ^ j + q ^ (j + 1)) =
        q ^ (j + 1 + 1) by ring]
    rw [div_mul_div_comm, div_pow, ← pow_add, ← pow_mul, sq (qInteger q N),
      show j + 1 + 1 + j = (j + 1) * 2 by ring]
  -- quadratic
  · obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    simp only [Nat.add_sub_cancel]; push_cast
    rw [← sub_div, show ((j : ℝ) + 1) / N + κ * (((j : ℝ) + 1) / N) ^ 2 - ((j : ℝ) / N + κ * ((j : ℝ) / N) ^ 2) =
      (N + κ * (2 * j + 1)) / N ^ 2 by field_simp; ring]
    have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    positivity
  · obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    simp only [Nat.add_sub_cancel]; push_cast
    rw [← sub_div, ← sub_div]
    apply div_le_div_of_nonneg_right _ (by linarith)
    have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    field_simp
    nlinarith
  · obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    simp only [Nat.add_sub_cancel]; push_cast
    have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    have e : ∀ x y : ℝ, (x / N + κ * (x / N) ^ 2) / (1 + κ) - (y / N + κ * (y / N) ^ 2) / (1 + κ) =
        (x - y) * (N + κ * (x + y)) / (N ^ 2 * (1 + κ)) := fun x y => by field_simp; ring
    rw [e, e, e]
    rw [div_mul_div_comm, div_pow, show ((N : ℝ) ^ 2 * (1 + κ)) * ((N : ℝ) ^ 2 * (1 + κ)) = ((N : ℝ) ^ 2 * (1 + κ)) ^ 2
      by ring, div_le_div_iff_of_pos_right (by positivity)]
    nlinarith [mul_nonneg hκ hj, mul_nonneg (mul_nonneg hκ hκ) hj, sq_nonneg κ, mul_nonneg hκ hN'.le]
  -- one kink: step ratios `1` (at `m - 1`) then `1 + δ` (at `m`) is an increase
  · obtain ⟨-, -, h3⟩ := h
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
    set S := ∑ j ∈ range N, kinkInc (k + 2) δ j with hSdef
    have hS : 0 < S :=
      Finset.sum_pos (fun j _ => by unfold kinkInc; split_ifs <;> linarith) ⟨0, by simp; omega⟩
    have inc : ∀ i, incProfile (kinkInc (k + 2) δ) N (i + 1) - incProfile (kinkInc (k + 2) δ) N i =
        kinkInc (k + 2) δ i / S := fun i => by
      simp only [incProfile, Finset.sum_range_succ, ← sub_div, hSdef]; ring
    have := h3 (k + 1) (by omega) (by omega)
    simp only [show k + 1 - 1 = k by omega, show k + 1 + 2 = k + 2 + 1 by omega,
      show k + 1 + 1 = k + 2 by omega] at this
    rw [inc (k + 2), inc k, show k + 2 = (k + 1) + 1 by omega, inc (k + 1)] at this
    simp only [kinkInc, if_neg (show ¬ k + 1 + 1 < k + 2 by omega), if_pos (show k < k + 2 by omega),
      if_pos (show k + 1 < k + 2 by omega)] at this
    rw [div_mul_div_comm, div_pow, show S * S = S ^ 2 by ring, div_le_div_iff_of_pos_right (by positivity)] at this
    linarith

end Szkraw
