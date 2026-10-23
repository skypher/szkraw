import Szkraw.LCConvolution
import Mathlib.Algebra.BigOperators.Intervals

/-!
# Proposition 8.14 (Walkup): log-concavity of Newton coefficients under products — groundwork

Layer-cake (Abel) decomposition of a symmetric sequence into centred intervals.
-/

namespace Szkraw

open Finset

/-- Telescoping increments of `u` starting from `0`. -/
def incr (u : ℕ → ℝ) (a : ℕ) : ℝ := u a - (if a = 0 then 0 else u (a - 1))

theorem sum_incr (u : ℕ → ℝ) : ∀ m, ∑ a ∈ range (m + 1), incr u a = u m
  | 0 => by simp [incr]
  | m + 1 => by
    rw [sum_range_succ, sum_incr u m]; simp [incr]

/-- Layer cake: for `u` symmetric on `[0, c]`,
`Σ_{i ≤ c} u i φ i = Σ_{a ≤ c/2} incr u a · Σ_{a ≤ i ≤ c - a} φ i`. -/
theorem layer_cake (c : ℕ) (u φ : ℕ → ℝ) (hsym : ∀ i ≤ c, u i = u (c - i)) :
    ∑ i ∈ range (c + 1), u i * φ i =
      ∑ a ∈ range (c / 2 + 1), incr u a * ∑ i ∈ Icc a (c - a), φ i := by
  have h1 : ∀ i ∈ range (c + 1), u i * φ i =
      (∑ a ∈ (range (c / 2 + 1)).filter (fun a => a ≤ i ∧ a ≤ c - i), incr u a) * φ i := by
    intro i hi
    simp only [mem_range] at hi
    have hm : (range (c / 2 + 1)).filter (fun a => a ≤ i ∧ a ≤ c - i) = range (min i (c - i) + 1) := by
      ext a; simp only [mem_filter, mem_range]; constructor
      · rintro ⟨_, h1, h2⟩; omega
      · intro h; refine ⟨by omega, by omega, by omega⟩
    rw [hm, sum_incr]
    congr 1
    rcases le_total i (c - i) with h | h
    · rw [min_eq_left h]
    · rw [min_eq_right h, ← hsym i (by omega)]
  rw [sum_congr rfl h1]
  simp only [sum_mul, mul_sum]
  rw [sum_comm' (t' := range (c / 2 + 1)) (s' := fun a => Icc a (c - a))]
  · intro i a
    simp only [mem_filter, mem_range, mem_Icc]
    constructor
    · rintro ⟨hi, ha, h1, h2⟩; exact ⟨⟨h1, by omega⟩, ha⟩
    · rintro ⟨⟨h1, h2⟩, ha⟩; refine ⟨by omega, ha, h1, by omega⟩

end Szkraw
