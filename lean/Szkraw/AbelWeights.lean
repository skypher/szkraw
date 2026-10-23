import Szkraw.NewtonProduct

/-!
# Lemma 8.15: the Abel criterion for quadratic forms in log-concave sequences

For a fixed weight `W`, the products `u_i u_{W-i}` (`2i ≤ W`) of an `LCNZ` sequence increase towards the
centre. Hence `Σ_{2i ≤ W} q_i u_i u_{W-i} ≥ 0` whenever all tail sums from the centre are `≥ 0`; if
`q_0 ≤ 0` and `q_i ≥ 0` for `i ≥ 2`, the full sum suffices (Wang–Yeh, Lemma 2.1 and Corollary 2.6).
-/

namespace Szkraw

open Finset

/-- Products `u_i u_{W-i}` increase towards the centre. -/
theorem LCNZ.pair_mono {u : ℕ → ℝ} (hu : LCNZ u) {W i : ℕ} (hi : 2 * (i + 1) ≤ W) :
    u i * u (W - i) ≤ u (i + 1) * u (W - (i + 1)) := by
  have := hu.balanced 1 (i + 1) (W - (i + 1)) (by omega) (by omega)
  have e1 : i + 1 - 1 = i := by omega
  have e2 : W - (i + 1) + 1 = W - i := by omega
  rw [e1, e2] at this; exact this

/-- Abel summation: with nonnegative nondecreasing weights `p` and nonnegative tail sums of `q`,
`Σ_{i ≤ n} q_i p_i ≥ 0`. -/
theorem abel_tails (n : ℕ) (q p : ℕ → ℝ) (hp0 : 0 ≤ p 0) (hp : ∀ i, i + 1 ≤ n → p i ≤ p (i + 1))
    (htail : ∀ k ≤ n, 0 ≤ ∑ i ∈ Icc k n, q i) : 0 ≤ ∑ i ∈ range (n + 1), q i * p i := by
  have h1 : ∀ i ∈ range (n + 1), q i * p i = ∑ k ∈ range (i + 1), q i * incr p k := by
    intro i _; rw [← mul_sum, sum_incr]
  rw [sum_congr rfl h1]
  rw [sum_comm' (t' := range (n + 1)) (s' := fun k => Icc k n)]
  · refine sum_nonneg (fun k hk => ?_)
    rw [← sum_mul, mul_comm]
    refine mul_nonneg ?_ (htail k (by simp at hk; omega))
    unfold incr
    by_cases h0 : k = 0
    · rw [if_pos h0, sub_zero, h0]; exact hp0
    · rw [if_neg h0]
      have := hp (k - 1) (by simp at hk; omega)
      rw [show k - 1 + 1 = k by omega] at this; linarith
  · intro i k; simp only [mem_range, mem_Icc]; omega

/-- **Lemma 8.15** for one weight `W`: if `q₀ ≤ 0`, `q_i ≥ 0` for `i ≥ 2` and the full sum is `≥ 0`, then
`Σ_{2i ≤ W} q_i u_i u_{W-i} ≥ 0` for every `LCNZ` sequence `u`. -/
theorem abel_weight {u : ℕ → ℝ} (hu : LCNZ u) (W : ℕ) (q : ℕ → ℝ) (hq0 : q 0 ≤ 0)
    (hq : ∀ i, 2 ≤ i → 2 * i ≤ W → 0 ≤ q i) (hN : 0 ≤ ∑ i ∈ range (W / 2 + 1), q i) :
    0 ≤ ∑ i ∈ range (W / 2 + 1), q i * (u i * u (W - i)) := by
  apply abel_tails (W / 2) q (fun i => u i * u (W - i)) (mul_nonneg (hu.1 _) (hu.1 _))
  · intro i hi; exact hu.pair_mono (by omega)
  · intro k hk
    have hfull : ∑ i ∈ Icc 0 (W / 2), q i = ∑ i ∈ range (W / 2 + 1), q i := by
      rw [range_eq_Ico]; rfl
    rcases Nat.lt_or_ge k 2 with hk2 | hk2
    · rcases (show k = 0 ∨ k = 1 by omega) with rfl | rfl
      · rw [hfull]; exact hN
      · -- tail from 1 = full sum - q 0 ≥ full sum
        have : ∑ i ∈ Icc 0 (W / 2), q i = q 0 + ∑ i ∈ Icc 1 (W / 2), q i := by
          rw [show Icc 0 (W / 2) = insert 0 (Icc 1 (W / 2)) by ext x; simp only [mem_Icc, mem_insert]; omega,
            sum_insert (by simp)]
        rw [hfull] at this; linarith
    · exact sum_nonneg (fun i hi => by simp only [mem_Icc] at hi; exact hq i (by omega) (by omega))

end Szkraw
