import Szkraw.VRMoves
import Szkraw.VRCorollaries

/-!
# Theorem 8.9 (linearly increasing ratio): sequences and Leibniz formulas

Setting: `ν` is the padded Newton sequence of the profile `d` (log-concave without internal zeros,
`ν 0 = 0`, zero beyond `N`), `c_i = (r + t i) d_i` and `b_i = (s - t i) d_i` with `s = 1 - r`,
`t = κ/N` and `(2N-1) t ≤ s`. The Newton sequence of `c` is the truncation at `N` of
`κ̂_i = (r + t i) ν_i + t i ν_{i-1}`, and that of `b` is `ν - κ`.
-/

namespace Szkraw

open Finset

/-! ### The Leibniz rule for a linear factor -/

theorem fwdDiff_iter_succ (F : ℕ → ℝ) (m x : ℕ) :
    (fwdDiff 1)^[m + 1] F x = (fwdDiff 1)^[m] F (x + 1) - (fwdDiff 1)^[m] F x := by
  rw [Function.iterate_succ_apply']; rfl

theorem fwdDiff_lin_mul (r t : ℝ) (d : ℕ → ℝ) : ∀ k x : ℕ,
    (fwdDiff 1)^[k + 1] (fun i : ℕ => (r + t * i) * d i) x =
      (r + t * ((x : ℝ) + k + 1)) * (fwdDiff 1)^[k + 1] d x + t * ((k : ℝ) + 1) * (fwdDiff 1)^[k] d x
  | 0, x => by
    rw [fwdDiff_iter_succ, fwdDiff_iter_succ]
    simp only [Function.iterate_zero, id]
    push_cast; ring
  | k + 1, x => by
    rw [fwdDiff_iter_succ (fun i : ℕ => (r + t * i) * d i) (k + 1) x, fwdDiff_lin_mul r t d k (x + 1),
      fwdDiff_lin_mul r t d k x, fwdDiff_iter_succ d (k + 1) x, fwdDiff_iter_succ d k x]
    push_cast; ring

theorem newtonCoeff_lin_mul (r t : ℝ) (d : ℕ → ℝ) (k : ℕ) (hk : 1 ≤ k) :
    newtonCoeff (fun i : ℕ => (r + t * i) * d i) k =
      (r + t * k) * newtonCoeff d k + t * k * newtonCoeff d (k - 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  rw [newtonCoeff_eq_iter, newtonCoeff_eq_iter, newtonCoeff_eq_iter, fwdDiff_lin_mul,
    show m + 1 - 1 = m by omega]
  push_cast; ring

/-! ### The sequences -/

/-- `κ̂_i = (r + t i) ν_i + t i ν_{i-1}`. -/
noncomputable def kapHat (r t : ℝ) (ν : ℕ → ℝ) (i : ℕ) : ℝ := (r + t * i) * ν i + t * i * ν (i - 1)

/-- The Newton sequence of `c`: `κ̂` truncated at `N`. -/
noncomputable def affU (N : ℕ) (r t : ℝ) (ν : ℕ → ℝ) (i : ℕ) : ℝ := if i ≤ N then kapHat r t ν i else 0

theorem LCNZ.trunc {g : ℕ → ℝ} (hg : LCNZ g) (N : ℕ) : LCNZ (fun i => if i ≤ N then g i else 0) := by
  obtain ⟨hnn, hlc, hint⟩ := hg
  refine ⟨fun i => by dsimp only; split_ifs <;> simp [hnn i], fun i => ?_, fun i j k hij hjk hi hk => ?_⟩
  · dsimp only
    by_cases h : i + 2 ≤ N
    · rw [if_pos (by omega), if_pos h, if_pos (by omega)]; exact hlc i
    · rw [if_neg h, mul_zero]; split_ifs <;> positivity
  · dsimp only at *
    split_ifs at hi hk with h1 h2
    · rw [if_pos (by omega)]; exact hint i j k hij hjk hi hk
    all_goals first | exact absurd hk (lt_irrefl _) | exact absurd hi (lt_irrefl _)

section Seq

variable {N : ℕ} {r t : ℝ} {ν : ℕ → ℝ}

theorem kapHat_zero (hν0 : ν 0 = 0) : kapHat r t ν 0 = 0 := by simp [kapHat, hν0]

theorem kapHat_lcnz (hr : 0 < r) (ht : 0 ≤ t) (hν : LCNZ ν) (hν0 : ν 0 = 0) : LCNZ (kapHat r t ν) := by
  have hnn := hν.1
  have hpos : ∀ i : ℕ, 0 < r + t * i := fun i => by positivity
  refine ⟨fun i => ?_, fun i => ?_, fun i j k hij hjk hi hk => ?_⟩
  · unfold kapHat
    exact add_nonneg (mul_nonneg (hpos i).le (hnn i)) (mul_nonneg (by positivity) (hnn _))
  · rcases i with _ | i
    · rw [kapHat_zero hν0, zero_mul]; positivity
    · -- center `i + 2`; values `ν i, ν (i+1), ν (i+2), ν (i+3)`
      have l1 := hν.2.1 (i + 1)
      have l2 := hν.2.1 i
      have l3 := hν.step (x := i) (y := i + 1) (by omega)
      simp only [kapHat, show i + 1 - 1 = i by omega, show i + 1 + 2 - 1 = i + 2 by omega,
        show i + 1 + 1 - 1 = i + 1 by omega, show i + 1 + 1 = i + 2 by omega,
        show i + 1 + 2 = i + 3 by omega]
      push_cast
      set x0 := ν i; set x1 := ν (i + 1); set x2 := ν (i + 2); set x3 := ν (i + 3)
      have e : ((r + t * ((i : ℝ) + 2)) * x2 + t * ((i : ℝ) + 2) * x1) ^ 2 -
          ((r + t * ((i : ℝ) + 1)) * x1 + t * ((i : ℝ) + 1) * x0) *
            ((r + t * ((i : ℝ) + 3)) * x3 + t * ((i : ℝ) + 3) * x2) =
          (r + t * ((i : ℝ) + 2)) ^ 2 * (x2 ^ 2 - x1 * x3) + (t * ((i : ℝ) + 2)) ^ 2 * (x1 ^ 2 - x0 * x2) +
          (t * ((i : ℝ) + 1)) * (r + t * ((i : ℝ) + 3)) * (x2 * x1 - x0 * x3) +
          t ^ 2 * (x1 * x3 + x0 * x2 + 2 * x2 * x1) := by ring
      have h1 : 0 ≤ (r + t * ((i : ℝ) + 2)) ^ 2 * (x2 ^ 2 - x1 * x3) :=
        mul_nonneg (sq_nonneg _) (by simp only [x1, x2, x3] at *; linarith)
      have h2 : 0 ≤ (t * ((i : ℝ) + 2)) ^ 2 * (x1 ^ 2 - x0 * x2) :=
        mul_nonneg (sq_nonneg _) (by simp only [x0, x1, x2] at *; linarith)
      have h3 : 0 ≤ (t * ((i : ℝ) + 1)) * (r + t * ((i : ℝ) + 3)) * (x2 * x1 - x0 * x3) := by
        refine mul_nonneg (mul_nonneg (by positivity) (by positivity)) ?_
        simp only [x0, x1, x2, x3] at *; linarith
      have h4 : 0 ≤ t ^ 2 * (x1 * x3 + x0 * x2 + 2 * x2 * x1) := by
        have := hnn i; have := hnn (i + 1); have := hnn (i + 2); have := hnn (i + 3)
        positivity
      nlinarith [e, h1, h2, h3, h4]
  · -- positive support is an interval
    have hjpos : 0 < ν j ∨ (1 ≤ j ∧ 0 < t ∧ 0 < ν (j - 1)) ∨ j = k := by
      unfold kapHat at hi hk
      -- some index `i' ∈ {i-1, i}` with `ν i' > 0`, `i' ≤ j`
      have hi' : ∃ i', i' ≤ j ∧ 0 < ν i' := by
        by_contra hcon
        push Not at hcon
        have h1 : ν i ≤ 0 := hcon i hij
        have h2 : ν (i - 1) ≤ 0 := hcon (i - 1) (by omega)
        have : (r + t * i) * ν i + t * i * ν (i - 1) ≤ 0 := by
          have := hnn i; have := hnn (i - 1)
          have e1 : ν i = 0 := le_antisymm h1 (hnn i)
          have e2 : ν (i - 1) = 0 := le_antisymm h2 (hnn _)
          rw [e1, e2]; ring_nf; exact le_rfl
        linarith
      obtain ⟨i', hi'j, hi'pos⟩ := hi'
      by_cases hkpos : 0 < ν k
      · exact Or.inl (hν.2.2 i' j k hi'j hjk hi'pos hkpos)
      · have hk0 : ν k = 0 := le_antisymm (not_lt.mp hkpos) (hnn k)
        rw [hk0, mul_zero, zero_add] at hk
        have hk1 : 0 < t * k * ν (k - 1) := hk
        have htk : 0 < t * k := by
          rcases (mul_pos_iff.mp hk1) with h | h
          · exact h.1
          · exact absurd h.2 (not_lt.mpr (hnn _))
        have hνk1 : 0 < ν (k - 1) := by
          rcases (mul_pos_iff.mp hk1) with h | h
          · exact h.2
          · exact absurd h.1 (not_lt.mpr htk.le)
        have ht0 : 0 < t := by
          rcases (mul_pos_iff.mp htk) with h | h
          · exact h.1
          · exact absurd h.2 (not_lt.mpr (Nat.cast_nonneg _))
        rcases Nat.lt_or_ge j k with hjk' | hjk'
        · exact Or.inl (hν.2.2 i' j (k - 1) hi'j (by omega) hi'pos hνk1)
        · exact Or.inr (Or.inr (le_antisymm hjk hjk'))
    rcases hjpos with h | ⟨hj1, ht0, h⟩ | h
    · unfold kapHat
      have := hnn (j - 1)
      have : 0 < (r + t * j) * ν j := mul_pos (hpos j) h
      have : 0 ≤ t * j * ν (j - 1) := by positivity
      linarith
    · unfold kapHat
      have : 0 ≤ (r + t * j) * ν j := mul_nonneg (hpos j).le (hnn j)
      have : 0 < t * j * ν (j - 1) := mul_pos (mul_pos ht0 (by exact_mod_cast hj1)) h
      linarith
    · rw [h]; exact hk

theorem affU_lcnz (hr : 0 < r) (ht : 0 ≤ t) (hν : LCNZ ν) (hν0 : ν 0 = 0) : LCNZ (affU N r t ν) :=
  (kapHat_lcnz hr ht hν hν0).trunc N

theorem affU_zero (hν0 : ν 0 = 0) : affU N r t ν 0 = 0 := by
  simp [affU, kapHat_zero hν0]

theorem affU_one_pos (hN : 1 ≤ N) (hr : 0 < r) (ht : 0 ≤ t) (hν : LCNZ ν) (hν1 : 0 < ν 1) :
    0 < affU N r t ν 1 := by
  unfold affU kapHat
  rw [if_pos hN]
  have := hν.1 0
  have : 0 < (r + t * ((1 : ℕ) : ℝ)) * ν 1 := mul_pos (by positivity) hν1
  have : 0 ≤ t * ((1 : ℕ) : ℝ) * ν (1 - 1) := by positivity
  linarith

/-- The Leibniz formula `φ_n(ℓ) = (r + t(ℓ+n)) f_n(ℓ) + t n f_{n-1}(ℓ)` for `ℓ + n ≤ N`. -/
theorem affU_leibniz : ∀ ℓ n, ℓ + n ≤ N →
    Szkraw.iterShift (affU N r t ν) ℓ n =
      (r + t * ((ℓ : ℝ) + n)) * Szkraw.iterShift ν ℓ n + t * n * Szkraw.iterShift ν ℓ (n - 1) := by
  intro ℓ
  induction ℓ with
  | zero =>
    intro n hn
    show affU N r t ν n = _
    simp only [affU, kapHat, if_pos (show n ≤ N by omega), Szkraw.iterShift]
    push_cast; ring
  | succ ℓ ih =>
    intro n hn
    show Szkraw.iterShift (affU N r t ν) ℓ n + Szkraw.iterShift (affU N r t ν) ℓ (n + 1) =
      _ * (Szkraw.iterShift ν ℓ n + Szkraw.iterShift ν ℓ (n + 1)) + _ * Szkraw.iterShift ν (ℓ + 1) (n - 1)
    rw [ih n (by omega), ih (n + 1) (by omega), show n + 1 - 1 = n by omega]
    rcases n with _ | n
    · simp only [Nat.cast_zero, mul_zero, zero_mul, add_zero]; push_cast; ring
    · have e : Szkraw.iterShift ν (ℓ + 1) (n + 1 - 1) = Szkraw.iterShift ν ℓ n + Szkraw.iterShift ν ℓ (n + 1) := by
        rw [show n + 1 - 1 = n by omega]; rfl
      rw [e, show n + 1 - 1 = n by omega]
      push_cast; ring

end Seq

end Szkraw
