import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Log-concave sequences without internal zeros (paper, Lemma 8.3, first part)

`LCNZ u` : `u` is nonnegative, log-concave, and its positive entries form an interval.
We prove that balanced products dominate and that `u ↦ (u i + u (i+1))` preserves `LCNZ`.
-/

namespace Szkraw

/-- Nonnegative, log-concave, without internal zeros. -/
def LCNZ (u : ℕ → ℝ) : Prop :=
  (∀ i, 0 ≤ u i) ∧ (∀ i, u i * u (i + 2) ≤ u (i + 1) ^ 2) ∧
  (∀ i j k, i ≤ j → j ≤ k → 0 < u i → 0 < u k → 0 < u j)

/-- One-step balanced product: `u (x+1) * u (y+1) ≥ u x * u (y+2)` for `x ≤ y`. -/
theorem LCNZ.step {u : ℕ → ℝ} (hu : LCNZ u) {x y : ℕ} (hxy : x ≤ y) :
    u x * u (y + 2) ≤ u (x + 1) * u (y + 1) := by
  obtain ⟨hnn, hlc, hint⟩ := hu
  by_cases h0 : u x = 0
  · rw [h0, zero_mul]; exact mul_nonneg (hnn _) (hnn _)
  by_cases h1 : u (y + 2) = 0
  · rw [h1, mul_zero]; exact mul_nonneg (hnn _) (hnn _)
  have hx : 0 < u x := lt_of_le_of_ne (hnn x) (Ne.symm h0)
  have hy : 0 < u (y + 2) := lt_of_le_of_ne (hnn _) (Ne.symm h1)
  have hpos : ∀ j, x ≤ j → j ≤ y + 2 → 0 < u j := fun j h1 h2 => hint x j (y + 2) h1 h2 hx hy
  -- induction on the gap y - x
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hxy
  clear hxy h0 h1 hy
  induction n with
  | zero => simpa [pow_two] using hlc x
  | succ n ih =>
    have ih' := ih (fun j h1 h2 => hpos j h1 (by omega))
    have hlc' := hlc (x + n + 1)
    have p1 : 0 < u (x + n + 1) := hpos _ (by omega) (by omega)
    have p2 : 0 < u (x + n + 2) := hpos _ (by omega) (by omega)
    have p0 : 0 < u (x + 1) := hpos _ (by omega) (by omega)
    -- ih': u x * u (x+n+2) ≤ u (x+1) * u (x+n+1);  hlc': u (x+n+1) * u (x+n+3) ≤ u (x+n+2)^2
    have key : u x * u (x + (n + 1) + 2) * u (x + n + 1) ≤ u (x + 1) * u (x + (n + 1) + 1) * u (x + n + 1) := by
      have e1 : x + (n + 1) + 2 = x + n + 1 + 2 := by omega
      have e2 : x + (n + 1) + 1 = x + n + 2 := by omega
      rw [e1, e2]
      have e3 : x + n + 1 + 1 = x + n + 2 := by omega
      rw [e3] at hlc'
      have ih'' : u x * u (x + n + 2) ≤ u (x + 1) * u (x + n + 1) := by
        have e4 : x + n + 2 = x + n + 2 := rfl
        simpa using ih'
      nlinarith [mul_le_mul_of_nonneg_left hlc' hx.le, mul_le_mul_of_nonneg_right ih'' p2.le,
                 hnn (x + n + 1 + 2)]
    exact le_of_mul_le_mul_right key p1

/-- Balanced products dominate: `u (a - c) * u (b + c) ≤ u a * u b` for `c ≤ a ≤ b`. -/
theorem LCNZ.balanced {u : ℕ → ℝ} (hu : LCNZ u) :
    ∀ c a b, c ≤ a → a ≤ b → u (a - c) * u (b + c) ≤ u a * u b := by
  intro c
  induction c with
  | zero => intro a b _ _; simp
  | succ c ih =>
    intro a b hca hab
    -- u (a-c-1) * u (b+c+1) ≤ u (a-c) * u (b+c) ≤ u a * u b
    have h1 : u (a - (c + 1)) * u (b + c + 2 - 1) ≤ u (a - (c + 1) + 1) * u (b + c - 1 + 1) := by
      have hs := hu.step (x := a - (c + 1)) (y := b + c - 1) (by omega)
      have e1 : b + c - 1 + 2 = b + c + 2 - 1 := by omega
      rw [e1] at hs; exact hs
    have e2 : b + c + 2 - 1 = b + (c + 1) := by omega
    have e3 : a - (c + 1) + 1 = a - c := by omega
    have e4 : b + c - 1 + 1 = b + c := by omega
    rw [e2, e3, e4] at h1
    exact le_trans h1 (ih a b (by omega) hab)

/-- The shifted sum `v i = u i + u (i+1)`. -/
def shiftSum (u : ℕ → ℝ) (i : ℕ) : ℝ := u i + u (i + 1)

theorem LCNZ.shiftSum {u : ℕ → ℝ} (hu : LCNZ u) : LCNZ (Szkraw.shiftSum u) := by
  have hnn := hu.1
  refine ⟨fun i => add_nonneg (hnn _) (hnn _), ?_, ?_⟩
  · intro i
    unfold Szkraw.shiftSum
    have l1 := hu.2.1 i
    have l2 := hu.2.1 (i + 1)
    have b := hu.step (x := i) (y := i + 1) (by omega)
    have e : i + 1 + 2 = i + 3 := by omega
    have e' : i + 2 + 1 = i + 3 := by omega
    have e'' : i + 1 + 1 = i + 2 := by omega
    rw [e''] at l2 b ⊢
    rw [e', e] at *
    nlinarith [l1, l2, b]
  · intro i j k hij hjk hi hk
    unfold Szkraw.shiftSum at *
    -- some positive entry of u in [i, i+1] and in [k, k+1]; then u is positive on [i or i+1, k or k+1] ∋ j or j+1
    have hi' : 0 < u i ∨ 0 < u (i + 1) := by
      by_contra h; push Not at h; linarith [hnn i, hnn (i + 1)]
    have hk' : 0 < u k ∨ 0 < u (k + 1) := by
      by_contra h; push Not at h; linarith [hnn k, hnn (k + 1)]
    have : 0 < u j ∨ 0 < u (j + 1) := by
      rcases hi' with h1 | h1 <;> rcases hk' with h2 | h2
      · left; exact hu.2.2 i j k hij hjk h1 h2
      · left; exact hu.2.2 i j (k + 1) hij (by omega) h1 h2
      · by_cases hj : i + 1 ≤ j
        · left; exact hu.2.2 (i + 1) j k hj hjk h1 h2
        · right; have : j = i := by omega
          subst this; exact h1
      · by_cases hj : i + 1 ≤ j
        · left; exact hu.2.2 (i + 1) j (k + 1) hj (by omega) h1 h2
        · right; have : j = i := by omega
          subst this; exact h1
    rcases this with h | h
    · linarith [hnn (j + 1)]
    · linarith [hnn j]

/-- Iterated shift sums. -/
def iterShift (u : ℕ → ℝ) : ℕ → ℕ → ℝ
  | 0 => u
  | n + 1 => Szkraw.shiftSum (iterShift u n)

theorem LCNZ.iterShift {u : ℕ → ℝ} (hu : LCNZ u) : ∀ n, LCNZ (Szkraw.iterShift u n)
  | 0 => hu
  | n + 1 => (LCNZ.iterShift hu n).shiftSum

/-- The key inequality of Lemma 8.3 for one `LCNZ` sequence `g`:
`g i * (g l + g (l+1)) ≥ (g 0 + g 1) * g (i + l)` for `i, l ≥ 1`. -/
theorem LCNZ.key {g : ℕ → ℝ} (hg : LCNZ g) {i l : ℕ} (hi : 1 ≤ i) (_hl : 1 ≤ l) :
    (g 0 + g 1) * g (i + l) ≤ g i * (g l + g (l + 1)) := by
  -- g i g l ≥ g 0 g (i+l)  and  g i g (l+1) ≥ g 1 g (i+l)
  have h1 : g 0 * g (i + l) ≤ g i * g l := by
    rcases le_total i l with h | h
    · have := hg.balanced i i l le_rfl h; simpa [Nat.sub_self, add_comm] using this
    · have := hg.balanced l l i le_rfl h
      rw [mul_comm (g i)]; simpa [Nat.sub_self] using this
  have h2 : g 1 * g (i + l) ≤ g i * g (l + 1) := by
    rcases le_total i (l + 1) with h | h
    · have := hg.balanced (i - 1) i (l + 1) (by omega) h
      have e1 : i - (i - 1) = 1 := by omega
      have e2 : l + 1 + (i - 1) = i + l := by omega
      rw [e1, e2] at this; exact this
    · have := hg.balanced l (l + 1) i (by omega) h
      have e1 : l + 1 - l = 1 := by omega
      have e2 : i + l = i + l := rfl
      rw [e1] at this; rw [mul_comm (g i)]; exact this
  nlinarith [h1, h2]

open Finset in
/-- `iterShift u ℓ i = Σ_{h ≤ ℓ} C(ℓ,h) u (i+h)`. -/
theorem iterShift_eq (u : ℕ → ℝ) : ∀ ℓ i,
    Szkraw.iterShift u ℓ i = ∑ h ∈ range (ℓ + 1), (ℓ.choose h : ℝ) * u (i + h)
  | 0, i => by simp [Szkraw.iterShift]
  | ℓ + 1, i => by
    show Szkraw.iterShift u ℓ i + Szkraw.iterShift u ℓ (i + 1) = _
    rw [iterShift_eq u ℓ i, iterShift_eq u ℓ (i + 1)]
    have hA : ∑ h ∈ range (ℓ + 1), (ℓ.choose h : ℝ) * u (i + h) =
        ∑ h ∈ range (ℓ + 2), (ℓ.choose h : ℝ) * u (i + h) := by
      rw [sum_range_succ _ (ℓ + 1)]; simp [Nat.choose_succ_self]
    rw [hA, sum_range_succ' (fun h => (ℓ.choose h : ℝ) * u (i + h)),
      sum_range_succ' (fun h => ((ℓ + 1).choose h : ℝ) * u (i + h))]
    have hB : ∑ h ∈ range (ℓ + 1), ((ℓ + 1).choose (h + 1) : ℝ) * u (i + (h + 1)) =
        ∑ h ∈ range (ℓ + 1), (ℓ.choose h : ℝ) * u (i + 1 + h) +
          ∑ h ∈ range (ℓ + 1), (ℓ.choose (h + 1) : ℝ) * u (i + (h + 1)) := by
      rw [← sum_add_distrib]
      refine sum_congr rfl (fun h _ => ?_)
      rw [Nat.choose_succ_succ', Nat.cast_add, add_mul]
      have e : i + 1 + h = i + (h + 1) := by omega
      rw [e]
    rw [hB]
    simp only [Nat.choose_zero_right, Nat.cast_one, one_mul, add_zero]
    ring

/-- Lemma 8.3 in iterated-shift form: with `f n ℓ = iterShift u ℓ n` for an `LCNZ` sequence `u`,
`f i ℓ * f l (ℓ+1) ≥ f 0 (ℓ+1) * f (i+l) ℓ` for `i, l ≥ 1`. -/
theorem lemma_8_3 {u : ℕ → ℝ} (hu : LCNZ u) (ℓ : ℕ) {i l : ℕ} (hi : 1 ≤ i) (hl : 1 ≤ l) :
    Szkraw.iterShift u (ℓ + 1) 0 * Szkraw.iterShift u ℓ (i + l) ≤
      Szkraw.iterShift u ℓ i * Szkraw.iterShift u (ℓ + 1) l := by
  have := (hu.iterShift ℓ).key hi hl
  simpa [Szkraw.iterShift, Szkraw.shiftSum] using this

end Szkraw
