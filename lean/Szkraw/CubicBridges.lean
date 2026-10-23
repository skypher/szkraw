import Szkraw.CubicDetours
import Szkraw.CubicKeyForms

/-!
# Theorem 8.17: bridges from the weight sums `Wt` to the linear forms `lf`

With `f = iterShift ν ℓ`, the weights `Wt` of the cubic detours are linear forms in `f`
with the coefficient sequences `cfX`, `cfY`, `cfYp`, `cfXp`, `cfH` of `GenFormK`.
-/

set_option linter.unusedSectionVars false

namespace Szkraw

open Finset

theorem Wt_one_lf (ν : ℕ → ℝ) (ℓ a : ℕ) : Wt ν 1 0 ℓ a = lf (a + 1) (cfX a) (Szkraw.iterShift ν ℓ) := by
  unfold Wt lf
  refine sum_congr rfl fun n _ => ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [cfX_zero]
  · rw [cfX_pos (a := a) hn, if_pos (show 1 ≤ n by omega)]
    simp

/-- `Y' = lf (a+1) (cfYp a)` for `a ≥ 3` (the content of `sYp_eq_beta'` and `beta'C_zero_lf`). -/
theorem sYp_lf (f : ℕ → ℝ) {a : ℕ} (ha : 3 ≤ a) : sYp f a = lf (a + 1) (cfYp a) f := by
  set g : ℕ → ℝ := fun j => if 2 ≤ j then ((a - 1).choose j : ℝ) else 0 with hg
  have e1 : sYp f a = lf a g f + ∑ j ∈ range a, g j * f (j + 1) := by
    unfold sYp lf; rw [← sum_add_distrib]; exact sum_congr rfl fun j _ => by rw [hg]; ring
  rw [e1, lf_shift a g]
  have e2 : lf a g f = lf (a + 1) g f :=
    lf_extend (by omega) (fun n hn => by simp [hg, choose_small_zero (by omega : a - 1 < n)])
  rw [e2]
  unfold lf; rw [← sum_add_distrib]
  refine sum_congr rfl fun n hn => ?_
  simp only [mem_range] at hn
  have pas : ∀ m, 1 ≤ m → ((a.choose m : ℕ) : ℝ) = ((a - 1).choose (m - 1) : ℝ) + ((a - 1).choose m : ℝ) := by
    intro m hm
    have := Nat.choose_succ_succ' (a - 1) (m - 1)
    rw [show a - 1 + 1 = a by omega, show m - 1 + 1 = m by omega] at this
    exact_mod_cast this
  rcases (show n = 0 ∨ n = 1 ∨ n = 2 ∨ 3 ≤ n by omega) with rfl | rfl | rfl | h
  · rw [cfYp_zero]; simp [hg]
  · rw [cfYp_one]; simp [hg]
  · rw [cfYp_two, pas 2 (by norm_num)]; simp [hg, cast_pred (show 1 ≤ a by omega)]
  · rw [cfYp_ge3 h, pas n (by omega)]; simp [hg, show 2 ≤ n by omega, show 2 ≤ n - 1 by omega,
      show 1 ≤ n by omega]; ring

theorem Wt_two_lf (ν : ℕ → ℝ) (ℓ a : ℕ) : Wt ν 2 0 ℓ a = lf (a + 1) (cfY a) (Szkraw.iterShift ν ℓ) := by
  unfold Wt lf
  refine sum_congr rfl fun n _ => ?_
  rcases (show n = 0 ∨ n = 1 ∨ 2 ≤ n by omega) with rfl | rfl | hn
  · simp [cfY_zero]
  · simp [cfY_one]
  · rw [cfY_ge2 (a := a) hn, if_pos hn]
    simp

theorem Wt_two_succ_lf (ν : ℕ → ℝ) (ℓ a : ℕ) (ha : 3 ≤ a) :
    Wt ν 2 0 (ℓ + 1) (a - 1) = lf (a + 1) (cfYp a) (Szkraw.iterShift ν ℓ) := by
  have hsucc : ∀ n, Szkraw.iterShift ν (ℓ + 1) n =
      Szkraw.iterShift ν ℓ n + Szkraw.iterShift ν ℓ (n + 1) := fun n => rfl
  have h1 : Wt ν 2 0 (ℓ + 1) (a - 1) = sYp (Szkraw.iterShift ν ℓ) a := by
    unfold Wt sYp
    rw [show a - 1 + 1 = a by omega]
    refine sum_congr rfl fun n _ => ?_
    rw [hsucc n]
    by_cases h : 2 ≤ n
    · simp [h]
    · simp [h]
  rw [h1]
  exact sYp_lf _ ha

theorem Wt_one_succ_lf (ν : ℕ → ℝ) (ℓ a : ℕ) (ha : 3 ≤ a) :
    Wt ν 1 0 (ℓ + 1) (a - 2) = lf (a + 1) (cfXp a) (Szkraw.iterShift ν ℓ) := by
  rw [Wt_one_zero, show ℓ + 1 + (a - 2) = ℓ + (a - 1) by omega, dd_shift_eq ν ℓ (a - 1),
    dd_shift_eq ν ℓ 1]
  exact Xp_lf (Szkraw.iterShift ν ℓ) ha

theorem sH_lf (u : ℕ → ℝ) (a : ℕ) : sH u a = lf (a + 1) (cfH a) u := by
  unfold sH lf
  refine sum_congr rfl fun n _ => ?_
  by_cases h : 3 ≤ n
  · rw [if_pos h, cfH_ge3 (a := a) h]
  · rw [if_neg h, cfH_le2 (a := a) (n := n) (by omega)]

end Szkraw
