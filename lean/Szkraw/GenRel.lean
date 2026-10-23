import Szkraw.GenFormL1

/-!
# Binomial relations for the generic case `n = p + 4 ≤ a = p + 4 + K` of the edge certificates
-/

namespace Szkraw

theorem rel_cm (p K : ℕ) :
    (((p + 4 + K).choose (p + 3) : ℕ) : ℝ) * ((K : ℝ) + 1) = ((p + 4 + K).choose (p + 4) : ℝ) * ((p : ℝ) + 4) := by
  have := choose_succ_real (p + 4 + K) (p + 3) (by omega)
  rw [show p + 3 + 1 = p + 4 by omega] at this
  have e : (((p + 4 + K : ℕ)) : ℝ) - ((p + 3 : ℕ) : ℝ) = (K : ℝ) + 1 := by push_cast; ring
  rw [e] at this; push_cast at this ⊢; linarith

theorem rel_cp (p K : ℕ) :
    (((p + 4 + K).choose (p + 4 + 1) : ℕ) : ℝ) * ((p : ℝ) + 5) = ((p + 4 + K).choose (p + 4) : ℝ) * (K : ℝ) := by
  have := choose_succ_real (p + 4 + K) (p + 4) (by omega)
  have e : (((p + 4 + K : ℕ)) : ℝ) - ((p + 4 : ℕ) : ℝ) = (K : ℝ) := by push_cast; ring
  rw [e] at this; push_cast at this ⊢; linarith

theorem rel_d (p K : ℕ) :
    (((p + 4 + K - 1).choose (p + 3) : ℕ) : ℝ) * ((p : ℝ) + 4 + K) = ((p + 4 + K).choose (p + 4) : ℝ) * ((p : ℝ) + 4) := by
  have := choose_pred_real (p + 4 + K) (p + 3) (by omega)
  rw [show p + 3 + 1 = p + 4 by omega] at this; push_cast at this ⊢; linarith

theorem rel_e (p K : ℕ) :
    (((p + 4 + K - 1).choose (p + 4) : ℕ) : ℝ) * ((p : ℝ) + 4 + K) = ((p + 4 + K).choose (p + 4) : ℝ) * (K : ℝ) := by
  have hp := choose_pred_real (p + 4 + K) (p + 4) (by omega)
  have := rel_cp p K
  push_cast at hp this ⊢; linarith

end Szkraw
