import Szkraw.Statements
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace Szkraw

theorem error_amplification : Stmt_error_amplification := by
  intro N η e hN hη he0 he1 hrec m hm hmN
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) ≤ N := le_trans (by norm_num) hNr
  have hL : (1 : ℝ) ≤ 8 * N := by linarith
  have hfac : 4 * (N : ℝ) * (8*N) + 14*N ≤ (8*N)^2 := by nlinarith
  have hb : ∀ k, k ≤ N → e k ≤ η * (8*N)^k := by
    intro k
    induction k using Nat.twoStepInduction with
    | zero =>
        intro _
        simpa [he0] using hη
    | one =>
        intro _
        calc
          e 1 ≤ 3*η := he1
          _ ≤ η*(8*N)^1 := by simp only [pow_one]; nlinarith
    | more k ih0 ih1 =>
        intro hkN
        have hk0 : k ≤ N := by omega
        have hk1 : k+1 ≤ N := by omega
        have hr := hrec (k+1) (by omega) (by omega)
        have hi0 := ih0 hk0
        have hi1 := ih1 hk1
        have hp : (1 : ℝ) ≤ (8*N)^k := one_le_pow₀ hL
        have hp0 : (0 : ℝ) ≤ (8*N)^k := le_trans (by norm_num) hp
        have hconst : 12*(N : ℝ)*η ≤ 12*N*η*(8*N)^k :=
          le_mul_of_one_le_right (by positivity) hp
        have hmul : η*((8*N)^k) * (4*N*(8*N)+14*N) ≤
            η*((8*N)^k) * (8*N)^2 :=
          mul_le_mul_of_nonneg_left hfac (mul_nonneg hη hp0)
        calc
          e (k+2) ≤ 4*N*e (k+1) + 2*N*e k + 12*N*η := by
            simpa using hr
          _ ≤ 4*N*(η*(8*N)^(k+1)) + 2*N*(η*(8*N)^k) + 12*N*η := by
            gcongr
          _ ≤ 4*N*(η*(8*N)^(k+1)) + 2*N*(η*(8*N)^k) +
              12*N*η*(8*N)^k := by linarith
          _ = η*((8*N)^k) * (4*N*(8*N)+14*N) := by rw [pow_succ]; ring
          _ ≤ η*((8*N)^k) * (8*N)^2 := hmul
          _ = η*(8*N)^(k+2) := by rw [pow_add]; ring
  exact hb m hmN

example : Stmt_error_amplification := error_amplification

end Szkraw
