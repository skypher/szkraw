import Szkraw.BooleanCoordinates
import Mathlib.Data.Nat.Choose.Bounds

namespace Szkraw

theorem normalizer_at_q_one (p : ℝ) (N k : ℕ) :
    normalizer p 1 N k = p^k*(N.choose k : ℝ) := by
  induction k with
  | zero => simp [normalizer]
  | succ k ih =>
      rw [normalizer,ih]
      simp only [one_pow,mul_one,qInteger_at_one]
      have hc : (N.choose (k+1) : ℝ)*(k+1) = (N.choose k : ℝ)*(N-k : ℕ) := by
        exact_mod_cast Nat.choose_succ_right_eq N k
      have hk : (k : ℝ)+1 ≠ 0 := by positivity
      calc
        _ = p^(k+1)*((N.choose k : ℝ)*(N-k : ℕ)/((k : ℝ)+1)) := by rw [pow_succ]; push_cast; ring
        _ = p^(k+1)*(N.choose (k+1) : ℝ) := by
          congr 1
          exact (div_eq_iff hk).mpr hc.symm

theorem inverse_kraw_normalizer (r : ℝ) (hr : 0 < r) (N k : ℕ) (hk : k ≤ N) :
    (normalizer (1/r) 1 N k)⁻¹ = r^k/(N.choose k : ℝ) := by
  rw [normalizer_at_q_one,one_div_pow]
  have hrk : r^k ≠ 0 := pow_ne_zero _ (ne_of_gt hr)
  have hc : (N.choose k : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hk).ne'
  field_simp

end Szkraw
