import Szkraw.Krawtchouk

namespace Szkraw

theorem perturbation_radius_nonneg (N : ℕ) (hN : 1 ≤ N) (r : ℝ)
    (hr : 0 < r) (hr1 : r < 1) : 0 ≤ perturbationRadius N r := by
  dsimp [perturbationRadius]
  have hs : 0 ≤ min r (1-r) := le_min (le_of_lt hr) (by linarith)
  positivity

theorem perturbation_radius_small (N : ℕ) (hN : 1 ≤ N) (r : ℝ)
    (hr : 0 < r) (hr1 : r < 1) : perturbationRadius N r ≤ 1/(2*(N : ℝ)) := by
  have hn : 0 < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hn1 : 1 ≤ (N : ℝ) := by exact_mod_cast hN
  let b := min r (1-r)/(32*(N : ℝ))
  have hs0 : 0 ≤ min r (1-r) := le_min (le_of_lt hr) (by linarith)
  have hs1 : min r (1-r) ≤ 1 := le_trans (min_le_left _ _) (le_of_lt hr1)
  have hb0 : 0 ≤ b := div_nonneg hs0 (by positivity)
  have hbN : b ≤ 1/(N : ℝ) := by
    calc
      _ ≤ 1/(32*(N : ℝ)) := div_le_div_of_nonneg_right hs1 (by positivity)
      _ ≤ _ := div_le_div_of_nonneg_left (by norm_num) hn (by nlinarith)
  have hb1 : b ≤ 1 := hbN.trans ((div_le_one hn).mpr hn1)
  have hp : b^N ≤ b := by
    obtain ⟨k,hk⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : N ≠ 0)
    rw [hk,pow_succ]
    exact (mul_le_mul_of_nonneg_right (pow_le_one₀ hb0 hb1) hb0).trans_eq (one_mul b)
  change (1/2 : ℝ)*b^N ≤ _
  calc
    _ ≤ (1/2 : ℝ)*b := mul_le_mul_of_nonneg_left hp (by norm_num)
    _ ≤ (1/2 : ℝ)*(1/(N : ℝ)) := mul_le_mul_of_nonneg_left hbN (by norm_num)
    _ = _ := by ring

/-- The stated coefficient radius keeps each interior leading coefficient away from zero. -/
theorem close_leading_lower {N : ℕ} (v : Coefficients N) (hv : Admissible v)
    (r : ℝ) (hr : 0 < r) (hr1 : r < 1) (hclose : CloseToKrawtchouk v r)
    (i : ℕ) (hi : 1 ≤ i) (hiN : i < N) : 1/(2*(N : ℝ)) ≤ v.a i := by
  have hn : 0 < (N : ℝ) := by exact_mod_cast (by have := hv.1; omega : 0 < N)
  have hd := (abs_le.mp (hclose.2 i (by omega)).1).1
  have hη := perturbation_radius_small N hv.1 r hr hr1
  have hgap : 1 ≤ (N : ℝ)-i := by
    have hh : (i : ℝ)+1 ≤ N := by exact_mod_cast (by omega : i+1 ≤ N)
    linarith
  have hbase : 1/(N : ℝ) ≤ ((N : ℝ)-i)/N :=
    div_le_div_of_nonneg_right hgap (le_of_lt hn)
  have heq : 1/(N : ℝ) = 2*(1/(2*(N : ℝ))) := by ring
  linarith

end Szkraw
