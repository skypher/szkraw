import Szkraw.ThreeTerm
import Mathlib.Tactic.FieldSimp

namespace Szkraw

theorem qInteger_nonneg (q : ℝ) (hq : 1 ≤ q) (n : ℕ) : 0 ≤ qInteger q n := by
  induction n with
  | zero => exact le_rfl
  | succ n ih =>
      rw [qInteger]
      exact add_nonneg ih (pow_nonneg (by linarith) _)

theorem qInteger_pos (q : ℝ) (hq : 1 ≤ q) (n : ℕ) (hn : 0 < n) :
    0 < qInteger q n := by
  cases n with
  | zero => omega
  | succ n =>
      rw [qInteger]
      exact add_pos_of_nonneg_of_pos (qInteger_nonneg q hq n) (pow_pos (by linarith) _)

noncomputable def normalizer (p q : ℝ) (N : ℕ) : ℕ → ℝ
  | 0 => 1
  | k+1 => normalizer p q N k * (p*q^k*qInteger q (N-k)/qInteger q (k+1))

theorem normalizer_pos (p q : ℝ) (hp : 1 ≤ p) (hq : 1 ≤ q)
    (N k : ℕ) (hk : k ≤ N) : 0 < normalizer p q N k := by
  induction k with
  | zero => norm_num [normalizer]
  | succ k ih =>
      rw [normalizer]
      exact mul_pos (ih (by omega))
        (div_pos (mul_pos (mul_pos (by linarith) (pow_pos (by linarith) _))
          (qInteger_pos q hq (N-k) (by omega)))
          (qInteger_pos q hq (k+1) (by omega)))

theorem normalizer_one (p q : ℝ) (N : ℕ) : normalizer p q N 1 = p*qInteger q N := by
  simp [normalizer, qInteger]

noncomputable def normalizedElementary (p q : ℝ) (N k : ℕ) : (tower p q N).Carrier :=
  (normalizer p q N k)⁻¹ • elementary p q N k

theorem normalized_elementary_nonneg (p q : ℝ) (hp : 1 ≤ p) (hq : 1 ≤ q)
    (N k : ℕ) (hk : k ≤ N) : towerNonneg p q N (normalizedElementary p q N k) := by
  exact tower_nonneg_smul p q _ (inv_nonneg.mpr (le_of_lt (normalizer_pos p q hp hq N k hk)))
    N _ (elementary_nonneg p q N k)

theorem normalized_coefficients_nonneg (p q : ℝ) (hp : 1 ≤ p) (hq : 1 ≤ q)
    (N : ℕ) (g : Fin (N+1) → ℝ)
    (hg : towerNonneg p q N (∑ k : Fin (N+1), g k • normalizedElementary p q N k.val)) :
    ∀ k, 0 ≤ g k := by
  have he : (∑ k : Fin (N+1), g k • normalizedElementary p q N k.val) =
      ∑ k : Fin (N+1), (g k*(normalizer p q N k.val)⁻¹) • elementary p q N k.val := by
    simp only [normalizedElementary, smul_smul]
  rw [he] at hg
  have h := elementary_coefficients_nonneg p q N _ hg
  intro k
  have ht := normalizer_pos p q hp hq N k.val (by omega)
  exact (mul_nonneg_iff_of_pos_right (inv_pos.mpr ht)).mp (h k)

end Szkraw
