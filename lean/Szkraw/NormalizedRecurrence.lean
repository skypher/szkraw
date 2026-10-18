import Szkraw.Normalization

namespace Szkraw

theorem normalized_elementary_zero (p q : ℝ) (N : ℕ) :
    normalizedElementary p q N 0 = 1 := by
  simp [normalizedElementary, normalizer, elementary_zero]

theorem normalized_three_term (p q : ℝ) (hp : 1 ≤ p) (hq : 1 ≤ q)
    (N k : ℕ) (hk : k+1 ≤ N) :
    normalizedElementary p q N 1 * normalizedElementary p q N (k+1) =
      (q^(k+1)*qInteger q (N-(k+1))/qInteger q N) • normalizedElementary p q N (k+2) +
      (((p-1)*qInteger q (k+1))/(p*qInteger q N)) • normalizedElementary p q N (k+1) +
      (qInteger q (k+1)/(p*qInteger q N)) • normalizedElementary p q N k := by
  have hp0 : 0 < p := by linarith
  have hq0 : 0 < q := by linarith
  have hQN : 0 < qInteger q N := qInteger_pos q hq N (by omega)
  have hQi : 0 < qInteger q (k+1) := qInteger_pos q hq _ (by omega)
  have hQj : 0 < qInteger q (k+2) := qInteger_pos q hq _ (by omega)
  have hQlow : 0 < qInteger q (N-k) := qInteger_pos q hq _ (by omega)
  have hTk : 0 < normalizer p q N k := normalizer_pos p q hp hq N k (by omega)
  have hTi : 0 < normalizer p q N (k+1) := normalizer_pos p q hp hq N _ hk
  have hD : p*qInteger q N ≠ 0 := ne_of_gt (mul_pos hp0 hQN)
  have hL : normalizedElementary p q N 1 * normalizedElementary p q N (k+1) =
      ((p*qInteger q N)⁻¹*(normalizer p q N (k+1))⁻¹) •
        ((tower p q N).sum * elementary p q N (k+1)) := by
    simp only [normalizedElementary, normalizer_one, elementary_one]
    algebra with ℝ
  rw [hL, elementary_three_term p q N k]
  have hc : (p*qInteger q N)⁻¹*(normalizer p q N (k+1))⁻¹ *
      (p*q^k*qInteger q (N-k)) =
      (qInteger q (k+1)/(p*qInteger q N))*(normalizer p q N k)⁻¹ := by
    rw [show normalizer p q N (k+1) =
      normalizer p q N k * (p*q^k*qInteger q (N-k)/qInteger q (k+1)) from rfl]
    field_simp [ne_of_gt hTk, ne_of_gt hp0, ne_of_gt hQN,
      ne_of_gt hQlow, ne_of_gt hQi, pow_ne_zero _ (ne_of_gt hq0)]
    <;> ring
  have hb : (p*qInteger q N)⁻¹*(normalizer p q N (k+1))⁻¹ *
      ((p-1)*qInteger q (k+1)) =
      (((p-1)*qInteger q (k+1))/(p*qInteger q N))*(normalizer p q N (k+1))⁻¹ := by
    ring
  by_cases hlt : k+1 < N
  · have hTj : 0 < normalizer p q N (k+2) := normalizer_pos p q hp hq N _ (by omega)
    have hQup : 0 < qInteger q (N-(k+1)) := qInteger_pos q hq _ (by omega)
    have ha : (p*qInteger q N)⁻¹*(normalizer p q N (k+1))⁻¹*qInteger q (k+2) =
        (q^(k+1)*qInteger q (N-(k+1))/qInteger q N)*(normalizer p q N (k+2))⁻¹ := by
      rw [show normalizer p q N (k+2) =
        normalizer p q N (k+1) * (p*q^(k+1)*qInteger q (N-(k+1))/qInteger q (k+2)) from rfl]
      field_simp [ne_of_gt hTi, ne_of_gt hp0, ne_of_gt hQN,
        ne_of_gt hQup, ne_of_gt hQj, pow_ne_zero _ (ne_of_gt hq0)]
      <;> ring
    simp only [smul_add, smul_smul, normalizedElementary]
    rw [ha, hb, hc]
  · have he : N = k+1 := by omega
    have helem : elementary p q N (k+2) = 0 := elementary_above p q N (k+2) (by omega)
    simp only [smul_add, smul_smul, normalizedElementary, helem, smul_zero, zero_add]
    rw [hb, hc]

end Szkraw
