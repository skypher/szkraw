import Szkraw.Geometric

namespace Szkraw

/-- Positive closure in the normalized elementary basis, including terminal products. -/
theorem normalized_elementary_products (p q : ℝ) (hp : 1 ≤ p) (hq : 1 ≤ q)
    (N : ℕ) (hN : 1 ≤ N) (m n : ℕ) (hm : m ≤ N) (hn : n ≤ N) :
    ∃ g : Fin (N+1) → ℝ, (∀ k, 0 ≤ g k) ∧
      normalizedElementary p q N m*normalizedElementary p q N n =
        ∑ k, g k • normalizedElementary p q N k.val := by
  let v := geometricCoefficients N p q
  let U := normalizedElementary p q N
  let X := U 1
  have hv := geometric_coefficients_admissible N hN p q hp hq
  have heval := recurrence_evaluation v hv U X (normalized_elementary_zero p q N) rfl
    (fun j hj => normalized_three_term p q hp hq N j (by omega)) m hm
  have hrep := representation_product v (fun j : Fin (N+1) => U j.val) X
    (geometric_row_action p q hp hq N hN) m (⟨n,by omega⟩ : Fin (N+1))
  rw [heval] at hrep
  exact ⟨fun k => productMatrix v m ⟨n,by omega⟩ k,
    geometric_family_matrix_positivity N hN p q hp hq m hm ⟨n,by omega⟩,hrep⟩

/-- The unnormalized positive product expansion asserted in the paper's subalgebra proposition. -/
theorem elementary_products (p q : ℝ) (hp : 1 ≤ p) (hq : 1 ≤ q)
    (N : ℕ) (hN : 1 ≤ N) (m n : ℕ) (hm : m ≤ N) (hn : n ≤ N) :
    ∃ g : Fin (N+1) → ℝ, (∀ k, 0 ≤ g k) ∧
      elementary p q N m*elementary p q N n = ∑ k, g k • elementary p q N k.val := by
  obtain ⟨g,hg,hprod⟩ := normalized_elementary_products p q hp hq N hN m n hm hn
  let t := normalizer p q N
  have htm : t m ≠ 0 := ne_of_gt (normalizer_pos p q hp hq N m hm)
  have htn : t n ≠ 0 := ne_of_gt (normalizer_pos p q hp hq N n hn)
  have hraw : elementary p q N m*elementary p q N n =
      (t m*t n) • (normalizedElementary p q N m*normalizedElementary p q N n) := by
    simp only [normalizedElementary,smul_mul_smul,smul_smul]
    have he : t m*t n*((t m)⁻¹*(t n)⁻¹) = 1 := by field_simp
    rw [he,one_smul]
  refine ⟨fun k => (t m*t n)*g k*(t k.val)⁻¹,?_,?_⟩
  · intro k
    have hm0 := le_of_lt (normalizer_pos p q hp hq N m hm)
    have hn0 := le_of_lt (normalizer_pos p q hp hq N n hn)
    have hk0 := inv_nonneg.mpr (le_of_lt (normalizer_pos p q hp hq N k.val (by omega)))
    exact mul_nonneg (mul_nonneg (mul_nonneg hm0 hn0) (hg k)) hk0
  · rw [hraw,hprod,Finset.smul_sum]
    simp only [normalizedElementary,smul_smul,mul_assoc,t]

end Szkraw
