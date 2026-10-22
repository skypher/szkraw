import Szkraw.KrawtchoukMargin
import Szkraw.GeometricCriterion

namespace Szkraw

theorem geometric_d (N : ℕ) (p q : ℝ) (hp : 1 ≤ p) (hq : 1 ≤ q) (i : ℕ) :
    (geometricCoefficients N p q).b i+(geometricCoefficients N p q).c i =
      qInteger q i/qInteger q N := by
  dsimp [geometricCoefficients]
  have hp0 : p ≠ 0 := ne_of_gt (by linarith : 0 < p)
  field_simp
  ring

theorem geometric_increment (N : ℕ) (p q : ℝ) (hp : 1 ≤ p) (hq : 1 ≤ q)
    (i : ℕ) (hi : 0 < i) :
    ((geometricCoefficients N p q).b i+(geometricCoefficients N p q).c i) -
      ((geometricCoefficients N p q).b (i-1)+(geometricCoefficients N p q).c (i-1)) =
      q^(i-1)/qInteger q N := by
  rw [geometric_d N p q hp hq,geometric_d N p q hp hq]
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0)
  simp only [Nat.succ_sub_one,qInteger]
  ring

/-- The converse direction of the paper's coefficient-parametrization lemma. -/
theorem geometric_family_hypotheses (N : ℕ) (hN : 1 ≤ N) (p q : ℝ)
    (hp : 1 ≤ p) (hq : 1 ≤ q) : Geometric (geometricCoefficients N p q) := by
  have hQN := qInteger_pos q hq N (by omega)
  refine ⟨p-1,q,by linarith,hq,?_,?_,?_⟩
  · intro i hi hiN
    dsimp [geometricCoefficients]
    ring
  · intro i hi hiN
    rw [geometric_increment N p q hp hq i hi]
    exact div_pos (pow_pos (by linarith) _) hQN
  · intro i hi hiN
    have hs := geometric_increment N p q hp hq (i+1) (by omega)
    simp only [Nat.add_sub_cancel] at hs
    rw [hs,geometric_increment N p q hp hq i hi]
    have he : i = (i-1)+1 := by omega
    conv_lhs => rw [he,pow_succ]
    ring

/-- For `N = 1` the coefficients `(eq:parameters)` do not depend on `q`, so one may choose `q = 1`. -/
theorem geometric_coefficients_N_one (p q : ℝ) (i : ℕ) (hi : i ≤ 1) :
    (geometricCoefficients 1 p q).a i = (geometricCoefficients 1 p 1).a i ∧
    (geometricCoefficients 1 p q).b i = (geometricCoefficients 1 p 1).b i ∧
    (geometricCoefficients 1 p q).c i = (geometricCoefficients 1 p 1).c i := by
  interval_cases i <;> simp [geometricCoefficients, qInteger]

/-- Its first two increments differ, hence no Krawtchouk reference has this coefficient profile. -/
theorem geometric_not_kraw (N : ℕ) (hN : 2 ≤ N) (p q : ℝ)
    (hp : 1 ≤ p) (hq : 1 < q) :
    ¬ ∃ r : ℝ, ∀ i, i ≤ N →
      (geometricCoefficients N p q).b i+(geometricCoefficients N p q).c i =
      (krawCoefficients N r).b i+(krawCoefficients N r).c i := by
  rintro ⟨r,he⟩
  have h0 := he 0 (by omega)
  have h1 := he 1 (by omega)
  have h2 := he 2 (by omega)
  rw [geometric_d N p q hp (le_of_lt hq)] at h0 h1 h2
  simp only [qInteger,pow_zero,pow_one,zero_add] at h0 h1 h2
  dsimp [krawCoefficients] at h0 h1 h2
  have hQN := ne_of_gt (qInteger_pos q (le_of_lt hq) N (by omega))
  norm_num only [Nat.cast_zero,Nat.cast_one] at h0 h1 h2
  have hx : (1+q)/qInteger q N = 2*(1/qInteger q N) := by
    calc
      _ = (1-r)*2/(N : ℝ)+r*2/N := h2
      _ = 2*((1-r)*1/(N : ℝ)+r*1/N) := by ring
      _ = _ := by rw [←h1]
  have hh := (div_eq_iff hQN).mp hx
  have hi : 1/qInteger q N*qInteger q N = 1 := div_mul_cancel₀ 1 hQN
  nlinarith

theorem additional_geometric_class (N : ℕ) (hN : 2 ≤ N) (p q : ℝ)
    (hp : 1 ≤ p) (hq : 1 < q) :
    Admissible (geometricCoefficients N p q) ∧ Geometric (geometricCoefficients N p q) ∧
    FiniteRealization (geometricCoefficients N p q) ∧ MatrixPositivity (geometricCoefficients N p q) ∧
    ¬ ∃ r : ℝ, ∀ i, i ≤ N →
      (geometricCoefficients N p q).b i+(geometricCoefficients N p q).c i =
      (krawCoefficients N r).b i+(krawCoefficients N r).c i := by
  have ha := geometric_coefficients_admissible N (by omega) p q hp (le_of_lt hq)
  have hg := geometric_family_hypotheses N (by omega) p q hp (le_of_lt hq)
  have ht := geometric_criterion N _ ha hg
  exact ⟨ha,hg,ht.1,ht.2,geometric_not_kraw N hN p q hp hq⟩

end Szkraw
