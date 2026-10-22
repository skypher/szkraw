import Szkraw.KrawtchoukMargin

namespace Szkraw

noncomputable def singlePerturbation (N : ℕ) (h : ℝ) : Coefficients N where
  a i := (krawCoefficients N (1/2)).a i - if i = 1 then h else 0
  b i := (krawCoefficients N (1/2)).b i + if i = 1 then h else 0
  c i := (krawCoefficients N (1/2)).c i

theorem half_radius_identity (N : ℕ) :
    (1/4 : ℝ)*((64*(N : ℝ))⁻¹)^N = perturbationRadius N (1/2)/2 := by
  unfold perturbationRadius
  norm_num only [show (1 : ℝ)-(1/2) = 1/2 by norm_num,min_self]
  have he : (1/2 : ℝ)/(32*N) = (64*(N : ℝ))⁻¹ := by ring
  rw [he]
  ring

theorem single_perturbation_admissible (N : ℕ) (hN : 2 ≤ N) (h : ℝ)
    (hh : 0 < h) (hhb : h ≤ (1/4 : ℝ)*((64*(N : ℝ))⁻¹)^N) :
    Admissible (singlePerturbation N h) := by
  have hv := kraw_admissible N (by omega) (1/2) (by norm_num) (by norm_num)
  have hn1 : N ≠ 1 := by omega
  have hn : 0 < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hη := perturbation_radius_small N (by omega) (1/2) (by norm_num) (by norm_num)
  rw [half_radius_identity] at hhb
  have hbase : 1/(N : ℝ) ≤ ((N : ℝ)-1)/N := by
    apply div_le_div_of_nonneg_right _ (le_of_lt hn)
    have hn2 : 2 ≤ (N : ℝ) := by exact_mod_cast hN
    linarith
  refine ⟨by omega,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa [singlePerturbation] using hv.2.1
  · simpa [singlePerturbation] using hv.2.2.1
  · exact hv.2.2.2.1
  · simpa [singlePerturbation,hn1] using hv.2.2.2.2.1
  · intro i hi
    have hs := hv.2.2.2.2.2.1 i hi
    dsimp [singlePerturbation]
    linarith
  · intro i hi
    by_cases hi1 : i = 1
    · subst i
      dsimp [singlePerturbation,krawCoefficients]
      simp only [ite_true,Nat.cast_one]
      have heq : 1/(2*(N : ℝ)) = (1/(N : ℝ))/2 := by ring
      rw [heq] at hη
      linarith
    · simpa [singlePerturbation,hi1] using hv.2.2.2.2.2.2.1 i hi
  · intro i hi hiN
    exact hv.2.2.2.2.2.2.2 i hi hiN

theorem single_perturbation_close (N : ℕ) (hN : 2 ≤ N) (h : ℝ)
    (hh : 0 < h) (hhb : h ≤ (1/4 : ℝ)*((64*(N : ℝ))⁻¹)^N) :
    CloseToKrawtchouk (singlePerturbation N h) (1/2) := by
  have hη := perturbation_radius_nonneg N (by omega) (1/2) (by norm_num) (by norm_num)
  rw [half_radius_identity] at hhb
  have hhη : h ≤ perturbationRadius N (1/2) := by linarith
  constructor
  · intro i hi
    dsimp [singlePerturbation,krawCoefficients]
    have hn : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
    have hi0 : 0 ≤ (i : ℝ) := Nat.cast_nonneg i
    split_ifs <;> positivity
  · intro i hi
    dsimp [singlePerturbation,krawCoefficients]
    by_cases hi1 : i = 1
    · simp [hi1,abs_of_nonneg (le_of_lt hh),abs_neg]
      simpa only [one_div] using And.intro hhη hη
    · simp [hi1]
      simpa only [one_div] using hη

/-- The constant-ratio hypothesis of the geometric criterion fails: `b_1/c_1 ≠ b_N/c_N`. -/
theorem single_perturbation_not_constant_ratio (N : ℕ) (hN : 2 ≤ N) (h : ℝ) (hh : 0 < h) :
    ¬ ∃ β : ℝ, ∀ i, 0 < i → i ≤ N → (singlePerturbation N h).b i = β * (singlePerturbation N h).c i := by
  rintro ⟨β,hratio⟩
  have hn1 : N ≠ 1 := by omega
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  have hlast := hratio N (by omega) le_rfl
  have hbN : (krawCoefficients N (1/2)).b N = 1/2 := by dsimp [krawCoefficients]; field_simp <;> norm_num
  have hcN : (krawCoefficients N (1/2)).c N = 1/2 := by dsimp [krawCoefficients]; field_simp <;> norm_num
  change (krawCoefficients N (1/2)).b N + (if N = 1 then h else 0) = β*(krawCoefficients N (1/2)).c N at hlast
  rw [if_neg hn1,hbN,hcN,add_zero] at hlast
  have he : β = 1 := by linarith
  have hfirst := hratio 1 (by omega) (by omega)
  dsimp [singlePerturbation,krawCoefficients] at hfirst
  norm_num [he] at hfirst
  linarith

theorem single_perturbation_not_geometric (N : ℕ) (hN : 2 ≤ N) (h : ℝ) (hh : 0 < h) :
    ¬ Geometric (singlePerturbation N h) := by
  rintro ⟨β,q,hβ,hq,hratio,hinc,hrec⟩
  exact single_perturbation_not_constant_ratio N hN h hh ⟨β,hratio⟩

/-- The paper's explicit finite examples outside the geometric family. -/
theorem nongeometric_perturbation_example (N : ℕ) (hN : 2 ≤ N) (h : ℝ)
    (hh : 0 < h) (hhb : h ≤ (1/4 : ℝ)*((64*(N : ℝ))⁻¹)^N) :
    Admissible (singlePerturbation N h) ∧ ¬ Geometric (singlePerturbation N h) ∧
    (¬ ∃ β : ℝ, ∀ i, 0 < i → i ≤ N → (singlePerturbation N h).b i = β * (singlePerturbation N h).c i) ∧
    FiniteRealization (singlePerturbation N h) ∧ MatrixPositivity (singlePerturbation N h) ∧
    PerturbationMargin (singlePerturbation N h) (1/2) := by
  have ha := single_perturbation_admissible N hN h hh hhb
  have hc := single_perturbation_close N hN h hh hhb
  have ht := perturbation_criterion N _ (1/2) ha (by norm_num) (by norm_num) hc
  exact ⟨ha,single_perturbation_not_geometric N hN h hh,single_perturbation_not_constant_ratio N hN h hh,
    ht.1,ht.2.1,ht.2.2⟩

end Szkraw
