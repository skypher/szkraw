import Szkraw.KrawtchoukMargin
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Algebra.Order.Field

namespace Szkraw

abbrev FiniteArray (N : ℕ) := Fin 3 → Fin (N+1) → ℝ

noncomputable def arrayCoefficients {N : ℕ} (A : FiniteArray N) : Coefficients N where
  a i := if hi : i ≤ N then A 0 ⟨i,by omega⟩ else 0
  b i := if hi : i ≤ N then A 1 ⟨i,by omega⟩ else 0
  c i := if hi : i ≤ N then A 2 ⟨i,by omega⟩ else 0

theorem array_coeff_a {N : ℕ} (A : FiniteArray N) (i : Fin (N+1)) :
    (arrayCoefficients A).a i.val = A 0 i := by simp [arrayCoefficients,show i.val ≤ N by omega]
theorem array_coeff_b {N : ℕ} (A : FiniteArray N) (i : Fin (N+1)) :
    (arrayCoefficients A).b i.val = A 1 i := by simp [arrayCoefficients,show i.val ≤ N by omega]
theorem array_coeff_c {N : ℕ} (A : FiniteArray N) (i : Fin (N+1)) :
    (arrayCoefficients A).c i.val = A 2 i := by simp [arrayCoefficients,show i.val ≤ N by omega]

def AffineConventions {N : ℕ} (A : FiniteArray N) : Prop :=
  A 0 0 = 1 ∧ A 1 0 = 0 ∧ A 2 0 = 0 ∧ A 0 ⟨N,by omega⟩ = 0 ∧
    ∀ i : Fin (N+1), A 0 i+A 1 i+A 2 i = 1

noncomputable def referenceArray (N : ℕ) (r : ℝ) : FiniteArray N := fun c i =>
  if c.val = 0 then (krawCoefficients N r).a i.val
  else if c.val = 1 then (krawCoefficients N r).b i.val
  else (krawCoefficients N r).c i.val

theorem reference_array_affine (N : ℕ) (hN : 1 ≤ N) (r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
    AffineConventions (referenceArray N r) := by
  have hv := kraw_admissible N hN r hr (le_of_lt hr1)
  refine ⟨?_,?_,?_,?_,?_⟩
  · simpa [referenceArray] using hv.2.1
  · simpa [referenceArray] using hv.2.2.1
  · simpa [referenceArray] using hv.2.2.2.1
  · simpa [referenceArray] using hv.2.2.2.2.1
  · intro i
    simpa [referenceArray] using hv.2.2.2.2.2.1 i.val (by omega)

noncomputable def coefficientWindow (N : ℕ) (r : ℝ) : Set (FiniteArray N) :=
  {A | (∀ c i, |A c i-referenceArray N r c i| < perturbationRadius N r) ∧
    (∀ c i, 0 < referenceArray N r c i → 0 < A c i)}

theorem coefficient_window_open (N : ℕ) (r : ℝ) : IsOpen (coefficientWindow N r) := by
  have heval (c : Fin 3) (i : Fin (N+1)) : Continuous (fun A : FiniteArray N => A c i) :=
    (continuous_apply i).comp (continuous_apply c)
  have hforall {ι : Type} [Finite ι] (P : ι → FiniteArray N → Prop)
      (h : ∀ i, IsOpen {A | P i A}) : IsOpen {A | ∀ i, P i A} :=
    (Set.ofPred_forall P).symm ▸ isOpen_iInter_of_finite h
  apply IsOpen.inter
  · refine hforall (fun c : Fin 3 => fun A => ∀ i : Fin (N+1),
      |A c i-referenceArray N r c i| < perturbationRadius N r) ?_
    intro c
    refine hforall (fun i : Fin (N+1) => fun A =>
      |A c i-referenceArray N r c i| < perturbationRadius N r) ?_
    intro i
    exact isOpen_lt ((heval c i).sub continuous_const).abs continuous_const
  · refine hforall (fun c : Fin 3 => fun A => ∀ i : Fin (N+1),
      0 < referenceArray N r c i → 0 < A c i) ?_
    intro c
    refine hforall (fun i : Fin (N+1) => fun A =>
      0 < referenceArray N r c i → 0 < A c i) ?_
    intro i
    by_cases hi : 0 < referenceArray N r c i
    · simpa only [hi,true_implies] using isOpen_lt continuous_const (heval c i)
    · simp [hi]

theorem reference_mem_window (N : ℕ) (hN : 1 ≤ N) (r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
    referenceArray N r ∈ coefficientWindow N r := by
  have hn : 0 < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hs : 0 < min r (1-r) := lt_min hr (by linarith)
  have hη : 0 < perturbationRadius N r := by unfold perturbationRadius; positivity
  exact ⟨fun _ _ => by simpa using hη,fun _ _ h => h⟩

theorem window_admissible_close {N : ℕ} (hN : 1 ≤ N) (r : ℝ) (hr : 0 < r) (hr1 : r < 1)
    (A : FiniteArray N) (hA : A ∈ coefficientWindow N r) (hconv : AffineConventions A) :
    Admissible (arrayCoefficients A) ∧ CloseToKrawtchouk (arrayCoefficients A) r := by
  have hv := kraw_admissible N hN r hr (le_of_lt hr1)
  have hn : 0 < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hbounds (i : ℕ) (hi : i ≤ N) := hA.1 (0 : Fin 3) (⟨i,by omega⟩ : Fin (N+1))
  have hapos (i : ℕ) (hi : i < N) : 0 < (arrayCoefficients A).a i := by
    let fi : Fin (N+1) := ⟨i,by omega⟩
    have hh := hA.2 0 fi (by simpa [referenceArray,fi] using hv.2.2.2.2.2.2.1 i hi)
    simpa [arrayCoefficients,show i ≤ N by omega,fi] using hh
  have hcpos (i : ℕ) (hi : 0 < i) (hiN : i ≤ N) : 0 < (arrayCoefficients A).c i := by
    let fi : Fin (N+1) := ⟨i,by omega⟩
    have hh := hA.2 2 fi (by simpa [referenceArray,fi] using hv.2.2.2.2.2.2.2 i hi hiN)
    simpa [arrayCoefficients,hiN,fi] using hh
  have hbnon (i : ℕ) (hi : i ≤ N) : 0 ≤ (arrayCoefficients A).b i := by
    by_cases hi0 : i = 0
    · subst i
      have hh := hconv.2.1
      simpa [arrayCoefficients] using le_of_eq hh.symm
    · let fi : Fin (N+1) := ⟨i,by omega⟩
      have hbase : 0 < referenceArray N r 1 fi := by
        simp only [referenceArray,Fin.isValue,Fin.val_one,one_ne_zero,ite_false,ite_true,krawCoefficients]
        exact div_pos (mul_pos (by linarith) (by exact_mod_cast (by omega : 0 < i))) hn
      have hh := le_of_lt (hA.2 1 fi hbase)
      simpa [arrayCoefficients,hi,fi] using hh
  constructor
  · refine ⟨hN,?_,?_,?_,?_,?_,hapos,hcpos⟩
    · simpa [arrayCoefficients] using hconv.1
    · simpa [arrayCoefficients] using hconv.2.1
    · simpa [arrayCoefficients] using hconv.2.2.1
    · simpa [arrayCoefficients] using hconv.2.2.2.1
    · intro i hi
      simpa [arrayCoefficients,hi] using hconv.2.2.2.2 ⟨i,by omega⟩
  · refine ⟨hbnon,?_⟩
    intro i hi
    have ha := le_of_lt (hA.1 0 ⟨i,by omega⟩)
    have hb := le_of_lt (hA.1 1 ⟨i,by omega⟩)
    have hc := le_of_lt (hA.1 2 ⟨i,by omega⟩)
    simpa [arrayCoefficients,referenceArray,krawCoefficients,hi] using And.intro ha (And.intro hb hc)

/-- Every array in this relative neighborhood has the full quantitative property. -/
theorem coefficient_neighborhood_application {N : ℕ} (hN : 1 ≤ N) (r : ℝ)
    (hr : 0 < r) (hr1 : r < 1) (A : FiniteArray N)
    (hA : A ∈ coefficientWindow N r) (hconv : AffineConventions A) :
    FiniteRealization (arrayCoefficients A) ∧ MatrixPositivity (arrayCoefficients A) ∧
      PerturbationMargin (arrayCoefficients A) r := by
  have hh := window_admissible_close hN r hr hr1 A hA hconv
  exact perturbation_criterion N _ r hh.1 hr hr1 hh.2

/-- A nonempty open neighborhood in the affine convention subspace, for every asymmetric reference. -/
theorem relatively_open_coefficient_neighborhood (N : ℕ) (hN : 1 ≤ N) (r : ℝ)
    (hr : 0 < r) (hr1 : r < 1) :
    ∃ U : Set {A : FiniteArray N // AffineConventions A}, IsOpen U ∧
      (⟨referenceArray N r,reference_array_affine N hN r hr hr1⟩ : {A : FiniteArray N // AffineConventions A}) ∈ U ∧
      ∀ A ∈ U, FiniteRealization (arrayCoefficients A.val) ∧ MatrixPositivity (arrayCoefficients A.val) ∧
        PerturbationMargin (arrayCoefficients A.val) r := by
  refine ⟨Subtype.val ⁻¹' coefficientWindow N r,
    (coefficient_window_open N r).preimage continuous_subtype_val,reference_mem_window N hN r hr hr1,?_⟩
  intro A hA
  exact coefficient_neighborhood_application hN r hr hr1 A.val hA A.property

end Szkraw
