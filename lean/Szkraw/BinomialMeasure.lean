import Szkraw.BooleanDistribution
import Szkraw.GeometricApplications

namespace Szkraw

noncomputable def binomialMass (p : ℝ) (N j : ℕ) : ℝ :=
  (N.choose j : ℝ)*(1/(p+1))^(N-j)*(p/(p+1))^j

noncomputable def binomialNode (p : ℝ) (N j : ℕ) : ℝ := 1-(p+1)*(j : ℝ)/(p*N)

theorem binomial_expectation_product (p : ℝ) (hp : 1 ≤ p) (N : ℕ) (hN : 1 ≤ N)
    (m n : ℕ) (hm : m ≤ N) (hn : n ≤ N) :
    (∑ j : Fin (N+1), binomialMass p N j.val *
      (recurrencePolynomial (geometricCoefficients N p 1) m).eval (binomialNode p N j.val) *
      (recurrencePolynomial (geometricCoefficients N p 1) n).eval (binomialNode p N j.val)) =
    towerTrace p 1 N (normalizedElementary p 1 N m*normalizedElementary p 1 N n) := by
  let f : ℕ → ℝ := fun j =>
    (recurrencePolynomial (geometricCoefficients N p 1) m).eval (binomialNode p N j)*
    (recurrencePolynomial (geometricCoefficients N p 1) n).eval (binomialNode p N j)
  have havg := cube_average_binomial p N f
  have heval (b : Fin N → Bool) : f (bitsWeight N b) =
      booleanEval p N b (normalizedElementary p 1 N m*normalizedElementary p 1 N n) := by
    rw [boolean_eval_mul]
    have hm' := boolean_polynomial_value p hp N hN b m hm
    have hn' := boolean_polynomial_value p hp N hN b n hn
    exact congrArg₂ (·*·) hm'.symm hn'.symm
  calc
    _ = cubeAverage p N (fun b => f (bitsWeight N b)) := by
      rw [havg]
      apply Finset.sum_congr rfl
      intro j _
      dsimp [f,binomialMass]
      ring
    _ = cubeAverage p N (fun b => booleanEval p N b
        (normalizedElementary p 1 N m*normalizedElementary p 1 N n)) := by
      congr 1
      funext b
      exact heval b
    _ = _ := cube_average_trace p hp N _

theorem binomial_orthogonal (p : ℝ) (hp : 1 ≤ p) (N : ℕ) (hN : 1 ≤ N)
    (m n : ℕ) (hm : m ≤ N) (hn : n ≤ N) (hmn : m ≠ n) :
    (∑ j : Fin (N+1), binomialMass p N j.val *
      (recurrencePolynomial (geometricCoefficients N p 1) m).eval (binomialNode p N j.val) *
      (recurrencePolynomial (geometricCoefficients N p 1) n).eval (binomialNode p N j.val)) = 0 := by
  rw [binomial_expectation_product p hp N hN m n hm hn]
  simp only [normalizedElementary,smul_mul_smul,tower_trace_smul,
    tower_trace_elementary_orthogonal p 1 N m n hmn,mul_zero]

theorem normalized_elementary_ne_zero (p q : ℝ) (hp : 1 ≤ p) (hq : 1 ≤ q)
    (N m : ℕ) (hm : m ≤ N) : normalizedElementary p q N m ≠ 0 := by
  obtain ⟨b,hb⟩ := bitsWeight_exists N m hm
  intro hz
  have he := congrArg (fun x => coordinate p q N x b) hz
  rw [normalizedElementary,coordinate_smul,coordinate_elementary,hb,if_pos rfl,
    coordinate_zero,mul_one] at he
  have ht := normalizer_pos p q hp hq N m hm
  exact (ne_of_gt (inv_pos.mpr ht)) he

theorem binomial_norm_pos (p : ℝ) (hp : 1 ≤ p) (N : ℕ) (hN : 1 ≤ N)
    (m : ℕ) (hm : m ≤ N) :
    0 < ∑ j : Fin (N+1), binomialMass p N j.val *
      ((recurrencePolynomial (geometricCoefficients N p 1) m).eval (binomialNode p N j.val))^2 := by
  have hh := binomial_expectation_product p hp N hN m m hm hm
  have ht := tower_trace_square_pos p 1 hp le_rfl N (normalizedElementary p 1 N m)
    (normalized_elementary_ne_zero p 1 hp le_rfl N m hm)
  rw [←hh] at ht
  simpa only [pow_two,mul_assoc] using ht

theorem binomial_mass_pos (p : ℝ) (hp : 1 ≤ p) (N : ℕ) (j : Fin (N+1)) :
    0 < binomialMass p N j.val := by
  have hc : 0 < (N.choose j.val : ℝ) := by exact_mod_cast Nat.choose_pos (by omega : j.val ≤ N)
  dsimp [binomialMass]
  positivity

theorem binomial_mass_sum (p : ℝ) (hp : 1 ≤ p) (N : ℕ) (hN : 1 ≤ N) :
    (∑ j : Fin (N+1), binomialMass p N j.val) = 1 := by
  have hh := binomial_expectation_product p hp N hN 0 0 (by omega) (by omega)
  have ht : ∀ L, towerTrace p 1 L 1 = 1 := by
    intro L
    induction L with
    | zero => rfl
    | succ L ih => exact ih
  simpa [recurrencePolynomial,polynomialPair,normalized_elementary_zero,ht N] using hh

theorem binomial_nodes_injective (p : ℝ) (hp : 1 ≤ p) (N : ℕ) (hN : 1 ≤ N) :
    Function.Injective (fun j : Fin (N+1) => binomialNode p N j.val) := by
  intro i j hij
  have hp0 : p ≠ 0 := ne_of_gt (by linarith : 0 < p)
  have hn0 : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  have hpN := mul_ne_zero hp0 hn0
  dsimp [binomialNode] at hij
  have hh : (p+1)*(i.val : ℝ)/(p*N) = (p+1)*(j.val : ℝ)/(p*N) := by linarith
  have he := congrArg (fun x : ℝ => x*(p*N)) hh
  rw [div_mul_cancel₀ _ hpN,div_mul_cancel₀ _ hpN] at he
  have hp1 : p+1 ≠ 0 := by linarith
  have hv := mul_left_cancel₀ hp1 he
  apply Fin.ext
  exact_mod_cast hv


theorem binomial_node_action (p : ℝ) (hp : 1 ≤ p) (N : ℕ) (hN : 1 ≤ N)
    (j i : Fin (N+1)) :
    binomialNode p N j.val *
      (recurrencePolynomial (geometricCoefficients N p 1) i.val).eval (binomialNode p N j.val) =
    ∑ k : Fin (N+1), recurrenceMatrix (geometricCoefficients N p 1) i k *
      (recurrencePolynomial (geometricCoefficients N p 1) k.val).eval (binomialNode p N j.val) := by
  obtain ⟨b,hb⟩ := bitsWeight_exists N j.val (by omega)
  let ε := booleanCharacter p N b
  let U := normalizedElementary p 1 N
  have hval (k : Fin (N+1)) : ε (normalizedElementary p 1 N k.val) =
      (recurrencePolynomial (geometricCoefficients N p 1) k.val).eval (binomialNode p N j.val) := by
    simpa only [ε,binomialNode,hb] using boolean_polynomial_value p hp N hN b k.val (by omega)
  have hx : ε (normalizedElementary p 1 N 1) = binomialNode p N j.val := by
    simpa only [ε,binomialNode,hb] using boolean_eval_normalized_one p hp N hN b
  have hh := congrArg ε (geometric_row_action p 1 hp le_rfl N hN i)
  simp only [map_mul,map_sum,map_smul] at hh
  rw [hx,hval i] at hh
  simpa only [hval,smul_eq_mul] using hh

theorem binomial_product_identity (p : ℝ) (hp : 1 ≤ p) (N : ℕ) (hN : 1 ≤ N)
    (m : ℕ) (n j : Fin (N+1)) :
    (recurrencePolynomial (geometricCoefficients N p 1) m).eval (binomialNode p N j.val) *
      (recurrencePolynomial (geometricCoefficients N p 1) n.val).eval (binomialNode p N j.val) =
    ∑ k : Fin (N+1), productMatrix (geometricCoefficients N p 1) m n k *
      (recurrencePolynomial (geometricCoefficients N p 1) k.val).eval (binomialNode p N j.val) := by
  simpa using representation_product (geometricCoefficients N p 1)
    (fun k => (recurrencePolynomial (geometricCoefficients N p 1) k.val).eval (binomialNode p N j.val))
    (binomialNode p N j.val) (fun i => by simpa using binomial_node_action p hp N hN j i) m n

/-- Exact parameter convention for the binomial measure in the manuscript. -/
theorem binomial_probability_parameters (p₀ : ℝ) (hp₀ : 0 < p₀) (hp₀half : p₀ ≤ 1/2) :
    1 ≤ (1-p₀)/p₀ ∧ 1/((1-p₀)/p₀+1) = p₀ ∧
      ((1-p₀)/p₀)/((1-p₀)/p₀+1) = 1-p₀ := by
  constructor
  · exact (le_div_iff₀ hp₀).mpr (by linarith)
  have hp0 := ne_of_gt hp₀
  constructor <;> field_simp <;> ring

/-- Orthogonality for the explicitly stated binomial weights, throughout the positive range. -/
theorem full_krawtchouk_binomial_range (N : ℕ) (hN : 1 ≤ N) (p₀ : ℝ)
    (hp₀ : 0 < p₀) (hp₀half : p₀ ≤ 1/2) :
    MatrixPositivity (geometricCoefficients N ((1-p₀)/p₀) 1) ∧
    (∀ m n, m ≤ N → n ≤ N → m ≠ n →
      ∑ j : Fin (N+1), (N.choose j.val : ℝ)*p₀^(N-j.val)*(1-p₀)^j.val *
        (recurrencePolynomial (geometricCoefficients N ((1-p₀)/p₀) 1) m).eval
          (binomialNode ((1-p₀)/p₀) N j.val) *
        (recurrencePolynomial (geometricCoefficients N ((1-p₀)/p₀) 1) n).eval
          (binomialNode ((1-p₀)/p₀) N j.val) = 0) ∧
    (∀ m, m ≤ N → 0 < ∑ j : Fin (N+1),
      (N.choose j.val : ℝ)*p₀^(N-j.val)*(1-p₀)^j.val *
        ((recurrencePolynomial (geometricCoefficients N ((1-p₀)/p₀) 1) m).eval
          (binomialNode ((1-p₀)/p₀) N j.val))^2) := by
  obtain ⟨hp,hα,hβ⟩ := binomial_probability_parameters p₀ hp₀ hp₀half
  refine ⟨geometric_family_matrix_positivity N hN _ 1 hp le_rfl,?_,?_⟩
  · intro m n hm hn hmn
    simpa only [binomialMass,hα,hβ] using binomial_orthogonal _ hp N hN m n hm hn hmn
  · intro m hm
    simpa only [binomialMass,hα,hβ] using binomial_norm_pos _ hp N hN m hm

theorem binomial_node_probability_convention (p₀ : ℝ) (hp₀ : 0 < p₀) (hp₀half : p₀ ≤ 1/2)
    (N : ℕ) (hN : 1 ≤ N) (j : ℕ) :
    binomialNode ((1-p₀)/p₀) N j = 1-(j : ℝ)/(N*(1-p₀)) := by
  have hp0 : p₀ ≠ 0 := ne_of_gt hp₀
  have hs : 1-p₀ ≠ 0 := by linarith
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  unfold binomialNode
  field_simp
  ring

theorem binomial_normalized_at_zero (p : ℝ) (hp : 1 ≤ p) (N : ℕ) (hN : 1 ≤ N)
    (m : ℕ) (hm : m ≤ N) :
    (recurrencePolynomial (geometricCoefficients N p 1) m).eval (binomialNode p N 0) = 1 := by
  simpa [binomialNode] using recurrence_normalized _
    (geometric_coefficients_admissible N hN p 1 hp le_rfl) m hm

end Szkraw
