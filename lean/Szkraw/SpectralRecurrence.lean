import Szkraw.Stationary
import Szkraw.Representation

namespace Szkraw

/-- The scalar recurrence determines every coordinate from its initial value. -/
theorem scalar_recurrence_solution {N : ℕ} (v : Coefficients N) (hv : Admissible v)
    (x : ℝ) (U : ℕ → ℝ)
    (h1 : U 1 = x * U 0)
    (hr : ∀ k, k+1 < N → x*U (k+1) =
      v.a (k+1)*U (k+2) + v.b (k+1)*U (k+1) + v.c (k+1)*U k)
    (m : ℕ) (hm : m ≤ N) :
    U m = (recurrencePolynomial v m).eval x * U 0 := by
  rcases hv with ⟨hN,ha0,hb0,hc0,haN,hsum,hapos,hcpos⟩
  induction m using Nat.twoStepInduction with
  | zero => simp [recurrencePolynomial,polynomialPair]
  | one => simpa [recurrencePolynomial,polynomialPair,ha0,hb0,hc0] using h1
  | more k ih0 ih1 =>
      have h := hr k (by omega)
      rw [ih0 (by omega),ih1 (by omega)] at h
      change U (k+2) = (Polynomial.C (v.a (k+1))⁻¹ *
        ((Polynomial.X-Polynomial.C (v.b (k+1))) * recurrencePolynomial v (k+1) -
          Polynomial.C (v.c (k+1)) * recurrencePolynomial v k)).eval x * U 0
      simp only [Polynomial.eval_mul,Polynomial.eval_sub,Polynomial.eval_C,Polynomial.eval_X]
      have ha := ne_of_gt (hapos (k+1) (by omega))
      apply (mul_left_cancel₀ ha)
      field_simp
      nlinarith [h]

/-- A right eigenvector of the finite Jacobi matrix is a polynomial sequence. -/
theorem eigenvector_polynomial {N : ℕ} (v : Coefficients N) (hv : Admissible v)
    (x : ℝ) (u : Fin (N+1) → ℝ)
    (hu : ∀ i, x*u i = ∑ j, recurrenceMatrix v i j*u j)
    (i : Fin (N+1)) :
    u i = (recurrencePolynomial v i.val).eval x * u 0 := by
  classical
  let U : ℕ → ℝ := fun k => if hk : k ≤ N then u ⟨k,by omega⟩ else 0
  have hU (j : Fin (N+1)) : U j.val = u j := by simp [U,show j.val ≤ N by omega]
  have hz : ∀ k, N < k → U k = 0 := by intro k hk; simp [U,show ¬k ≤ N by omega]
  have hrow (j : Fin (N+1)) : x*U j.val =
      v.a j.val*U (j.val+1) + v.b j.val*U j.val +
      (if j.val = 0 then 0 else v.c j.val*U (j.val-1)) := by
    have hh := recurrence_row_action v U hz j
    simp only [smul_eq_mul,hU] at hh
    rw [hU,hu,hh]
  have h1 : U 1 = x*U 0 := by
    have hh := hrow 0
    simpa [hv.2.1,hv.2.2.1] using hh.symm
  have hr : ∀ k, k+1 < N → x*U (k+1) =
      v.a (k+1)*U (k+2)+v.b (k+1)*U (k+1)+v.c (k+1)*U k := by
    intro k hk
    simpa using hrow ⟨k+1,by omega⟩
  have hh := scalar_recurrence_solution v hv x U h1 hr i.val (by omega)
  simpa [U,show i.val ≤ N by omega] using hh

/-- No nonzero eigenvector can vanish at the distinguished endpoint. -/
theorem eigenvector_initial_nonzero {N : ℕ} (v : Coefficients N) (hv : Admissible v)
    (x : ℝ) (u : Fin (N+1) → ℝ)
    (hu : ∀ i, x*u i = ∑ j, recurrenceMatrix v i j*u j)
    (hne : u ≠ 0) : u 0 ≠ 0 := by
  intro hz
  apply hne
  funext i
  rw [eigenvector_polynomial v hv x u hu i,hz,mul_zero]
  rfl

/-- Diagonal similarity transports the symmetric eigenvectors to right eigenvectors. -/
theorem symmetrized_eigenvector {N : ℕ} (v : Coefficients N) (hv : Admissible v)
    (x : ℝ) (u : Fin (N+1) → ℝ)
    (hu : ∀ i, ∑ j, symmetrizedMatrix v i j*u j = x*u i)
    (i : Fin (N+1)) :
    x*(u i / Real.sqrt (reversibleWeight v i.val)) =
      ∑ j, recurrenceMatrix v i j*(u j / Real.sqrt (reversibleWeight v j.val)) := by
  have hs : Real.sqrt (reversibleWeight v i.val) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr (reversible_weight_pos v hv i.val (by omega)))
  apply (mul_left_cancel₀ hs)
  calc
    _ = x*u i := by field_simp
    _ = ∑ j, symmetrizedMatrix v i j*u j := (hu i).symm
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      dsimp [symmetrizedMatrix]
      ring

/-- Every nonzero symmetric eigenvector has nonzero endpoint coordinate. -/
theorem symmetrized_initial_nonzero {N : ℕ} (v : Coefficients N) (hv : Admissible v)
    (x : ℝ) (u : Fin (N+1) → ℝ)
    (hu : ∀ i, ∑ j, symmetrizedMatrix v i j*u j = x*u i)
    (hne : u ≠ 0) : u 0 ≠ 0 := by
  let w : Fin (N+1) → ℝ := fun i => u i / Real.sqrt (reversibleWeight v i.val)
  have hw : w ≠ 0 := by
    intro hz
    apply hne
    funext i
    have hh := congrFun hz i
    have hs : Real.sqrt (reversibleWeight v i.val) ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.mpr (reversible_weight_pos v hv i.val (by omega)))
    simpa [w,hs] using hh
  have hh := eigenvector_initial_nonzero v hv x w (symmetrized_eigenvector v hv x u hu) hw
  simpa [w,reversibleWeight] using hh

/-- Positivity of the endpoint spectral weights for the actual spectral basis. -/
theorem spectral_weight_pos {N : ℕ} (v : Coefficients N) (hv : Admissible v)
    (t : Fin (N+1)) :
    0 < (((symmetrized_matrix_hermitian v hv).eigenvectorBasis t) 0 : ℝ)^2 := by
  let hH := symmetrized_matrix_hermitian v hv
  have he := hH.mulVec_eigenvectorBasis t
  have hu : ∀ i, ∑ j, symmetrizedMatrix v i j*
      (hH.eigenvectorBasis t) j = hH.eigenvalues t*(hH.eigenvectorBasis t) i := by
    intro i
    exact congrFun he i
  have hn : (fun i => (hH.eigenvectorBasis t) i) ≠ 0 :=
    (WithLp.ofLp_eq_zero 2).ne.2 (hH.eigenvectorBasis.orthonormal.ne_zero t)
  exact sq_pos_of_ne_zero (symmetrized_initial_nonzero v hv _ _ hu hn)

end Szkraw
