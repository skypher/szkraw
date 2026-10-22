import Szkraw.ParitySplit
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Symmetry of the orthogonality measure of a symmetric array (paper, Theorem 7.1)

For `b ≡ 0` the polynomials have parity, `R_m(-y) = (-1)^m R_m(y)`, so the terminal polynomial is
even or odd and the reflection of a support point is again a support point (the support consists
of the `N + 1` distinct roots of a polynomial of degree `N + 1`). The weights are determined by
`Σ_t w_t R_m(x_t) = [m = 0]`, an invertible linear system, so they are reflection invariant.
-/

namespace Szkraw

open Finset Polynomial

variable {N : ℕ}

/-- The data of a finite realization (the body of `FiniteRealization`). -/
def IsRealization (v : Coefficients N) (x w : Fin (N + 1) → ℝ) : Prop :=
  Function.Injective x ∧
    (∀ t, 0 < w t) ∧ (∑ t, w t) = 1 ∧
    (∀ m, m ≤ N → (recurrencePolynomial v m).eval 1 = 1) ∧
    (∀ (m : ℕ) (n : Fin (N+1)), m ≤ N →
      ∑ k : Fin (N+1), productMatrix v m n k = 1) ∧
    (∀ m n, m ≤ N → n ≤ N → m ≠ n →
      ∑ t, w t * (recurrencePolynomial v m).eval (x t) *
        (recurrencePolynomial v n).eval (x t) = 0) ∧
    (∀ m, m ≤ N → 0 < ∑ t, w t * ((recurrencePolynomial v m).eval (x t))^2) ∧
    (∀ t, (x t-v.b N) * (recurrencePolynomial v N).eval (x t) -
      v.c N * (recurrencePolynomial v (N-1)).eval (x t) = 0) ∧
    (∀ (m : ℕ) (n t : Fin (N+1)), m ≤ N →
      (recurrencePolynomial v m).eval (x t) *
        (recurrencePolynomial v n.val).eval (x t) =
      ∑ k : Fin (N+1), productMatrix v m n k *
        (recurrencePolynomial v k.val).eval (x t))

theorem finiteRealization_iff (v : Coefficients N) :
    FiniteRealization v ↔ ∃ x w, IsRealization v x w := Iff.rfl

/-- Parity of the polynomials of a symmetric array. -/
theorem poly_parity (v : Coefficients N) (hb : ∀ i, i ≤ N → v.b i = 0) :
    ∀ m, m ≤ N + 1 → ∀ y : ℝ, (polynomialPair v m).2.eval (-y) = (-1) ^ m * (polynomialPair v m).2.eval y ∧
      (polynomialPair v m).1.eval (-y) = (-1) ^ (m + 1) * (polynomialPair v m).1.eval y := by
  intro m
  induction m with
  | zero => intro _ y; simp [polynomialPair]
  | succ m ih =>
    intro hm y
    obtain ⟨h2, h1⟩ := ih (by omega) y
    refine ⟨?_, ?_⟩
    · show (C (v.a m)⁻¹ * ((X - C (v.b m)) * (polynomialPair v m).2 - C (v.c m) * (polynomialPair v m).1)).eval (-y) =
        (-1) ^ (m + 1) * (C (v.a m)⁻¹ * ((X - C (v.b m)) * (polynomialPair v m).2 -
          C (v.c m) * (polynomialPair v m).1)).eval y
      simp only [eval_mul, eval_sub, eval_C, eval_X, h1, h2, hb m (by omega)]
      ring
    · show (polynomialPair v m).2.eval (-y) = (-1) ^ (m + 1 + 1) * (polynomialPair v m).2.eval y
      rw [h2, pow_succ, pow_succ]; ring

/-- Coefficients: `R_m` has degree at most `m` with nonzero coefficient of `x^m`. -/
theorem poly_coeff (v : Coefficients N) (ha : ∀ i, i < N → v.a i ≠ 0) :
    ∀ m, m ≤ N → (∀ j, m < j → (polynomialPair v m).2.coeff j = 0) ∧
      (polynomialPair v m).2.coeff m ≠ 0 ∧ (∀ j, m ≤ j → (polynomialPair v m).1.coeff j = 0) := by
  intro m
  induction m with
  | zero =>
    intro _
    refine ⟨fun j hj => ?_, by simp [polynomialPair], fun j _ => by simp [polynomialPair]⟩
    show (1 : ℝ[X]).coeff j = 0
    rw [coeff_one, if_neg (by omega)]
  | succ m ih =>
    intro hm
    obtain ⟨hP, hPm, hQ⟩ := ih (by omega)
    have e : (polynomialPair v (m + 1)).2 = C (v.a m)⁻¹ * ((X - C (v.b m)) * (polynomialPair v m).2 -
        C (v.c m) * (polynomialPair v m).1) := rfl
    have hco : ∀ j, ((X - C (v.b m)) * (polynomialPair v m).2 - C (v.c m) * (polynomialPair v m).1).coeff (j + 1) =
        (polynomialPair v m).2.coeff j - v.b m * (polynomialPair v m).2.coeff (j + 1) -
          v.c m * (polynomialPair v m).1.coeff (j + 1) := by
      intro j
      rw [coeff_sub, sub_mul, coeff_sub, coeff_X_mul, coeff_C_mul, coeff_C_mul]
    refine ⟨fun j hj => ?_, ?_, fun j hj => hP j (by omega)⟩
    · obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
      rw [e, coeff_C_mul, hco, hP j' (by omega), hP (j' + 1) (by omega), hQ (j' + 1) (by omega)]
      ring
    · rw [e, coeff_C_mul, hco, hP (m + 1) (by omega), hQ (m + 1) (by omega)]
      simp only [mul_zero, sub_zero]
      exact mul_ne_zero (inv_ne_zero (ha m (by omega))) hPm

/-- **Theorem 7.1**, symmetry of the measure: every finite realization of an array with `b ≡ 0` is
symmetric: the support is invariant under `x ↦ -x`, with equal weights at `x` and `-x`. -/
theorem realization_symmetric (v : Coefficients N) (hv : Admissible v) (hb : ∀ i, i ≤ N → v.b i = 0)
    (x w : Fin (N + 1) → ℝ) (hr : IsRealization v x w) :
    ∀ t, ∃ t', x t' = -x t ∧ w t' = w t := by
  obtain ⟨hinj, hwpos, hwsum, _, _, horth, hnorm, hterm, _⟩ := hr
  have ha : ∀ i, i < N → v.a i ≠ 0 := fun i hi => (hv.2.2.2.2.2.2.1 i hi).ne'
  have hN := hv.1
  have hpar := poly_parity v hb
  have hco := poly_coeff v ha
  -- `R_{N-1}` is the first component of the pair at `N`
  have hQ : (polynomialPair v N).1 = recurrencePolynomial v (N - 1) := by
    exact congrArg (fun k => (polynomialPair v k).1) (show N = N - 1 + 1 by omega)
  set T : ℝ[X] := (X - C (v.b N)) * recurrencePolynomial v N - C (v.c N) * (polynomialPair v N).1 with hT
  have hTeval : ∀ y, T.eval y = (y - v.b N) * (recurrencePolynomial v N).eval y -
      v.c N * (recurrencePolynomial v (N - 1)).eval y := by
    intro y; rw [hT, ← hQ]; simp [eval_mul, eval_sub]
  obtain ⟨hP0, hPN0, hQc⟩ := hco N le_rfl
  have hP : ∀ j, N < j → (recurrencePolynomial v N).coeff j = 0 := hP0
  have hPN : (recurrencePolynomial v N).coeff N ≠ 0 := hPN0
  have hTc : ∀ j, T.coeff (j + 1) = (recurrencePolynomial v N).coeff j -
      v.b N * (recurrencePolynomial v N).coeff (j + 1) - v.c N * (polynomialPair v N).1.coeff (j + 1) := by
    intro j; rw [hT, coeff_sub, sub_mul, coeff_sub, coeff_X_mul, coeff_C_mul, coeff_C_mul]
  have hT0 : T ≠ 0 := by
    intro h
    have := hTc N
    rw [h, coeff_zero, hP (N + 1) (by omega), hQc (N + 1) (by omega)] at this
    apply hPN; linarith
  have hTdeg : T.natDegree ≤ N + 1 := by
    rw [natDegree_le_iff_coeff_eq_zero]
    intro j hj
    obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    rw [hTc, hP j' (by omega), hP (j' + 1) (by omega), hQc (j' + 1) (by omega)]; ring
  have hroot : ∀ t, T.eval (x t) = 0 := fun t => by rw [hTeval]; exact hterm t
  have hroot' : ∀ t, T.eval (-x t) = 0 := by
    intro t
    have h1 := (hpar N (by omega) (x t)).1
    have h2 := (hpar N (by omega) (x t)).2
    have e : T.eval (-x t) = (-1) ^ (N + 1) * T.eval (x t) := by
      rw [hT]
      simp only [eval_mul, eval_sub, eval_C, eval_X, hb N le_rfl, sub_zero]
      show -x t * (polynomialPair v N).2.eval (-x t) - v.c N * (polynomialPair v N).1.eval (-x t) =
        (-1) ^ (N + 1) * (x t * (polynomialPair v N).2.eval (x t) - v.c N * (polynomialPair v N).1.eval (x t))
      rw [h1, h2, pow_succ]; ring
    rw [e, hroot t, mul_zero]
  -- reflection of nodes
  have hrefl : ∀ t, ∃ t', x t' = -x t := by
    intro t
    by_contra hne
    push Not at hne
    have hnot : -x t ∉ univ.image x := by
      simp only [Finset.mem_image, Finset.mem_univ, true_and, not_exists]; exact hne
    have hsub : insert (-x t) (univ.image x) ⊆ T.roots.toFinset := by
      intro y hy
      rw [Multiset.mem_toFinset, mem_roots hT0]
      rcases Finset.mem_insert.mp hy with h | h
      · rw [h]; exact hroot' t
      · obtain ⟨s, _, rfl⟩ := Finset.mem_image.mp h; exact hroot s
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_insert_of_notMem hnot, Finset.card_image_of_injective _ hinj, Finset.card_univ,
      Fintype.card_fin] at hcard
    have := (Multiset.toFinset_card_le T.roots).trans (card_roots' T)
    omega
  choose σ hσ using hrefl
  have hσinj : Function.Injective σ := by
    intro t1 t2 h
    apply hinj
    have := congrArg x h
    rw [hσ, hσ] at this; linarith
  have hσbij : Function.Bijective σ := (Finite.injective_iff_bijective).mp hσinj
  set e := Equiv.ofBijective σ hσbij
  -- weights: `Σ_t R_m(x_t) (w(σ t) - w t) = 0`, and the matrix `R_m(x_t)` is invertible
  set M : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ := fun m t => (recurrencePolynomial v m.val).eval (x t)
  have hmom : ∀ m : Fin (N + 1), ∑ t, (recurrencePolynomial v m.val).eval (x t) * w t =
      if m.val = 0 then 1 else 0 := by
    intro m
    split_ifs with h
    · rw [h]; simp [recurrencePolynomial, polynomialPair, hwsum]
    · have := horth m.val 0 (by omega) (by omega) h
      have h0 : recurrencePolynomial v 0 = 1 := rfl
      rw [h0] at this
      simp only [eval_one, mul_one] at this
      rw [← this]; apply sum_congr rfl; intro t _; ring
  set z : Fin (N + 1) → ℝ := fun t => w (σ t) - w t
  have hz : M.mulVec z = 0 := by
    ext m
    simp only [Matrix.mulVec, dotProduct, M, z, Pi.zero_apply, mul_sub, sum_sub_distrib]
    have h1 : ∑ t, (recurrencePolynomial v m.val).eval (x t) * w (σ t) =
        (-1) ^ m.val * ∑ s, (recurrencePolynomial v m.val).eval (x s) * w s := by
      rw [mul_sum]
      have := Equiv.sum_comp e (fun s => (-1) ^ m.val * ((recurrencePolynomial v m.val).eval (x s) * w s))
      rw [← this]
      apply sum_congr rfl; intro t _
      show _ = (-1) ^ m.val * ((recurrencePolynomial v m.val).eval (x (σ t)) * w (σ t))
      have hp := (hpar m.val (by omega) (x (σ t))).1
      rw [show -x (σ t) = x t by rw [hσ]; ring] at hp
      show (polynomialPair v m.val).2.eval (x t) * _ = _
      rw [hp]; simp only [recurrencePolynomial]; ring
    rw [h1, hmom m]
    split_ifs with h
    · rw [h]; ring
    · ring
  have hdet : M.det ≠ 0 := by
    have hG : M * Matrix.diagonal w * M.transpose =
        Matrix.diagonal (fun m : Fin (N + 1) => ∑ t, w t * ((recurrencePolynomial v m.val).eval (x t)) ^ 2) := by
      ext m n
      rw [Matrix.mul_apply, Matrix.diagonal_apply]
      simp_rw [Matrix.mul_diagonal, Matrix.transpose_apply]
      split_ifs with h
      · subst h; apply sum_congr rfl; intro t _; simp only [M]; ring
      · have := horth m.val n.val (by omega) (by omega) (fun h' => h (Fin.ext h'))
        rw [← this]; apply sum_congr rfl; intro t _; simp only [M]; ring
    have hdG := congrArg Matrix.det hG
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, Matrix.det_diagonal,
      Matrix.det_diagonal] at hdG
    intro h0
    rw [h0, zero_mul, zero_mul] at hdG
    have hpos : 0 < ∏ m : Fin (N + 1), ∑ t, w t * ((recurrencePolynomial v m.val).eval (x t)) ^ 2 :=
      prod_pos (fun m _ => hnorm m.val (by omega))
    linarith
  have hz0 := Matrix.eq_zero_of_mulVec_eq_zero hdet hz
  intro t
  refine ⟨σ t, hσ t, ?_⟩
  have := congrFun hz0 t
  simp only [z, Pi.zero_apply] at this
  linarith

/-- **Theorem 7.1** in full: for `0 < p_0 ≤ 1/2`, the array (7.2) has a finite realization (a
positive measure on `2N + 1` points with the product identities and coefficient sums one),
nonnegative linearization, and every such measure is symmetric. Sharpness is `szwarc_sharp`. -/
def Stmt_szwarc_full : Prop :=
  ∀ (N : ℕ), 1 ≤ N → ∀ p : ℝ, 0 < p → p ≤ 1 / 2 →
    FiniteRealization (szwarcCoefficients N p) ∧ MatrixPositivity (szwarcCoefficients N p) ∧
    ∀ x w, IsRealization (szwarcCoefficients N p) x w → ∀ t, ∃ t', x t' = -x t ∧ w t' = w t

theorem szwarc_full : Stmt_szwarc_full := by
  intro N hN p hp hp2
  obtain ⟨h1, h2⟩ := szwarc_system N hN p hp hp2
  exact ⟨h1, h2, fun x w hr => realization_symmetric _ (szwarc_admissible N hN p hp (by linarith))
    (fun _ _ => rfl) x w hr⟩

end Szkraw
