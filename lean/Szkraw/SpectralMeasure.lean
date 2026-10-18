import Szkraw.SpectralRecurrence

namespace Szkraw

noncomputable def spectralNode {N : ℕ} (v : Coefficients N) (hv : Admissible v) :=
  (symmetrized_matrix_hermitian v hv).eigenvalues

noncomputable def spectralEntry {N : ℕ} (v : Coefficients N) (hv : Admissible v)
    (i t : Fin (N+1)) : ℝ :=
  (symmetrized_matrix_hermitian v hv).eigenvectorBasis t i

noncomputable def spectralWeight {N : ℕ} (v : Coefficients N) (hv : Admissible v)
    (t : Fin (N+1)) : ℝ := spectralEntry v hv 0 t ^ 2

theorem spectral_rows {N : ℕ} (v : Coefficients N) (hv : Admissible v)
    (i j : Fin (N+1)) :
    ∑ t, spectralEntry v hv i t * spectralEntry v hv j t = if i = j then 1 else 0 := by
  have h := congrArg (fun M : Matrix (Fin (N+1)) (Fin (N+1)) ℝ => M i j)
    (Unitary.coe_mul_star_self (symmetrized_matrix_hermitian v hv).eigenvectorUnitary)
  simpa [Matrix.mul_apply,Matrix.star_apply,Matrix.one_apply,spectralEntry] using h

theorem spectral_columns {N : ℕ} (v : Coefficients N) (hv : Admissible v)
    (s t : Fin (N+1)) :
    ∑ i, spectralEntry v hv i s * spectralEntry v hv i t = if s = t then 1 else 0 := by
  have h := congrArg (fun M : Matrix (Fin (N+1)) (Fin (N+1)) ℝ => M s t)
    (Unitary.coe_star_mul_self (symmetrized_matrix_hermitian v hv).eigenvectorUnitary)
  simpa [Matrix.mul_apply,Matrix.star_apply,Matrix.one_apply,spectralEntry] using h

theorem spectral_weight_sum {N : ℕ} (v : Coefficients N) (hv : Admissible v) :
    ∑ t, spectralWeight v hv t = 1 := by
  simpa [spectralWeight,pow_two] using spectral_rows v hv 0 0

theorem spectral_entry_polynomial {N : ℕ} (v : Coefficients N) (hv : Admissible v)
    (i t : Fin (N+1)) :
    spectralEntry v hv i t = Real.sqrt (reversibleWeight v i.val) *
      (recurrencePolynomial v i.val).eval (spectralNode v hv t) * spectralEntry v hv 0 t := by
  let u := fun i => spectralEntry v hv i t
  have he := (symmetrized_matrix_hermitian v hv).mulVec_eigenvectorBasis t
  have hu : ∀ i, ∑ j, symmetrizedMatrix v i j*u j = spectralNode v hv t*u i := by
    intro i
    exact congrFun he i
  have hh := eigenvector_polynomial v hv (spectralNode v hv t)
    (fun j => u j / Real.sqrt (reversibleWeight v j.val))
    (symmetrized_eigenvector v hv _ u hu) i
  have hs : Real.sqrt (reversibleWeight v i.val) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr (reversible_weight_pos v hv i.val (by omega)))
  simp only [Fin.val_zero,reversibleWeight,Real.sqrt_one,div_one] at hh
  apply (div_eq_iff hs).mp at hh
  dsimp [u] at hh
  rw [hh]
  ring

theorem spectral_nodes_injective {N : ℕ} (v : Coefficients N) (hv : Admissible v) :
    Function.Injective (spectralNode v hv) := by
  intro s t he
  by_contra hst
  have hc := spectral_columns v hv s t
  have hd := spectral_columns v hv s s
  simp only [if_neg hst] at hc
  simp only [ite_true] at hd
  have hx (i : Fin (N+1)) :
      spectralEntry v hv i s * spectralEntry v hv 0 t =
        spectralEntry v hv i t * spectralEntry v hv 0 s := by
    rw [spectral_entry_polynomial v hv i s,spectral_entry_polynomial v hv i t,he]
    ring
  have hz : spectralEntry v hv 0 t = 0 := by
    calc
      _ = (∑ i, spectralEntry v hv i s * spectralEntry v hv i s) *
          spectralEntry v hv 0 t := by rw [hd,one_mul]
      _ = (∑ i, spectralEntry v hv i s * spectralEntry v hv i t) *
          spectralEntry v hv 0 s := by
        simp only [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i _
        calc
          _ = spectralEntry v hv i s * (spectralEntry v hv i s * spectralEntry v hv 0 t) := by ring
          _ = spectralEntry v hv i s * (spectralEntry v hv i t * spectralEntry v hv 0 s) := by rw [hx]
          _ = _ := by ring
      _ = 0 := by rw [hc,zero_mul]
  have hp := spectral_weight_pos v hv t
  change 0 < spectralEntry v hv 0 t ^ 2 at hp
  rw [hz] at hp
  norm_num at hp

theorem spectral_moment_scaled {N : ℕ} (v : Coefficients N) (hv : Admissible v)
    (i j : Fin (N+1)) :
    (Real.sqrt (reversibleWeight v i.val) * Real.sqrt (reversibleWeight v j.val)) *
      (∑ t, spectralWeight v hv t *
        (recurrencePolynomial v i.val).eval (spectralNode v hv t) *
        (recurrencePolynomial v j.val).eval (spectralNode v hv t)) =
      if i = j then 1 else 0 := by
  rw [←spectral_rows v hv i j,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t _
  rw [spectral_entry_polynomial v hv i t,spectral_entry_polynomial v hv j t]
  dsimp [spectralWeight]
  ring

theorem spectral_orthogonal {N : ℕ} (v : Coefficients N) (hv : Admissible v)
    (i j : Fin (N+1)) (hij : i ≠ j) :
    ∑ t, spectralWeight v hv t *
      (recurrencePolynomial v i.val).eval (spectralNode v hv t) *
      (recurrencePolynomial v j.val).eval (spectralNode v hv t) = 0 := by
  have h := spectral_moment_scaled v hv i j
  rw [if_neg hij] at h
  have hi := Real.sqrt_pos.mpr (reversible_weight_pos v hv i.val (by omega))
  have hj := Real.sqrt_pos.mpr (reversible_weight_pos v hv j.val (by omega))
  exact (mul_eq_zero.mp h).resolve_left (ne_of_gt (mul_pos hi hj))

theorem spectral_norm_pos {N : ℕ} (v : Coefficients N) (hv : Admissible v)
    (i : Fin (N+1)) :
    0 < ∑ t, spectralWeight v hv t *
      ((recurrencePolynomial v i.val).eval (spectralNode v hv t))^2 := by
  have h := spectral_moment_scaled v hv i i
  simp only [ite_true] at h
  have hi := Real.sqrt_pos.mpr (reversible_weight_pos v hv i.val (by omega))
  have hh : 0 < ∑ t, spectralWeight v hv t *
      (recurrencePolynomial v i.val).eval (spectralNode v hv t) *
      (recurrencePolynomial v i.val).eval (spectralNode v hv t) := by
    exact (mul_pos_iff_of_pos_left (mul_pos hi hi)).mp (by rw [h]; norm_num)
  simpa only [pow_two,mul_assoc] using hh

theorem spectral_node_action {N : ℕ} (v : Coefficients N) (hv : Admissible v)
    (t i : Fin (N+1)) :
    spectralNode v hv t * (recurrencePolynomial v i.val).eval (spectralNode v hv t) =
      ∑ j, recurrenceMatrix v i j *
        (recurrencePolynomial v j.val).eval (spectralNode v hv t) := by
  let u := fun j => spectralEntry v hv j t
  let w := fun j => u j / Real.sqrt (reversibleWeight v j.val)
  have he := (symmetrized_matrix_hermitian v hv).mulVec_eigenvectorBasis t
  have hu : ∀ j, ∑ k, symmetrizedMatrix v j k*u k = spectralNode v hv t*u j := by
    intro j
    exact congrFun he j
  have hw := symmetrized_eigenvector v hv (spectralNode v hv t) u hu
  have hf (j : Fin (N+1)) : w j =
      (recurrencePolynomial v j.val).eval (spectralNode v hv t)*w 0 :=
    eigenvector_polynomial v hv _ w hw j
  have hn : w 0 ≠ 0 := by
    have hp := spectral_weight_pos v hv t
    change 0 < spectralEntry v hv 0 t ^ 2 at hp
    intro hz
    have hz0 : spectralEntry v hv 0 t = 0 := by simpa [w,u,reversibleWeight] using hz
    rw [hz0] at hp
    norm_num at hp
  apply mul_right_cancel₀ hn
  calc
    _ = spectralNode v hv t*w i := by
      simpa only [mul_assoc] using (congrArg (fun z => spectralNode v hv t*z) (hf i)).symm
    _ = ∑ j, recurrenceMatrix v i j*w j := hw i
    _ = _ := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _
      rw [hf j]
      ring

end Szkraw
