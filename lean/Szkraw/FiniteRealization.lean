import Szkraw.SpectralMeasure

namespace Szkraw

theorem recurrence_normalized {N : ℕ} (v : Coefficients N) (hv : Admissible v)
    (m : ℕ) (hm : m ≤ N) : (recurrencePolynomial v m).eval 1 = 1 := by
  have hh := recurrence_evaluation v hv (fun _ => (1 : ℝ)) 1 rfl rfl
    (fun k hk => by simpa only [smul_eq_mul,mul_one] using (hv.2.2.2.2.2.1 (k+1) (by omega)).symm) m hm
  simpa using hh

theorem recurrence_row_sum {N : ℕ} (v : Coefficients N) (hv : Admissible v)
    (i : Fin (N+1)) : ∑ j, recurrenceMatrix v i j = 1 := by
  classical
  let U : ℕ → ℝ := fun k => if k ≤ N then 1 else 0
  have hU (j : Fin (N+1)) : U j.val = 1 := by simp [U,show j.val ≤ N by omega]
  have hh := recurrence_row_action v U (by intro j hj; simp [U,show ¬j ≤ N by omega]) i
  simp only [smul_eq_mul,hU,mul_one] at hh
  rw [hh]
  by_cases hi : i.val = 0
  · simp [hi,U,hv.1,hv.2.1,hv.2.2.1]
  · by_cases hn : i.val = N
    · simp [hn,hv.2.2.2.2.1,show N ≠ 0 by omega,U,show N-1 ≤ N by omega]
      have h := hv.2.2.2.2.2.1 N le_rfl
      rw [hv.2.2.2.2.1] at h
      linarith
    · simpa [hi,U,show i.val+1 ≤ N by omega,show i.val-1 ≤ N by omega] using
        hv.2.2.2.2.2.1 i.val (by omega)

theorem product_row_sum {N : ℕ} (v : Coefficients N) (hv : Admissible v)
    (m : ℕ) (hm : m ≤ N) (i : Fin (N+1)) :
    ∑ j, productMatrix v m i j = 1 := by
  have hh := representation_product v (fun _ => (1 : ℝ)) 1
    (fun j => by simpa using (recurrence_row_sum v hv j).symm) m i
  simpa [recurrence_normalized v hv m hm] using hh.symm

theorem spectral_terminal {N : ℕ} (v : Coefficients N) (hv : Admissible v)
    (t : Fin (N+1)) :
    (spectralNode v hv t-v.b N)*(recurrencePolynomial v N).eval (spectralNode v hv t) -
      v.c N*(recurrencePolynomial v (N-1)).eval (spectralNode v hv t) = 0 := by
  classical
  let U : ℕ → ℝ := fun k => if k ≤ N then
    (recurrencePolynomial v k).eval (spectralNode v hv t) else 0
  have hU (j : Fin (N+1)) : U j.val =
      (recurrencePolynomial v j.val).eval (spectralNode v hv t) := by
    simp [U,show j.val ≤ N by omega]
  have hh := recurrence_row_action v U (by intro j hj; simp [U,show ¬j ≤ N by omega]) ⟨N,by omega⟩
  simp only [smul_eq_mul,hU] at hh
  have he := spectral_node_action v hv t ⟨N,by omega⟩
  rw [hh] at he
  simp [hv.2.2.2.2.1,show N ≠ 0 by have := hv.1; omega,U,show N-1 ≤ N by omega] at he
  nlinarith

theorem finite_realization {N : ℕ} (v : Coefficients N) (hv : Admissible v) :
    FiniteRealization v := by
  refine ⟨spectralNode v hv,spectralWeight v hv,spectral_nodes_injective v hv,
    ?_,spectral_weight_sum v hv,recurrence_normalized v hv,?_,?_,?_,spectral_terminal v hv,?_⟩
  · exact spectral_weight_pos v hv
  · intro m n hm
    exact product_row_sum v hv m hm n
  · intro m n hm hn hmn
    exact spectral_orthogonal v hv ⟨m,by omega⟩ ⟨n,by omega⟩ (by intro h; apply hmn; exact congrArg Fin.val h)
  · intro m hm
    exact spectral_norm_pos v hv ⟨m,by omega⟩
  · intro m n t hm
    have hh := representation_product v
      (fun j => (recurrencePolynomial v j.val).eval (spectralNode v hv t))
      (spectralNode v hv t) (fun i => by simpa using spectral_node_action v hv t i) m n
    simpa using hh

end Szkraw
