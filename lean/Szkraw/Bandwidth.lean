import Szkraw.FiniteRealization

namespace Szkraw

def HasBandwidth {N : ℕ} (m : ℕ) (M : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) : Prop :=
  ∀ i j, i.val+m < j.val ∨ j.val+m < i.val → M i j = 0

theorem recurrence_entry_zero {N : ℕ} (v : Coefficients N) (i j : Fin (N+1))
    (h : i.val+1 < j.val ∨ j.val+1 < i.val) : recurrenceMatrix v i j = 0 := by
  have h1 : j.val ≠ i.val+1 := by omega
  have h2 : j ≠ i := by intro he; have := congrArg Fin.val he; omega
  have h3 : i.val ≠ j.val+1 := by omega
  simp [recurrenceMatrix,h1,h2,h3]

theorem bandwidth_recurrence_mul {N : ℕ} (v : Coefficients N)
    (m : ℕ) (M : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) (hM : HasBandwidth m M) :
    HasBandwidth (m+1) (recurrenceMatrix v*M) := by
  intro i j hij
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro k _
  by_cases hk : i.val+1 < k.val ∨ k.val+1 < i.val
  · rw [recurrence_entry_zero v i k hk,zero_mul]
  · rw [hM k j (by omega),mul_zero]

theorem product_bandwidth {N : ℕ} (v : Coefficients N) (m : ℕ) :
    HasBandwidth m (productMatrix v m) := by
  have hpair : ∀ k, HasBandwidth k (matrixPair v k).1 ∧
      HasBandwidth k (matrixPair v k).2 := by
    intro k
    induction k with
    | zero =>
        constructor
        · intro i j _; rfl
        · intro i j hij
          have hn : i ≠ j := by intro he; have := congrArg Fin.val he; omega
          simp [matrixPair,Matrix.one_apply,hn]
    | succ k ih =>
        constructor
        · intro i j hij
          exact ih.2 i j (by omega)
        · have hh := bandwidth_recurrence_mul v k (matrixPair v k).2 ih.2
          intro i j hij
          have h0 := ih.1 i j (by omega : i.val+k < j.val ∨ j.val+k < i.val)
          have h1 := ih.2 i j (by omega : i.val+k < j.val ∨ j.val+k < i.val)
          have h2 := hh i j hij
          simp only [matrixPair,Matrix.smul_apply,Matrix.sub_apply,Matrix.sub_mul,Matrix.smul_mul,
            Matrix.one_mul,h0,h1,h2,smul_eq_mul,mul_zero,sub_zero]
  exact (hpair m).2

noncomputable def spectralNorm {N : ℕ} (v : Coefficients N) (hv : Admissible v)
    (k : Fin (N+1)) : ℝ := ∑ t, spectralWeight v hv t *
      ((recurrencePolynomial v k.val).eval (spectralNode v hv t))^2

theorem product_coefficient_moment {N : ℕ} (v : Coefficients N) (hv : Admissible v)
    (m : ℕ) (n k : Fin (N+1)) :
    productMatrix v m n k * spectralNorm v hv k =
      ∑ t, spectralWeight v hv t *
        (recurrencePolynomial v m).eval (spectralNode v hv t) *
        (recurrencePolynomial v n.val).eval (spectralNode v hv t) *
        (recurrencePolynomial v k.val).eval (spectralNode v hv t) := by
  classical
  have hprod (t : Fin (N+1)) :
      (recurrencePolynomial v m).eval (spectralNode v hv t) *
        (recurrencePolynomial v n.val).eval (spectralNode v hv t) =
      ∑ j, productMatrix v m n j *
        (recurrencePolynomial v j.val).eval (spectralNode v hv t) := by
    simpa using representation_product v
      (fun j => (recurrencePolynomial v j.val).eval (spectralNode v hv t))
      (spectralNode v hv t) (fun i => by simpa using spectral_node_action v hv t i) m n
  have hinner (j : Fin (N+1)) :
      (∑ t, spectralWeight v hv t *
        (recurrencePolynomial v j.val).eval (spectralNode v hv t) *
        (recurrencePolynomial v k.val).eval (spectralNode v hv t)) =
        if j = k then spectralNorm v hv k else 0 := by
    by_cases hj : j = k
    · subst j; simp [spectralNorm,pow_two,mul_assoc]
    · rw [if_neg hj]; exact spectral_orthogonal v hv j k hj
  symm
  calc
    _ = ∑ t, ∑ j, productMatrix v m n j * (spectralWeight v hv t *
        (recurrencePolynomial v j.val).eval (spectralNode v hv t) *
        (recurrencePolynomial v k.val).eval (spectralNode v hv t)) := by
      apply Finset.sum_congr rfl
      intro t _
      calc
        _ = spectralWeight v hv t *
            ((recurrencePolynomial v m).eval (spectralNode v hv t) *
              (recurrencePolynomial v n.val).eval (spectralNode v hv t)) *
            (recurrencePolynomial v k.val).eval (spectralNode v hv t) := by ring
        _ = _ := by rw [hprod t]; simp only [Finset.mul_sum,Finset.sum_mul]; apply Finset.sum_congr rfl; intro j _; ring
    _ = ∑ j, productMatrix v m n j * (∑ t, spectralWeight v hv t *
        (recurrencePolynomial v j.val).eval (spectralNode v hv t) *
        (recurrencePolynomial v k.val).eval (spectralNode v hv t)) := by
      rw [Finset.sum_comm]; simp only [Finset.mul_sum]
    _ = _ := by simp_rw [hinner]; simp

theorem product_triangle_zero {N : ℕ} (v : Coefficients N) (hv : Admissible v)
    (m : ℕ) (hm : m ≤ N) (n k : Fin (N+1)) (h : ¬ Triangle m n.val k.val) :
    productMatrix v m n k = 0 := by
  by_cases hb : n.val+m < k.val ∨ k.val+m < n.val
  · exact product_bandwidth v m n k hb
  · have ha : n.val+k.val < m := by dsimp [Triangle] at h; omega
    let im : Fin (N+1) := ⟨m,by omega⟩
    have hz := product_bandwidth v n.val im k (Or.inr (by dsimp [im]; omega))
    have h1 := product_coefficient_moment v hv m n k
    have h2 := product_coefficient_moment v hv n.val im k
    have he : productMatrix v m n k * spectralNorm v hv k = 0 := by
      rw [h1]
      have hs : (∑ t, spectralWeight v hv t *
          (recurrencePolynomial v m).eval (spectralNode v hv t) *
          (recurrencePolynomial v n.val).eval (spectralNode v hv t) *
          (recurrencePolynomial v k.val).eval (spectralNode v hv t)) =
          ∑ t, spectralWeight v hv t *
          (recurrencePolynomial v n.val).eval (spectralNode v hv t) *
          (recurrencePolynomial v m).eval (spectralNode v hv t) *
          (recurrencePolynomial v k.val).eval (spectralNode v hv t) := by
        apply Finset.sum_congr rfl; intro t _; ring
      rw [hs,←h2,hz,zero_mul]
    exact (mul_eq_zero.mp he).resolve_right (ne_of_gt (spectral_norm_pos v hv k))

end Szkraw
