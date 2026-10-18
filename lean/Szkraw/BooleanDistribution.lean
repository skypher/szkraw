import Szkraw.BooleanCounting
import Szkraw.BooleanEvaluation

namespace Szkraw

noncomputable def cubeMass (p : ℝ) : (N : ℕ) → (Fin N → Bool) → ℝ
  | 0, _ => 1
  | N+1, b => (if b 0 then p/(p+1) else 1/(p+1))*cubeMass p N (Fin.tail b)

theorem cube_mass_formula (p : ℝ) (N : ℕ) (b : Fin N → Bool) :
    cubeMass p N b = (1/(p+1))^(N-bitsWeight N b)*(p/(p+1))^(bitsWeight N b) := by
  induction N with
  | zero => simp [cubeMass,bitsWeight]
  | succ N ih =>
      have hw := bits_weight_le N (Fin.tail b)
      cases hb : b 0
      · have he : N+1-bitsWeight N (Fin.tail b) = (N-bitsWeight N (Fin.tail b))+1 := by omega
        simp [cubeMass,bitsWeight,hb,ih,he,pow_succ]
        ring
      · have he : N+1-(1+bitsWeight N (Fin.tail b)) = N-bitsWeight N (Fin.tail b) := by omega
        simp [cubeMass,bitsWeight,hb,ih,he,pow_add]
        ring

theorem cube_average_sum (p : ℝ) (N : ℕ) (f : (Fin N → Bool) → ℝ) :
    cubeAverage p N f = ∑ b, cubeMass p N b*f b := by
  induction N with
  | zero =>
      simp [cubeAverage,cubeMass]
      congr 1
  | succ N ih =>
      rw [sum_bits_succ]
      simp only [cubeMass,Fin.cons_zero,Bool.false_eq_true,ite_false,ite_true,Fin.tail_cons]
      simp only [mul_assoc,←Finset.mul_sum]
      rw [←ih,←ih]
      rfl

def countFin (N : ℕ) (b : Fin N → Bool) : Fin (N+1) := ⟨bitsWeight N b,by have := bits_weight_le N b; omega⟩

theorem count_fin_fiber_card (N : ℕ) (j : Fin (N+1)) :
    Fintype.card {b : Fin N → Bool // countFin N b = j} = N.choose j.val := by
  classical
  have e : {b : Fin N → Bool // countFin N b = j} ≃ {b : Fin N → Bool // bitsWeight N b = j.val} :=
    Equiv.subtypeEquivRight (fun b => Fin.ext_iff)
  rw [Fintype.card_congr e,bits_fiber_card]

/-- Grouping the product distribution gives exactly the stated binomial masses. -/
theorem cube_average_binomial (p : ℝ) (N : ℕ) (f : ℕ → ℝ) :
    cubeAverage p N (fun b => f (bitsWeight N b)) =
      ∑ j : Fin (N+1), (N.choose j.val : ℝ)*(1/(p+1))^(N-j.val)*(p/(p+1))^j.val*f j.val := by
  classical
  rw [cube_average_sum,←Fintype.sum_fiberwise (countFin N)]
  apply Finset.sum_congr rfl
  intro j _
  have hf (b : {b : Fin N → Bool // countFin N b = j}) : bitsWeight N b.val = j.val :=
    congrArg Fin.val b.property
  simp_rw [cube_mass_formula,hf]
  rw [Finset.sum_const]
  simp only [nsmul_eq_mul,Finset.card_univ,count_fin_fiber_card]
  ring

end Szkraw
