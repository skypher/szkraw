import Szkraw.TowerTrace
import Szkraw.TowerCharacter
import Szkraw.Krawtchouk

namespace Szkraw

def booleanRoot (p : ℝ) (b : Bool) : ℝ := if b then -1 else p

noncomputable def booleanEval (p : ℝ) :
    (N : ℕ) → (Fin N → Bool) → (tower p 1 N).Carrier → ℝ
  | 0, _, x => x
  | N+1, b, x => booleanEval p N (Fin.tail b) x.re +
      booleanRoot p (b 0)*booleanEval p N (Fin.tail b) x.im

theorem boolean_eval_zero (p : ℝ) (N : ℕ) (b : Fin N → Bool) : booleanEval p N b 0 = 0 := by
  induction N with
  | zero => rfl
  | succ N ih => change booleanEval p N _ 0+booleanRoot p (b 0)*booleanEval p N _ 0 = 0; rw [ih]; ring

theorem boolean_eval_add (p : ℝ) (N : ℕ) (b : Fin N → Bool) (x y : (tower p 1 N).Carrier) :
    booleanEval p N b (x+y) = booleanEval p N b x+booleanEval p N b y := by
  induction N with
  | zero => rfl
  | succ N ih =>
      change booleanEval p N _ (x.re+y.re)+booleanRoot p (b 0)*booleanEval p N _ (x.im+y.im) = _
      rw [ih,ih]
      simp only [booleanEval]
      ring

theorem boolean_eval_smul (p r : ℝ) (N : ℕ) (b : Fin N → Bool) (x : (tower p 1 N).Carrier) :
    booleanEval p N b (r • x) = r*booleanEval p N b x := by
  induction N with
  | zero => rfl
  | succ N ih =>
      change booleanEval p N _ (r • x.re)+booleanRoot p (b 0)*booleanEval p N _ (r • x.im) = _
      rw [ih,ih]
      simp only [booleanEval]
      ring

theorem boolean_eval_scalar (p r : ℝ) (N : ℕ) (b : Fin N → Bool) :
    booleanEval p N b (algebraMap ℝ (tower p 1 N).Carrier r) = r := by
  induction N with
  | zero => rfl
  | succ N ih =>
      change booleanEval p N _ (algebraMap ℝ (tower p 1 N).Carrier r)+
        booleanRoot p (b 0)*booleanEval p N _ 0 = r
      rw [ih,boolean_eval_zero]
      ring

theorem boolean_eval_one (p : ℝ) (N : ℕ) (b : Fin N → Bool) : booleanEval p N b 1 = 1 := by
  simpa using boolean_eval_scalar p 1 N b

theorem boolean_eval_mul (p : ℝ) (N : ℕ) (b : Fin N → Bool) (x y : (tower p 1 N).Carrier) :
    booleanEval p N b (x*y) = booleanEval p N b x*booleanEval p N b y := by
  induction N with
  | zero => rfl
  | succ N ih =>
      change booleanEval p N _ (x.re*y.re+
        algebraMap ℝ (tower p 1 N).Carrier (p*1^N)*x.im*y.im) +
        booleanRoot p (b 0)*booleanEval p N _ (x.re*y.im+x.im*y.re+
          ((1-1) • (tower p 1 N).sum+algebraMap ℝ (tower p 1 N).Carrier (p-1))*x.im*y.im) = _
      simp only [one_pow,mul_one,sub_self,zero_smul,zero_add,
        boolean_eval_add,ih,boolean_eval_scalar,booleanEval]
      cases hb : b 0 <;> simp only [booleanRoot,hb,Bool.false_eq_true,ite_false,ite_true] <;> ring

noncomputable def booleanCharacter (p : ℝ) (N : ℕ) (b : Fin N → Bool) :
    (tower p 1 N).Carrier →ₐ[ℝ] ℝ where
  toFun := booleanEval p N b
  map_one' := boolean_eval_one p N b
  map_mul' := boolean_eval_mul p N b
  map_zero' := boolean_eval_zero p N b
  map_add' := boolean_eval_add p N b
  commutes' r := boolean_eval_scalar p r N b

/-- Product expectation with probabilities 1/(p+1) and p/(p+1). -/
noncomputable def cubeAverage (p : ℝ) : (N : ℕ) → ((Fin N → Bool) → ℝ) → ℝ
  | 0, f => f (fun i => Fin.elim0 i)
  | N+1, f => (1/(p+1))*cubeAverage p N (fun b => f (Fin.cons false b)) +
      (p/(p+1))*cubeAverage p N (fun b => f (Fin.cons true b))

theorem cube_average_add (p : ℝ) (N : ℕ) (f g : (Fin N → Bool) → ℝ) :
    cubeAverage p N (fun b => f b+g b) = cubeAverage p N f+cubeAverage p N g := by
  induction N with
  | zero => rfl
  | succ N ih => simp only [cubeAverage,ih]; ring

theorem cube_average_smul (p r : ℝ) (N : ℕ) (f : (Fin N → Bool) → ℝ) :
    cubeAverage p N (fun b => r*f b) = r*cubeAverage p N f := by
  induction N with
  | zero => rfl
  | succ N ih => simp only [cubeAverage,ih]; ring

/-- The product distribution realizes the constant-coordinate trace. -/
theorem cube_average_trace (p : ℝ) (hp : 1 ≤ p) (N : ℕ) (x : (tower p 1 N).Carrier) :
    cubeAverage p N (fun b => booleanEval p N b x) = towerTrace p 1 N x := by
  induction N with
  | zero => rfl
  | succ N ih =>
      simp only [cubeAverage,booleanEval,Fin.cons_zero,Fin.tail_cons,booleanRoot,
        Bool.false_eq_true,ite_false,ite_true,cube_average_add,cube_average_smul,ih]
      have hp1 : p+1 ≠ 0 := by linarith
      change 1/(p+1)*(towerTrace p 1 N x.re+p*towerTrace p 1 N x.im)+
        p/(p+1)*(towerTrace p 1 N x.re+(-1)*towerTrace p 1 N x.im) = towerTrace p 1 N x.re
      field_simp
      ring

theorem boolean_eval_sum (p : ℝ) (N : ℕ) (b : Fin N → Bool) :
    booleanEval p N b (tower p 1 N).sum =
      p*(N : ℝ)-(p+1)*(bitsWeight N b : ℝ) := by
  induction N with
  | zero => simp [booleanEval,tower,bitsWeight]
  | succ N ih =>
      change booleanEval p N (Fin.tail b) (tower p 1 N).sum+
        booleanRoot p (b 0)*booleanEval p N (Fin.tail b) 1 = _
      rw [ih,boolean_eval_one]
      cases hb : b 0 <;> simp [booleanRoot,bitsWeight,hb,Nat.cast_add] <;> ring

theorem boolean_eval_normalized_one (p : ℝ) (hp : 1 ≤ p) (N : ℕ) (hN : 1 ≤ N)
    (b : Fin N → Bool) :
    booleanCharacter p N b (normalizedElementary p 1 N 1) =
      1-(p+1)*(bitsWeight N b : ℝ)/(p*N) := by
  change booleanEval p N b (normalizedElementary p 1 N 1) = _
  rw [normalizedElementary,boolean_eval_smul,elementary_one,boolean_eval_sum,normalizer_one]
  rw [qInteger_at_one]
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  have hp0 : p ≠ 0 := ne_of_gt (by linarith : 0 < p)
  field_simp

/-- The normalized canonical polynomials depend only on the negative-coordinate count. -/
theorem boolean_polynomial_value (p : ℝ) (hp : 1 ≤ p) (N : ℕ) (hN : 1 ≤ N)
    (b : Fin N → Bool) (m : ℕ) (hm : m ≤ N) :
    booleanCharacter p N b (normalizedElementary p 1 N m) =
      (recurrencePolynomial (geometricCoefficients N p 1) m).eval
        (1-(p+1)*(bitsWeight N b : ℝ)/(p*N)) := by
  let v := geometricCoefficients N p 1
  let U := normalizedElementary p 1 N
  let X := U 1
  have hv := geometric_coefficients_admissible N hN p 1 hp le_rfl
  have heval := recurrence_evaluation v hv U X (normalized_elementary_zero p 1 N) rfl
    (fun j hj => normalized_three_term p 1 hp le_rfl N j (by omega)) m hm
  change booleanCharacter p N b (U m) = _
  rw [←heval,←Polynomial.aeval_algHom_apply]
  rw [boolean_eval_normalized_one p hp N hN b]
  rfl

end Szkraw
