import Szkraw.FiniteRealization

namespace Szkraw

noncomputable def towerEval (p q : ℝ) : (N : ℕ) → (tower p q N).Carrier → ℝ
  | 0, x => x
  | N+1, x => towerEval p q N x.re + p*q^N*towerEval p q N x.im

theorem tower_eval_zero (p q : ℝ) (N : ℕ) : towerEval p q N 0 = 0 := by
  induction N with
  | zero => rfl
  | succ N ih => change towerEval p q N 0+p*q^N*towerEval p q N 0 = 0; rw [ih]; ring

theorem tower_eval_add (p q : ℝ) (N : ℕ) (x y : (tower p q N).Carrier) :
    towerEval p q N (x+y) = towerEval p q N x+towerEval p q N y := by
  induction N with
  | zero => rfl
  | succ N ih =>
      change towerEval p q N (x.re+y.re)+p*q^N*towerEval p q N (x.im+y.im) = _
      rw [ih,ih]
      simp only [towerEval]
      ring

theorem tower_eval_smul (p q r : ℝ) (N : ℕ) (x : (tower p q N).Carrier) :
    towerEval p q N (r • x) = r*towerEval p q N x := by
  induction N with
  | zero => rfl
  | succ N ih =>
      change towerEval p q N (r • x.re)+p*q^N*towerEval p q N (r • x.im) = _
      rw [ih,ih]
      change _ = r*(towerEval p q N x.re+p*q^N*towerEval p q N x.im)
      ring

theorem tower_eval_scalar (p q r : ℝ) (N : ℕ) :
    towerEval p q N (algebraMap ℝ (tower p q N).Carrier r) = r := by
  induction N with
  | zero => rfl
  | succ N ih =>
      change towerEval p q N (algebraMap ℝ (tower p q N).Carrier r)+p*q^N*towerEval p q N 0 = r
      rw [ih,tower_eval_zero]
      ring

theorem tower_eval_one (p q : ℝ) (N : ℕ) : towerEval p q N 1 = 1 := by
  simpa using tower_eval_scalar p q 1 N

theorem tower_eval_sum (p q : ℝ) (N : ℕ) :
    towerEval p q N (tower p q N).sum = p*qInteger q N := by
  induction N with
  | zero => simp [towerEval,tower,qInteger]
  | succ N ih =>
      change towerEval p q N (tower p q N).sum+p*q^N*towerEval p q N 1 = _
      rw [ih,tower_eval_one,qInteger]
      ring

theorem qInteger_geometric_identity (q : ℝ) (N : ℕ) :
    (q-1)*qInteger q N = q^N-1 := by
  induction N with
  | zero => simp [qInteger]
  | succ N ih => rw [qInteger,pow_succ]; nlinarith

theorem tower_eval_mul (p q : ℝ) (N : ℕ) (x y : (tower p q N).Carrier) :
    towerEval p q N (x*y) = towerEval p q N x*towerEval p q N y := by
  induction N with
  | zero => rfl
  | succ N ih =>
      change towerEval p q N (x.re*y.re+
          algebraMap ℝ (tower p q N).Carrier (p*q^N)*x.im*y.im) +
        p*q^N*towerEval p q N (x.re*y.im+x.im*y.re+
          ((q-1) • (tower p q N).sum+algebraMap ℝ (tower p q N).Carrier (p-1))*x.im*y.im) =
        (towerEval p q N x.re+p*q^N*towerEval p q N x.im)*
        (towerEval p q N y.re+p*q^N*towerEval p q N y.im)
      simp only [tower_eval_add,ih,tower_eval_scalar,tower_eval_smul,tower_eval_sum]
      have hq := qInteger_geometric_identity q N
      nlinarith [congrArg (fun z : ℝ => p^2*q^N*towerEval p q N x.im*towerEval p q N y.im*z) hq]

noncomputable def towerCharacter (p q : ℝ) (N : ℕ) : (tower p q N).Carrier →ₐ[ℝ] ℝ where
  toFun := towerEval p q N
  map_one' := tower_eval_one p q N
  map_mul' := tower_eval_mul p q N
  map_zero' := tower_eval_zero p q N
  map_add' := tower_eval_add p q N
  commutes' := fun r => tower_eval_scalar p q r N

theorem tower_character_normalized (p q : ℝ) (hp : 1 ≤ p) (hq : 1 ≤ q)
    (N : ℕ) (hN : 1 ≤ N) (k : ℕ) (hk : k ≤ N) :
    towerCharacter p q N (normalizedElementary p q N k) = 1 := by
  let v := geometricCoefficients N p q
  let U := normalizedElementary p q N
  let X := U 1
  let ε := towerCharacter p q N
  have hv := geometric_coefficients_admissible N hN p q hp hq
  have heval := recurrence_evaluation v hv U X (normalized_elementary_zero p q N) rfl
    (fun j hj => normalized_three_term p q hp hq N j (by omega)) k hk
  have hQN : 0 < qInteger q N := qInteger_pos q hq N (by omega)
  have hp0 : 0 < p := by linarith
  have hX : ε X = 1 := by
    change towerEval p q N (normalizedElementary p q N 1) = 1
    rw [normalizedElementary,tower_eval_smul,elementary_one,tower_eval_sum,normalizer_one]
    exact inv_mul_cancel₀ (ne_of_gt (mul_pos hp0 hQN))
  change ε (U k) = 1
  rw [←heval,←Polynomial.aeval_algHom_apply ε X,hX]
  simpa using recurrence_normalized v hv k hk

theorem tower_character_elementary (p q : ℝ) (hp : 1 ≤ p) (hq : 1 ≤ q)
    (N : ℕ) (hN : 1 ≤ N) (k : ℕ) (hk : k ≤ N) :
    towerCharacter p q N (elementary p q N k) = normalizer p q N k := by
  have h := tower_character_normalized p q hp hq N hN k hk
  change towerEval p q N ((normalizer p q N k)⁻¹ • elementary p q N k) = 1 at h
  rw [tower_eval_smul] at h
  have ht := normalizer_pos p q hp hq N k hk
  have hh := congrArg (fun x : ℝ => normalizer p q N k*x) h
  field_simp at hh
  exact hh

theorem tower_character_nonneg (p q : ℝ) (hp : 1 ≤ p) (hq : 1 ≤ q)
    (N : ℕ) (x : (tower p q N).Carrier) (hx : towerNonneg p q N x) :
    0 ≤ towerCharacter p q N x := by
  change 0 ≤ towerEval p q N x
  induction N with
  | zero => exact hx
  | succ N ih =>
      change 0 ≤ towerEval p q N x.re+p*q^N*towerEval p q N x.im
      exact add_nonneg (ih x.re hx.1) (mul_nonneg (by positivity) (ih x.im hx.2))

noncomputable def towerGenerator (p q : ℝ) : (N : ℕ) → Fin N → (tower p q N).Carrier
  | 0, i => Fin.elim0 i
  | N+1, i => Fin.cases ⟨0,1⟩ (fun j => ⟨towerGenerator p q N j,0⟩) i

theorem tower_character_generator (p q : ℝ) (N : ℕ) (i : Fin N) :
    towerCharacter p q N (towerGenerator p q N i) = p*q^(N-1-i.val) := by
  change towerEval p q N (towerGenerator p q N i) = _
  induction N with
  | zero => exact Fin.elim0 i
  | succ N ih =>
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [towerGenerator,towerEval,tower_eval_zero,tower_eval_one]
      · change towerEval p q N (towerGenerator p q N j)+p*q^N*towerEval p q N 0 = _
        rw [ih,tower_eval_zero,mul_zero,add_zero]
        congr 2
        simp only [Fin.val_succ]
        omega

theorem character_normalizer_ratio (p q : ℝ) (hp : 1 ≤ p) (hq : 1 ≤ q)
    (N k : ℕ) (hk : k < N) :
    normalizer p q N (k+1)/normalizer p q N k =
      p*q^k*qInteger q (N-k)/qInteger q (k+1) := by
  have ht : normalizer p q N k ≠ 0 := ne_of_gt (normalizer_pos p q hp hq N k (by omega))
  rw [normalizer]
  field_simp

end Szkraw
