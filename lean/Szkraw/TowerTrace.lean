import Szkraw.Elementary
import Mathlib.Tactic.Linarith

namespace Szkraw

noncomputable def towerTrace (p q : ℝ) : (N : ℕ) → (tower p q N).Carrier → ℝ
  | 0, x => x
  | N+1, x => towerTrace p q N x.re

theorem tower_trace_zero (p q : ℝ) (N : ℕ) : towerTrace p q N 0 = 0 := by
  induction N with
  | zero => rfl
  | succ N ih => exact ih

theorem tower_trace_add (p q : ℝ) (N : ℕ) (x y : (tower p q N).Carrier) :
    towerTrace p q N (x+y) = towerTrace p q N x+towerTrace p q N y := by
  induction N with
  | zero => rfl
  | succ N ih => exact ih x.re y.re

theorem tower_trace_smul (p q r : ℝ) (N : ℕ) (x : (tower p q N).Carrier) :
    towerTrace p q N (r • x) = r*towerTrace p q N x := by
  induction N with
  | zero => rfl
  | succ N ih => exact ih x.re

theorem tower_trace_coordinate (p q : ℝ) (N : ℕ) (x : (tower p q N).Carrier) :
    towerTrace p q N x = coordinate p q N x (fun _ => false) := by
  induction N with
  | zero => rfl
  | succ N ih =>
      change towerTrace p q N x.re = coordinate p q N x.re (Fin.tail (fun _ : Fin (N+1) => false))
      exact ih x.re

theorem tower_trace_product (p q : ℝ) (N : ℕ) (x y : (tower p q (N+1)).Carrier) :
    towerTrace p q (N+1) (x*y) = towerTrace p q N (x.re*y.re) +
      (p*q^N)*towerTrace p q N (x.im*y.im) := by
  change towerTrace p q N (x.re*y.re+
    algebraMap ℝ (tower p q N).Carrier (p*q^N)*x.im*y.im) = _
  rw [tower_trace_add]
  have ha : algebraMap ℝ (tower p q N).Carrier (p*q^N)*x.im*y.im =
      (p*q^N) • (x.im*y.im) := by
    simp [Algebra.algebraMap_eq_smul_one,smul_mul_assoc]
  rw [ha,tower_trace_smul]

theorem tower_trace_square_nonneg (p q : ℝ) (hp : 1 ≤ p) (hq : 1 ≤ q)
    (N : ℕ) (x : (tower p q N).Carrier) : 0 ≤ towerTrace p q N (x*x) := by
  induction N with
  | zero => exact mul_self_nonneg x
  | succ N ih =>
      rw [tower_trace_product]
      exact add_nonneg (ih x.re) (mul_nonneg (by positivity) (ih x.im))

theorem tower_trace_square_eq_zero (p q : ℝ) (hp : 1 ≤ p) (hq : 1 ≤ q)
    (N : ℕ) (x : (tower p q N).Carrier) : towerTrace p q N (x*x) = 0 ↔ x = 0 := by
  induction N with
  | zero => exact mul_self_eq_zero
  | succ N ih =>
      constructor
      · intro hx
        rw [tower_trace_product] at hx
        have hre := tower_trace_square_nonneg p q hp hq N x.re
        have him := tower_trace_square_nonneg p q hp hq N x.im
        have hcoef : 0 < p*q^N := by positivity
        have hr0 : towerTrace p q N (x.re*x.re) = 0 := by nlinarith
        have hi0 : towerTrace p q N (x.im*x.im) = 0 := by nlinarith
        have hrx := (ih x.re).mp hr0
        have hix := (ih x.im).mp hi0
        apply QuadraticAlgebra.ext <;> assumption
      · intro hx
        rw [hx,mul_zero,tower_trace_zero]

theorem tower_trace_square_pos (p q : ℝ) (hp : 1 ≤ p) (hq : 1 ≤ q)
    (N : ℕ) (x : (tower p q N).Carrier) (hx : x ≠ 0) :
    0 < towerTrace p q N (x*x) := by
  have hn := tower_trace_square_nonneg p q hp hq N x
  have he := (tower_trace_square_eq_zero p q hp hq N x).not.mpr hx
  exact lt_of_le_of_ne hn (Ne.symm he)

theorem tower_trace_self_adjoint (p q : ℝ) (N : ℕ) (h x y : (tower p q N).Carrier) :
    towerTrace p q N ((h*x)*y) = towerTrace p q N (x*(h*y)) := by
  congr 1
  ring

noncomputable def squarefree (p q : ℝ) : (N : ℕ) → (Fin N → Bool) → (tower p q N).Carrier
  | 0, _ => 1
  | N+1, b => if b 0 then ⟨0,squarefree p q N (Fin.tail b)⟩
    else ⟨squarefree p q N (Fin.tail b),0⟩

def bitsExponent : (N : ℕ) → (Fin N → Bool) → ℕ
  | 0, _ => 0
  | N+1, b => (if b 0 then N else 0)+bitsExponent N (Fin.tail b)

theorem squarefree_trace_diagonal (p q : ℝ) (N : ℕ) (b c : Fin N → Bool) :
    towerTrace p q N (squarefree p q N b*squarefree p q N c) =
      if b = c then p^(bitsWeight N b)*q^(bitsExponent N b) else 0 := by
  classical
  induction N with
  | zero =>
      have he : b = c := Subsingleton.elim _ _
      simp [he,squarefree,towerTrace,bitsWeight,bitsExponent]
  | succ N ih =>
      have he : b = c ↔ b 0 = c 0 ∧ Fin.tail b = Fin.tail c := by
        constructor
        · intro h; subst c; exact ⟨rfl,rfl⟩
        · rintro ⟨h0,ht⟩
          rw [←Fin.cons_self_tail b,←Fin.cons_self_tail c,h0,ht]
      rw [tower_trace_product]
      cases hb : b 0 <;> cases hc : c 0 <;>
        simp [squarefree,hb,hc,tower_trace_zero,bitsWeight,bitsExponent,he,
          ih,pow_add] <;> ring

theorem tower_trace_elementary (p q : ℝ) (N k : ℕ) :
    towerTrace p q N (elementary p q N k) = if k = 0 then 1 else 0 := by
  rw [tower_trace_coordinate,coordinate_elementary]
  have hh : bitsWeight N (fun _ => false) = 0 := by
    induction N with
    | zero => rfl
    | succ N ih =>
        simp only [bitsWeight,Bool.false_eq_true,ite_false,zero_add]
        exact ih
  rw [hh]

theorem tower_trace_elementary_orthogonal (p q : ℝ) (N m n : ℕ) (hmn : m ≠ n) :
    towerTrace p q N (elementary p q N m*elementary p q N n) = 0 := by
  induction N generalizing m n with
  | zero =>
      cases m <;> cases n <;> simp_all [elementary,towerTrace]
  | succ N ih =>
      cases m with
      | zero =>
          simp only [elementary_zero,one_mul,tower_trace_elementary]
          simp [Ne.symm hmn]
      | succ m =>
          cases n with
          | zero => simp [elementary_zero,mul_one,tower_trace_elementary]
          | succ n =>
              rw [tower_trace_product]
              change towerTrace p q N (elementary p q N (m+1)*elementary p q N (n+1))+
                p*q^N*towerTrace p q N (elementary p q N m*elementary p q N n) = 0
              rw [ih (m+1) (n+1) hmn,ih m n (by omega)]
              ring

end Szkraw
