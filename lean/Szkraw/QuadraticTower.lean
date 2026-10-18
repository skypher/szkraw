import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Positivity

namespace Szkraw

structure AlgebraStage where
  Carrier : Type
  [ring : CommRing Carrier]
  [algebra : Algebra ℝ Carrier]
  sum : Carrier

attribute [instance] AlgebraStage.ring AlgebraStage.algebra

@[reducible] noncomputable def tower (p q : ℝ) : ℕ → AlgebraStage
  | 0 => { Carrier := ℝ, sum := 0 }
  | n+1 =>
    let T := tower p q n
    { Carrier := QuadraticAlgebra T.Carrier (algebraMap ℝ T.Carrier (p*q^n))
        ((q-1) • T.sum + algebraMap ℝ T.Carrier (p-1))
      sum := ⟨T.sum, 1⟩ }

noncomputable def towerNonneg (p q : ℝ) : (n : ℕ) → (tower p q n).Carrier → Prop
  | 0, x => (0 : ℝ) ≤ x
  | n+1, x => towerNonneg p q n x.re ∧ towerNonneg p q n x.im

def Stmt_tower_mul_nonneg : Prop :=
  ∀ (p q : ℝ), 1 ≤ p → 1 ≤ q → ∀ (n : ℕ) (x y : (tower p q n).Carrier),
    towerNonneg p q n x → towerNonneg p q n y → towerNonneg p q n (x*y)

theorem tower_nonneg_zero (p q : ℝ) (n : ℕ) :
    towerNonneg p q n 0 := by
  induction n with
  | zero => exact le_rfl
  | succ n ih => exact ⟨ih, ih⟩

theorem tower_nonneg_add (p q : ℝ) (n : ℕ) (x y : (tower p q n).Carrier)
    (hx : towerNonneg p q n x) (hy : towerNonneg p q n y) :
    towerNonneg p q n (x+y) := by
  induction n with
  | zero => exact add_nonneg hx hy
  | succ n ih =>
      exact ⟨ih x.re y.re hx.1 hy.1, ih x.im y.im hx.2 hy.2⟩

theorem tower_nonneg_smul (p q r : ℝ) (hr : 0 ≤ r) (n : ℕ)
    (x : (tower p q n).Carrier) (hx : towerNonneg p q n x) :
    towerNonneg p q n (r • x) := by
  induction n with
  | zero => exact mul_nonneg hr hx
  | succ n ih => exact ⟨ih x.re hx.1, ih x.im hx.2⟩

theorem tower_nonneg_scalar (p q r : ℝ) (hr : 0 ≤ r) (n : ℕ) :
    towerNonneg p q n (algebraMap ℝ (tower p q n).Carrier r) := by
  induction n with
  | zero => exact hr
  | succ n ih => exact ⟨ih, tower_nonneg_zero p q n⟩

theorem tower_nonneg_one (p q : ℝ) (n : ℕ) :
    towerNonneg p q n 1 := by
  simpa using tower_nonneg_scalar p q 1 (by norm_num) n

theorem tower_nonneg_sum (p q : ℝ) (n : ℕ) :
    towerNonneg p q n (tower p q n).sum := by
  induction n with
  | zero => exact le_rfl
  | succ n ih => exact ⟨ih, tower_nonneg_one p q n⟩

theorem tower_mul_nonneg : Stmt_tower_mul_nonneg := by
  intro p q hp hq n
  induction n with
  | zero =>
      intro x y hx hy
      exact mul_nonneg hx hy
  | succ n ih =>
      intro x y hx hy
      have ha : towerNonneg p q n
          (algebraMap ℝ (tower p q n).Carrier (p*q^n)) :=
        tower_nonneg_scalar p q _ (by positivity) n
      have hb : towerNonneg p q n
          ((q-1) • (tower p q n).sum + algebraMap ℝ (tower p q n).Carrier (p-1)) :=
        tower_nonneg_add p q n _ _
          (tower_nonneg_smul p q _ (by linarith) n _ (tower_nonneg_sum p q n))
          (tower_nonneg_scalar p q _ (by linarith) n)
      exact ⟨tower_nonneg_add p q n _ _ (ih _ _ hx.1 hy.1)
          (ih _ _ (ih _ _ ha hx.2) hy.2),
        tower_nonneg_add p q n _ _
          (tower_nonneg_add p q n _ _ (ih _ _ hx.1 hy.2) (ih _ _ hx.2 hy.1))
          (ih _ _ (ih _ _ hb hx.2) hy.2)⟩

example : Stmt_tower_mul_nonneg := tower_mul_nonneg

end Szkraw
