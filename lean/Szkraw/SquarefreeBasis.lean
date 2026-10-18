import Szkraw.TowerTrace
import Mathlib.LinearAlgebra.Basis.Defs

namespace Szkraw

noncomputable def fromCoordinates (p q : ℝ) :
    (N : ℕ) → ((Fin N → Bool) → ℝ) → (tower p q N).Carrier
  | 0, f => f (fun i => Fin.elim0 i)
  | N+1, f => ⟨fromCoordinates p q N (fun b => f (Fin.cons false b)),
      fromCoordinates p q N (fun b => f (Fin.cons true b))⟩

theorem from_coordinates_coordinate (p q : ℝ) (N : ℕ) (x : (tower p q N).Carrier) :
    fromCoordinates p q N (coordinate p q N x) = x := by
  induction N with
  | zero => rfl
  | succ N ih =>
      apply QuadraticAlgebra.ext
      · change fromCoordinates p q N (fun b => coordinate p q (N+1) x (Fin.cons false b)) = x.re
        simpa only [coordinate,Fin.cons_zero,Bool.false_eq_true,ite_false,Fin.tail_cons] using ih x.re
      · change fromCoordinates p q N (fun b => coordinate p q (N+1) x (Fin.cons true b)) = x.im
        simpa only [coordinate,Fin.cons_zero,ite_true,Fin.tail_cons] using ih x.im

theorem coordinate_from_coordinates (p q : ℝ) (N : ℕ) (f : (Fin N → Bool) → ℝ)
    (b : Fin N → Bool) : coordinate p q N (fromCoordinates p q N f) b = f b := by
  induction N with
  | zero =>
      change f _ = f b
      congr 1
      exact Subsingleton.elim _ _
  | succ N ih =>
      cases hb : b 0 <;> simp only [coordinate,hb,Bool.false_eq_true,ite_false,ite_true,fromCoordinates]
      · rw [ih]
        congr 1
        have hh := Fin.cons_self_tail b
        simpa only [hb] using hh
      · rw [ih]
        congr 1
        have hh := Fin.cons_self_tail b
        simpa only [hb] using hh

noncomputable def coordinateEquiv (p q : ℝ) (N : ℕ) :
    (tower p q N).Carrier ≃ₗ[ℝ] ((Fin N → Bool) → ℝ) where
  toFun := coordinate p q N
  invFun := fromCoordinates p q N
  left_inv := from_coordinates_coordinate p q N
  right_inv f := funext (coordinate_from_coordinates p q N f)
  map_add' x y := funext (coordinate_add p q N x y)
  map_smul' r x := funext (coordinate_smul p q r N x)

noncomputable def squarefreeBasis (p q : ℝ) (N : ℕ) :
    Module.Basis (Fin N → Bool) ℝ (tower p q N).Carrier :=
  Module.Basis.ofEquivFun (coordinateEquiv p q N)

theorem coordinate_squarefree (p q : ℝ) (N : ℕ) (b c : Fin N → Bool) :
    coordinate p q N (squarefree p q N b) c = if b = c then 1 else 0 := by
  classical
  induction N with
  | zero =>
      have he : b = c := Subsingleton.elim _ _
      simp [squarefree,coordinate,he]
  | succ N ih =>
      have he : b = c ↔ b 0 = c 0 ∧ Fin.tail b = Fin.tail c := by
        constructor
        · intro h; subst c; exact ⟨rfl,rfl⟩
        · rintro ⟨h0,ht⟩
          rw [←Fin.cons_self_tail b,←Fin.cons_self_tail c,h0,ht]
      cases hb : b 0 <;> cases hc : c 0 <;>
        simp [squarefree,coordinate,hb,hc,coordinate_zero,he,ih]

theorem squarefree_basis_apply (p q : ℝ) (N : ℕ) (b : Fin N → Bool) :
    squarefreeBasis p q N b = squarefree p q N b := by
  classical
  apply (coordinateEquiv p q N).injective
  funext c
  change (squarefreeBasis p q N).repr (squarefreeBasis p q N b) c = _
  rw [Module.Basis.repr_self_apply]
  exact (coordinate_squarefree p q N b c).symm

theorem squarefree_nonneg (p q : ℝ) (N : ℕ) (b : Fin N → Bool) :
    towerNonneg p q N (squarefree p q N b) := by
  induction N with
  | zero => exact tower_nonneg_one p q 0
  | succ N ih =>
      cases hb : b 0 <;> simp only [squarefree,hb,Bool.false_eq_true,ite_false,ite_true]
      · exact ⟨ih (Fin.tail b),tower_nonneg_zero p q N⟩
      · exact ⟨tower_nonneg_zero p q N,ih (Fin.tail b)⟩

theorem squarefree_product_nonneg (p q : ℝ) (hp : 1 ≤ p) (hq : 1 ≤ q)
    (N : ℕ) (b c d : Fin N → Bool) :
    0 ≤ (squarefreeBasis p q N).repr (squarefreeBasis p q N b*squarefreeBasis p q N c) d := by
  change 0 ≤ coordinate p q N (squarefreeBasis p q N b*squarefreeBasis p q N c) d
  rw [squarefree_basis_apply,squarefree_basis_apply]
  exact coordinate_nonneg p q N _
    (tower_mul_nonneg p q hp hq N _ _ (squarefree_nonneg p q N b) (squarefree_nonneg p q N c)) d

theorem squarefree_index_card (N : ℕ) : Fintype.card (Fin N → Bool) = 2^N := by simp

end Szkraw
