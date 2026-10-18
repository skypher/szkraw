import Szkraw.Elementary
import Mathlib.Data.Fintype.Powerset
import Mathlib.Algebra.BigOperators.Fin

namespace Szkraw

theorem bits_weight_eq_sum (N : ℕ) (b : Fin N → Bool) :
    bitsWeight N b = ∑ i : Fin N, if b i then 1 else 0 := by
  induction N with
  | zero => simp [bitsWeight]
  | succ N ih => rw [bitsWeight,Fin.sum_univ_succ,ih]; rfl

theorem bits_weight_le (N : ℕ) (b : Fin N → Bool) : bitsWeight N b ≤ N := by
  induction N with
  | zero => rfl
  | succ N ih =>
      have hh := ih (Fin.tail b)
      cases hb : b 0 <;> simp [bitsWeight,hb] <;> omega

def bitsSet (N : ℕ) (b : Fin N → Bool) : Finset (Fin N) := Finset.univ.filter (fun i => b i = true)

theorem bits_set_card (N : ℕ) (b : Fin N → Bool) : (bitsSet N b).card = bitsWeight N b := by
  rw [bits_weight_eq_sum]
  simp only [bitsSet,Finset.card_eq_sum_ones,Finset.sum_filter]

def bitsSetEquiv (N : ℕ) : (Fin N → Bool) ≃ Finset (Fin N) where
  toFun := bitsSet N
  invFun s i := decide (i ∈ s)
  left_inv b := by
    funext i
    cases hb : b i <;> simp [bitsSet,hb]
  right_inv s := by ext i; simp [bitsSet]

noncomputable def bitsFiberEquiv (N k : ℕ) :
    {b : Fin N → Bool // bitsWeight N b = k} ≃ {s : Finset (Fin N) // s.card = k} where
  toFun b := ⟨bitsSetEquiv N b.val,by
    change (bitsSet N b.val).card = k
    rw [bits_set_card]
    exact b.property⟩
  invFun s := ⟨(bitsSetEquiv N).symm s.val,by
    have hh := bits_set_card N ((bitsSetEquiv N).symm s.val)
    change ((bitsSetEquiv N) ((bitsSetEquiv N).symm s.val)).card = _ at hh
    rw [Equiv.apply_symm_apply] at hh
    exact hh.symm.trans s.property⟩
  left_inv b := by apply Subtype.ext; exact (bitsSetEquiv N).symm_apply_apply b.val
  right_inv s := by apply Subtype.ext; exact (bitsSetEquiv N).apply_symm_apply s.val

theorem bits_fiber_card (N k : ℕ) :
    Fintype.card {b : Fin N → Bool // bitsWeight N b = k} = N.choose k := by
  classical
  rw [Fintype.card_congr (bitsFiberEquiv N k),Fintype.card_finset_len,Fintype.card_fin]

def bitsHeadEquiv (N : ℕ) : (Fin (N+1) → Bool) ≃ Bool × (Fin N → Bool) where
  toFun b := (b 0,Fin.tail b)
  invFun x := Fin.cons x.1 x.2
  left_inv := Fin.cons_self_tail
  right_inv x := by cases x; simp

theorem sum_bits_succ (N : ℕ) (f : (Fin (N+1) → Bool) → ℝ) :
    (∑ b, f b) = (∑ b, f (Fin.cons false b))+(∑ b, f (Fin.cons true b)) := by
  have hh := Fintype.sum_equiv (bitsHeadEquiv N) f (fun x => f (Fin.cons x.1 x.2))
    (fun b => congrArg f (Fin.cons_self_tail b).symm)
  rw [Fintype.sum_prod_type] at hh
  simpa [Fintype.sum_bool,add_comm] using hh

end Szkraw
