import Szkraw.LCDetours
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic.NoncommRing
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Tactic.Module

/-!
# The resummation of Theorem 8.9 (paper, proof of Theorem 8.9, *Resummation*)

Matrices on a finite index set with a level function, entrywise order. All move operators strictly
raise the level. With `G = Σ_{m ≤ K} (P/2)^m = (I - P/2)⁻¹`, the operator `M = G(R + C + A)G` is
nonnegative, where `R = U + P²/4 - Q`; the function `v = (I - P/2)ω` satisfies `v = Gβ + Mv`, so
`ω = G Σ_q M^q Gβ ≥ 0`. The detour inequalities are used with the constant `4` throughout; the
paper's constant `6` for the `H`, `V` and `C` families gives more room than needed.
-/

set_option linter.unusedSectionVars false

namespace Szkraw

open Finset Matrix

section Resum

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Entrywise nonnegative matrices. -/
def MNN (X : Matrix ι ι ℝ) : Prop := ∀ i j, 0 ≤ X i j

theorem MNN.add {X Y : Matrix ι ι ℝ} (hX : MNN X) (hY : MNN Y) : MNN (X + Y) :=
  fun i j => by rw [Matrix.add_apply]; exact add_nonneg (hX i j) (hY i j)

theorem MNN.mul {X Y : Matrix ι ι ℝ} (hX : MNN X) (hY : MNN Y) : MNN (X * Y) :=
  fun i j => by rw [Matrix.mul_apply]; exact sum_nonneg fun k _ => mul_nonneg (hX i k) (hY k j)

theorem MNN.smul {X : Matrix ι ι ℝ} (hX : MNN X) {c : ℝ} (hc : 0 ≤ c) : MNN (c • X) :=
  fun i j => by rw [Matrix.smul_apply, smul_eq_mul]; exact mul_nonneg hc (hX i j)

theorem MNN.one : MNN (1 : Matrix ι ι ℝ) := fun i j => by
  rw [Matrix.one_apply]; split_ifs <;> norm_num

theorem MNN.pow {X : Matrix ι ι ℝ} (hX : MNN X) : ∀ n, MNN (X ^ n)
  | 0 => by rw [pow_zero]; exact MNN.one
  | n + 1 => by rw [pow_succ]; exact (MNN.pow hX n).mul hX

theorem MNN.sum {α : Type*} {s : Finset α} {X : α → Matrix ι ι ℝ} (h : ∀ k ∈ s, MNN (X k)) :
    MNN (∑ k ∈ s, X k) :=
  fun i j => by rw [Matrix.sum_apply]; exact sum_nonneg fun k hk => h k hk i j

theorem MNN.of_le {X Y : Matrix ι ι ℝ} (h : ∀ i j, X i j ≤ Y i j) : MNN (Y - X) :=
  fun i j => by rw [Matrix.sub_apply]; linarith [h i j]

theorem MNN.of_smul {X : Matrix ι ι ℝ} {c : ℝ} (hc : 0 < c) (h : MNN (c • X)) : MNN X := fun i j => by
  have := h i j
  rw [Matrix.smul_apply, smul_eq_mul] at this
  by_contra hneg
  push Not at hneg
  nlinarith

theorem MNN.mulVec {X : Matrix ι ι ℝ} (hX : MNN X) {v : ι → ℝ} (hv : ∀ i, 0 ≤ v i) (i : ι) :
    0 ≤ (X *ᵥ v) i := by
  simp only [Matrix.mulVec, dotProduct]; exact sum_nonneg fun k _ => mul_nonneg (hX i k) (hv k)

/-- Entries vanish unless the level rises by at least `k`. -/
def Raise (lev : ι → ℕ) (k : ℕ) (X : Matrix ι ι ℝ) : Prop := ∀ i j, lev i < lev j + k → X i j = 0

variable {lev : ι → ℕ}

theorem Raise.add {k : ℕ} {X Y : Matrix ι ι ℝ} (hX : Raise lev k X) (hY : Raise lev k Y) :
    Raise lev k (X + Y) := fun i j h => by rw [Matrix.add_apply, hX i j h, hY i j h, add_zero]

theorem Raise.sub {k : ℕ} {X Y : Matrix ι ι ℝ} (hX : Raise lev k X) (hY : Raise lev k Y) :
    Raise lev k (X - Y) := fun i j h => by rw [Matrix.sub_apply, hX i j h, hY i j h, sub_zero]

theorem Raise.smul {k : ℕ} {X : Matrix ι ι ℝ} (hX : Raise lev k X) (c : ℝ) : Raise lev k (c • X) :=
  fun i j h => by rw [Matrix.smul_apply, hX i j h, smul_zero]

theorem Raise.sum {k : ℕ} {α : Type*} {s : Finset α} {X : α → Matrix ι ι ℝ}
    (h : ∀ a ∈ s, Raise lev k (X a)) : Raise lev k (∑ a ∈ s, X a) := fun i j hij => by
  rw [Matrix.sum_apply]; exact sum_eq_zero fun a ha => h a ha i j hij

theorem Raise.mono {k k' : ℕ} {X : Matrix ι ι ℝ} (hX : Raise lev k X) (h : k' ≤ k) : Raise lev k' X :=
  fun i j hij => hX i j (by omega)

theorem Raise.mul {k m : ℕ} {X Y : Matrix ι ι ℝ} (hX : Raise lev k X) (hY : Raise lev m Y) :
    Raise lev (k + m) (X * Y) := fun i j hij => by
  rw [Matrix.mul_apply]
  refine sum_eq_zero fun l _ => ?_
  rcases lt_or_ge (lev i) (lev l + k) with h | h
  · rw [hX i l h, zero_mul]
  · rw [hY l j (by omega), mul_zero]

theorem raise_one : Raise lev 0 (1 : Matrix ι ι ℝ) := fun i j h => by
  rw [Matrix.one_apply, if_neg]; rintro rfl; omega

theorem Raise.pow {k : ℕ} {X : Matrix ι ι ℝ} (hX : Raise lev k X) : ∀ n, Raise lev (k * n) (X ^ n)
  | 0 => by rw [pow_zero, Nat.mul_zero]; exact raise_one
  | n + 1 => by rw [pow_succ, Nat.mul_succ]; exact (Raise.pow hX n).mul hX

theorem Raise.eq_zero {K : ℕ} (hK : ∀ i, lev i ≤ K) {X : Matrix ι ι ℝ} (hX : Raise lev (K + 1) X) :
    X = 0 := by
  ext i j; rw [hX i j (by have := hK i; omega), Matrix.zero_apply]

/-- **The resummation.** Under the operator inequalities of the proof of Theorem 8.9, every
solution of `ω = β + (U + P - Q + C₊ - C₋ + A₀ + H₊ - H₋ - H₁ + V₊ - V₋) ω` with `β ≥ 0`
is nonnegative. -/
theorem resum_nonneg (K : ℕ) (hK : ∀ i, lev i ≤ K)
    {U P Q Cp Cm A0 Hp Hm H1 Vp Vm V1 : Matrix ι ι ℝ}
    (hU : MNN U) (hP : MNN P) (hCp : MNN Cp) (hA0 : MNN A0) (hHp : MNN Hp) (hVp : MNN Vp)
    (rU : Raise lev 1 U) (rP : Raise lev 1 P) (rQ : Raise lev 1 Q) (rCp : Raise lev 1 Cp)
    (rCm : Raise lev 1 Cm) (rA0 : Raise lev 1 A0) (rHp : Raise lev 1 Hp) (rHm : Raise lev 1 Hm)
    (rH1 : Raise lev 1 H1) (rVp : Raise lev 1 Vp) (rVm : Raise lev 1 Vm)
    (dQ : ∀ i j, 4 * Q i j ≤ (P * P) i j)
    (dH : ∀ i j, 4 * Hm i j ≤ (Hp * P) i j)
    (dV : ∀ i j, 4 * Vm i j ≤ (Vp * P) i j)
    (dC : ∀ i j, 4 * Cm i j ≤ (Cp * P) i j)
    (dV1 : ∀ i j, V1 i j ≤ Vp i j)
    (dkey : ∀ i j, 4 * H1 i j ≤ (A0 * P) i j + (P * A0) i j + 2 * V1 i j)
    {β ω : ι → ℝ} (hβ : ∀ i, 0 ≤ β i)
    (hrec : ω = β + (U + P - Q + Cp - Cm + A0 + Hp - Hm - H1 + Vp - Vm) *ᵥ ω) :
    ∀ i, 0 ≤ ω i := by
  set X : Matrix ι ι ℝ := (1 / 2 : ℝ) • P with hXdef
  have hPX : P = (2 : ℝ) • X := by rw [hXdef, smul_smul]; norm_num
  have hX : MNN X := hP.smul (by norm_num)
  have rX : Raise lev 1 X := rP.smul _
  set G : Matrix ι ι ℝ := ∑ m ∈ range (K + 1), X ^ m with hGdef
  have hXn : X ^ (K + 1) = 0 := Raise.eq_zero hK (by simpa using rX.pow (K + 1))
  have hGl : (1 - X) * G = 1 := by rw [hGdef, mul_neg_geom_sum, hXn, sub_zero]
  have hGr : G * (1 - X) = 1 := by rw [hGdef, geom_sum_mul_neg, hXn, sub_zero]
  have hXG : X * G = G - 1 := by
    have : G - X * G = 1 := by rw [← hGl]; noncomm_ring
    rw [← this]; abel
  have hGX : G * X = G - 1 := by
    have : G - G * X = 1 := by rw [← hGr]; noncomm_ring
    rw [← this]; abel
  have hG : MNN G := MNN.sum fun m _ => hX.pow m
  have rG : Raise lev 0 G := Raise.sum fun m _ => (rX.pow m).mono (Nat.zero_le _)
  -- the defects of the detour inequalities
  set EQ := X * X - Q with hEQ
  set EC := Cp * X - (2 : ℝ) • Cm with hEC
  set EH := Hp * X - (2 : ℝ) • Hm with hEH
  set EV := Vp * X - (2 : ℝ) • Vm with hEV
  set EK := A0 * X + X * A0 + V1 - (2 : ℝ) • H1 with hEK
  have conv : ∀ (Y : Matrix ι ι ℝ) (i j : ι), (Y * P) i j = 2 * (Y * X) i j := by
    intro Y i j; rw [hPX, Matrix.mul_smul, Matrix.smul_apply, smul_eq_mul]
  have conv' : ∀ (Y : Matrix ι ι ℝ) (i j : ι), (P * Y) i j = 2 * (X * Y) i j := by
    intro Y i j; rw [hPX, Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul]
  have hEQn : MNN EQ := fun i j => by
    have h := dQ i j
    rw [hPX, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.smul_apply, smul_eq_mul] at h
    rw [hEQ, Matrix.sub_apply]; linarith
  have hECn : MNN EC := fun i j => by
    have h := dC i j; rw [conv] at h
    rw [hEC, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]; linarith
  have hEHn : MNN EH := fun i j => by
    have h := dH i j; rw [conv] at h
    rw [hEH, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]; linarith
  have hEVn : MNN EV := fun i j => by
    have h := dV i j; rw [conv] at h
    rw [hEV, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]; linarith
  have hEKn : MNN EK := fun i j => by
    have h := dkey i j; rw [conv, conv'] at h
    rw [hEK, Matrix.sub_apply, Matrix.add_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    linarith
  have hVd : MNN (Vp - V1) := MNN.of_le dV1
  -- the operator `S = R + C + A` and `M = G S G`
  set S := U + EQ + (Cp - Cm) + (A0 + Hp - Hm - H1 + Vp - Vm) with hS
  set M := G * S * G with hM
  have hMid : (2 : ℝ) • M = (2 : ℝ) • (G * U * G) + (2 : ℝ) • (G * EQ * G) +
      (G * Cp * G + G * Cp + G * EC * G) +
      (G * A0 + A0 * G + G * EK * G + G * (Vp - V1) * G +
        (G * Hp * G + G * Hp + G * EH * G) + (G * Vp + G * EV * G)) := by
    have e1 : G * EC * G = G * Cp * (X * G) - (2 : ℝ) • (G * Cm * G) := by
      rw [hEC]; simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
    have e2 : G * EH * G = G * Hp * (X * G) - (2 : ℝ) • (G * Hm * G) := by
      rw [hEH]; simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
    have e3 : G * EV * G = G * Vp * (X * G) - (2 : ℝ) • (G * Vm * G) := by
      rw [hEV]; simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
    have e4 : G * EK * G = G * A0 * (X * G) + (G * X) * A0 * G + G * V1 * G - (2 : ℝ) • (G * H1 * G) := by
      rw [hEK]
      simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul,
        Matrix.smul_mul, Matrix.mul_assoc]
    rw [e1, e2, e3, e4, hXG, hGX, hM, hS]
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one,
      Matrix.one_mul, Matrix.mul_assoc]
    module
  have hMn : MNN M := by
    refine MNN.of_smul (c := 2) (by norm_num) ?_
    rw [hMid]
    have g3 : ∀ Y : Matrix ι ι ℝ, MNN Y → MNN (G * Y * G) := fun Y hY => (hG.mul hY).mul hG
    refine ((((g3 U hU).smul (by norm_num)).add ((g3 EQ hEQn).smul (by norm_num))).add
      (((g3 Cp hCp).add (hG.mul hCp)).add (g3 EC hECn))).add ?_
    exact (((((hG.mul hA0).add (hA0.mul hG)).add (g3 EK hEKn)).add (g3 _ hVd)).add
      (((g3 Hp hHp).add (hG.mul hHp)).add (g3 EH hEHn))).add ((hG.mul hVp).add (g3 EV hEVn))
  have rS : Raise lev 1 S := by
    have rEQ : Raise lev 1 EQ := ((rX.mul rX).mono (by norm_num)).sub rQ
    exact ((rU.add rEQ).add (rCp.sub rCm)).add (((((rA0.add rHp).sub rHm).sub rH1).add rVp).sub rVm)
  have rM : Raise lev 1 M := by simpa using (rG.mul rS).mul rG
  have hMn' : M ^ (K + 1) = 0 := Raise.eq_zero hK (by simpa using rM.pow (K + 1))
  -- `v = (I - X) ω` satisfies `v = Gβ + Mv`
  set v := (1 - X) *ᵥ ω with hv
  have hT : U + P - Q + Cp - Cm + A0 + Hp - Hm - H1 + Vp - Vm = S + (2 : ℝ) • X - X * X := by
    rw [hS, hEQ, ← hPX]; abel
  have hGv : G *ᵥ v = ω := by rw [hv, Matrix.mulVec_mulVec, hGr, Matrix.one_mulVec]
  have hrec' : ω - (U + P - Q + Cp - Cm + A0 + Hp - Hm - H1 + Vp - Vm) *ᵥ ω = β :=
    sub_eq_iff_eq_add.mpr hrec
  have hv2 : (1 - X) *ᵥ v = β + S *ᵥ ω := by
    have h2 : (1 - X) * (1 - X) = 1 - (2 : ℝ) • X + X * X := by
      rw [two_smul]; noncomm_ring
    rw [hv, Matrix.mulVec_mulVec, h2, ← hrec', hT]
    simp only [Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec]
    abel
  set w := G *ᵥ β with hw
  have hvrec : v = w + M *ᵥ v := by
    calc v = G *ᵥ ((1 - X) *ᵥ v) := by rw [Matrix.mulVec_mulVec, hGr, Matrix.one_mulVec]
      _ = G *ᵥ (β + S *ᵥ ω) := by rw [hv2]
      _ = w + M *ᵥ v := by
        rw [Matrix.mulVec_add, ← hGv, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hM]
  have iter : ∀ n, v = (∑ q ∈ range n, M ^ q) *ᵥ w + (M ^ n) *ᵥ v := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have e : M ^ n *ᵥ v = M ^ n *ᵥ w + M ^ (n + 1) *ᵥ v := by
        conv_lhs => rw [hvrec]
        rw [Matrix.mulVec_add, Matrix.mulVec_mulVec v (M ^ n) M, ← pow_succ]
      calc v = (∑ q ∈ range n, M ^ q) *ᵥ w + M ^ n *ᵥ v := ih
        _ = _ := by rw [e, sum_range_succ, Matrix.add_mulVec]; abel
  have hvnn : ∀ i, 0 ≤ v i := by
    intro i
    have h := iter (K + 1)
    rw [hMn', Matrix.zero_mulVec, add_zero] at h
    rw [h]
    exact (MNN.sum fun q _ => hMn.pow q).mulVec (hG.mulVec hβ) i
  intro i
  rw [← hGv]
  exact hG.mulVec hvnn i

end Resum

end Szkraw
