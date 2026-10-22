import Szkraw.VRResum

/-!
# The resummation with a third family of `A`-moves (paper, proof of Theorem 8.11)

As `resum_nonneg`, with an additional family `W₊ - W₋` (signs like `V`) dominated with constant `3`,
and the key inequality `A₀P + PA₀ + 2V₁ + W₁ ≥ 4H₁`.
-/

set_option linter.unusedSectionVars false

namespace Szkraw

open Finset Matrix

section Resum2

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {lev : ι → ℕ}

theorem resum_nonneg2 (K : ℕ) (hK : ∀ i, lev i ≤ K)
    {U P Q Cp Cm A0 Hp Hm H1 Vp Vm V1 Wp Wm W1 : Matrix ι ι ℝ}
    (hU : MNN U) (hP : MNN P) (hCp : MNN Cp) (hA0 : MNN A0) (hHp : MNN Hp) (hVp : MNN Vp) (hWp : MNN Wp)
    (rU : Raise lev 1 U) (rP : Raise lev 1 P) (rQ : Raise lev 1 Q) (rCp : Raise lev 1 Cp)
    (rCm : Raise lev 1 Cm) (rA0 : Raise lev 1 A0) (rHp : Raise lev 1 Hp) (rHm : Raise lev 1 Hm)
    (rH1 : Raise lev 1 H1) (rVp : Raise lev 1 Vp) (rVm : Raise lev 1 Vm)
    (rWp : Raise lev 1 Wp) (rWm : Raise lev 1 Wm)
    (dQ : ∀ i j, 4 * Q i j ≤ (P * P) i j)
    (dH : ∀ i j, 4 * Hm i j ≤ (Hp * P) i j)
    (dV : ∀ i j, 4 * Vm i j ≤ (Vp * P) i j)
    (dC : ∀ i j, 4 * Cm i j ≤ (Cp * P) i j)
    (dW : ∀ i j, 3 * Wm i j ≤ (Wp * P) i j)
    (dV1 : ∀ i j, V1 i j ≤ Vp i j) (dW1 : ∀ i j, W1 i j ≤ Wp i j)
    (dkey : ∀ i j, 4 * H1 i j ≤ (A0 * P) i j + (P * A0) i j + 2 * V1 i j + W1 i j)
    {β ω : ι → ℝ} (hβ : ∀ i, 0 ≤ β i)
    (hrec : ω = β + (U + P - Q + Cp - Cm + A0 + Hp - Hm - H1 + Vp - Vm + Wp - Wm) *ᵥ ω) :
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
  set EW := (2 : ℝ) • (Wp * X) - (3 : ℝ) • Wm with hEW
  set EK := (2 : ℝ) • (A0 * X) + (2 : ℝ) • (X * A0) + (2 : ℝ) • V1 + W1 - (4 : ℝ) • H1 with hEK
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
  have hEWn : MNN EW := fun i j => by
    have h := dW i j; rw [conv] at h
    rw [hEW, Matrix.sub_apply, Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul]; linarith
  have hEKn : MNN EK := fun i j => by
    have h := dkey i j; rw [conv, conv'] at h
    simp only [hEK, Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    linarith
  have hVd : MNN (Vp - V1) := MNN.of_le dV1
  have hWd : MNN (Wp - W1) := MNN.of_le dW1
  -- the operator `S = R + C + A` and `M = G S G`
  set S := U + EQ + (Cp - Cm) + (A0 + Hp - Hm - H1 + Vp - Vm + Wp - Wm) with hS
  set M := G * S * G with hM
  have hMid : (12 : ℝ) • M = (12 : ℝ) • (G * U * G) + (12 : ℝ) • (G * EQ * G) +
      (6 : ℝ) • (G * Cp * G + G * Cp + G * EC * G) +
      ((6 : ℝ) • (G * A0) + (6 : ℝ) • (A0 * G) + (3 : ℝ) • (G * EK * G) + (6 : ℝ) • (G * (Vp - V1) * G) +
        (6 : ℝ) • (G * Vp) + (6 : ℝ) • (G * EV * G) + (6 : ℝ) • (G * Hp * G + G * Hp + G * EH * G) +
        (3 : ℝ) • (G * (Wp - W1) * G) + G * Wp * G + (8 : ℝ) • (G * Wp) + (4 : ℝ) • (G * EW * G)) := by
    have e1 : G * EC * G = G * Cp * (X * G) - (2 : ℝ) • (G * Cm * G) := by
      rw [hEC]; simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
    have e2 : G * EH * G = G * Hp * (X * G) - (2 : ℝ) • (G * Hm * G) := by
      rw [hEH]; simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
    have e3 : G * EV * G = G * Vp * (X * G) - (2 : ℝ) • (G * Vm * G) := by
      rw [hEV]; simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
    have e5 : G * EW * G = (2 : ℝ) • (G * Wp * (X * G)) - (3 : ℝ) • (G * Wm * G) := by
      rw [hEW]; simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
    have e4 : G * EK * G = (2 : ℝ) • (G * A0 * (X * G)) + (2 : ℝ) • ((G * X) * A0 * G) + (2 : ℝ) • (G * V1 * G) +
        G * W1 * G - (4 : ℝ) • (G * H1 * G) := by
      rw [hEK]
      simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul,
        Matrix.smul_mul, Matrix.mul_assoc]
    rw [e1, e2, e3, e4, e5, hXG, hGX, hM, hS]
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one,
      Matrix.one_mul, Matrix.mul_assoc, Matrix.mul_smul, Matrix.smul_mul]
    module
  have hMn : MNN M := by
    refine MNN.of_smul (c := 12) (by norm_num) ?_
    rw [hMid]
    have g3 : ∀ Y : Matrix ι ι ℝ, MNN Y → MNN (G * Y * G) := fun Y hY => (hG.mul hY).mul hG
    have s0 : ∀ (c : ℝ) (Y : Matrix ι ι ℝ), 0 ≤ c → MNN Y → MNN (c • Y) := fun c Y hc hY => hY.smul hc
    refine ((s0 _ _ (by norm_num) (g3 U hU)).add (s0 _ _ (by norm_num) (g3 EQ hEQn))).add
      (s0 _ _ (by norm_num) (((g3 Cp hCp).add (hG.mul hCp)).add (g3 EC hECn))) |>.add ?_
    refine (((((((((((s0 _ _ (by norm_num) (hG.mul hA0)).add (s0 _ _ (by norm_num) (hA0.mul hG))).add
      (s0 _ _ (by norm_num) (g3 EK hEKn))).add (s0 _ _ (by norm_num) (g3 _ hVd))).add
      (s0 _ _ (by norm_num) (hG.mul hVp))).add (s0 _ _ (by norm_num) (g3 EV hEVn))).add
      (s0 _ _ (by norm_num) (((g3 Hp hHp).add (hG.mul hHp)).add (g3 EH hEHn)))).add
      (s0 _ _ (by norm_num) (g3 _ hWd))).add (g3 Wp hWp)).add (s0 _ _ (by norm_num) (hG.mul hWp))).add
      (s0 _ _ (by norm_num) (g3 EW hEWn)))
  have rS : Raise lev 1 S := by
    have rEQ : Raise lev 1 EQ := ((rX.mul rX).mono (by norm_num)).sub rQ
    exact ((rU.add rEQ).add (rCp.sub rCm)).add (((((((rA0.add rHp).sub rHm).sub rH1).add rVp).sub rVm).add rWp).sub rWm)
  have rM : Raise lev 1 M := by simpa using (rG.mul rS).mul rG
  have hMn' : M ^ (K + 1) = 0 := Raise.eq_zero hK (by simpa using rM.pow (K + 1))
  -- `v = (I - X) ω` satisfies `v = Gβ + Mv`
  set v := (1 - X) *ᵥ ω with hv
  have hT : U + P - Q + Cp - Cm + A0 + Hp - Hm - H1 + Vp - Vm + Wp - Wm = S + (2 : ℝ) • X - X * X := by
    rw [hS, hEQ, ← hPX]; abel
  have hGv : G *ᵥ v = ω := by rw [hv, Matrix.mulVec_mulVec, hGr, Matrix.one_mulVec]
  have hrec' : ω - (U + P - Q + Cp - Cm + A0 + Hp - Hm - H1 + Vp - Vm + Wp - Wm) *ᵥ ω = β :=
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

end Resum2

end Szkraw
