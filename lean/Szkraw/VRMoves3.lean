import Szkraw.VRMoves2
import Szkraw.VRResum3

/-!
# Move operators for Theorem 8.16

As `gkernel_resum2`, with the `W`-moves dominated with constant `2` and the key inequality
`4 c H₁ ≤ A₀ B₀' + B₀ A₀' + 2 c V₁` (no `W₁` term).
-/

set_option linter.unusedSectionVars false

namespace Szkraw

open Finset Matrix

section Moves3

variable {cc : ℕ → ℝ} {N : ℕ} {A B C : ℕ → ℕ → ℕ → ℝ} {s : ℕ → ℕ → ℝ}

/-- Hypotheses of the resummation, on `Ω = {ℓ + a ≤ N}`: the `A`-weights of positive index split
as `H - V - W`; the weights `A₀, B, C, H, V, W` and the straight weight `s` are nonnegative; the
`B`, `C`, `H`, `V` (constant `4`) and `W` (constant `3`) moves are dominated by detours through `B₀`;
and the key inequality controls `H₁`. -/
structure ResumWeights3 (cc : ℕ → ℝ) (A B C H V W : ℕ → ℕ → ℕ → ℝ) (s : ℕ → ℕ → ℝ) (N : ℕ) : Prop where
  cc_pos : ∀ n, 1 ≤ n → 0 < cc n
  split : ∀ j ℓ a, 1 ≤ j → ℓ + a ≤ N → A j ℓ a = H j ℓ a - V j ℓ a - W j ℓ a
  A0_nn : ∀ ℓ a, ℓ + a ≤ N → 0 ≤ A 0 ℓ a
  B_nn : ∀ j ℓ a, ℓ + a ≤ N → 0 ≤ B j ℓ a
  C_nn : ∀ j ℓ a, ℓ + a ≤ N → 0 ≤ C j ℓ a
  H_nn : ∀ j ℓ a, ℓ + a ≤ N → 0 ≤ H j ℓ a
  V_nn : ∀ j ℓ a, ℓ + a ≤ N → 0 ≤ V j ℓ a
  W_nn : ∀ j ℓ a, ℓ + a ≤ N → 0 ≤ W j ℓ a
  s_nn : ∀ ℓ a, ℓ + a ≤ N → 0 ≤ s ℓ a
  domB : ∀ j ℓ a, 1 ≤ j → ℓ + a ≤ N → 4 * cc (ℓ + 1) * B j ℓ a ≤ B 0 ℓ a * B (j - 1) (ℓ + 1) (a - 2)
  domC : ∀ j ℓ a, 1 ≤ j → ℓ + a ≤ N → 4 * cc (ℓ + 1) * C j ℓ a ≤ B 0 ℓ a * C (j - 1) (ℓ + 1) (a - 2)
  domH : ∀ j ℓ a, 2 ≤ j → ℓ + a ≤ N → 4 * cc (ℓ + 1) * H j ℓ a ≤ B 0 ℓ a * H (j - 1) (ℓ + 1) (a - 2)
  domV : ∀ j ℓ a, 2 ≤ j → ℓ + a ≤ N → 4 * cc (ℓ + 1) * V j ℓ a ≤ B 0 ℓ a * V (j - 1) (ℓ + 1) (a - 2)
  domW : ∀ j ℓ a, 2 ≤ j → ℓ + a ≤ N → 2 * cc (ℓ + 1) * W j ℓ a ≤ B 0 ℓ a * W (j - 1) (ℓ + 1) (a - 2)
  key : ∀ ℓ a, ℓ + a ≤ N → 3 ≤ a → 4 * cc (ℓ + 1) * H 1 ℓ a ≤
    A 0 ℓ a * B 0 (ℓ + 1) (a - 1) + B 0 ℓ a * A 0 (ℓ + 1) (a - 2) + 2 * cc (ℓ + 1) * V 1 ℓ a

/-- **Resummation induction.** Every solution of the generic kernel recurrence with nonnegative
initial values and the support property is nonnegative under `ResumWeights2`. -/
theorem gkernel_resum3 {H V W : ℕ → ℕ → ℕ → ℝ} {ω : ℕ → ℕ → ℝ} (hN : 1 ≤ N)
    (hw : ResumWeights3 cc A B C H V W s N) (hrec : GenRec cc A B C s ω)
    (h0 : ∀ a, 0 ≤ ω 0 a) (hsupp : ∀ ℓ a, N < ℓ + a → ω ℓ a = 0) : ∀ ℓ a, 0 ≤ ω ℓ a := by
  have hcc := hw.cc_pos
  set R := range (N + 1) with hR
  -- the move families
  set fA : ℕ → Matrix (Idx N) (Idx N) ℝ := fun j => smv cc N (j + 1) (2 * j + 1) (A j) with hfA
  set fB : ℕ → Matrix (Idx N) (Idx N) ℝ := fun j => smv cc N (j + 1) (2 * j + 2) (B j) with hfB
  set fC : ℕ → Matrix (Idx N) (Idx N) ℝ := fun j => smv cc N (j + 2) (2 * j + 2) (C j) with hfC
  set fH : ℕ → Matrix (Idx N) (Idx N) ℝ := fun j => smv cc N (j + 1) (2 * j + 1) (H j) with hfH
  set fV : ℕ → Matrix (Idx N) (Idx N) ℝ := fun j => smv cc N (j + 1) (2 * j + 1) (V j) with hfV
  set fW : ℕ → Matrix (Idx N) (Idx N) ℝ := fun j => smv cc N (j + 1) (2 * j + 1) (W j) with hfW
  set U := smv cc N 1 0 s with hU
  set P := ∑ j ∈ R.filter Even, fB j with hP
  set Q := ∑ j ∈ R.filter Odd, fB j with hQ
  set Cp := ∑ j ∈ R.filter Even, fC j with hCp
  set Cm := ∑ j ∈ R.filter Odd, fC j with hCm
  set A0 := fA 0 with hA0
  set Hp := ∑ j ∈ R.filter (fun j => Even j ∧ 2 ≤ j), fH j with hHp
  set Hm := ∑ j ∈ R.filter (fun j => Odd j ∧ 3 ≤ j), fH j with hHm
  set H1 := fH 1 with hH1
  set Vp := ∑ j ∈ R.filter Odd, fV j with hVp
  set Vm := ∑ j ∈ R.filter (fun j => Even j ∧ 2 ≤ j), fV j with hVm
  set V1 := fV 1 with hV1
  set Wp := ∑ j ∈ R.filter Odd, fW j with hWp
  set Wm := ∑ j ∈ R.filter (fun j => Even j ∧ 2 ≤ j), fW j with hWm
  have h0R : 0 ∈ R := mem_range.mpr (by omega)
  have h1R : 1 ∈ R := mem_range.mpr (by omega)
  -- nonnegativity and raising
  have nB : ∀ j, MNN (fB j) := fun j => smv_nonneg hcc (by omega) (fun ℓ a h => hw.B_nn j ℓ a h)
  have nC : ∀ j, MNN (fC j) := fun j => smv_nonneg hcc (by omega) (fun ℓ a h => hw.C_nn j ℓ a h)
  have nH : ∀ j, MNN (fH j) := fun j => smv_nonneg hcc (by omega) (fun ℓ a h => hw.H_nn j ℓ a h)
  have nV : ∀ j, MNN (fV j) := fun j => smv_nonneg hcc (by omega) (fun ℓ a h => hw.V_nn j ℓ a h)
  have nW : ∀ j, MNN (fW j) := fun j => smv_nonneg hcc (by omega) (fun ℓ a h => hw.W_nn j ℓ a h)
  have nU : MNN U := smv_nonneg hcc le_rfl hw.s_nn
  have nA0 : MNN A0 := smv_nonneg hcc (by omega) hw.A0_nn
  have nP : MNN P := MNN.sum fun j _ => nB j
  have rf : ∀ (d1 d2 : ℕ → ℕ) (W : ℕ → ℕ → ℕ → ℝ) (J : Finset ℕ), (∀ j, 1 ≤ d1 j) →
      Raise lvl 1 (∑ j ∈ J, smv cc N (d1 j) (d2 j) (W j)) :=
    fun d1 d2 W J hd => Raise.sum fun j _ => smv_raise (hd j) _
  -- the matrix equation
  have hdecomp : Tmat cc N A B C s = U + P - Q + Cp - Cm + A0 + Hp - Hm - H1 + Vp - Vm + Wp - Wm := by
    have hAsplit : ∀ j, 1 ≤ j → fA j = fH j - fV j - fW j := fun j hj => by
      simp only [hfA, hfH, hfV, hfW]
      rw [← smv_sub, ← smv_sub]
      exact smv_congr fun ℓ a hla _ => hw.split j ℓ a hj hla
    unfold Tmat
    simp only [smul_add, sum_add_distrib]
    rw [sign_split_mat, sign_split_mat, sign_split_mat]
    -- the `A`-family
    have hEvenA : ∑ j ∈ R.filter Even, fA j = A0 + Hp - Vm - Wm := by
      have hs : R.filter Even = insert 0 (R.filter (fun j => Even j ∧ 2 ≤ j)) := by
        ext j; simp only [mem_insert, mem_filter, mem_range, hR]
        constructor
        · rintro ⟨h1, h2⟩
          by_cases hj : j = 0
          · exact Or.inl hj
          · right; refine ⟨h1, h2, ?_⟩; obtain ⟨k, rfl⟩ := h2; omega
        · rintro (rfl | ⟨h1, h2, _⟩)
          · exact ⟨by omega, (⟨0, rfl⟩ : Even 0)⟩
          · exact ⟨h1, h2⟩
      rw [hs, sum_insert (by simp), hA0, hHp, hVm, hWm, add_sub_assoc, add_sub_assoc, ← sum_sub_distrib,
        ← sum_sub_distrib]
      congr 1
      exact sum_congr rfl fun j hj => hAsplit j (by have := (mem_filter.mp hj).2.2; omega)
    have hOddA : ∑ j ∈ R.filter Odd, fA j = H1 + Hm - Vp - Wp := by
      have hs : R.filter Odd = insert 1 (R.filter (fun j => Odd j ∧ 3 ≤ j)) := by
        ext j; simp only [mem_insert, mem_filter, mem_range, hR]
        constructor
        · rintro ⟨h1, h2⟩
          by_cases hj : j = 1
          · exact Or.inl hj
          · right; refine ⟨h1, h2, ?_⟩; obtain ⟨k, rfl⟩ := h2; omega
        · rintro (rfl | ⟨h1, h2, _⟩)
          · exact ⟨by omega, odd_one⟩
          · exact ⟨h1, h2⟩
      have hsum : ∑ j ∈ R.filter Odd, fA j = ∑ j ∈ R.filter Odd, fH j - Vp - Wp := by
        rw [hVp, hWp, ← sum_sub_distrib, ← sum_sub_distrib]
        exact sum_congr rfl fun j hj => hAsplit j (by obtain ⟨k, rfl⟩ := (mem_filter.mp hj).2; omega)
      rw [hsum, hs, sum_insert (by simp), hH1, hHm]
    rw [hEvenA, hOddA]
    abel
  set ωv : Idx N → ℝ := fun k => ω k.1 k.2 with hωv
  set β : Idx N → ℝ := fun i => if (i.1 : ℕ) = 0 then ω i.1 i.2 else 0 with hβ
  have rT : Raise lvl 1 (U + P - Q + Cp - Cm + A0 + Hp - Hm - H1 + Vp - Vm + Wp - Wm) := by
    have rU : Raise lvl 1 U := smv_raise le_rfl _
    have rA0 : Raise lvl 1 A0 := smv_raise (by omega) _
    have rH1 : Raise lvl 1 H1 := smv_raise (by omega) _
    exact (((((((((rU.add (rf _ _ _ _ fun j => by omega)).sub (rf _ _ _ _ fun j => by omega)).add
      (rf _ _ _ _ fun j => by omega)).sub (rf _ _ _ _ fun j => by omega)).add rA0).add
      (rf _ _ _ _ fun j => by omega)).sub (rf _ _ _ _ fun j => by omega)).sub rH1).add
      (rf _ _ _ _ fun j => by omega)).sub (rf _ _ _ _ fun j => by omega) |>.add
      (rf _ _ _ _ fun j => by omega) |>.sub (rf _ _ _ _ fun j => by omega)
  have heq : ωv = β + (U + P - Q + Cp - Cm + A0 + Hp - Hm - H1 + Vp - Vm + Wp - Wm) *ᵥ ωv := by
    funext i
    rw [Pi.add_apply]
    by_cases hi : (i.1 : ℕ) = 0
    · rw [Raise.mulVec_zero rT ωv hi, add_zero, hβ]; simp only [if_pos hi]; rfl
    · rw [← hdecomp, Tmat_rec hcc hrec hsupp i (by omega), hβ]; simp only [if_neg hi, zero_add]; rfl
  -- the operator inequalities
  have hYP : ∀ i k, fB 0 i k ≤ P i k := le_sum_MNN (fun j _ => nB j) (mem_filter.mpr ⟨h0R, (⟨0, rfl⟩ : Even 0)⟩)
  have det : ∀ (W : ℕ → ℕ → ℕ → ℝ) (e o : ℕ) (j0 : ℕ), o ≤ 1 →
      (∀ j ℓ a, j0 ≤ j → ℓ + a ≤ N → 4 * cc (ℓ + 1) * W j ℓ a ≤ B 0 ℓ a * W (j - 1) (ℓ + 1) (a - 2)) →
      ∀ j, j0 ≤ j → 1 ≤ j → ∀ i k, 4 * smv cc N (j + 1 + e) (2 * j + 2 - o) (W j) i k ≤
        (smv cc N (j - 1 + 1 + e) (2 * (j - 1) + 2 - o) (W (j - 1)) * fB 0) i k := by
    intro W e o j0 ho hW j hj hj1 i k
    have : fB 0 = smv cc N 1 2 (B 0) := by simp [hfB]
    rw [this]
    exact smv_detour hcc (by omega) (by omega) (fun ℓ a hla _ _ => hW j ℓ a hj hla) i k
  have dQ : ∀ i k, 4 * Q i k ≤ (P * P) i k := by
    refine fam_detour (fun j hj => ?_) (fun j _ => nB j) (nB 0) hYP (fun j hj i k => ?_)
    · obtain ⟨hjR, hjo⟩ := mem_filter.mp hj
      obtain ⟨m, rfl⟩ := hjo
      exact ⟨by omega, mem_filter.mpr ⟨mem_range.mpr (by have := mem_range.mp hjR; omega), ⟨m, by omega⟩⟩⟩
    · have hj1 : 1 ≤ j := by obtain ⟨m, rfl⟩ := (mem_filter.mp hj).2; omega
      have := det B 0 0 1 (by norm_num) (fun j ℓ a hj hla => hw.domB j ℓ a hj hla) j hj1 hj1 i k
      simpa [hfB, show 2 * (j - 1) + 2 = 2 * j by omega, show j - 1 + 1 = j by omega] using this
  have dC : ∀ i k, 4 * Cm i k ≤ (Cp * P) i k := by
    refine fam_detour (fun j hj => ?_) (fun j _ => nC j) (nB 0) hYP (fun j hj i k => ?_)
    · obtain ⟨hjR, hjo⟩ := mem_filter.mp hj
      obtain ⟨m, rfl⟩ := hjo
      exact ⟨by omega, mem_filter.mpr ⟨mem_range.mpr (by have := mem_range.mp hjR; omega), ⟨m, by omega⟩⟩⟩
    · have hj1 : 1 ≤ j := by obtain ⟨m, rfl⟩ := (mem_filter.mp hj).2; omega
      have := det C 1 0 1 (by norm_num) (fun j ℓ a hj hla => hw.domC j ℓ a hj hla) j hj1 hj1 i k
      simpa [hfC, show 2 * (j - 1) + 2 = 2 * j by omega, show j - 1 + 1 + 1 = j + 1 by omega,
        show j + 1 + 1 = j + 2 by omega] using this
  have dH : ∀ i k, 4 * Hm i k ≤ (Hp * P) i k := by
    refine fam_detour (fun j hj => ?_) (fun j _ => nH j) (nB 0) hYP (fun j hj i k => ?_)
    · obtain ⟨hjR, hjo, hj3⟩ := mem_filter.mp hj
      obtain ⟨m, rfl⟩ := hjo
      exact ⟨by omega, mem_filter.mpr ⟨mem_range.mpr (by have := mem_range.mp hjR; omega), ⟨m, by omega⟩, by omega⟩⟩
    · have hj3 : 3 ≤ j := (mem_filter.mp hj).2.2
      have := det H 0 1 2 (by norm_num) (fun j ℓ a hj hla => hw.domH j ℓ a hj hla) j (by omega) (by omega) i k
      simpa [hfH, show 2 * (j - 1) + 2 - 1 = 2 * j - 1 by omega, show 2 * j + 2 - 1 = 2 * j + 1 by omega,
        show j - 1 + 1 = j by omega, show 2 * (j - 1) + 1 = 2 * j - 1 by omega] using this
  have dV : ∀ i k, 4 * Vm i k ≤ (Vp * P) i k := by
    refine fam_detour (fun j hj => ?_) (fun j _ => nV j) (nB 0) hYP (fun j hj i k => ?_)
    · obtain ⟨hjR, hje, hj2⟩ := mem_filter.mp hj
      obtain ⟨m, rfl⟩ := hje
      exact ⟨by omega, mem_filter.mpr ⟨mem_range.mpr (by have := mem_range.mp hjR; omega), ⟨m - 1, by omega⟩⟩⟩
    · have hj2 : 2 ≤ j := (mem_filter.mp hj).2.2
      have := det V 0 1 2 (by norm_num) (fun j ℓ a hj hla => hw.domV j ℓ a hj hla) j hj2 (by omega) i k
      simpa [hfV, show 2 * (j - 1) + 2 - 1 = 2 * j - 1 by omega, show 2 * j + 2 - 1 = 2 * j + 1 by omega,
        show j - 1 + 1 = j by omega, show 2 * (j - 1) + 1 = 2 * j - 1 by omega] using this
  have detc : ∀ (W' : ℕ → ℕ → ℕ → ℝ) (κ : ℝ) (e o : ℕ) (j0 : ℕ), o ≤ 1 →
      (∀ j ℓ a, j0 ≤ j → ℓ + a ≤ N → κ * cc (ℓ + 1) * W' j ℓ a ≤ B 0 ℓ a * W' (j - 1) (ℓ + 1) (a - 2)) →
      ∀ j, j0 ≤ j → 1 ≤ j → ∀ i k, κ * smv cc N (j + 1 + e) (2 * j + 2 - o) (W' j) i k ≤
        (smv cc N (j - 1 + 1 + e) (2 * (j - 1) + 2 - o) (W' (j - 1)) * fB 0) i k := by
    intro W' κ e o j0 ho hW j hj hj1 i k
    have : fB 0 = smv cc N 1 2 (B 0) := by simp [hfB]
    rw [this]
    exact smv_detour_c hcc (by omega) (by omega) (fun ℓ a hla _ _ => hW j ℓ a hj hla) i k
  have dW : ∀ i k, 2 * Wm i k ≤ (Wp * P) i k := by
    refine fam_detour_c (fun j hj => ?_) (fun j _ => nW j) (nB 0) hYP (fun j hj i k => ?_)
    · obtain ⟨hjR, hje, hj2⟩ := mem_filter.mp hj
      obtain ⟨m, rfl⟩ := hje
      exact ⟨by omega, mem_filter.mpr ⟨mem_range.mpr (by have := mem_range.mp hjR; omega), ⟨m - 1, by omega⟩⟩⟩
    · have hj2 : 2 ≤ j := (mem_filter.mp hj).2.2
      have := detc W 2 0 1 2 (by norm_num) (fun j ℓ a hj hla => hw.domW j ℓ a hj hla) j hj2 (by omega) i k
      simpa [hfW, show 2 * (j - 1) + 2 - 1 = 2 * j - 1 by omega, show 2 * j + 2 - 1 = 2 * j + 1 by omega,
        show j - 1 + 1 = j by omega, show 2 * (j - 1) + 1 = 2 * j - 1 by omega] using this
  have dV1 : ∀ i k, V1 i k ≤ Vp i k := le_sum_MNN (fun j _ => nV j) (mem_filter.mpr ⟨h1R, odd_one⟩)
  have dkey : ∀ i k, 4 * H1 i k ≤ (A0 * P) i k + (P * A0) i k + 2 * V1 i k := by
    intro i k
    have e1 : A0 * fB 0 = smv cc N 2 3 (fun ℓ a => B 0 ℓ a * A 0 (ℓ + 1) (a - 2) / cc (ℓ + 1)) := by
      show smv cc N 1 1 (A 0) * smv cc N 1 2 (B 0) = _
      rw [smv_mul (by norm_num : (1 : ℕ) ≤ 2)]
    have e2 : fB 0 * A0 = smv cc N 2 3 (fun ℓ a => A 0 ℓ a * B 0 (ℓ + 1) (a - 1) / cc (ℓ + 1)) := by
      show smv cc N 1 2 (B 0) * smv cc N 1 1 (A 0) = _
      rw [smv_mul (by norm_num : (1 : ℕ) ≤ 1)]
    have l1 := mul_le_mul_left_MNN nA0 hYP i k
    have l2 := mul_le_mul_right_MNN nA0 hYP i k
    rw [e1] at l1; rw [e2] at l2
    have hk : 4 * H1 i k ≤ smv cc N 2 3 (fun ℓ a => B 0 ℓ a * A 0 (ℓ + 1) (a - 2) / cc (ℓ + 1)) i k +
        smv cc N 2 3 (fun ℓ a => A 0 ℓ a * B 0 (ℓ + 1) (a - 1) / cc (ℓ + 1)) i k + 2 * V1 i k := by
      have hV1' : V1 = smv cc N 2 3 (V 1) := by simp [hV1, hfV]
      have hH1' : H1 = smv cc N 2 3 (H 1) := by simp [hH1, hfH]
      have hlin : ∀ (F1 F2 F3 : ℕ → ℕ → ℝ), smv cc N 2 3 F1 i k + smv cc N 2 3 F2 i k + 2 * smv cc N 2 3 F3 i k =
          smv cc N 2 3 (fun ℓ a => F1 ℓ a + F2 ℓ a + 2 * F3 ℓ a) i k := by
        intro F1 F2 F3; simp only [smv]; split_ifs <;> ring
      rw [hV1', hH1', hlin]
      refine smv_le_c hcc (by norm_num) (fun ℓ a hla ha _ => ?_) i k
      have hc := hcc (ℓ + 1) (by omega)
      have key := hw.key ℓ a hla ha
      have h2 : 4 * H 1 ℓ a - 2 * V 1 ℓ a ≤
          (B 0 ℓ a * A 0 (ℓ + 1) (a - 2) + A 0 ℓ a * B 0 (ℓ + 1) (a - 1)) / cc (ℓ + 1) := by
        rw [le_div_iff₀ hc]; linarith
      rw [add_div] at h2
      linarith
    linarith
  -- the resummation
  have hnn := resum_nonneg3 (lev := lvl) N (fun i => by unfold lvl; have := i.1.isLt; omega)
    nU nP (MNN.sum fun j _ => nC j) nA0 (MNN.sum fun j _ => nH j) (MNN.sum fun j _ => nV j)
    (MNN.sum fun j _ => nW j)
    (smv_raise le_rfl _) (rf _ _ _ _ fun j => by omega) (rf _ _ _ _ fun j => by omega)
    (rf _ _ _ _ fun j => by omega) (rf _ _ _ _ fun j => by omega) (smv_raise (by omega) _)
    (rf _ _ _ _ fun j => by omega) (rf _ _ _ _ fun j => by omega) (smv_raise (by omega) _)
    (rf _ _ _ _ fun j => by omega) (rf _ _ _ _ fun j => by omega)
    (rf _ _ _ _ fun j => by omega) (rf _ _ _ _ fun j => by omega)
    dQ dH dV dC dW dV1 dkey (β := β) (fun i => by
      simp only [hβ]; split_ifs with h
      · have := h0 i.2; rw [← h] at this; exact this
      · exact le_rfl) heq
  intro ℓ a
  by_cases h : ℓ + a ≤ N
  · have := hnn (⟨ℓ, by omega⟩, ⟨a, by omega⟩)
    simpa [hωv] using this
  · rw [hsupp ℓ a (by omega)]


end Moves3

end Szkraw
