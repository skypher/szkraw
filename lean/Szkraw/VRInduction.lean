import Szkraw.LCDetours
import Mathlib.Algebra.BigOperators.Intervals

/-!
# The operator induction with abstract move weights (paper, proofs of Theorems 8.6 and 8.8)

`ω` satisfies `cc(ℓ+1) ω(ℓ+1,a) = s(ℓ,a) ω(ℓ,a) + Σ_{j ≤ ℓ} (-1)^j grp_j(ℓ,a)`, where group `j`
consists of an `A`-move from `(ℓ-j, a+2j+1)`, a `B`-move from `(ℓ-j, a+2j+2)` and a `C`-move from
`(ℓ-j-1, a+2j+2)`, with weights `A j`, `B j`, `C j` evaluated at the source. If `ω` vanishes off
`Ω = {ℓ + a ≤ N}`, the weights and `s` are nonnegative on `Ω`, and the odd moves are dominated by
two-step detours through even moves on `Ω` (the three inequalities of Lemma 8.4), then `ω ≥ 0`.
Only sources in `Ω` matter, since `ω` vanishes elsewhere.
-/

namespace Szkraw

open Finset

variable (cc : ℕ → ℝ) (A B C : ℕ → ℕ → ℕ → ℝ) (s : ℕ → ℕ → ℝ) (ω : ℕ → ℕ → ℝ)

noncomputable def gmA (j ℓ a : ℕ) : ℝ := A j (ℓ - j) (a + 2 * j + 1) * ω (ℓ - j) (a + 2 * j + 1)
noncomputable def gmB (j ℓ a : ℕ) : ℝ := B j (ℓ - j) (a + 2 * j + 2) * ω (ℓ - j) (a + 2 * j + 2)
noncomputable def gmC (j ℓ a : ℕ) : ℝ :=
  if j < ℓ then C j (ℓ - j - 1) (a + 2 * j + 2) * ω (ℓ - j - 1) (a + 2 * j + 2) else 0

noncomputable def ggrp (j ℓ a : ℕ) : ℝ := gmA A ω j ℓ a + gmB B ω j ℓ a + gmC C ω j ℓ a

noncomputable def gPin (ℓ a : ℕ) : ℝ := ∑ j ∈ (range (ℓ + 1)).filter Even, ggrp A B C ω j ℓ a
noncomputable def gQin (ℓ a : ℕ) : ℝ := ∑ j ∈ (range (ℓ + 1)).filter Odd, ggrp A B C ω j ℓ a

/-- The generic kernel recurrence. -/
def GenRec : Prop :=
  ∀ ℓ a, cc (ℓ + 1) * ω (ℓ + 1) a = s ℓ a * ω ℓ a + ∑ j ∈ range (ℓ + 1), (-1 : ℝ) ^ j * ggrp A B C ω j ℓ a

/-- Hypotheses on the weights, on `Ω = {ℓ + a ≤ N}`. -/
structure GenWeights (N : ℕ) : Prop where
  cc_pos : ∀ n, 1 ≤ n → 0 < cc n
  A_nn : ∀ j ℓ a, ℓ + a ≤ N → 0 ≤ A j ℓ a
  B_nn : ∀ j ℓ a, ℓ + a ≤ N → 0 ≤ B j ℓ a
  C_nn : ∀ j ℓ a, ℓ + a ≤ N → 0 ≤ C j ℓ a
  s_nn : ∀ ℓ a, ℓ + a ≤ N → 0 ≤ s ℓ a
  domA : ∀ j ℓ a, 1 ≤ j → ℓ + a ≤ N →
    4 * cc (ℓ + 1) * A j ℓ a ≤ A 0 ℓ a * B (j - 1) (ℓ + 1) (a - 1) + B 0 ℓ a * A (j - 1) (ℓ + 1) (a - 2)
  domB : ∀ j ℓ a, 1 ≤ j → ℓ + a ≤ N → 4 * cc (ℓ + 1) * B j ℓ a ≤ B 0 ℓ a * B (j - 1) (ℓ + 1) (a - 2)
  domC : ∀ j ℓ a, 1 ≤ j → ℓ + a ≤ N → 4 * cc (ℓ + 1) * C j ℓ a ≤ B 0 ℓ a * C (j - 1) (ℓ + 1) (a - 2)

theorem gsign_split (ℓ a : ℕ) :
    ∑ j ∈ range (ℓ + 1), (-1 : ℝ) ^ j * ggrp A B C ω j ℓ a = gPin A B C ω ℓ a - gQin A B C ω ℓ a := by
  unfold gPin gQin
  rw [← sum_filter_add_sum_filter_not (range (ℓ + 1)) Even]
  have h1 : ∑ j ∈ (range (ℓ + 1)).filter Even, (-1 : ℝ) ^ j * ggrp A B C ω j ℓ a =
      ∑ j ∈ (range (ℓ + 1)).filter Even, ggrp A B C ω j ℓ a := by
    refine sum_congr rfl (fun j hj => ?_)
    rw [(mem_filter.mp hj).2.neg_one_pow, one_mul]
  have h2 : ∑ j ∈ (range (ℓ + 1)).filter (fun j => ¬ Even j), (-1 : ℝ) ^ j * ggrp A B C ω j ℓ a =
      -∑ j ∈ (range (ℓ + 1)).filter Odd, ggrp A B C ω j ℓ a := by
    rw [← sum_neg_distrib]
    have : (range (ℓ + 1)).filter (fun j => ¬ Even j) = (range (ℓ + 1)).filter Odd := by
      ext j; simp [Nat.not_even_iff_odd]
    rw [this]
    refine sum_congr rfl (fun j hj => ?_)
    rw [(mem_filter.mp hj).2.neg_one_pow]; ring
  rw [h1, h2]; ring

variable {cc A B C s ω}

/-- A weight times `ω` at its source is nonnegative: in `Ω` by the weight hypothesis, outside since
`ω` vanishes there. -/
theorem wmul_nonneg {N : ℕ} (hsupp : ∀ ℓ a, N < ℓ + a → ω ℓ a = 0) {W : ℝ} {ℓ a : ℕ}
    (hW : ℓ + a ≤ N → 0 ≤ W) (hω : 0 ≤ ω ℓ a) : 0 ≤ W * ω ℓ a := by
  by_cases h : ℓ + a ≤ N
  · exact mul_nonneg (hW h) hω
  · rw [hsupp ℓ a (by omega), mul_zero]

theorem ggrp_nonneg {N : ℕ} (hw : GenWeights cc A B C s N) (hsupp : ∀ ℓ a, N < ℓ + a → ω ℓ a = 0)
    {ℓ : ℕ} (hnn : ∀ ℓ' ≤ ℓ, ∀ a', 0 ≤ ω ℓ' a') (j a : ℕ) : 0 ≤ ggrp A B C ω j ℓ a := by
  unfold ggrp gmA gmB gmC
  refine add_nonneg (add_nonneg ?_ ?_) ?_
  · exact wmul_nonneg hsupp (hw.A_nn _ _ _) (hnn _ (by omega) _)
  · exact wmul_nonneg hsupp (hw.B_nn _ _ _) (hnn _ (by omega) _)
  · split_ifs
    · exact wmul_nonneg hsupp (hw.C_nn _ _ _) (hnn _ (by omega) _)
    · exact le_rfl

theorem gPin_ge_grp0 {N : ℕ} (hw : GenWeights cc A B C s N) (hsupp : ∀ ℓ a, N < ℓ + a → ω ℓ a = 0)
    {ℓ : ℕ} (hnn : ∀ ℓ' ≤ ℓ, ∀ a', 0 ≤ ω ℓ' a') (a : ℕ) :
    ggrp A B C ω 0 ℓ a ≤ gPin A B C ω ℓ a := by
  unfold gPin
  have hmem : 0 ∈ (range (ℓ + 1)).filter Even := mem_filter.mpr ⟨mem_range.mpr (by omega), ⟨0, rfl⟩⟩
  exact single_le_sum (fun j _ => ggrp_nonneg hw hsupp hnn j a) hmem

/-- Domination of one odd group by the preceding even group: `2 grp_j ≤ grp_{j-1}`. -/
theorem godd_dom {N : ℕ} (hw : GenWeights cc A B C s N) (hsupp : ∀ ℓ a, N < ℓ + a → ω ℓ a = 0) {ℓ : ℕ}
    (hnn : ∀ ℓ' ≤ ℓ, ∀ a', 0 ≤ ω ℓ' a')
    (hP : ∀ ℓ' < ℓ, ∀ a', (1 / 2 : ℝ) * gPin A B C ω ℓ' a' ≤ cc (ℓ' + 1) * ω (ℓ' + 1) a')
    {j : ℕ} (hj1 : 1 ≤ j) (hjl : j ≤ ℓ) (a : ℕ) :
    2 * ggrp A B C ω j ℓ a ≤ ggrp A B C ω (j - 1) ℓ a := by
  obtain ⟨L, rfl⟩ : ∃ L, ℓ = L + j := ⟨ℓ - j, by omega⟩
  set ωx := ω L (a + 2 * j + 1)
  set ωx' := ω L (a + 2 * j + 2)
  set ωz1 := ω (L + 1) (a + 2 * j)
  set ωz2 := ω (L + 1) (a + 2 * j - 1)
  set A0 := A 0 L (a + 2 * j + 1)
  set B0x := B 0 L (a + 2 * j + 1)
  set B0x' := B 0 L (a + 2 * j + 2)
  set Aj := A j L (a + 2 * j + 1)
  set Bj := B j L (a + 2 * j + 2)
  set Bm := B (j - 1) (L + 1) (a + 2 * j)
  set Am := A (j - 1) (L + 1) (a + 2 * j - 1)
  set D1 := cc (L + 1)
  have hD1 : 0 < D1 := hw.cc_pos (L + 1) (by omega)
  have hωx : 0 ≤ ωx := hnn _ (by omega) _
  have hωx' : 0 ≤ ωx' := hnn _ (by omega) _
  have hωz1 : 0 ≤ ωz1 := hnn _ (by omega) _
  have hωz2 : 0 ≤ ωz2 := hnn _ (by omega) _
  have hgm : ggrp A B C ω (j - 1) (L + j) a = Am * ωz2 + Bm * ωz1 + gmC C ω (j - 1) (L + j) a := by
    unfold ggrp gmA gmB
    have e2 : L + j - (j - 1) = L + 1 := by omega
    have e3 : a + 2 * (j - 1) + 1 = a + 2 * j - 1 := by omega
    have e5 : a + 2 * (j - 1) + 2 = a + 2 * j := by omega
    rw [e2, e3, e5]
  have hgj : ggrp A B C ω j (L + j) a = Aj * ωx + Bj * ωx' + gmC C ω j (L + j) a := by
    unfold ggrp gmA gmB
    have e2 : L + j - j = L := by omega
    rw [e2]
  -- the A/B part
  have pAB : 2 * (Aj * ωx + Bj * ωx') ≤ Am * ωz2 + Bm * ωz1 := by
    have hR : 0 ≤ Am * ωz2 + Bm * ωz1 :=
      add_nonneg (wmul_nonneg hsupp (hw.A_nn _ _ _) hωz2) (wmul_nonneg hsupp (hw.B_nn _ _ _) hωz1)
    by_cases hx : L + (a + 2 * j + 1) ≤ N
    · have hAm : 0 ≤ Am := hw.A_nn _ _ _ (by omega)
      have hBm : 0 ≤ Bm := hw.B_nn _ _ _ (by omega)
      have f1 : (1 / 2 : ℝ) * (A0 * ωx + B0x' * ωx') ≤ D1 * ωz1 := by
        have h := hP L (by omega) (a + 2 * j)
        have g := gPin_ge_grp0 hw hsupp (ℓ := L) (fun ℓ' h a' => hnn ℓ' (by omega) a') (a + 2 * j)
        have hg0 : ggrp A B C ω 0 L (a + 2 * j) = A0 * ωx + B0x' * ωx' + gmC C ω 0 L (a + 2 * j) := by
          unfold ggrp gmA gmB; simp only [Nat.sub_zero, mul_zero, add_zero]; rfl
        have hc0 : 0 ≤ gmC C ω 0 L (a + 2 * j) := by
          unfold gmC; split_ifs
          · exact wmul_nonneg hsupp (hw.C_nn _ _ _) (hnn _ (by omega) _)
          · exact le_rfl
        linarith
      have f2 : (1 / 2 : ℝ) * (B0x * ωx) ≤ D1 * ωz2 := by
        have h := hP L (by omega) (a + 2 * j - 1)
        have g := gPin_ge_grp0 hw hsupp (ℓ := L) (fun ℓ' h a' => hnn ℓ' (by omega) a') (a + 2 * j - 1)
        have hB : gmB B ω 0 L (a + 2 * j - 1) = B0x * ωx := by
          unfold gmB
          have e : a + 2 * j - 1 + 2 = a + 2 * j + 1 := by omega
          simp only [Nat.sub_zero, mul_zero, add_zero]; rw [e]
        have hA0 : 0 ≤ gmA A ω 0 L (a + 2 * j - 1) := by
          unfold gmA; exact wmul_nonneg hsupp (hw.A_nn _ _ _) (hnn _ (by omega) _)
        have hc0 : 0 ≤ gmC C ω 0 L (a + 2 * j - 1) := by
          unfold gmC; split_ifs
          · exact wmul_nonneg hsupp (hw.C_nn _ _ _) (hnn _ (by omega) _)
          · exact le_rfl
        unfold ggrp at g
        linarith
      have g1 : 4 * D1 * Aj ≤ A0 * Bm + B0x * Am := by
        have h := hw.domA j L (a + 2 * j + 1) hj1 hx
        have e1 : a + 2 * j + 1 - 1 = a + 2 * j := by omega
        have e2 : a + 2 * j + 1 - 2 = a + 2 * j - 1 := by omega
        rw [e1, e2] at h; exact h
      have g2 : 4 * D1 * Bj * ωx' ≤ B0x' * Bm * ωx' := by
        by_cases hx' : L + (a + 2 * j + 2) ≤ N
        · have h := hw.domB j L (a + 2 * j + 2) hj1 hx'
          have e1 : a + 2 * j + 2 - 2 = a + 2 * j := by omega
          rw [e1] at h; exact mul_le_mul_of_nonneg_right h hωx'
        · have : ωx' = 0 := hsupp _ _ (by omega)
          rw [this, mul_zero, mul_zero]
      have k1 := mul_le_mul_of_nonneg_left f2 hAm
      have k2 := mul_le_mul_of_nonneg_left f1 hBm
      have k3 := mul_le_mul_of_nonneg_right g1 hωx
      have : D1 * (2 * (Aj * ωx + Bj * ωx')) ≤ D1 * (Am * ωz2 + Bm * ωz1) := by nlinarith
      exact le_of_mul_le_mul_left this hD1
    · have h1 : ωx = 0 := hsupp _ _ (by omega)
      have h2 : ωx' = 0 := hsupp _ _ (by omega)
      rw [h1, h2, mul_zero, mul_zero, add_zero, mul_zero]
      exact hR
  -- the C part
  have pC : 2 * gmC C ω j (L + j) a ≤ gmC C ω (j - 1) (L + j) a := by
    have hR : 0 ≤ gmC C ω (j - 1) (L + j) a := by
      unfold gmC; split_ifs
      · exact wmul_nonneg hsupp (hw.C_nn _ _ _) (hnn _ (by omega) _)
      · exact le_rfl
    unfold gmC
    by_cases hL : j < L + j
    · rw [if_pos hL, if_pos (by omega)]
      have e1 : L + j - j - 1 = L - 1 := by omega
      have e2 : L + j - (j - 1) - 1 = L := by omega
      have e5 : a + 2 * (j - 1) + 2 = a + 2 * j := by omega
      rw [e1, e2, e5]
      have hL1 : 1 ≤ L := by omega
      by_cases hy : L - 1 + (a + 2 * j + 2) ≤ N
      · set D0 := cc L
        have hD0 : 0 < D0 := hw.cc_pos L hL1
        have hCm : 0 ≤ C (j - 1) L (a + 2 * j) := hw.C_nn _ _ _ (by omega)
        have f3 : (1 / 2 : ℝ) * (B 0 (L - 1) (a + 2 * j + 2) * ω (L - 1) (a + 2 * j + 2)) ≤ D0 * ω L (a + 2 * j) := by
          have h := hP (L - 1) (by omega) (a + 2 * j)
          have e6 : L - 1 + 1 = L := by omega
          rw [e6] at h
          have g := gPin_ge_grp0 hw hsupp (ℓ := L - 1) (fun ℓ' h a' => hnn ℓ' (by omega) a') (a + 2 * j)
          have hB : gmB B ω 0 (L - 1) (a + 2 * j) = B 0 (L - 1) (a + 2 * j + 2) * ω (L - 1) (a + 2 * j + 2) := by
            unfold gmB; simp only [Nat.sub_zero, mul_zero, add_zero]
          have hA0 : 0 ≤ gmA A ω 0 (L - 1) (a + 2 * j) := by
            unfold gmA; exact wmul_nonneg hsupp (hw.A_nn _ _ _) (hnn _ (by omega) _)
          have hc0 : 0 ≤ gmC C ω 0 (L - 1) (a + 2 * j) := by
            unfold gmC; split_ifs
            · exact wmul_nonneg hsupp (hw.C_nn _ _ _) (hnn _ (by omega) _)
            · exact le_rfl
          unfold ggrp at g
          linarith
        have g3 : 4 * D0 * C j (L - 1) (a + 2 * j + 2) ≤ B 0 (L - 1) (a + 2 * j + 2) * C (j - 1) L (a + 2 * j) := by
          have h := hw.domC j (L - 1) (a + 2 * j + 2) hj1 hy
          have e6 : L - 1 + 1 = L := by omega
          have e7 : a + 2 * j + 2 - 2 = a + 2 * j := by omega
          rw [e6, e7] at h; exact h
        have hωy : 0 ≤ ω (L - 1) (a + 2 * j + 2) := hnn _ (by omega) _
        have k1 := mul_le_mul_of_nonneg_left f3 hCm
        have k2 := mul_le_mul_of_nonneg_right g3 hωy
        have : D0 * (2 * (C j (L - 1) (a + 2 * j + 2) * ω (L - 1) (a + 2 * j + 2))) ≤
            D0 * (C (j - 1) L (a + 2 * j) * ω L (a + 2 * j)) := by nlinarith
        exact le_of_mul_le_mul_left this hD0
      · have : ω (L - 1) (a + 2 * j + 2) = 0 := hsupp _ _ (by omega)
        rw [this, mul_zero, mul_zero]
        exact wmul_nonneg hsupp (hw.C_nn _ _ _) (hnn _ (by omega) _)
    · rw [if_neg hL]
      unfold gmC at hR
      linarith
  rw [hgm, hgj]
  linarith

theorem gQin_le_half_Pin {N : ℕ} (hw : GenWeights cc A B C s N) (hsupp : ∀ ℓ a, N < ℓ + a → ω ℓ a = 0)
    {ℓ : ℕ} (hnn : ∀ ℓ' ≤ ℓ, ∀ a', 0 ≤ ω ℓ' a')
    (hP : ∀ ℓ' < ℓ, ∀ a', (1 / 2 : ℝ) * gPin A B C ω ℓ' a' ≤ cc (ℓ' + 1) * ω (ℓ' + 1) a') (a : ℕ) :
    gQin A B C ω ℓ a ≤ (1 / 2 : ℝ) * gPin A B C ω ℓ a := by
  unfold gQin gPin
  set Od := (range (ℓ + 1)).filter Odd
  set Ev := (range (ℓ + 1)).filter Even
  have step1 : ∑ j ∈ Od, ggrp A B C ω j ℓ a ≤ ∑ j ∈ Od, (1 / 2 : ℝ) * ggrp A B C ω (j - 1) ℓ a := by
    refine sum_le_sum (fun j hj => ?_)
    obtain ⟨hjr, hjo⟩ := mem_filter.mp hj
    have hj1 : 1 ≤ j := by obtain ⟨k, rfl⟩ := hjo; omega
    have := godd_dom hw hsupp hnn hP hj1 (by have := mem_range.mp hjr; omega) a
    linarith
  have hinj : Set.InjOn (fun j => j - 1) (Od : Set ℕ) := by
    intro x hx y hy hxy
    have hx1 : 1 ≤ x := by obtain ⟨k, rfl⟩ := (mem_filter.mp hx).2; omega
    have hy1 : 1 ≤ y := by obtain ⟨k, rfl⟩ := (mem_filter.mp hy).2; omega
    simp only at hxy; omega
  have step2 : ∑ j ∈ Od, ggrp A B C ω (j - 1) ℓ a = ∑ j' ∈ Od.image (fun j => j - 1), ggrp A B C ω j' ℓ a :=
    (sum_image (f := fun j' => ggrp A B C ω j' ℓ a) (fun x hx y hy h => hinj hx hy h)).symm
  have hsub : Od.image (fun j => j - 1) ⊆ Ev := by
    intro j' hj'
    obtain ⟨j, hj, rfl⟩ := mem_image.mp hj'
    obtain ⟨hjr, hjo⟩ := mem_filter.mp hj
    refine mem_filter.mpr ⟨mem_range.mpr (by have := mem_range.mp hjr; omega), ?_⟩
    obtain ⟨k, rfl⟩ := hjo; exact ⟨k, by omega⟩
  have step3 : ∑ j' ∈ Od.image (fun j => j - 1), ggrp A B C ω j' ℓ a ≤ ∑ j' ∈ Ev, ggrp A B C ω j' ℓ a :=
    sum_le_sum_of_subset_of_nonneg hsub (fun j _ _ => ggrp_nonneg hw hsupp hnn j a)
  rw [← mul_sum] at step1
  linarith

/-- Every solution of the generic kernel recurrence with nonnegative initial values and the support
property is nonnegative. -/
theorem gkernel_nonneg {N : ℕ} (hw : GenWeights cc A B C s N) (hrec : GenRec cc A B C s ω)
    (h0 : ∀ a, 0 ≤ ω 0 a) (hsupp : ∀ ℓ a, N < ℓ + a → ω ℓ a = 0) : ∀ ℓ a, 0 ≤ ω ℓ a := by
  have claim : ∀ ℓ, (∀ ℓ' ≤ ℓ, ∀ a, 0 ≤ ω ℓ' a) ∧
      (∀ ℓ' < ℓ, ∀ a, (1 / 2 : ℝ) * gPin A B C ω ℓ' a ≤ cc (ℓ' + 1) * ω (ℓ' + 1) a) := by
    intro ℓ
    induction ℓ with
    | zero => exact ⟨fun ℓ' h a => by rw [Nat.le_zero.mp h]; exact h0 a, fun ℓ' h => absurd h (Nat.not_lt_zero _)⟩
    | succ ℓ ih =>
      obtain ⟨hnn, hP⟩ := ih
      have hnew : ∀ a, (1 / 2 : ℝ) * gPin A B C ω ℓ a ≤ cc (ℓ + 1) * ω (ℓ + 1) a := by
        intro a
        have hq := gQin_le_half_Pin hw hsupp hnn hP a
        have hr := hrec ℓ a
        rw [gsign_split] at hr
        have hs : 0 ≤ s ℓ a * ω ℓ a := wmul_nonneg hsupp (hw.s_nn ℓ a) (hnn ℓ le_rfl a)
        linarith
      have hPnn : ∀ a, 0 ≤ gPin A B C ω ℓ a := fun a =>
        sum_nonneg (fun j _ => ggrp_nonneg hw hsupp hnn j a)
      refine ⟨fun ℓ' h a => ?_, fun ℓ' h a => ?_⟩
      · rcases Nat.lt_or_ge ℓ' (ℓ + 1) with h' | h'
        · exact hnn ℓ' (by omega) a
        · have e : ℓ' = ℓ + 1 := by omega
          subst e
          have hd := hw.cc_pos (ℓ + 1) (by omega)
          have h1 := hnew a
          have h2 : 0 ≤ cc (ℓ + 1) * ω (ℓ + 1) a := by linarith [hPnn a]
          by_contra hneg
          push Not at hneg
          nlinarith
      · rcases Nat.lt_or_ge ℓ' ℓ with h' | h'
        · exact hP ℓ' h' a
        · have e : ℓ' = ℓ := by omega
          subst e; exact hnew a
  intro ℓ a
  exact (claim ℓ).1 ℓ le_rfl a

end Szkraw
