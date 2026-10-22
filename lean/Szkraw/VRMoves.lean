import Szkraw.VRResum
import Szkraw.VRInduction
import Mathlib.Algebra.BigOperators.Field

/-!
# Move operators of the kernel recurrence (paper, proof of Theorem 8.9)

The moves of the generic kernel recurrence (`GenRec`, `VRInduction.lean`) as matrices on the
index set `{0,…,N}²` of the pairs `(ℓ, a)`: a move of displacement `(d₁, -d₂)` with weight `F` at
the source, divided by `cc` at the destination level, and counted only for sources in
`Ω = {ℓ + a ≤ N}`. The recurrence reads `ω = β + Tω`; when the `A`-weights of positive index split
as `A_j = H_j - V_j` on `Ω`, `T` is the operator `U + P - Q + C₊ - C₋ + A₀ + H₊ - H₋ - H₁ + V₊ - V₋`
of the paper. Under the detour inequalities and the key inequality (`ResumWeights`), the
resummation (`VRResum.lean`) gives `ω ≥ 0`.
-/

set_option linter.unusedSectionVars false

namespace Szkraw

open Finset Matrix

/-- The index set `{0,…,N}²` of the pairs `(ℓ, a)`. -/
abbrev Idx (N : ℕ) := Fin (N + 1) × Fin (N + 1)

/-- The level `ℓ` of an index. -/
def lvl {N : ℕ} (i : Idx N) : ℕ := i.1

section Moves

variable (cc : ℕ → ℝ) (N : ℕ)

/-- A move of displacement `(d₁, -d₂)` with weight `F` at the source, divided by `cc` at the
destination level; only sources in `Ω = {ℓ + a ≤ N}` count. -/
noncomputable def smv (d1 d2 : ℕ) (F : ℕ → ℕ → ℝ) : Matrix (Idx N) (Idx N) ℝ := fun i k =>
  if (k.1 : ℕ) + k.2 ≤ N ∧ (k.1 : ℕ) + d1 = i.1 ∧ (k.2 : ℕ) = i.2 + d2 then F k.1 k.2 / cc i.1 else 0

variable {cc N}

theorem smv_nonneg (hcc : ∀ n, 1 ≤ n → 0 < cc n) {d1 d2 : ℕ} (hd1 : 1 ≤ d1) {F : ℕ → ℕ → ℝ}
    (hF : ∀ ℓ a, ℓ + a ≤ N → 0 ≤ F ℓ a) : MNN (smv cc N d1 d2 F) := by
  intro i k
  unfold smv
  split_ifs with h
  · exact div_nonneg (hF _ _ h.1) (hcc _ (by omega)).le
  · exact le_rfl

theorem smv_raise {d1 d2 : ℕ} (hd1 : 1 ≤ d1) (F : ℕ → ℕ → ℝ) : Raise lvl 1 (smv cc N d1 d2 F) := by
  intro i k h
  unfold smv lvl at *
  rw [if_neg]; omega

theorem smv_le_c (hcc : ∀ n, 1 ≤ n → 0 < cc n) {d1 d2 : ℕ} (hd1 : 1 ≤ d1) {F F' : ℕ → ℕ → ℝ} {c : ℝ}
    (h : ∀ ℓ a, ℓ + a ≤ N → d2 ≤ a → ℓ + d1 ≤ N → c * F ℓ a ≤ F' ℓ a) (i k : Idx N) :
    c * smv cc N d1 d2 F i k ≤ smv cc N d1 d2 F' i k := by
  unfold smv
  have hi1 := i.1.isLt
  split_ifs with hk
  · have hc := hcc (i.1 : ℕ) (by omega)
    rw [mul_div_assoc']
    exact div_le_div_of_nonneg_right (h _ _ hk.1 (by omega) (by omega)) hc.le
  · simp

theorem smv_congr {d1 d2 : ℕ} {F F' : ℕ → ℕ → ℝ}
    (h : ∀ ℓ a, ℓ + a ≤ N → d2 ≤ a → F ℓ a = F' ℓ a) : smv cc N d1 d2 F = smv cc N d1 d2 F' := by
  ext i k
  unfold smv
  split_ifs with hk
  · rw [h _ _ hk.1 (by omega)]
  · rfl

theorem smv_sub {d1 d2 : ℕ} (F F' : ℕ → ℕ → ℝ) :
    smv cc N d1 d2 (fun ℓ a => F ℓ a - F' ℓ a) = smv cc N d1 d2 F - smv cc N d1 d2 F' := by
  ext i k
  simp only [smv, Matrix.sub_apply]
  split_ifs <;> ring

theorem smv_lin3 {d1 d2 : ℕ} (F F' F'' : ℕ → ℕ → ℝ) (c : ℝ) (i k : Idx N) :
    smv cc N d1 d2 F i k + smv cc N d1 d2 F' i k + c * smv cc N d1 d2 F'' i k =
      smv cc N d1 d2 (fun ℓ a => F ℓ a + F' ℓ a + c * F'' ℓ a) i k := by
  simp only [smv]
  split_ifs <;> ring

/-- Composition of two moves: first `(d₁, -d₂)`, then `(d₁', -d₂')`. The intermediate point lies
in `Ω` when `d₁ ≤ d₂`. -/
theorem smv_mul {d1 d2 d1' d2' : ℕ} (hd : d1 ≤ d2) (F1 F2 : ℕ → ℕ → ℝ) :
    smv cc N d1' d2' F2 * smv cc N d1 d2 F1 =
      smv cc N (d1 + d1') (d2 + d2') (fun ℓ a => F1 ℓ a * F2 (ℓ + d1) (a - d2) / cc (ℓ + d1)) := by
  ext i k
  rw [Matrix.mul_apply]
  have hi1 := i.1.isLt; have hi2 := i.2.isLt; have hk1 := k.1.isLt; have hk2 := k.2.isLt
  by_cases hc : (k.1 : ℕ) + k.2 ≤ N ∧ (k.1 : ℕ) + (d1 + d1') = i.1 ∧ (k.2 : ℕ) = i.2 + (d2 + d2')
  · let m : Idx N := (⟨k.1 + d1, by omega⟩, ⟨k.2 - d2, by omega⟩)
    have hm1 : (m.1 : ℕ) = k.1 + d1 := rfl
    have hm2 : (m.2 : ℕ) = k.2 - d2 := rfl
    rw [sum_eq_single m]
    · unfold smv
      rw [if_pos ⟨by omega, by omega, by omega⟩, if_pos ⟨hc.1, by omega, by omega⟩, if_pos hc, hm1, hm2]
      ring
    · intro b _ hb
      unfold smv
      split_ifs with h1 h2
      · exfalso; apply hb
        ext
        · simp only [hm1]; omega
        · simp only [hm2]; omega
      all_goals simp
    · intro h; exact absurd (mem_univ m) h
  · unfold smv
    rw [if_neg hc]
    refine sum_eq_zero fun b _ => ?_
    split_ifs with h1 h2
    · exact absurd ⟨h2.1, by omega, by omega⟩ hc
    all_goals simp

theorem smv_mulVec {ω : ℕ → ℕ → ℝ} (hsupp : ∀ ℓ a, N < ℓ + a → ω ℓ a = 0) {d1 d2 : ℕ}
    (F : ℕ → ℕ → ℝ) (i : Idx N) :
    (smv cc N d1 d2 F *ᵥ fun k => ω k.1 k.2) i =
      if d1 ≤ (i.1 : ℕ) then F (i.1 - d1) (i.2 + d2) * ω (i.1 - d1) (i.2 + d2) / cc i.1 else 0 := by
  simp only [Matrix.mulVec, dotProduct]
  have hi1 := i.1.isLt; have hi2 := i.2.isLt
  by_cases hc : d1 ≤ (i.1 : ℕ) ∧ (i.1 : ℕ) - d1 + (i.2 + d2) ≤ N
  · let k0 : Idx N := (⟨i.1 - d1, by omega⟩, ⟨i.2 + d2, by omega⟩)
    have hk1 : (k0.1 : ℕ) = i.1 - d1 := rfl
    have hk2 : (k0.2 : ℕ) = i.2 + d2 := rfl
    rw [sum_eq_single k0, if_pos hc.1]
    · unfold smv
      rw [if_pos ⟨by omega, by omega, by omega⟩, hk1, hk2]
      ring
    · intro b _ hb
      unfold smv
      rw [if_neg, zero_mul]
      intro h; apply hb
      ext
      · simp only [hk1]; omega
      · simp only [hk2]; omega
    · intro h; exact absurd (mem_univ k0) h
  · have hz : ∀ b : Idx N, smv cc N d1 d2 F i b * ω b.1 b.2 = 0 := by
      intro b; unfold smv; rw [if_neg, zero_mul]; intro h; apply hc; omega
    rw [sum_eq_zero fun b _ => hz b]
    split_ifs with h
    · rw [hsupp _ _ (by omega)]; ring
    · rfl

theorem Raise.mulVec_zero {N : ℕ} {X : Matrix (Idx N) (Idx N) ℝ} (hX : Raise lvl 1 X) (v : Idx N → ℝ)
    {i : Idx N} (hi : (i.1 : ℕ) = 0) : (X *ᵥ v) i = 0 := by
  simp only [Matrix.mulVec, dotProduct]
  exact sum_eq_zero fun k _ => by rw [hX i k (by unfold lvl; omega), zero_mul]

/-- `Y ≤ P` and `Z ≥ 0` give `ZY ≤ ZP` and `YZ ≤ PZ` entrywise. -/
theorem mul_le_mul_left_MNN {ι : Type*} [Fintype ι] [DecidableEq ι] {Z Y P : Matrix ι ι ℝ} (hZ : MNN Z)
    (h : ∀ i k, Y i k ≤ P i k) (i k : ι) : (Z * Y) i k ≤ (Z * P) i k := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  exact sum_le_sum fun m _ => mul_le_mul_of_nonneg_left (h m k) (hZ i m)

theorem mul_le_mul_right_MNN {ι : Type*} [Fintype ι] [DecidableEq ι] {Z Y P : Matrix ι ι ℝ} (hZ : MNN Z)
    (h : ∀ i k, Y i k ≤ P i k) (i k : ι) : (Y * Z) i k ≤ (P * Z) i k := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  exact sum_le_sum fun m _ => mul_le_mul_of_nonneg_right (h i m) (hZ m k)

/-- A member of a sum of nonnegative matrices is below the sum. -/
theorem le_sum_MNN {ι α : Type*} [Fintype ι] [DecidableEq ι] {s : Finset α} {X : α → Matrix ι ι ℝ}
    (h : ∀ j ∈ s, MNN (X j)) {j0 : α} (hj0 : j0 ∈ s) (i k : ι) : X j0 i k ≤ (∑ j ∈ s, X j) i k := by
  rw [Matrix.sum_apply]
  exact single_le_sum (f := fun j => X j i k) (fun j hj => h j hj i k) hj0

/-- Detours of a family: if each move of `Jm` is dominated by the composition of `Y ≤ P` with the
move of index `j - 1` of `Jp`, then `4 Σ_{Jm} ≤ (Σ_{Jp}) P` entrywise. -/
theorem fam_detour {ι : Type*} [Fintype ι] [DecidableEq ι] {Jm Jp : Finset ℕ} (hsub : ∀ j ∈ Jm, 1 ≤ j ∧ j - 1 ∈ Jp)
    {Xm Xp : ℕ → Matrix ι ι ℝ} {Y P : Matrix ι ι ℝ}
    (hXp : ∀ j ∈ Jp, MNN (Xp j)) (hY : MNN Y) (hYP : ∀ i k, Y i k ≤ P i k)
    (hdet : ∀ j ∈ Jm, ∀ i k, 4 * Xm j i k ≤ (Xp (j - 1) * Y) i k) (i k : ι) :
    4 * (∑ j ∈ Jm, Xm j) i k ≤ ((∑ j ∈ Jp, Xp j) * P) i k := by
  have hinj : Set.InjOn (fun j => j - 1) (Jm : Set ℕ) := by
    intro x hx y hy hxy
    have := (hsub x hx).1; have := (hsub y hy).1
    simp only at hxy; omega
  calc 4 * (∑ j ∈ Jm, Xm j) i k = ∑ j ∈ Jm, 4 * Xm j i k := by rw [Matrix.sum_apply, mul_sum]
    _ ≤ ∑ j ∈ Jm, (Xp (j - 1) * Y) i k := sum_le_sum fun j hj => hdet j hj i k
    _ = ∑ j' ∈ Jm.image (fun j => j - 1), (Xp j' * Y) i k :=
        (sum_image (f := fun j' => (Xp j' * Y) i k) (fun x hx y hy h => hinj hx hy h)).symm
    _ ≤ ∑ j' ∈ Jp, (Xp j' * Y) i k := by
        refine sum_le_sum_of_subset_of_nonneg ?_ fun j hj _ => (hXp j hj).mul hY i k
        intro j' hj'
        obtain ⟨j, hj, rfl⟩ := mem_image.mp hj'
        exact (hsub j hj).2
    _ = ((∑ j ∈ Jp, Xp j) * Y) i k := by rw [Finset.sum_mul, Matrix.sum_apply]
    _ ≤ ((∑ j ∈ Jp, Xp j) * P) i k := mul_le_mul_left_MNN (MNN.sum hXp) hYP i k

/-- One detour step for `smv` moves: `(dp₁, -dp₂)` after the `B₀`-move `(1, -2)`. -/
theorem smv_detour (hcc : ∀ n, 1 ≤ n → 0 < cc n) {dm1 dm2 dp1 dp2 : ℕ} (h1 : 1 + dp1 = dm1)
    (h2 : 2 + dp2 = dm2) {Fm Fp B0 : ℕ → ℕ → ℝ}
    (hw : ∀ ℓ a, ℓ + a ≤ N → dm2 ≤ a → ℓ + dm1 ≤ N →
      4 * cc (ℓ + 1) * Fm ℓ a ≤ B0 ℓ a * Fp (ℓ + 1) (a - 2)) (i k : Idx N) :
    4 * smv cc N dm1 dm2 Fm i k ≤ (smv cc N dp1 dp2 Fp * smv cc N 1 2 B0) i k := by
  rw [smv_mul (by norm_num : 1 ≤ 2), h1, h2]
  refine smv_le_c hcc (by omega) (fun ℓ a hla ha hl => ?_) i k
  have hc := hcc (ℓ + 1) (by omega)
  rw [le_div_iff₀ hc]
  have := hw ℓ a hla ha hl
  linarith

/-! ### The generic recurrence as a matrix equation -/

variable (cc N)
variable (A B C : ℕ → ℕ → ℕ → ℝ) (s : ℕ → ℕ → ℝ)

/-- The move operator of the generic recurrence. -/
noncomputable def Tmat : Matrix (Idx N) (Idx N) ℝ :=
  smv cc N 1 0 s + ∑ j ∈ range (N + 1), (-1 : ℝ) ^ j •
    (smv cc N (j + 1) (2 * j + 1) (A j) + smv cc N (j + 1) (2 * j + 2) (B j) +
      smv cc N (j + 2) (2 * j + 2) (C j))

variable {cc N A B C s}

theorem Tmat_rec {ω : ℕ → ℕ → ℝ} (hcc : ∀ n, 1 ≤ n → 0 < cc n) (hrec : GenRec cc A B C s ω)
    (hsupp : ∀ ℓ a, N < ℓ + a → ω ℓ a = 0) (i : Idx N) (hi : 1 ≤ (i.1 : ℕ)) :
    (Tmat cc N A B C s *ᵥ fun k => ω k.1 k.2) i = ω i.1 i.2 := by
  obtain ⟨⟨l, hl⟩, ⟨a, ha⟩⟩ := i
  simp only at hi ⊢
  obtain ⟨ℓ, rfl⟩ : ∃ ℓ, l = ℓ + 1 := ⟨l - 1, by omega⟩
  have hc := hcc (ℓ + 1) (by omega)
  unfold Tmat
  rw [Matrix.add_mulVec, Matrix.sum_mulVec, Pi.add_apply, Finset.sum_apply]
  simp only [Matrix.smul_mulVec, Matrix.add_mulVec, Pi.smul_apply, Pi.add_apply, smul_eq_mul,
    smv_mulVec hsupp]
  simp only [if_pos (show 1 ≤ ℓ + 1 by omega), show ℓ + 1 - 1 = ℓ by omega, add_zero]
  have hsum : ∑ j ∈ range (N + 1), (-1 : ℝ) ^ j *
      ((if j + 1 ≤ ℓ + 1 then A j (ℓ + 1 - (j + 1)) (a + (2 * j + 1)) * ω (ℓ + 1 - (j + 1)) (a + (2 * j + 1)) / cc (ℓ + 1) else 0) +
       (if j + 1 ≤ ℓ + 1 then B j (ℓ + 1 - (j + 1)) (a + (2 * j + 2)) * ω (ℓ + 1 - (j + 1)) (a + (2 * j + 2)) / cc (ℓ + 1) else 0) +
       (if j + 2 ≤ ℓ + 1 then C j (ℓ + 1 - (j + 2)) (a + (2 * j + 2)) * ω (ℓ + 1 - (j + 2)) (a + (2 * j + 2)) / cc (ℓ + 1) else 0)) =
      (∑ j ∈ range (ℓ + 1), (-1 : ℝ) ^ j * ggrp A B C ω j ℓ a) / cc (ℓ + 1) := by
    rw [sum_div]
    refine ((sum_subset (range_subset_range.mpr (show ℓ + 1 ≤ N + 1 by omega))
      (fun j hj hj' => ?_)).symm).trans ?_
    · rw [mem_range] at hj'
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]; ring
    · refine sum_congr rfl fun j hj => ?_
      rw [mem_range] at hj
      rw [if_pos (by omega), if_pos (by omega)]
      have e1 : ℓ + 1 - (j + 1) = ℓ - j := by omega
      have e2 : a + (2 * j + 1) = a + 2 * j + 1 := by ring
      have e3 : a + (2 * j + 2) = a + 2 * j + 2 := by ring
      unfold ggrp gmA gmB gmC
      rw [e1, e2, e3]
      by_cases hj2 : j < ℓ
      · rw [if_pos (by omega), if_pos hj2, show ℓ + 1 - (j + 2) = ℓ - j - 1 by omega]; ring
      · rw [if_neg (by omega), if_neg hj2]; ring
  rw [hsum, ← add_div, ← hrec ℓ a, mul_div_cancel_left₀ _ hc.ne']

/-! ### The operator inequalities and the induction -/

/-- Hypotheses of the resummation, on `Ω = {ℓ + a ≤ N}`: the `A`-weights of positive index split
as `H - V`; the weights `A₀, B, C, H, V` and the straight weight `s` are nonnegative; the
`B`, `C`, `H` and `V` moves are dominated by detours through `B₀`; and the key inequality
controls `H₁`. -/
structure ResumWeights (cc : ℕ → ℝ) (A B C H V : ℕ → ℕ → ℕ → ℝ) (s : ℕ → ℕ → ℝ) (N : ℕ) : Prop where
  cc_pos : ∀ n, 1 ≤ n → 0 < cc n
  split : ∀ j ℓ a, 1 ≤ j → ℓ + a ≤ N → A j ℓ a = H j ℓ a - V j ℓ a
  A0_nn : ∀ ℓ a, ℓ + a ≤ N → 0 ≤ A 0 ℓ a
  B_nn : ∀ j ℓ a, ℓ + a ≤ N → 0 ≤ B j ℓ a
  C_nn : ∀ j ℓ a, ℓ + a ≤ N → 0 ≤ C j ℓ a
  H_nn : ∀ j ℓ a, ℓ + a ≤ N → 0 ≤ H j ℓ a
  V_nn : ∀ j ℓ a, ℓ + a ≤ N → 0 ≤ V j ℓ a
  s_nn : ∀ ℓ a, ℓ + a ≤ N → 0 ≤ s ℓ a
  domB : ∀ j ℓ a, 1 ≤ j → ℓ + a ≤ N → 4 * cc (ℓ + 1) * B j ℓ a ≤ B 0 ℓ a * B (j - 1) (ℓ + 1) (a - 2)
  domC : ∀ j ℓ a, 1 ≤ j → ℓ + a ≤ N → 4 * cc (ℓ + 1) * C j ℓ a ≤ B 0 ℓ a * C (j - 1) (ℓ + 1) (a - 2)
  domH : ∀ j ℓ a, 2 ≤ j → ℓ + a ≤ N → 4 * cc (ℓ + 1) * H j ℓ a ≤ B 0 ℓ a * H (j - 1) (ℓ + 1) (a - 2)
  domV : ∀ j ℓ a, 2 ≤ j → ℓ + a ≤ N → 4 * cc (ℓ + 1) * V j ℓ a ≤ B 0 ℓ a * V (j - 1) (ℓ + 1) (a - 2)
  key : ∀ ℓ a, ℓ + a ≤ N → 3 ≤ a → 4 * cc (ℓ + 1) * H 1 ℓ a ≤
    A 0 ℓ a * B 0 (ℓ + 1) (a - 1) + B 0 ℓ a * A 0 (ℓ + 1) (a - 2) + 2 * cc (ℓ + 1) * V 1 ℓ a

theorem sign_split {M : Type*} [AddCommGroup M] [Module ℝ M] (R : Finset ℕ) (X : ℕ → M) :
    ∑ j ∈ R, (-1 : ℝ) ^ j • X j = ∑ j ∈ R.filter Even, X j - ∑ j ∈ R.filter Odd, X j := by
  rw [← sum_filter_add_sum_filter_not R Even]
  have h1 : ∑ j ∈ R.filter Even, (-1 : ℝ) ^ j • X j = ∑ j ∈ R.filter Even, X j :=
    sum_congr rfl fun j hj => by rw [(mem_filter.mp hj).2.neg_one_pow, one_smul]
  have h2 : ∑ j ∈ R.filter (fun j => ¬ Even j), (-1 : ℝ) ^ j • X j = -∑ j ∈ R.filter Odd, X j := by
    rw [← sum_neg_distrib]
    have : R.filter (fun j => ¬ Even j) = R.filter Odd := by ext j; simp [Nat.not_even_iff_odd]
    rw [this]
    exact sum_congr rfl fun j hj => by rw [(mem_filter.mp hj).2.neg_one_pow, neg_one_smul]
  rw [h1, h2, sub_eq_add_neg]

/-- **Resummation induction.** Every solution of the generic kernel recurrence with nonnegative
initial values and the support property is nonnegative under `ResumWeights`. -/
theorem gkernel_resum {H V : ℕ → ℕ → ℕ → ℝ} {ω : ℕ → ℕ → ℝ} (hN : 1 ≤ N)
    (hw : ResumWeights cc A B C H V s N) (hrec : GenRec cc A B C s ω)
    (h0 : ∀ a, 0 ≤ ω 0 a) (hsupp : ∀ ℓ a, N < ℓ + a → ω ℓ a = 0) : ∀ ℓ a, 0 ≤ ω ℓ a := by
  have hcc := hw.cc_pos
  set R := range (N + 1) with hR
  -- the move families
  set fA : ℕ → Matrix (Idx N) (Idx N) ℝ := fun j => smv cc N (j + 1) (2 * j + 1) (A j) with hfA
  set fB : ℕ → Matrix (Idx N) (Idx N) ℝ := fun j => smv cc N (j + 1) (2 * j + 2) (B j) with hfB
  set fC : ℕ → Matrix (Idx N) (Idx N) ℝ := fun j => smv cc N (j + 2) (2 * j + 2) (C j) with hfC
  set fH : ℕ → Matrix (Idx N) (Idx N) ℝ := fun j => smv cc N (j + 1) (2 * j + 1) (H j) with hfH
  set fV : ℕ → Matrix (Idx N) (Idx N) ℝ := fun j => smv cc N (j + 1) (2 * j + 1) (V j) with hfV
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
  have h0R : 0 ∈ R := mem_range.mpr (by omega)
  have h1R : 1 ∈ R := mem_range.mpr (by omega)
  -- nonnegativity and raising
  have nB : ∀ j, MNN (fB j) := fun j => smv_nonneg hcc (by omega) (fun ℓ a h => hw.B_nn j ℓ a h)
  have nC : ∀ j, MNN (fC j) := fun j => smv_nonneg hcc (by omega) (fun ℓ a h => hw.C_nn j ℓ a h)
  have nH : ∀ j, MNN (fH j) := fun j => smv_nonneg hcc (by omega) (fun ℓ a h => hw.H_nn j ℓ a h)
  have nV : ∀ j, MNN (fV j) := fun j => smv_nonneg hcc (by omega) (fun ℓ a h => hw.V_nn j ℓ a h)
  have nU : MNN U := smv_nonneg hcc le_rfl hw.s_nn
  have nA0 : MNN A0 := smv_nonneg hcc (by omega) hw.A0_nn
  have nP : MNN P := MNN.sum fun j _ => nB j
  have rf : ∀ (d1 d2 : ℕ → ℕ) (W : ℕ → ℕ → ℕ → ℝ) (J : Finset ℕ), (∀ j, 1 ≤ d1 j) →
      Raise lvl 1 (∑ j ∈ J, smv cc N (d1 j) (d2 j) (W j)) :=
    fun d1 d2 W J hd => Raise.sum fun j _ => smv_raise (hd j) _
  -- the matrix equation
  have hdecomp : Tmat cc N A B C s = U + P - Q + Cp - Cm + A0 + Hp - Hm - H1 + Vp - Vm := by
    have hAsplit : ∀ j, 1 ≤ j → fA j = fH j - fV j := fun j hj => by
      simp only [hfA, hfH, hfV]
      rw [← smv_sub]
      exact smv_congr fun ℓ a hla _ => hw.split j ℓ a hj hla
    unfold Tmat
    simp only [smul_add, sum_add_distrib]
    rw [sign_split, sign_split, sign_split]
    -- the `A`-family
    have hEvenA : ∑ j ∈ R.filter Even, fA j = A0 + Hp - Vm := by
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
      rw [hs, sum_insert (by simp), hA0, hHp, hVm, add_sub_assoc, ← sum_sub_distrib]
      congr 1
      exact sum_congr rfl fun j hj => hAsplit j (by have := (mem_filter.mp hj).2.2; omega)
    have hOddA : ∑ j ∈ R.filter Odd, fA j = H1 + Hm - Vp := by
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
      have hsum : ∑ j ∈ R.filter Odd, fA j = ∑ j ∈ R.filter Odd, fH j - Vp := by
        rw [hVp, ← sum_sub_distrib]
        exact sum_congr rfl fun j hj => hAsplit j (by obtain ⟨k, rfl⟩ := (mem_filter.mp hj).2; omega)
      rw [hsum, hs, sum_insert (by simp), hH1, hHm]
    rw [hEvenA, hOddA]
    abel
  set ωv : Idx N → ℝ := fun k => ω k.1 k.2 with hωv
  set β : Idx N → ℝ := fun i => if (i.1 : ℕ) = 0 then ω i.1 i.2 else 0 with hβ
  have rT : Raise lvl 1 (U + P - Q + Cp - Cm + A0 + Hp - Hm - H1 + Vp - Vm) := by
    have rU : Raise lvl 1 U := smv_raise le_rfl _
    have rA0 : Raise lvl 1 A0 := smv_raise (by omega) _
    have rH1 : Raise lvl 1 H1 := smv_raise (by omega) _
    exact (((((((((rU.add (rf _ _ _ _ fun j => by omega)).sub (rf _ _ _ _ fun j => by omega)).add
      (rf _ _ _ _ fun j => by omega)).sub (rf _ _ _ _ fun j => by omega)).add rA0).add
      (rf _ _ _ _ fun j => by omega)).sub (rf _ _ _ _ fun j => by omega)).sub rH1).add
      (rf _ _ _ _ fun j => by omega)).sub (rf _ _ _ _ fun j => by omega)
  have heq : ωv = β + (U + P - Q + Cp - Cm + A0 + Hp - Hm - H1 + Vp - Vm) *ᵥ ωv := by
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
      rw [hV1', hH1', smv_lin3]
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
  have hnn := resum_nonneg (lev := lvl) N (fun i => by unfold lvl; have := i.1.isLt; omega)
    nU nP (MNN.sum fun j _ => nC j) nA0 (MNN.sum fun j _ => nH j) (MNN.sum fun j _ => nV j)
    (smv_raise le_rfl _) (rf _ _ _ _ fun j => by omega) (rf _ _ _ _ fun j => by omega)
    (rf _ _ _ _ fun j => by omega) (rf _ _ _ _ fun j => by omega) (smv_raise (by omega) _)
    (rf _ _ _ _ fun j => by omega) (rf _ _ _ _ fun j => by omega) (smv_raise (by omega) _)
    (rf _ _ _ _ fun j => by omega) (rf _ _ _ _ fun j => by omega)
    dQ dH dV dC dV1 dkey (β := β) (fun i => by
      simp only [hβ]; split_ifs with h
      · have := h0 i.2; rw [← h] at this; exact this
      · exact le_rfl) heq
  intro ℓ a
  by_cases h : ℓ + a ≤ N
  · have := hnn (⟨ℓ, by omega⟩, ⟨a, by omega⟩)
    simpa [hωv] using this
  · rw [hsupp ℓ a (by omega)]

end Moves

end Szkraw
