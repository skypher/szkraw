import Szkraw.LCDetours
import Mathlib.Algebra.BigOperators.Intervals

/-!
# The operator induction of Theorem 8.1 (F7)

Any `ω` satisfying the kernel recurrence (8.1) with nonnegative initial values and the support
property is nonnegative. Moves into the node `(ℓ+1, a)` (equation at level `ℓ`):
`A`-moves from `(ℓ-j, a+2j+1)` (weight `t * A_j`), `B`-moves from `(ℓ-j, a+2j+2)` (weight `B_j`),
`C`-moves from `(ℓ-j-1, a+2j+2)` (weight `C_j`), with sign `(-1)^j`.
-/

namespace Szkraw

open Finset

variable (u : ℕ → ℝ) (t : ℝ) (ω : ℕ → ℕ → ℝ)

/-- profile value `d ℓ = f_0(ℓ)` -/
noncomputable def dd (ℓ : ℕ) : ℝ := Szkraw.iterShift u ℓ 0

noncomputable def moveA (j ℓ a : ℕ) : ℝ := t * Wt u (2 * j + 1) j (ℓ - j) (a + 2 * j + 1) * ω (ℓ - j) (a + 2 * j + 1)
noncomputable def moveB (j ℓ a : ℕ) : ℝ := Wt u (2 * j + 2) j (ℓ - j) (a + 2 * j + 2) * ω (ℓ - j) (a + 2 * j + 2)
noncomputable def moveC (j ℓ a : ℕ) : ℝ :=
  if j < ℓ then Wt u (2 * j + 2) (j + 1) (ℓ - j - 1) (a + 2 * j + 2) * ω (ℓ - j - 1) (a + 2 * j + 2) else 0

/-- all moves of index `j` into `(ℓ+1, a)` -/
noncomputable def grp (j ℓ a : ℕ) : ℝ := moveA u t ω j ℓ a + moveB u ω j ℓ a + moveC u ω j ℓ a

/-- even-index inflow `P` and odd-index inflow `Q` into `(ℓ+1, a)` -/
noncomputable def Pin (ℓ a : ℕ) : ℝ := ∑ j ∈ (range (ℓ + 1)).filter Even, grp u t ω j ℓ a
noncomputable def Qin (ℓ a : ℕ) : ℝ := ∑ j ∈ (range (ℓ + 1)).filter Odd, grp u t ω j ℓ a

/-- The kernel recurrence (8.1). -/
def KernelRec (T : ℝ) : Prop :=
  ∀ ℓ a, dd u (ℓ + 1) * ω (ℓ + 1) a =
    (T - dd u (ℓ + a)) * ω ℓ a + ∑ j ∈ range (ℓ + 1), (-1 : ℝ) ^ j * grp u t ω j ℓ a

theorem dd_pos {u : ℕ → ℝ} (hu : LCNZ u) (hu1 : 0 < u 1) {n : ℕ} (hn : 1 ≤ n) : 0 < dd u n := by
  unfold dd
  rw [iterShift_eq]
  have hmem : 1 ∈ range (n + 1) := mem_range.mpr (by omega)
  have := single_le_sum (f := fun h => (n.choose h : ℝ) * u (0 + h))
    (fun i _ => mul_nonneg (Nat.cast_nonneg _) (hu.1 _)) hmem
  have h1 : (0 : ℝ) < (n.choose 1 : ℝ) * u (0 + 1) := by
    rw [Nat.choose_one_right]; simp only [zero_add]; exact mul_pos (by exact_mod_cast hn) hu1
  linarith

theorem sign_split (ℓ a : ℕ) :
    ∑ j ∈ range (ℓ + 1), (-1 : ℝ) ^ j * grp u t ω j ℓ a = Pin u t ω ℓ a - Qin u t ω ℓ a := by
  unfold Pin Qin
  rw [← sum_filter_add_sum_filter_not (range (ℓ + 1)) Even]
  have h1 : ∑ j ∈ (range (ℓ + 1)).filter Even, (-1 : ℝ) ^ j * grp u t ω j ℓ a =
      ∑ j ∈ (range (ℓ + 1)).filter Even, grp u t ω j ℓ a := by
    refine sum_congr rfl (fun j hj => ?_)
    rw [(mem_filter.mp hj).2.neg_one_pow, one_mul]
  have h2 : ∑ j ∈ (range (ℓ + 1)).filter (fun j => ¬ Even j), (-1 : ℝ) ^ j * grp u t ω j ℓ a =
      -∑ j ∈ (range (ℓ + 1)).filter Odd, grp u t ω j ℓ a := by
    rw [← sum_neg_distrib]
    have : (range (ℓ + 1)).filter (fun j => ¬ Even j) = (range (ℓ + 1)).filter Odd := by
      ext j; simp [Nat.not_even_iff_odd]
    rw [this]
    refine sum_congr rfl (fun j hj => ?_)
    rw [(mem_filter.mp hj).2.neg_one_pow]; ring
  rw [h1, h2]; ring

variable {u t ω}

theorem grp_nonneg (hu : LCNZ u) (ht : 0 ≤ t) {ℓ : ℕ} (hnn : ∀ ℓ' ≤ ℓ, ∀ a', 0 ≤ ω ℓ' a') (j a : ℕ) :
    0 ≤ grp u t ω j ℓ a := by
  unfold grp moveA moveB moveC
  refine add_nonneg (add_nonneg ?_ ?_) ?_
  · exact mul_nonneg (mul_nonneg ht (Wt_nonneg hu _ _ _ _)) (hnn _ (by omega) _)
  · exact mul_nonneg (Wt_nonneg hu _ _ _ _) (hnn _ (by omega) _)
  · split_ifs
    · exact mul_nonneg (Wt_nonneg hu _ _ _ _) (hnn _ (by omega) _)
    · exact le_rfl

theorem Pin_ge_grp0 (hu : LCNZ u) (ht : 0 ≤ t) {ℓ : ℕ} (hnn : ∀ ℓ' ≤ ℓ, ∀ a', 0 ≤ ω ℓ' a') (a : ℕ) :
    grp u t ω 0 ℓ a ≤ Pin u t ω ℓ a := by
  unfold Pin
  have hmem : 0 ∈ (range (ℓ + 1)).filter Even := mem_filter.mpr ⟨mem_range.mpr (by omega), ⟨0, rfl⟩⟩
  exact single_le_sum (fun j _ => grp_nonneg hu ht hnn j a) hmem

/-- Domination of one odd group by the preceding even group: `2 grp_j ≤ grp_{j-1}`. -/
theorem odd_dom (hu : LCNZ u) (hu1 : 0 < u 1) (ht : 0 ≤ t) {ℓ : ℕ}
    (hnn : ∀ ℓ' ≤ ℓ, ∀ a', 0 ≤ ω ℓ' a')
    (hP : ∀ ℓ' < ℓ, ∀ a', (1 / 2 : ℝ) * Pin u t ω ℓ' a' ≤ dd u (ℓ' + 1) * ω (ℓ' + 1) a')
    {j : ℕ} (hj1 : 1 ≤ j) (hjl : j ≤ ℓ) (a : ℕ) :
    2 * grp u t ω j ℓ a ≤ grp u t ω (j - 1) ℓ a := by
  obtain ⟨L, rfl⟩ : ∃ L, ℓ = L + j := ⟨ℓ - j, by omega⟩
  -- named quantities
  set ωx := ω L (a + 2 * j + 1)
  set ωx' := ω L (a + 2 * j + 2)
  set ωz1 := ω (L + 1) (a + 2 * j)
  set ωz2 := ω (L + 1) (a + 2 * j - 1)
  set A0 := Wt u 1 0 L (a + 2 * j + 1)
  set B0x := Wt u 2 0 L (a + 2 * j + 1)
  set B0x' := Wt u 2 0 L (a + 2 * j + 2)
  set Aj := Wt u (2 * j + 1) j L (a + 2 * j + 1)
  set Bj := Wt u (2 * j + 2) j L (a + 2 * j + 2)
  set Bm := Wt u (2 * j) (j - 1) (L + 1) (a + 2 * j)
  set Am := Wt u (2 * j - 1) (j - 1) (L + 1) (a + 2 * j - 1)
  set D1 := dd u (L + 1)
  have hD1 : 0 < D1 := dd_pos hu hu1 (by omega)
  have hωx : 0 ≤ ωx := hnn _ (by omega) _
  have hωx' : 0 ≤ ωx' := hnn _ (by omega) _
  have hωz1 : 0 ≤ ωz1 := hnn _ (by omega) _
  have hωz2 : 0 ≤ ωz2 := hnn _ (by omega) _
  -- the even group j-1 and the odd group j, written out
  have hgm : grp u t ω (j - 1) (L + j) a =
      t * Am * ωz2 + Bm * ωz1 + moveC u ω (j - 1) (L + j) a := by
    unfold grp moveA moveB
    have e1 : 2 * (j - 1) + 1 = 2 * j - 1 := by omega
    have e2 : L + j - (j - 1) = L + 1 := by omega
    have e3 : a + 2 * (j - 1) + 1 = a + 2 * j - 1 := by omega
    have e4 : 2 * (j - 1) + 2 = 2 * j := by omega
    have e5 : a + 2 * (j - 1) + 2 = a + 2 * j := by omega
    rw [e1, e2, e3, e4, e5]
  have hgj : grp u t ω j (L + j) a = t * Aj * ωx + Bj * ωx' + moveC u ω j (L + j) a := by
    unfold grp moveA moveB
    have e2 : L + j - j = L := by omega
    rw [e2]
  -- induction hypothesis at z1 = (L+1, a+2j) and z2 = (L+1, a+2j-1)
  have f1 : (1 / 2 : ℝ) * (t * A0 * ωx + B0x' * ωx') ≤ D1 * ωz1 := by
    have h := hP L (by omega) (a + 2 * j)
    have g := Pin_ge_grp0 hu ht (ℓ := L) (fun ℓ' h a' => hnn ℓ' (by omega) a') (a + 2 * j)
    have hg0 : grp u t ω 0 L (a + 2 * j) = t * A0 * ωx + B0x' * ωx' + moveC u ω 0 L (a + 2 * j) := by
      unfold grp moveA moveB; simp only [Nat.sub_zero, mul_zero, zero_add, add_zero]; rfl
    have hc0 : 0 ≤ moveC u ω 0 L (a + 2 * j) := by
      unfold moveC; split_ifs
      · exact mul_nonneg (Wt_nonneg hu _ _ _ _) (hnn _ (by omega) _)
      · exact le_rfl
    linarith
  have f2 : (1 / 2 : ℝ) * (B0x * ωx) ≤ D1 * ωz2 := by
    have h := hP L (by omega) (a + 2 * j - 1)
    have g := Pin_ge_grp0 hu ht (ℓ := L) (fun ℓ' h a' => hnn ℓ' (by omega) a') (a + 2 * j - 1)
    have hB : moveB u ω 0 L (a + 2 * j - 1) = B0x * ωx := by
      unfold moveB
      have e : a + 2 * j - 1 + 2 = a + 2 * j + 1 := by omega
      simp only [Nat.sub_zero, mul_zero, add_zero]; rw [e]
    have hA0 : 0 ≤ moveA u t ω 0 L (a + 2 * j - 1) := by
      unfold moveA; exact mul_nonneg (mul_nonneg ht (Wt_nonneg hu _ _ _ _)) (hnn _ (by omega) _)
    have hc0 : 0 ≤ moveC u ω 0 L (a + 2 * j - 1) := by
      unfold moveC; split_ifs
      · exact mul_nonneg (Wt_nonneg hu _ _ _ _) (hnn _ (by omega) _)
      · exact le_rfl
    unfold grp at g
    linarith
  -- Lemma 8.4, A and B families, at x = (L, a+2j+1) and x' = (L, a+2j+2)
  have g1 : 4 * D1 * Aj ≤ A0 * Bm + B0x * Am := by
    have h := lemma_8_4_A hu j L (a + 2 * j + 1) hj1
    have e1 : a + 2 * j + 1 - 1 = a + 2 * j := by omega
    have e2 : a + 2 * j + 1 - 2 = a + 2 * j - 1 := by omega
    rw [e1, e2] at h; exact h
  have g2 : 4 * D1 * Bj ≤ B0x' * Bm := by
    have h := lemma_8_4_B hu j L (a + 2 * j + 2) hj1
    have e1 : a + 2 * j + 2 - 2 = a + 2 * j := by omega
    rw [e1] at h; exact h
  have hAm := Wt_nonneg hu (2 * j - 1) (j - 1) (L + 1) (a + 2 * j - 1)
  have hBm := Wt_nonneg hu (2 * j) (j - 1) (L + 1) (a + 2 * j)
  -- A/B part: 2 (t Aj ωx + Bj ωx') ≤ t Am ωz2 + Bm ωz1
  have pAB : 2 * (t * Aj * ωx + Bj * ωx') ≤ t * Am * ωz2 + Bm * ωz1 := by
    have k1 := mul_le_mul_of_nonneg_left f2 (mul_nonneg ht hAm)
    have k2 := mul_le_mul_of_nonneg_left f1 hBm
    have k3 := mul_le_mul_of_nonneg_right g1 (mul_nonneg ht hωx)
    have k4 := mul_le_mul_of_nonneg_right g2 hωx'
    have : D1 * (2 * (t * Aj * ωx + Bj * ωx')) ≤ D1 * (t * Am * ωz2 + Bm * ωz1) := by nlinarith
    exact le_of_mul_le_mul_left this hD1
  -- C part
  have pC : 2 * moveC u ω j (L + j) a ≤ moveC u ω (j - 1) (L + j) a := by
    unfold moveC
    by_cases hL : j < L + j
    · rw [if_pos hL, if_pos (by omega)]
      have e1 : L + j - j - 1 = L - 1 := by omega
      have e2 : 2 * (j - 1) + 2 = 2 * j := by omega
      have e3 : j - 1 + 1 = j := by omega
      have e4 : L + j - (j - 1) - 1 = L := by omega
      have e5 : a + 2 * (j - 1) + 2 = a + 2 * j := by omega
      rw [e1, e2, e3, e4, e5]
      have hL1 : 1 ≤ L := by omega
      set D0 := dd u L
      have hD0 : 0 < D0 := dd_pos hu hu1 hL1
      have f3 : (1 / 2 : ℝ) * (Wt u 2 0 (L - 1) (a + 2 * j + 2) * ω (L - 1) (a + 2 * j + 2)) ≤ D0 * ω L (a + 2 * j) := by
        have h := hP (L - 1) (by omega) (a + 2 * j)
        have e6 : L - 1 + 1 = L := by omega
        rw [e6] at h
        have g := Pin_ge_grp0 hu ht (ℓ := L - 1) (fun ℓ' h a' => hnn ℓ' (by omega) a') (a + 2 * j)
        have hB : moveB u ω 0 (L - 1) (a + 2 * j) = Wt u 2 0 (L - 1) (a + 2 * j + 2) * ω (L - 1) (a + 2 * j + 2) := by
          unfold moveB; simp only [Nat.sub_zero, mul_zero, zero_add, add_zero]
        have hA0 : 0 ≤ moveA u t ω 0 (L - 1) (a + 2 * j) := by
          unfold moveA; exact mul_nonneg (mul_nonneg ht (Wt_nonneg hu _ _ _ _)) (hnn _ (by omega) _)
        have hc0 : 0 ≤ moveC u ω 0 (L - 1) (a + 2 * j) := by
          unfold moveC; split_ifs
          · exact mul_nonneg (Wt_nonneg hu _ _ _ _) (hnn _ (by omega) _)
          · exact le_rfl
        unfold grp at g
        linarith
      have g3 : 4 * D0 * Wt u (2 * j + 2) (j + 1) (L - 1) (a + 2 * j + 2) ≤
          Wt u 2 0 (L - 1) (a + 2 * j + 2) * Wt u (2 * j) j L (a + 2 * j) := by
        have h := lemma_8_4_C hu j (L - 1) (a + 2 * j + 2) hj1
        have e6 : L - 1 + 1 = L := by omega
        have e7 : a + 2 * j + 2 - 2 = a + 2 * j := by omega
        rw [e6, e7] at h; exact h
      have hCm := Wt_nonneg hu (2 * j) j L (a + 2 * j)
      have hωx'' : 0 ≤ ω (L - 1) (a + 2 * j + 2) := hnn _ (by omega) _
      have k1 := mul_le_mul_of_nonneg_left f3 hCm
      have k2 := mul_le_mul_of_nonneg_right g3 hωx''
      have : D0 * (2 * (Wt u (2 * j + 2) (j + 1) (L - 1) (a + 2 * j + 2) * ω (L - 1) (a + 2 * j + 2))) ≤
          D0 * (Wt u (2 * j) j L (a + 2 * j) * ω L (a + 2 * j)) := by nlinarith
      exact le_of_mul_le_mul_left this hD0
    · rw [if_neg hL]
      have : 0 ≤ (if j - 1 < L + j then Wt u (2 * (j - 1) + 2) (j - 1 + 1) (L + j - (j - 1) - 1) (a + 2 * (j - 1) + 2) *
          ω (L + j - (j - 1) - 1) (a + 2 * (j - 1) + 2) else 0) := by
        split_ifs
        · exact mul_nonneg (Wt_nonneg hu _ _ _ _) (hnn _ (by omega) _)
        · exact le_rfl
      linarith
  rw [hgm, hgj]
  linarith

theorem Qin_le_half_Pin (hu : LCNZ u) (hu1 : 0 < u 1) (ht : 0 ≤ t) {ℓ : ℕ}
    (hnn : ∀ ℓ' ≤ ℓ, ∀ a', 0 ≤ ω ℓ' a')
    (hP : ∀ ℓ' < ℓ, ∀ a', (1 / 2 : ℝ) * Pin u t ω ℓ' a' ≤ dd u (ℓ' + 1) * ω (ℓ' + 1) a') (a : ℕ) :
    Qin u t ω ℓ a ≤ (1 / 2 : ℝ) * Pin u t ω ℓ a := by
  unfold Qin Pin
  set Od := (range (ℓ + 1)).filter Odd
  set Ev := (range (ℓ + 1)).filter Even
  have step1 : ∑ j ∈ Od, grp u t ω j ℓ a ≤ ∑ j ∈ Od, (1 / 2 : ℝ) * grp u t ω (j - 1) ℓ a := by
    refine sum_le_sum (fun j hj => ?_)
    obtain ⟨hjr, hjo⟩ := mem_filter.mp hj
    have hj1 : 1 ≤ j := by obtain ⟨k, rfl⟩ := hjo; omega
    have := odd_dom hu hu1 ht hnn hP hj1 (by have := mem_range.mp hjr; omega) a
    linarith
  have hinj : Set.InjOn (fun j => j - 1) (Od : Set ℕ) := by
    intro x hx y hy hxy
    have hx1 : 1 ≤ x := by obtain ⟨k, rfl⟩ := (mem_filter.mp hx).2; omega
    have hy1 : 1 ≤ y := by obtain ⟨k, rfl⟩ := (mem_filter.mp hy).2; omega
    simp only at hxy; omega
  have step2 : ∑ j ∈ Od, grp u t ω (j - 1) ℓ a = ∑ j' ∈ Od.image (fun j => j - 1), grp u t ω j' ℓ a :=
    (sum_image (f := fun j' => grp u t ω j' ℓ a) (fun x hx y hy h => hinj hx hy h)).symm
  have hsub : Od.image (fun j => j - 1) ⊆ Ev := by
    intro j' hj'
    obtain ⟨j, hj, rfl⟩ := mem_image.mp hj'
    obtain ⟨hjr, hjo⟩ := mem_filter.mp hj
    refine mem_filter.mpr ⟨mem_range.mpr (by have := mem_range.mp hjr; omega), ?_⟩
    obtain ⟨k, rfl⟩ := hjo; exact ⟨k, by omega⟩
  have step3 : ∑ j' ∈ Od.image (fun j => j - 1), grp u t ω j' ℓ a ≤ ∑ j' ∈ Ev, grp u t ω j' ℓ a :=
    sum_le_sum_of_subset_of_nonneg hsub (fun j _ _ => grp_nonneg hu ht hnn j a)
  rw [← mul_sum] at step1
  linarith

/-- F7: every solution of the kernel recurrence (8.1) with nonnegative initial values and the
support property is nonnegative. -/
theorem kernel_nonneg (hu : LCNZ u) (hu1 : 0 < u 1) (ht : 0 ≤ t) (T : ℝ) (N : ℕ)
    (hT : ∀ n ≤ N, dd u n ≤ T) (hrec : KernelRec u t ω T) (h0 : ∀ a, 0 ≤ ω 0 a)
    (hsupp : ∀ ℓ a, N < ℓ + a → ω ℓ a = 0) : ∀ ℓ a, 0 ≤ ω ℓ a := by
  have claim : ∀ ℓ, (∀ ℓ' ≤ ℓ, ∀ a, 0 ≤ ω ℓ' a) ∧
      (∀ ℓ' < ℓ, ∀ a, (1 / 2 : ℝ) * Pin u t ω ℓ' a ≤ dd u (ℓ' + 1) * ω (ℓ' + 1) a) := by
    intro ℓ
    induction ℓ with
    | zero => exact ⟨fun ℓ' h a => by rw [Nat.le_zero.mp h]; exact h0 a, fun ℓ' h => absurd h (Nat.not_lt_zero _)⟩
    | succ ℓ ih =>
      obtain ⟨hnn, hP⟩ := ih
      have hnew : ∀ a, (1 / 2 : ℝ) * Pin u t ω ℓ a ≤ dd u (ℓ + 1) * ω (ℓ + 1) a := by
        intro a
        have hq := Qin_le_half_Pin hu hu1 ht hnn hP a
        have hr := hrec ℓ a
        rw [sign_split] at hr
        have hs : 0 ≤ (T - dd u (ℓ + a)) * ω ℓ a := by
          by_cases hN : ℓ + a ≤ N
          · exact mul_nonneg (by linarith [hT (ℓ + a) hN]) (hnn ℓ le_rfl a)
          · rw [hsupp ℓ a (by omega), mul_zero]
        linarith
      have hPnn : ∀ a, 0 ≤ Pin u t ω ℓ a := fun a =>
        sum_nonneg (fun j _ => grp_nonneg hu ht hnn j a)
      refine ⟨fun ℓ' h a => ?_, fun ℓ' h a => ?_⟩
      · rcases Nat.lt_or_ge ℓ' (ℓ + 1) with h' | h'
        · exact hnn ℓ' (by omega) a
        · have e : ℓ' = ℓ + 1 := by omega
          subst e
          have hd := dd_pos hu hu1 (n := ℓ + 1) (by omega)
          have := hnew a
          have : 0 ≤ dd u (ℓ + 1) * ω (ℓ + 1) a := by linarith [hPnn a]
          exact nonneg_of_mul_nonneg_right (by linarith) hd |> fun h => by
            rcases le_or_gt 0 (ω (ℓ + 1) a) with h1 | h1
            · exact h1
            · nlinarith
      · rcases Nat.lt_or_ge ℓ' ℓ with h' | h'
        · exact hP ℓ' h' a
        · have e : ℓ' = ℓ := by omega
          subst e; exact hnew a
  intro ℓ a
  exact (claim ℓ).1 ℓ le_rfl a

end Szkraw
