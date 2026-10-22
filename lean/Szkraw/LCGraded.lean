import Szkraw.LCInduction

/-!
# The operator induction of Theorem 8.1, coefficientwise in `t`

The kernel of Theorem 8.1 is a polynomial in `t`. Writing `Ω ℓ a p` for the coefficient of `t^p`,
recurrence (8.1) becomes a graded recurrence in which the `A`-moves lower the degree by one. The
induction of `LCInduction.lean` goes through degreewise (the factor `t` becomes the indicator
`τ_p` of `p ≥ 1` and the `A`-moves read degree `p - 1`), so every coefficient is nonnegative.
-/

namespace Szkraw

open Finset

variable (u : ℕ → ℝ) (Ω : ℕ → ℕ → ℕ → ℝ)

/-- `τ_p = [p ≥ 1]`. -/
noncomputable def tau (p : ℕ) : ℝ := if 1 ≤ p then 1 else 0

theorem tau_nonneg (p : ℕ) : 0 ≤ tau p := by unfold tau; split_ifs <;> norm_num

noncomputable def moveAG (j ℓ a p : ℕ) : ℝ :=
  tau p * Wt u (2 * j + 1) j (ℓ - j) (a + 2 * j + 1) * Ω (ℓ - j) (a + 2 * j + 1) (p - 1)
noncomputable def moveBG (j ℓ a p : ℕ) : ℝ :=
  Wt u (2 * j + 2) j (ℓ - j) (a + 2 * j + 2) * Ω (ℓ - j) (a + 2 * j + 2) p
noncomputable def moveCG (j ℓ a p : ℕ) : ℝ :=
  if j < ℓ then Wt u (2 * j + 2) (j + 1) (ℓ - j - 1) (a + 2 * j + 2) * Ω (ℓ - j - 1) (a + 2 * j + 2) p
  else 0

noncomputable def grpG (j ℓ a p : ℕ) : ℝ := moveAG u Ω j ℓ a p + moveBG u Ω j ℓ a p + moveCG u Ω j ℓ a p

noncomputable def PinG (ℓ a p : ℕ) : ℝ := ∑ j ∈ (range (ℓ + 1)).filter Even, grpG u Ω j ℓ a p
noncomputable def QinG (ℓ a p : ℕ) : ℝ := ∑ j ∈ (range (ℓ + 1)).filter Odd, grpG u Ω j ℓ a p

/-- The graded kernel recurrence: (8.1) for the coefficient of `t^p`. -/
def KernelRecG (T : ℝ) : Prop :=
  ∀ ℓ a p, dd u (ℓ + 1) * Ω (ℓ + 1) a p =
    (T - dd u (ℓ + a)) * Ω ℓ a p + ∑ j ∈ range (ℓ + 1), (-1 : ℝ) ^ j * grpG u Ω j ℓ a p

theorem sign_splitG (ℓ a p : ℕ) :
    ∑ j ∈ range (ℓ + 1), (-1 : ℝ) ^ j * grpG u Ω j ℓ a p = PinG u Ω ℓ a p - QinG u Ω ℓ a p := by
  unfold PinG QinG
  rw [← sum_filter_add_sum_filter_not (range (ℓ + 1)) Even]
  have h1 : ∑ j ∈ (range (ℓ + 1)).filter Even, (-1 : ℝ) ^ j * grpG u Ω j ℓ a p =
      ∑ j ∈ (range (ℓ + 1)).filter Even, grpG u Ω j ℓ a p := by
    refine sum_congr rfl (fun j hj => ?_)
    rw [(mem_filter.mp hj).2.neg_one_pow, one_mul]
  have h2 : ∑ j ∈ (range (ℓ + 1)).filter (fun j => ¬ Even j), (-1 : ℝ) ^ j * grpG u Ω j ℓ a p =
      -∑ j ∈ (range (ℓ + 1)).filter Odd, grpG u Ω j ℓ a p := by
    rw [← sum_neg_distrib]
    have : (range (ℓ + 1)).filter (fun j => ¬ Even j) = (range (ℓ + 1)).filter Odd := by
      ext j; simp [Nat.not_even_iff_odd]
    rw [this]
    refine sum_congr rfl (fun j hj => ?_)
    rw [(mem_filter.mp hj).2.neg_one_pow]; ring
  rw [h1, h2]; ring

variable {u Ω}

theorem grpG_nonneg (hu : LCNZ u) {ℓ : ℕ} (hnn : ∀ ℓ' ≤ ℓ, ∀ a' p', 0 ≤ Ω ℓ' a' p') (j a p : ℕ) :
    0 ≤ grpG u Ω j ℓ a p := by
  unfold grpG moveAG moveBG moveCG
  refine add_nonneg (add_nonneg ?_ ?_) ?_
  · exact mul_nonneg (mul_nonneg (tau_nonneg p) (Wt_nonneg hu _ _ _ _)) (hnn _ (by omega) _ _)
  · exact mul_nonneg (Wt_nonneg hu _ _ _ _) (hnn _ (by omega) _ _)
  · split_ifs
    · exact mul_nonneg (Wt_nonneg hu _ _ _ _) (hnn _ (by omega) _ _)
    · exact le_rfl

theorem PinG_ge_grp0 (hu : LCNZ u) {ℓ : ℕ} (hnn : ∀ ℓ' ≤ ℓ, ∀ a' p', 0 ≤ Ω ℓ' a' p') (a p : ℕ) :
    grpG u Ω 0 ℓ a p ≤ PinG u Ω ℓ a p := by
  unfold PinG
  have hmem : 0 ∈ (range (ℓ + 1)).filter Even := mem_filter.mpr ⟨mem_range.mpr (by omega), ⟨0, rfl⟩⟩
  exact single_le_sum (fun j _ => grpG_nonneg hu hnn j a p) hmem

/-- Degreewise domination of one odd group by the preceding even group. -/
theorem odd_domG (hu : LCNZ u) (hu1 : 0 < u 1) {ℓ : ℕ}
    (hnn : ∀ ℓ' ≤ ℓ, ∀ a' p', 0 ≤ Ω ℓ' a' p')
    (hP : ∀ ℓ' < ℓ, ∀ a' p', (1 / 2 : ℝ) * PinG u Ω ℓ' a' p' ≤ dd u (ℓ' + 1) * Ω (ℓ' + 1) a' p')
    {j : ℕ} (hj1 : 1 ≤ j) (hjl : j ≤ ℓ) (a p : ℕ) :
    2 * grpG u Ω j ℓ a p ≤ grpG u Ω (j - 1) ℓ a p := by
  obtain ⟨L, rfl⟩ : ∃ L, ℓ = L + j := ⟨ℓ - j, by omega⟩
  set t := tau p
  have ht : 0 ≤ t := tau_nonneg p
  set ωx := Ω L (a + 2 * j + 1) (p - 1)
  set ωx' := Ω L (a + 2 * j + 2) p
  set ωz1 := Ω (L + 1) (a + 2 * j) p
  set ωz2 := Ω (L + 1) (a + 2 * j - 1) (p - 1)
  set A0 := Wt u 1 0 L (a + 2 * j + 1)
  set B0x := Wt u 2 0 L (a + 2 * j + 1)
  set B0x' := Wt u 2 0 L (a + 2 * j + 2)
  set Aj := Wt u (2 * j + 1) j L (a + 2 * j + 1)
  set Bj := Wt u (2 * j + 2) j L (a + 2 * j + 2)
  set Bm := Wt u (2 * j) (j - 1) (L + 1) (a + 2 * j)
  set Am := Wt u (2 * j - 1) (j - 1) (L + 1) (a + 2 * j - 1)
  set D1 := dd u (L + 1)
  have hD1 : 0 < D1 := dd_pos hu hu1 (by omega)
  have hωx : 0 ≤ ωx := hnn _ (by omega) _ _
  have hωx' : 0 ≤ ωx' := hnn _ (by omega) _ _
  have hωz1 : 0 ≤ ωz1 := hnn _ (by omega) _ _
  have hωz2 : 0 ≤ ωz2 := hnn _ (by omega) _ _
  have hgm : grpG u Ω (j - 1) (L + j) a p =
      t * Am * ωz2 + Bm * ωz1 + moveCG u Ω (j - 1) (L + j) a p := by
    unfold grpG moveAG moveBG
    have e1 : 2 * (j - 1) + 1 = 2 * j - 1 := by omega
    have e2 : L + j - (j - 1) = L + 1 := by omega
    have e3 : a + 2 * (j - 1) + 1 = a + 2 * j - 1 := by omega
    have e4 : 2 * (j - 1) + 2 = 2 * j := by omega
    have e5 : a + 2 * (j - 1) + 2 = a + 2 * j := by omega
    rw [e1, e2, e3, e4, e5]
  have hgj : grpG u Ω j (L + j) a p = t * Aj * ωx + Bj * ωx' + moveCG u Ω j (L + j) a p := by
    unfold grpG moveAG moveBG
    have e2 : L + j - j = L := by omega
    rw [e2]
  -- the invariant at z1 = (L+1, a+2j) in degree p and at z2 = (L+1, a+2j-1) in degree p-1
  have f1 : (1 / 2 : ℝ) * (t * A0 * ωx + B0x' * ωx') ≤ D1 * ωz1 := by
    have h := hP L (by omega) (a + 2 * j) p
    have g := PinG_ge_grp0 hu (ℓ := L) (fun ℓ' h a' p' => hnn ℓ' (by omega) a' p') (a + 2 * j) p
    have hg0 : grpG u Ω 0 L (a + 2 * j) p = t * A0 * ωx + B0x' * ωx' + moveCG u Ω 0 L (a + 2 * j) p := by
      unfold grpG moveAG moveBG; simp only [Nat.sub_zero, mul_zero, zero_add, add_zero]; rfl
    have hc0 : 0 ≤ moveCG u Ω 0 L (a + 2 * j) p := by
      unfold moveCG; split_ifs
      · exact mul_nonneg (Wt_nonneg hu _ _ _ _) (hnn _ (by omega) _ _)
      · exact le_rfl
    linarith
  have f2 : (1 / 2 : ℝ) * (B0x * ωx) ≤ D1 * ωz2 := by
    have h := hP L (by omega) (a + 2 * j - 1) (p - 1)
    have g := PinG_ge_grp0 hu (ℓ := L) (fun ℓ' h a' p' => hnn ℓ' (by omega) a' p') (a + 2 * j - 1) (p - 1)
    have hB : moveBG u Ω 0 L (a + 2 * j - 1) (p - 1) = B0x * ωx := by
      unfold moveBG
      have e : a + 2 * j - 1 + 2 = a + 2 * j + 1 := by omega
      simp only [Nat.sub_zero, mul_zero, add_zero]; rw [e]
    have hA0 : 0 ≤ moveAG u Ω 0 L (a + 2 * j - 1) (p - 1) := by
      unfold moveAG
      exact mul_nonneg (mul_nonneg (tau_nonneg _) (Wt_nonneg hu _ _ _ _)) (hnn _ (by omega) _ _)
    have hc0 : 0 ≤ moveCG u Ω 0 L (a + 2 * j - 1) (p - 1) := by
      unfold moveCG; split_ifs
      · exact mul_nonneg (Wt_nonneg hu _ _ _ _) (hnn _ (by omega) _ _)
      · exact le_rfl
    unfold grpG at g
    linarith
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
  have pAB : 2 * (t * Aj * ωx + Bj * ωx') ≤ t * Am * ωz2 + Bm * ωz1 := by
    have k1 := mul_le_mul_of_nonneg_left f2 (mul_nonneg ht hAm)
    have k2 := mul_le_mul_of_nonneg_left f1 hBm
    have k3 := mul_le_mul_of_nonneg_right g1 (mul_nonneg ht hωx)
    have k4 := mul_le_mul_of_nonneg_right g2 hωx'
    have : D1 * (2 * (t * Aj * ωx + Bj * ωx')) ≤ D1 * (t * Am * ωz2 + Bm * ωz1) := by nlinarith
    exact le_of_mul_le_mul_left this hD1
  have pC : 2 * moveCG u Ω j (L + j) a p ≤ moveCG u Ω (j - 1) (L + j) a p := by
    unfold moveCG
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
      have f3 : (1 / 2 : ℝ) * (Wt u 2 0 (L - 1) (a + 2 * j + 2) * Ω (L - 1) (a + 2 * j + 2) p) ≤
          D0 * Ω L (a + 2 * j) p := by
        have h := hP (L - 1) (by omega) (a + 2 * j) p
        have e6 : L - 1 + 1 = L := by omega
        rw [e6] at h
        have g := PinG_ge_grp0 hu (ℓ := L - 1) (fun ℓ' h a' p' => hnn ℓ' (by omega) a' p') (a + 2 * j) p
        have hB : moveBG u Ω 0 (L - 1) (a + 2 * j) p =
            Wt u 2 0 (L - 1) (a + 2 * j + 2) * Ω (L - 1) (a + 2 * j + 2) p := by
          unfold moveBG; simp only [Nat.sub_zero, mul_zero, zero_add, add_zero]
        have hA0 : 0 ≤ moveAG u Ω 0 (L - 1) (a + 2 * j) p := by
          unfold moveAG
          exact mul_nonneg (mul_nonneg (tau_nonneg _) (Wt_nonneg hu _ _ _ _)) (hnn _ (by omega) _ _)
        have hc0 : 0 ≤ moveCG u Ω 0 (L - 1) (a + 2 * j) p := by
          unfold moveCG; split_ifs
          · exact mul_nonneg (Wt_nonneg hu _ _ _ _) (hnn _ (by omega) _ _)
          · exact le_rfl
        unfold grpG at g
        linarith
      have g3 : 4 * D0 * Wt u (2 * j + 2) (j + 1) (L - 1) (a + 2 * j + 2) ≤
          Wt u 2 0 (L - 1) (a + 2 * j + 2) * Wt u (2 * j) j L (a + 2 * j) := by
        have h := lemma_8_4_C hu j (L - 1) (a + 2 * j + 2) hj1
        have e6 : L - 1 + 1 = L := by omega
        have e7 : a + 2 * j + 2 - 2 = a + 2 * j := by omega
        rw [e6, e7] at h; exact h
      have hCm := Wt_nonneg hu (2 * j) j L (a + 2 * j)
      have hωx'' : 0 ≤ Ω (L - 1) (a + 2 * j + 2) p := hnn _ (by omega) _ _
      have k1 := mul_le_mul_of_nonneg_left f3 hCm
      have k2 := mul_le_mul_of_nonneg_right g3 hωx''
      have : D0 * (2 * (Wt u (2 * j + 2) (j + 1) (L - 1) (a + 2 * j + 2) * Ω (L - 1) (a + 2 * j + 2) p)) ≤
          D0 * (Wt u (2 * j) j L (a + 2 * j) * Ω L (a + 2 * j) p) := by nlinarith
      exact le_of_mul_le_mul_left this hD0
    · rw [if_neg hL]
      have : 0 ≤ (if j - 1 < L + j then Wt u (2 * (j - 1) + 2) (j - 1 + 1) (L + j - (j - 1) - 1)
          (a + 2 * (j - 1) + 2) * Ω (L + j - (j - 1) - 1) (a + 2 * (j - 1) + 2) p else 0) := by
        split_ifs
        · exact mul_nonneg (Wt_nonneg hu _ _ _ _) (hnn _ (by omega) _ _)
        · exact le_rfl
      linarith
  rw [hgm, hgj]
  linarith

theorem QinG_le_half_Pin (hu : LCNZ u) (hu1 : 0 < u 1) {ℓ : ℕ}
    (hnn : ∀ ℓ' ≤ ℓ, ∀ a' p', 0 ≤ Ω ℓ' a' p')
    (hP : ∀ ℓ' < ℓ, ∀ a' p', (1 / 2 : ℝ) * PinG u Ω ℓ' a' p' ≤ dd u (ℓ' + 1) * Ω (ℓ' + 1) a' p')
    (a p : ℕ) : QinG u Ω ℓ a p ≤ (1 / 2 : ℝ) * PinG u Ω ℓ a p := by
  unfold QinG PinG
  set Od := (range (ℓ + 1)).filter Odd
  set Ev := (range (ℓ + 1)).filter Even
  have step1 : ∑ j ∈ Od, grpG u Ω j ℓ a p ≤ ∑ j ∈ Od, (1 / 2 : ℝ) * grpG u Ω (j - 1) ℓ a p := by
    refine sum_le_sum (fun j hj => ?_)
    obtain ⟨hjr, hjo⟩ := mem_filter.mp hj
    have hj1 : 1 ≤ j := by obtain ⟨k, rfl⟩ := hjo; omega
    have := odd_domG hu hu1 hnn hP hj1 (by have := mem_range.mp hjr; omega) a p
    linarith
  have hinj : Set.InjOn (fun j => j - 1) (Od : Set ℕ) := by
    intro x hx y hy hxy
    have hx1 : 1 ≤ x := by obtain ⟨k, rfl⟩ := (mem_filter.mp hx).2; omega
    have hy1 : 1 ≤ y := by obtain ⟨k, rfl⟩ := (mem_filter.mp hy).2; omega
    simp only at hxy; omega
  have step2 : ∑ j ∈ Od, grpG u Ω (j - 1) ℓ a p = ∑ j' ∈ Od.image (fun j => j - 1), grpG u Ω j' ℓ a p :=
    (sum_image (f := fun j' => grpG u Ω j' ℓ a p) (fun x hx y hy h => hinj hx hy h)).symm
  have hsub : Od.image (fun j => j - 1) ⊆ Ev := by
    intro j' hj'
    obtain ⟨j, hj, rfl⟩ := mem_image.mp hj'
    obtain ⟨hjr, hjo⟩ := mem_filter.mp hj
    refine mem_filter.mpr ⟨mem_range.mpr (by have := mem_range.mp hjr; omega), ?_⟩
    obtain ⟨k, rfl⟩ := hjo; exact ⟨k, by omega⟩
  have step3 : ∑ j' ∈ Od.image (fun j => j - 1), grpG u Ω j' ℓ a p ≤ ∑ j' ∈ Ev, grpG u Ω j' ℓ a p :=
    sum_le_sum_of_subset_of_nonneg hsub (fun j _ _ => grpG_nonneg hu hnn j a p)
  rw [← mul_sum] at step1
  linarith

/-- Graded F7: every solution of the graded recurrence with nonnegative initial values and the
support property is nonnegative in every degree. -/
theorem kernel_nonnegG (hu : LCNZ u) (hu1 : 0 < u 1) (T : ℝ) (N : ℕ)
    (hT : ∀ n ≤ N, dd u n ≤ T) (hrec : KernelRecG u Ω T) (h0 : ∀ a p, 0 ≤ Ω 0 a p)
    (hsupp : ∀ ℓ a p, N < ℓ + a → Ω ℓ a p = 0) : ∀ ℓ a p, 0 ≤ Ω ℓ a p := by
  have claim : ∀ ℓ, (∀ ℓ' ≤ ℓ, ∀ a p, 0 ≤ Ω ℓ' a p) ∧
      (∀ ℓ' < ℓ, ∀ a p, (1 / 2 : ℝ) * PinG u Ω ℓ' a p ≤ dd u (ℓ' + 1) * Ω (ℓ' + 1) a p) := by
    intro ℓ
    induction ℓ with
    | zero => exact ⟨fun ℓ' h a p => by rw [Nat.le_zero.mp h]; exact h0 a p,
        fun ℓ' h => absurd h (Nat.not_lt_zero _)⟩
    | succ ℓ ih =>
      obtain ⟨hnn, hP⟩ := ih
      have hnew : ∀ a p, (1 / 2 : ℝ) * PinG u Ω ℓ a p ≤ dd u (ℓ + 1) * Ω (ℓ + 1) a p := by
        intro a p
        have hq := QinG_le_half_Pin hu hu1 hnn hP a p
        have hr := hrec ℓ a p
        rw [sign_splitG] at hr
        have hs : 0 ≤ (T - dd u (ℓ + a)) * Ω ℓ a p := by
          by_cases hN : ℓ + a ≤ N
          · exact mul_nonneg (by linarith [hT (ℓ + a) hN]) (hnn ℓ le_rfl a p)
          · rw [hsupp ℓ a p (by omega), mul_zero]
        linarith
      have hPnn : ∀ a p, 0 ≤ PinG u Ω ℓ a p := fun a p =>
        sum_nonneg (fun j _ => grpG_nonneg hu hnn j a p)
      refine ⟨fun ℓ' h a p => ?_, fun ℓ' h a p => ?_⟩
      · rcases Nat.lt_or_ge ℓ' (ℓ + 1) with h' | h'
        · exact hnn ℓ' (by omega) a p
        · have e : ℓ' = ℓ + 1 := by omega
          subst e
          have hd := dd_pos hu hu1 (n := ℓ + 1) (by omega)
          have := hnew a p
          have h2 : 0 ≤ dd u (ℓ + 1) * Ω (ℓ + 1) a p := by linarith [hPnn a p]
          exact nonneg_of_mul_nonneg_right (by linarith) hd
      · rcases Nat.lt_or_ge ℓ' ℓ with h' | h'
        · exact hP ℓ' h' a p
        · have e : ℓ' = ℓ := by omega
          subst e; exact hnew a p
  intro ℓ a p
  exact (claim ℓ).1 ℓ le_rfl a p

end Szkraw
