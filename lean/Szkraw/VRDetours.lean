import Szkraw.LCDetours

/-!
# Mixed detour inequalities (paper, proofs of Theorem 8.6 and Corollary 8.7)

`u` is the (padded) Newton sequence of the downward coefficients `c`, assumed `LCNZ`, and `v` that
of the diagonal coefficients `b`, assumed nonnegative. Under the two mixed inequalities of
Theorem 8.6, the `A`-moves (built from `v`) and the `v`-part of the `C`-moves satisfy the detour
inequalities of Lemma 8.4. Corollary 8.7: if `v_k = w_k u_k` with `w` nonincreasing, the mixed
inequalities hold; the proof uses that the cross-ratio order `H_k G_i ≤ H_i G_k` (`i ≤ k`) is
preserved by the shift sums.
-/

namespace Szkraw

open Finset

theorem iterShift_nonneg_of {v : ℕ → ℝ} (hv : ∀ i, 0 ≤ v i) (ℓ n : ℕ) : 0 ≤ Szkraw.iterShift v ℓ n := by
  rw [iterShift_eq]; exact sum_nonneg fun h _ => mul_nonneg (Nat.cast_nonneg _) (hv _)

theorem Wt_nonneg_of {v : ℕ → ℝ} (hv : ∀ i, 0 ≤ v i) (p q ℓ a : ℕ) : 0 ≤ Wt v p q ℓ a := by
  unfold Wt
  refine sum_nonneg (fun n _ => mul_nonneg (mul_nonneg ?_ (Nat.cast_nonneg _)) (iterShift_nonneg_of hv ℓ n))
  split_ifs <;> positivity

theorem Wt_ge_term_of {v : ℕ → ℝ} (hv : ∀ i, 0 ≤ v i) (p q ℓ a n : ℕ) (hpn : p ≤ n) (hna : n ≤ a) :
    ((n - p + q).choose q : ℝ) * (a.choose n : ℝ) * Szkraw.iterShift v ℓ n ≤ Wt v p q ℓ a := by
  unfold Wt
  have hmem : n ∈ range (a + 1) := mem_range.mpr (by omega)
  have := single_le_sum (f := fun n => (if p ≤ n then ((n - p + q).choose q : ℝ) else 0) *
      (a.choose n : ℝ) * Szkraw.iterShift v ℓ n)
    (fun i _ => mul_nonneg (mul_nonneg (by split_ifs <;> positivity) (Nat.cast_nonneg _))
      (iterShift_nonneg_of hv ℓ i)) hmem
  simpa [hpn] using this

/-- The two mixed inequalities of Theorem 8.6, for `0 ≤ ℓ ≤ N - 1`. -/
def MixedIneq (u v : ℕ → ℝ) (N : ℕ) : Prop :=
  (∀ ℓ n, ℓ < N → 2 ≤ n →
    Szkraw.iterShift u (ℓ + 1) 0 * Szkraw.iterShift v ℓ (n + 1) ≤
      Szkraw.iterShift v ℓ 1 * Szkraw.iterShift u (ℓ + 1) n) ∧
  (∀ ℓ n, ℓ < N → 1 ≤ n →
    Szkraw.iterShift u (ℓ + 1) 0 * Szkraw.iterShift v ℓ (n + 2) ≤
      Szkraw.iterShift u ℓ 2 * Szkraw.iterShift v (ℓ + 1) n)

variable {u v : ℕ → ℝ} {N : ℕ}

/-- First mixed detour bound for the `A`-family. -/
theorem detourA_firstV (hu : LCNZ u) (hv : ∀ i, 0 ≤ v i) (hMI : MixedIneq u v N) (j ℓ a : ℕ) (hℓ : ℓ < N)
    (hj : 1 ≤ j) (ha : 1 ≤ a) :
    ∑ m ∈ range (a + 1), (if 2 * j + 1 ≤ m then ((m - j - 2).choose (j - 1) : ℝ) else 0) *
        ((m : ℝ) * (a.choose m : ℝ)) * (Szkraw.iterShift u (ℓ + 1) 0 * Szkraw.iterShift v ℓ m) ≤
      Wt v 1 0 ℓ a * Wt u (2 * j) (j - 1) (ℓ + 1) (a - 1) := by
  set G : ℕ → ℝ := fun m => (if 2 * j + 1 ≤ m then ((m - j - 2).choose (j - 1) : ℝ) else 0) *
        ((m : ℝ) * (a.choose m : ℝ)) * (Szkraw.iterShift u (ℓ + 1) 0 * Szkraw.iterShift v ℓ m) with hG
  have hW10 : (a : ℝ) * Szkraw.iterShift v ℓ 1 ≤ Wt v 1 0 ℓ a := by
    have := Wt_ge_term_of hv 1 0 ℓ a 1 le_rfl ha
    simpa using this
  have hsplit : a - 1 + 1 = a := by omega
  calc ∑ m ∈ range (a + 1), G m = ∑ n ∈ range a, G (n + 1) := (reindex1 G a (by simp [hG])).symm
    _ ≤ ∑ n ∈ range a, (if 2 * j ≤ n then ((n - 2 * j + (j - 1)).choose (j - 1) : ℝ) else 0) *
          ((a - 1).choose n : ℝ) * Szkraw.iterShift u (ℓ + 1) n *
          ((a : ℝ) * Szkraw.iterShift v ℓ 1) := by
        refine sum_le_sum (fun n _ => ?_)
        simp only [hG]
        by_cases hn : 2 * j ≤ n
        · rw [if_pos (by omega), if_pos hn]
          have e1 : n + 1 - j - 2 = n - 2 * j + (j - 1) := by omega
          rw [e1]
          have hc := Nat.add_one_mul_choose_eq (a - 1) n
          rw [hsplit] at hc
          have hc' : ((n + 1 : ℕ) : ℝ) * (a.choose (n + 1) : ℝ) = (a : ℝ) * ((a - 1).choose n : ℝ) := by
            have : ((a * (a - 1).choose n : ℕ) : ℝ) = ((a.choose (n + 1) * (n + 1) : ℕ) : ℝ) := by rw [hc]
            push_cast at this ⊢; linarith
          rw [hc']
          have key := hMI.1 ℓ n hℓ (by omega)
          have hC : (0 : ℝ) ≤ ((n - 2 * j + (j - 1)).choose (j - 1) : ℝ) := Nat.cast_nonneg _
          have hA : (0 : ℝ) ≤ (a : ℝ) * ((a - 1).choose n : ℝ) := by positivity
          calc ((n - 2 * j + (j - 1)).choose (j - 1) : ℝ) * ((a : ℝ) * ((a - 1).choose n : ℝ)) *
                (Szkraw.iterShift u (ℓ + 1) 0 * Szkraw.iterShift v ℓ (n + 1))
              ≤ ((n - 2 * j + (j - 1)).choose (j - 1) : ℝ) * ((a : ℝ) * ((a - 1).choose n : ℝ)) *
                (Szkraw.iterShift v ℓ 1 * Szkraw.iterShift u (ℓ + 1) n) :=
                mul_le_mul_of_nonneg_left key (mul_nonneg hC hA)
            _ = _ := by ring
        · rw [if_neg (by omega), if_neg hn]; simp
    _ = ((a : ℝ) * Szkraw.iterShift v ℓ 1) * Wt u (2 * j) (j - 1) (ℓ + 1) (a - 1) := by
        rw [Wt, hsplit, mul_sum]; refine sum_congr rfl (fun n _ => by ring)
    _ ≤ Wt v 1 0 ℓ a * Wt u (2 * j) (j - 1) (ℓ + 1) (a - 1) :=
        mul_le_mul_of_nonneg_right hW10 (Wt_nonneg hu _ _ _ _)

/-- Generic second mixed detour: for `p ≥ 1`,
`Σ_m [p+2 ≤ m] C(m-2-p+q, q) C(m,2) C(a,m) c_{ℓ+1} g_m(ℓ) ≤ W^c_{2,0}(ℓ,a) W^b_{p,q}(ℓ+1,a-2)`. -/
theorem detour_secondV (hu : LCNZ u) (hv : ∀ i, 0 ≤ v i) (hMI : MixedIneq u v N) (p q ℓ a : ℕ) (hℓ : ℓ < N)
    (hp : 1 ≤ p) (ha : 2 ≤ a) :
    ∑ m ∈ range (a + 1), (if p + 2 ≤ m then ((m - 2 - p + q).choose q : ℝ) else 0) *
        ((m.choose 2 : ℝ) * (a.choose m : ℝ)) * (Szkraw.iterShift u (ℓ + 1) 0 * Szkraw.iterShift v ℓ m) ≤
      Wt u 2 0 ℓ a * Wt v p q (ℓ + 1) (a - 2) := by
  set G : ℕ → ℝ := fun m => (if p + 2 ≤ m then ((m - 2 - p + q).choose q : ℝ) else 0) *
        ((m.choose 2 : ℝ) * (a.choose m : ℝ)) * (Szkraw.iterShift u (ℓ + 1) 0 * Szkraw.iterShift v ℓ m) with hG
  have hW20 : (a.choose 2 : ℝ) * Szkraw.iterShift u ℓ 2 ≤ Wt u 2 0 ℓ a := by
    have := Wt_ge_term hu 2 0 ℓ a 2 le_rfl ha
    simpa using this
  have hsplit' : a - 2 + 1 = a - 1 := by omega
  have hre : ∑ m ∈ range (a + 1), G m = ∑ n ∈ range (a - 1), G (n + 2) := by
    rw [reindex2 G (a - 1) (by simp [hG]) (by simp [hG]), show a - 1 + 2 = a + 1 by omega]
  calc ∑ m ∈ range (a + 1), G m = ∑ n ∈ range (a - 1), G (n + 2) := hre
    _ ≤ ∑ n ∈ range (a - 1), (if p ≤ n then ((n - p + q).choose q : ℝ) else 0) *
          ((a - 2).choose n : ℝ) * Szkraw.iterShift v (ℓ + 1) n *
          ((a.choose 2 : ℝ) * Szkraw.iterShift u ℓ 2) := by
        refine sum_le_sum (fun n _ => ?_)
        simp only [hG]
        by_cases hn : p ≤ n
        · rw [if_pos (by omega), if_pos hn]
          have e1 : n + 2 - 2 - p + q = n - p + q := by omega
          rw [e1]
          have hc := Nat.choose_mul (n := a) (k := n + 2) (s := 2) (by omega)
          have e2 : n + 2 - 2 = n := by omega
          rw [e2] at hc
          have hc' : ((n + 2).choose 2 : ℝ) * (a.choose (n + 2) : ℝ) = (a.choose 2 : ℝ) * ((a - 2).choose n : ℝ) := by
            have : ((a.choose (n + 2) * (n + 2).choose 2 : ℕ) : ℝ) = ((a.choose 2 * (a - 2).choose n : ℕ) : ℝ) := by
              rw [hc]
            push_cast at this; linarith
          rw [hc']
          have key := hMI.2 ℓ n hℓ (by omega)
          have hC : (0 : ℝ) ≤ ((n - p + q).choose q : ℝ) := Nat.cast_nonneg _
          have hA : (0 : ℝ) ≤ (a.choose 2 : ℝ) * ((a - 2).choose n : ℝ) := by positivity
          calc ((n - p + q).choose q : ℝ) * ((a.choose 2 : ℝ) * ((a - 2).choose n : ℝ)) *
                (Szkraw.iterShift u (ℓ + 1) 0 * Szkraw.iterShift v ℓ (n + 2))
              ≤ ((n - p + q).choose q : ℝ) * ((a.choose 2 : ℝ) * ((a - 2).choose n : ℝ)) *
                (Szkraw.iterShift u ℓ 2 * Szkraw.iterShift v (ℓ + 1) n) :=
                mul_le_mul_of_nonneg_left key (mul_nonneg hC hA)
            _ = _ := by ring
        · rw [if_neg (by omega), if_neg hn]; simp
    _ = ((a.choose 2 : ℝ) * Szkraw.iterShift u ℓ 2) * Wt v p q (ℓ + 1) (a - 2) := by
        rw [Wt, hsplit', mul_sum]; refine sum_congr rfl (fun n _ => by ring)
    _ ≤ Wt u 2 0 ℓ a * Wt v p q (ℓ + 1) (a - 2) :=
        mul_le_mul_of_nonneg_right hW20 (Wt_nonneg_of hv _ _ _ _)

/-- Mixed Lemma 8.4, `A`-family:
`4 c_{ℓ+1} A^b_j(ℓ,a) ≤ A^b_0(ℓ,a) B_{j-1}(ℓ+1,a-1) + B_0(ℓ,a) A^b_{j-1}(ℓ+1,a-2)`. -/
theorem lemma_8_4_AV (hu : LCNZ u) (hv : ∀ i, 0 ≤ v i) (hMI : MixedIneq u v N) (j ℓ a : ℕ) (hj : 1 ≤ j)
    (hla : ℓ + a ≤ N) :
    4 * Szkraw.iterShift u (ℓ + 1) 0 * Wt v (2 * j + 1) j ℓ a ≤
      Wt v 1 0 ℓ a * Wt u (2 * j) (j - 1) (ℓ + 1) (a - 1) +
      Wt u 2 0 ℓ a * Wt v (2 * j - 1) (j - 1) (ℓ + 1) (a - 2) := by
  have hF0 := iterShift_nonneg hu (ℓ + 1) 0
  by_cases ha : a < 2 * j + 1
  · rw [Wt_eq_zero _ _ _ _ ha, mul_zero]
    exact add_nonneg (mul_nonneg (Wt_nonneg_of hv _ _ _ _) (Wt_nonneg hu _ _ _ _))
      (mul_nonneg (Wt_nonneg hu _ _ _ _) (Wt_nonneg_of hv _ _ _ _))
  push Not at ha
  have hℓ : ℓ < N := by omega
  have h1 := detourA_firstV hu hv hMI j ℓ a hℓ hj (by omega)
  have h2 := detour_secondV hu hv hMI (2 * j - 1) (j - 1) ℓ a hℓ (by omega) (by omega)
  refine le_trans ?_ (add_le_add h1 h2)
  rw [← sum_add_distrib, Wt, mul_sum]
  refine sum_le_sum (fun m _ => ?_)
  by_cases hm : 2 * j + 1 ≤ m
  · rw [if_pos hm, if_pos hm, if_pos (by omega)]
    have e1 : m - (2 * j + 1) + j = m - j - 1 := by omega
    have e2 : m - 2 - (2 * j - 1) + (j - 1) = m - j - 2 := by omega
    rw [e1, e2]
    have hco := coeffA j m hj hm
    have hpas : (m + 1).choose 2 = m + m.choose 2 := by
      rw [show (2 : ℕ) = 1 + 1 from rfl, Nat.choose_succ_succ, Nat.choose_one_right]
    rw [hpas] at hco
    have hco' : (4 : ℝ) * ((m - j - 1).choose j : ℝ) ≤ ((m : ℝ) + (m.choose 2 : ℝ)) * ((m - j - 2).choose (j - 1) : ℝ) := by
      exact_mod_cast hco
    have hf := iterShift_nonneg_of hv ℓ m
    have hc : (0 : ℝ) ≤ (a.choose m : ℝ) := Nat.cast_nonneg _
    have : 4 * Szkraw.iterShift u (ℓ + 1) 0 * (((m - j - 1).choose j : ℝ) * (a.choose m : ℝ) * Szkraw.iterShift v ℓ m) =
        (4 * ((m - j - 1).choose j : ℝ)) * ((a.choose m : ℝ) * (Szkraw.iterShift u (ℓ + 1) 0 * Szkraw.iterShift v ℓ m)) := by ring
    rw [this]
    have rhs : ((m - j - 2).choose (j - 1) : ℝ) * ((m : ℝ) * (a.choose m : ℝ)) *
          (Szkraw.iterShift u (ℓ + 1) 0 * Szkraw.iterShift v ℓ m) +
        ((m - j - 2).choose (j - 1) : ℝ) * ((m.choose 2 : ℝ) * (a.choose m : ℝ)) *
          (Szkraw.iterShift u (ℓ + 1) 0 * Szkraw.iterShift v ℓ m) =
        (((m : ℝ) + (m.choose 2 : ℝ)) * ((m - j - 2).choose (j - 1) : ℝ)) *
          ((a.choose m : ℝ) * (Szkraw.iterShift u (ℓ + 1) 0 * Szkraw.iterShift v ℓ m)) := by ring
    rw [rhs]
    exact mul_le_mul_of_nonneg_right hco' (mul_nonneg hc (mul_nonneg hF0 hf))
  · rw [if_neg hm, if_neg hm, if_neg (by omega)]; simp

/-- Mixed Lemma 8.4, `v`-part of the `C`-family: `4 c_{ℓ+1} C^b_j(ℓ,a) ≤ B_0(ℓ,a) C^b_{j-1}(ℓ+1,a-2)`. -/
theorem lemma_8_4_CV (hu : LCNZ u) (hv : ∀ i, 0 ≤ v i) (hMI : MixedIneq u v N) (j ℓ a : ℕ) (hj : 1 ≤ j)
    (hla : ℓ + a ≤ N) :
    4 * Szkraw.iterShift u (ℓ + 1) 0 * Wt v (2 * j + 2) (j + 1) ℓ a ≤
      Wt u 2 0 ℓ a * Wt v (2 * j) j (ℓ + 1) (a - 2) := by
  have hF0 := iterShift_nonneg hu (ℓ + 1) 0
  by_cases ha : a < 2 * j + 2
  · rw [Wt_eq_zero _ _ _ _ ha, mul_zero]
    exact mul_nonneg (Wt_nonneg hu _ _ _ _) (Wt_nonneg_of hv _ _ _ _)
  push Not at ha
  have hℓ : ℓ < N := by omega
  refine le_trans ?_ (detour_secondV hu hv hMI (2 * j) j ℓ a hℓ (by omega) (by omega))
  rw [Wt, mul_sum]
  refine sum_le_sum (fun m _ => ?_)
  by_cases hm : 2 * j + 2 ≤ m
  · rw [if_pos hm, if_pos hm]
    have e1 : m - (2 * j + 2) + (j + 1) = m - j - 1 := by omega
    have e2 : m - 2 - 2 * j + j = m - j - 2 := by omega
    rw [e1, e2]
    have hco' : (4 : ℝ) * ((m - j - 1).choose (j + 1) : ℝ) ≤ (m.choose 2 : ℝ) * ((m - j - 2).choose j : ℝ) := by
      exact_mod_cast coeffC j m hj hm
    have hf := iterShift_nonneg_of hv ℓ m
    have hc : (0 : ℝ) ≤ (a.choose m : ℝ) := Nat.cast_nonneg _
    calc 4 * Szkraw.iterShift u (ℓ + 1) 0 * (((m - j - 1).choose (j + 1) : ℝ) * (a.choose m : ℝ) * Szkraw.iterShift v ℓ m)
        = (4 * ((m - j - 1).choose (j + 1) : ℝ)) * ((a.choose m : ℝ) * (Szkraw.iterShift u (ℓ + 1) 0 * Szkraw.iterShift v ℓ m)) := by ring
      _ ≤ ((m.choose 2 : ℝ) * ((m - j - 2).choose j : ℝ)) * ((a.choose m : ℝ) * (Szkraw.iterShift u (ℓ + 1) 0 * Szkraw.iterShift v ℓ m)) :=
          mul_le_mul_of_nonneg_right hco' (mul_nonneg hc (mul_nonneg hF0 hf))
      _ = _ := by ring
  · rw [if_neg hm, if_neg hm]; simp

/-! ### Corollary 8.7: nonincreasing weights give the mixed inequalities -/

/-- The cross-ratio order: `H k * G i ≤ H i * G k` for `i ≤ k`. -/
def CrossOrder (G H : ℕ → ℝ) : Prop := ∀ i k, i ≤ k → H k * G i ≤ H i * G k

theorem CrossOrder.shiftSum {G H : ℕ → ℝ} (h : CrossOrder G H) :
    CrossOrder (Szkraw.shiftSum G) (Szkraw.shiftSum H) := by
  intro i k hik
  unfold Szkraw.shiftSum
  rcases Nat.eq_or_lt_of_le hik with e | hlt
  · subst e; exact le_refl _
  have t1 := h i k hik
  have t2 := h (i + 1) k (by omega)
  have t3 := h i (k + 1) (by omega)
  have t4 := h (i + 1) (k + 1) (by omega)
  nlinarith

theorem CrossOrder.iterShift {G H : ℕ → ℝ} (h : CrossOrder G H) :
    ∀ ℓ, CrossOrder (Szkraw.iterShift G ℓ) (Szkraw.iterShift H ℓ)
  | 0 => h
  | ℓ + 1 => (CrossOrder.iterShift h ℓ).shiftSum

theorem iterShift_one_pos (hu : LCNZ u) (hu1 : 0 < u 1) (ℓ : ℕ) : 0 < Szkraw.iterShift u ℓ 1 := by
  rw [iterShift_eq]
  have hmem : 0 ∈ range (ℓ + 1) := mem_range.mpr (by omega)
  have := single_le_sum (f := fun h => (ℓ.choose h : ℝ) * u (1 + h))
    (fun i _ => mul_nonneg (Nat.cast_nonneg _) (hu.1 _)) hmem
  simp only [Nat.choose_zero_right, Nat.cast_one, one_mul, add_zero] at this
  linarith

/-- **Corollary 8.7, inequalities**: if `u` is `LCNZ` with `u 1 > 0`, `v ≥ 0`, and `(u, v)` is in
cross-ratio order (which holds when `v k = w k u k` with `w` nonincreasing), the mixed
inequalities hold. -/
theorem mixedIneq_of_crossOrder (hu : LCNZ u) (hu1 : 0 < u 1) (hv : ∀ i, 0 ≤ v i)
    (hco : CrossOrder u v) (N : ℕ) : MixedIneq u v N := by
  refine ⟨fun ℓ n _ hn => ?_, fun ℓ n _ hn => ?_⟩
  · set G := Szkraw.iterShift u ℓ
    set H := Szkraw.iterShift v ℓ
    have hG := hu.iterShift ℓ
    have hc := hco.iterShift ℓ
    have hG1 : 0 < G 1 := iterShift_one_pos hu hu1 ℓ
    have e0 : Szkraw.iterShift u (ℓ + 1) 0 = G 0 + G 1 := rfl
    have en : Szkraw.iterShift u (ℓ + 1) n = G n + G (n + 1) := rfl
    rw [e0, en]
    -- H(n+1) G1 ≤ H1 G(n+1), and G0 H(n+1) ≤ H1 Gn via G0 G(n+1) ≤ G1 Gn
    have c1 := hc 1 (n + 1) (by omega)
    have bal : G 0 * G (n + 1) ≤ G 1 * G n := by
      have := hG.balanced 1 1 n le_rfl (by omega)
      simpa [Nat.sub_self, add_comm] using this
    have hH1 : 0 ≤ H 1 := iterShift_nonneg_of hv ℓ 1
    have hHn1 : 0 ≤ H (n + 1) := iterShift_nonneg_of hv ℓ (n + 1)
    have hG0 : 0 ≤ G 0 := hG.1 0
    have k : G 1 * (G 0 * H (n + 1)) ≤ G 1 * (H 1 * G n) := by
      calc G 1 * (G 0 * H (n + 1)) = G 0 * (H (n + 1) * G 1) := by ring
        _ ≤ G 0 * (H 1 * G (n + 1)) := mul_le_mul_of_nonneg_left c1 hG0
        _ = H 1 * (G 0 * G (n + 1)) := by ring
        _ ≤ H 1 * (G 1 * G n) := mul_le_mul_of_nonneg_left bal hH1
        _ = G 1 * (H 1 * G n) := by ring
    have k' := le_of_mul_le_mul_left k hG1
    nlinarith
  · set G := Szkraw.iterShift u ℓ
    set H := Szkraw.iterShift v ℓ
    have hG := hu.iterShift ℓ
    have hc := hco.iterShift ℓ
    have hG1 : 0 < G 1 := iterShift_one_pos hu hu1 ℓ
    have e0 : Szkraw.iterShift u (ℓ + 1) 0 = G 0 + G 1 := rfl
    have en : Szkraw.iterShift v (ℓ + 1) n = H n + H (n + 1) := rfl
    rw [e0, en]
    have key := hG.key (i := 2) (l := n) (by omega) hn
    rw [add_comm 2 n] at key
    have hH : ∀ i, 0 ≤ H i := iterShift_nonneg_of hv ℓ
    rcases eq_or_lt_of_le (hG.1 (n + 2)) with h0 | hpos
    · -- G (n+2) = 0 forces H (n+2) = 0
      have c := hc 1 (n + 2) (by omega)
      rw [← h0, mul_zero] at c
      have hz : H (n + 2) = 0 := le_antisymm (by nlinarith [hH (n + 2)]) (hH (n + 2))
      rw [hz, mul_zero]
      exact mul_nonneg (hG.1 2) (add_nonneg (hH n) (hH (n + 1)))
    · have c1 := hc n (n + 2) (by omega)
      have c2 := hc (n + 1) (n + 2) (by omega)
      have hG2 : 0 ≤ G 2 := hG.1 2
      have hHn2 : 0 ≤ H (n + 2) := hH (n + 2)
      have k : G (n + 2) * ((G 0 + G 1) * H (n + 2)) ≤ G (n + 2) * (G 2 * (H n + H (n + 1))) := by
        calc G (n + 2) * ((G 0 + G 1) * H (n + 2)) = H (n + 2) * ((G 0 + G 1) * G (n + 2)) := by ring
          _ ≤ H (n + 2) * (G 2 * (G n + G (n + 1))) := mul_le_mul_of_nonneg_left key hHn2
          _ = G 2 * (H (n + 2) * G n + H (n + 2) * G (n + 1)) := by ring
          _ ≤ G 2 * (H n * G (n + 2) + H (n + 1) * G (n + 2)) :=
              mul_le_mul_of_nonneg_left (add_le_add c1 c2) hG2
          _ = G (n + 2) * (G 2 * (H n + H (n + 1))) := by ring
      exact le_of_mul_le_mul_left k hpos

/-- Nonincreasing weights give the cross-ratio order. -/
theorem crossOrder_of_weights {w : ℕ → ℝ} (hu0 : ∀ i, 0 ≤ u i) (hvw : ∀ i, v i = w i * u i)
    (hw : ∀ i k, i ≤ k → u i ≠ 0 → u k ≠ 0 → w k ≤ w i) : CrossOrder u v := by
  intro i k hik
  rw [hvw k, hvw i]
  by_cases hi : u i = 0
  · rw [hi]; simp
  by_cases hk : u k = 0
  · rw [hk]; simp
  have := hw i k hik hi hk
  have hp : 0 ≤ u i * u k := mul_nonneg (hu0 i) (hu0 k)
  nlinarith

end Szkraw
