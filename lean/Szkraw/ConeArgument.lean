import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Szwarc's cone argument on a finite square (paper, Theorems 7.10 and 7.12)

For coefficients `α, β, γ` let `(Hu)(i,j)` be the difference of the two three-term actions
`α_{i+1}u(i+1,j) + β_i u(i,j) + γ_{i-1}u(i-1,j)` and the same in `j`. If `Hu = 0` on
`{0,…,N}²`, `u` vanishes outside that square, `u` is symmetric with `u(·,0) ≥ 0`, and the
coefficients satisfy the monotonicity and edge hypotheses of Theorem 7.12, then `u ≥ 0`.
The proof pairs `Hu = 0` with the indicator of the cone `D(n,m)` and transposes.
-/

namespace Szkraw

open Finset

section cone

variable (α β γ : ℕ → ℝ)

/-- `(Hu)(i,j)`. -/
noncomputable def Hop (u : ℕ → ℕ → ℝ) (i j : ℕ) : ℝ :=
  (α (i + 1) * u (i + 1) j + β i * u i j + (if 1 ≤ i then γ (i - 1) * u (i - 1) j else 0)) -
  (α (j + 1) * u i (j + 1) + β j * u i j + (if 1 ≤ j then γ (j - 1) * u i (j - 1) else 0))

/-- The transpose `(H^*v)(i,j)`. -/
noncomputable def Hadj (v : ℕ → ℕ → ℝ) (i j : ℕ) : ℝ :=
  ((if 1 ≤ i then α i * v (i - 1) j else 0) + γ i * v (i + 1) j + β i * v i j) -
  ((if 1 ≤ j then α j * v i (j - 1) else 0) + γ j * v i (j + 1) + β j * v i j)

theorem by_parts_1d (B : ℕ) (hB : 1 ≤ B) (f g : ℕ → ℝ) (hg1 : g (B - 1) = 0) (hg2 : g B = 0) :
    ∑ i ∈ range B, (α (i + 1) * f (i + 1) + β i * f i +
        (if 1 ≤ i then γ (i - 1) * f (i - 1) else 0)) * g i =
      ∑ i ∈ range B, f i * ((if 1 ≤ i then α i * g (i - 1) else 0) + γ i * g (i + 1) + β i * g i) := by
  obtain ⟨B', rfl⟩ : ∃ B', B = B' + 1 := ⟨B - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at hg1
  simp only [add_mul, mul_add, sum_add_distrib]
  have t1 : ∑ i ∈ range (B' + 1), α (i + 1) * f (i + 1) * g i =
      ∑ i ∈ range (B' + 1), f i * (if 1 ≤ i then α i * g (i - 1) else 0) := by
    rw [sum_range_succ, hg1, mul_zero, add_zero, sum_range_succ' (fun i => f i * _)]
    simp only [show ¬(1 ≤ 0) by omega, if_false, mul_zero, add_zero]
    apply sum_congr rfl; intro i _
    rw [if_pos (by omega), Nat.add_sub_cancel]; ring
  have t3 : ∑ i ∈ range (B' + 1), (if 1 ≤ i then γ (i - 1) * f (i - 1) else 0) * g i =
      ∑ i ∈ range (B' + 1), f i * (γ i * g (i + 1)) := by
    rw [sum_range_succ' (fun i => (if 1 ≤ i then γ (i - 1) * f (i - 1) else 0) * g i),
      sum_range_succ (fun i => f i * (γ i * g (i + 1))), hg2]
    simp only [show ¬(1 ≤ 0) by omega, if_false, zero_mul, add_zero, mul_zero]
    apply sum_congr rfl; intro i _
    rw [if_pos (by omega), Nat.add_sub_cancel]; ring
  rw [t1, t3]
  have t2 : ∑ i ∈ range (B' + 1), β i * f i * g i = ∑ i ∈ range (B' + 1), f i * (β i * g i) :=
    sum_congr rfl (fun i _ => by ring)
  rw [t2]; ring

theorem by_parts (B : ℕ) (hB : 1 ≤ B) (u v : ℕ → ℕ → ℝ)
    (hv : ∀ i j, B ≤ i + 1 ∨ B ≤ j + 1 → v i j = 0) :
    ∑ i ∈ range B, ∑ j ∈ range B, Hop α β γ u i j * v i j =
      ∑ i ∈ range B, ∑ j ∈ range B, u i j * Hadj α β γ v i j := by
  unfold Hop Hadj
  simp only [sub_mul, mul_sub, sum_sub_distrib]
  congr 1
  · -- the `i`-direction: swap the sums and transpose in `i`
    rw [sum_comm, sum_comm (s := range B) (t := range B)
      (f := fun i j => u i j * ((if 1 ≤ i then α i * v (i - 1) j else 0) + γ i * v (i + 1) j +
        β i * v i j))]
    apply sum_congr rfl; intro j _
    exact by_parts_1d α β γ B hB (fun i => u i j) (fun i => v i j) (hv _ _ (Or.inl (by omega)))
      (hv _ _ (Or.inl (by omega)))
  · apply sum_congr rfl; intro i _
    exact by_parts_1d α β γ B hB (fun j => u i j) (fun j => v i j) (hv _ _ (Or.inr (by omega)))
      (hv _ _ (Or.inr (by omega)))

/-- Indicator of the cone `D(n,m)`: `j < m`, `|i - n| < m - j`, `n + m - i - j` odd. -/
noncomputable def vD (n m i j : ℕ) : ℝ :=
  if j < m ∧ n + j < i + m ∧ i + j < n + m ∧ (n + m - i - j) % 2 = 1 then 1 else 0

theorem vD_pos {n m i j : ℕ} (h : j < m ∧ n + j < i + m ∧ i + j < n + m ∧ (n + m - i - j) % 2 = 1) :
    vD n m i j = 1 := if_pos h

theorem vD_zero {n m i j : ℕ} (h : ¬(j < m ∧ n + j < i + m ∧ i + j < n + m ∧ (n + m - i - j) % 2 = 1)) :
    vD n m i j = 0 := if_neg h

/-- Hypotheses of Theorem 7.12 on the coefficients `α, β, γ` over `{0,…,N}`. -/
structure ConeHyp (N : ℕ) : Prop where
  α_nonneg : ∀ i, i ≤ N → 0 ≤ α i
  γ_nonneg : ∀ i, i ≤ N → 0 ≤ γ i
  β_mono : ∀ j i, j ≤ i → i ≤ N → β j ≤ β i
  α_mono : ∀ j i, j ≤ i → i ≤ N → α j ≤ α i
  αγ_mono : ∀ j i, j ≤ i → i ≤ N → α j + γ j ≤ α i + γ i
  edge : ∀ j i, j ≤ i → i + 1 ≤ N → α j ≤ γ i

variable {α β γ}

/-- `H^*v ≥ 0` away from the apex, inside the square. -/
theorem Hadj_vD_nonneg {N : ℕ} (h : ConeHyp α β γ N) {n m i j : ℕ} (hn : n ≤ N) (hmn : m ≤ n)
    (hi : i ≤ N) (hne : ¬(i = n ∧ j = m)) : 0 ≤ Hadj α β γ (vD n m) i j := by
  unfold Hadj
  by_cases hD : j < m ∧ n + j < i + m ∧ i + j < n + m ∧ (n + m - i - j) % 2 = 1
  · -- a point of the cone: its neighbours have the other parity
    have e1 : (if 1 ≤ i then α i * vD n m (i - 1) j else 0) = 0 := by
      split_ifs
      · rw [vD_zero (i := i - 1) (j := j) (by omega), mul_zero]
      · rfl
    have e2 : (if 1 ≤ j then α j * vD n m i (j - 1) else 0) = 0 := by
      split_ifs
      · rw [vD_zero (i := i) (j := j - 1) (by omega), mul_zero]
      · rfl
    rw [e1, e2, vD_pos hD, vD_zero (i := i + 1) (j := j) (by omega),
      vD_zero (i := i) (j := j + 1) (by omega)]
    have := h.β_mono j i (by omega) hi
    linarith
  rw [vD_zero hD]
  have hα := h.α_nonneg i hi
  have hγ := h.γ_nonneg i hi
  by_cases hE : j + 1 < m ∧ n + (j + 1) < i + m ∧ i + (j + 1) < n + m ∧ (n + m - i - (j + 1)) % 2 = 1
  · -- interior or bottom: both horizontal neighbours lie in the cone
    rw [vD_pos hE, if_pos (by omega : 1 ≤ i), vD_pos (by omega), vD_pos (by omega)]
    by_cases hj : 1 ≤ j
    · rw [if_pos hj, vD_pos (by omega)]
      have := h.αγ_mono j i (by omega) hi
      linarith
    · rw [if_neg hj]
      have := h.αγ_mono 0 i (by omega) hi
      have := h.α_nonneg 0 (by omega)
      have hj0 : j = 0 := by omega
      subst hj0
      linarith
  rw [vD_zero hE]
  by_cases hC : 1 ≤ j ∧ j - 1 < m ∧ n + (j - 1) < i + m ∧ i + (j - 1) < n + m ∧
      (n + m - i - (j - 1)) % 2 = 1
  · rw [if_pos hC.1, vD_pos hC.2]
    by_cases hA : 1 ≤ i ∧ j < m ∧ n + j < (i - 1) + m ∧ (i - 1) + j < n + m ∧
        (n + m - (i - 1) - j) % 2 = 1
    · -- upper edge: `α_i - α_j ≥ 0`
      rw [if_pos hA.1, vD_pos hA.2]
      have := h.α_mono j i (by omega) hi
      have hB : 0 ≤ γ i * vD n m (i + 1) j := by
        unfold vD; split_ifs <;> nlinarith
      linarith
    · -- lower edge: `γ_i - α_j ≥ 0`, with `i ≤ n - 1`
      have hB : j < m ∧ n + j < (i + 1) + m ∧ (i + 1) + j < n + m ∧
          (n + m - (i + 1) - j) % 2 = 1 := by omega
      rw [vD_pos hB]
      have := h.edge j i (by omega) (by omega)
      have hA0 : 0 ≤ (if 1 ≤ i then α i * vD n m (i - 1) j else 0) := by
        split_ifs
        · unfold vD; split_ifs <;> nlinarith
        · exact le_refl 0
      linarith
  · have hC0 : (if 1 ≤ j then α j * vD n m i (j - 1) else 0) = 0 := by
      split_ifs with hj
      · rw [vD_zero (by omega), mul_zero]
      · rfl
    rw [hC0]
    have hA0 : 0 ≤ (if 1 ≤ i then α i * vD n m (i - 1) j else 0) := by
      split_ifs
      · unfold vD; split_ifs <;> nlinarith
      · exact le_refl 0
    have hB : 0 ≤ γ i * vD n m (i + 1) j := by
      unfold vD; split_ifs <;> nlinarith
    linarith

/-- `H^*v` vanishes at points with `j ≥ m` or `i < j`, other than the apex. -/
theorem Hadj_vD_zero {n m i j : ℕ} (hmn : m ≤ n) (hne : ¬(i = n ∧ j = m)) (h : m ≤ j ∨ i < j) :
    Hadj α β γ (vD n m) i j = 0 := by
  unfold Hadj
  have e1 : (if 1 ≤ i then α i * vD n m (i - 1) j else 0) = 0 := by
    split_ifs
    · rw [vD_zero (i := i - 1) (j := j) (by omega), mul_zero]
    · rfl
  have e2 : (if 1 ≤ j then α j * vD n m i (j - 1) else 0) = 0 := by
    split_ifs
    · rw [vD_zero (i := i) (j := j - 1) (by omega), mul_zero]
    · rfl
  rw [e1, e2, vD_zero (i := i) (j := j) (by omega), vD_zero (i := i + 1) (j := j) (by omega),
    vD_zero (i := i) (j := j + 1) (by omega)]
  ring

/-- At the apex, `H^*v = -α_m`. -/
theorem Hadj_vD_apex {n m : ℕ} (hm : 1 ≤ m) : Hadj α β γ (vD n m) n m = -α m := by
  unfold Hadj
  have e1 : (if 1 ≤ n then α n * vD n m (n - 1) m else 0) = 0 := by
    split_ifs
    · rw [vD_zero (i := n - 1) (j := m) (by omega), mul_zero]
    · rfl
  rw [e1, if_pos hm, vD_pos (i := n) (j := m - 1) (by omega), vD_zero (i := n) (j := m) (by omega),
    vD_zero (i := n + 1) (j := m) (by omega), vD_zero (i := n) (j := m + 1) (by omega)]
  ring

/-- **Cone argument.** -/
theorem cone_nonneg {N : ℕ} (h : ConeHyp α β γ N) (hγN : γ N = 0)
    (hαpos : ∀ m, 1 ≤ m → m ≤ N → 0 < α m) (u : ℕ → ℕ → ℝ)
    (hout : ∀ i j, N < i ∨ N < j → u i j = 0) (hH : ∀ i j, i ≤ N → j ≤ N → Hop α β γ u i j = 0)
    (hsym : ∀ i j, u i j = u j i) (h0 : ∀ i, 0 ≤ u i 0) : ∀ n m, 0 ≤ u n m := by
  -- `Hu = 0` everywhere
  have hHall : ∀ i j, Hop α β γ u i j = 0 := by
    intro i j
    by_cases hin : i ≤ N ∧ j ≤ N
    · exact hH i j hin.1 hin.2
    unfold Hop
    have z : ∀ a b, N < a ∨ N < b → u a b = 0 := hout
    by_cases hi : N < i
    · rw [z i j (Or.inl hi), z (i + 1) j (Or.inl (by omega)), z i (j + 1) (Or.inl hi)]
      have e1 : (if 1 ≤ i then γ (i - 1) * u (i - 1) j else 0) = 0 := by
        rw [if_pos (by omega)]
        by_cases hi1 : i = N + 1
        · subst hi1; rw [Nat.add_sub_cancel, hγN, zero_mul]
        · rw [z (i - 1) j (Or.inl (by omega)), mul_zero]
      have e2 : (if 1 ≤ j then γ (j - 1) * u i (j - 1) else 0) = 0 := by
        split_ifs
        · rw [z i (j - 1) (Or.inl hi), mul_zero]
        · rfl
      rw [e1, e2]; ring
    · have hj : N < j := by omega
      rw [z i j (Or.inr hj), z i (j + 1) (Or.inr (by omega)), z (i + 1) j (Or.inr hj)]
      have e1 : (if 1 ≤ j then γ (j - 1) * u i (j - 1) else 0) = 0 := by
        rw [if_pos (by omega)]
        by_cases hj1 : j = N + 1
        · subst hj1; rw [Nat.add_sub_cancel, hγN, zero_mul]
        · rw [z i (j - 1) (Or.inr (by omega)), mul_zero]
      have e2 : (if 1 ≤ i then γ (i - 1) * u (i - 1) j else 0) = 0 := by
        split_ifs
        · rw [z (i - 1) j (Or.inr hj), mul_zero]
        · rfl
      rw [e1, e2]; ring
  -- induction on the second index, for `n ≥ m`
  have main : ∀ m n, m ≤ n → 0 ≤ u n m := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro n hmn
      rcases Nat.eq_zero_or_pos m with hm0 | hm1
      · subst hm0; exact h0 n
      by_cases hnN : N < n
      · rw [hout n m (Or.inl hnN)]
      push Not at hnN
      set B := 2 * N + 2 with hB
      have hv : ∀ i j, B ≤ i + 1 ∨ B ≤ j + 1 → vD n m i j = 0 := by
        intro i j hij; exact vD_zero (by omega)
      have hsum := by_parts α β γ B (by omega) u (vD n m) hv
      have hz : ∑ i ∈ range B, ∑ j ∈ range B, Hop α β γ u i j * vD n m i j = 0 := by
        apply sum_eq_zero; intro i _; apply sum_eq_zero; intro j _; rw [hHall, zero_mul]
      rw [hz, ← Finset.sum_product'] at hsum
      have hmem : (n, m) ∈ range B ×ˢ range B := by
        simp only [Finset.mem_product, Finset.mem_range]; omega
      rw [← Finset.add_sum_erase _ _ hmem] at hsum
      simp only at hsum
      rw [Hadj_vD_apex hm1] at hsum
      have hrest : 0 ≤ ∑ p ∈ (range B ×ˢ range B).erase (n, m), u p.1 p.2 * Hadj α β γ (vD n m) p.1 p.2 := by
        apply sum_nonneg
        rintro ⟨i, j⟩ hp
        simp only [Finset.mem_erase, ne_eq, Prod.mk.injEq] at hp
        have hne : ¬(i = n ∧ j = m) := hp.1
        by_cases hiN : N < i
        · rw [hout i j (Or.inl hiN), zero_mul]
        push Not at hiN
        by_cases hfar : m ≤ j ∨ i < j
        · rw [Hadj_vD_zero hmn hne hfar, mul_zero]
        push Not at hfar
        exact mul_nonneg (ih j hfar.1 i hfar.2) (Hadj_vD_nonneg h hnN hmn hiN hne)
      have hαm := hαpos m hm1 (by omega)
      have : α m * u n m ≥ 0 := by linarith
      exact nonneg_of_mul_nonneg_right (by linarith) hαm
  intro n m
  rcases le_total m n with hmn | hnm
  · exact main m n hmn
  · rw [hsym]; exact main n m hnm

end cone

end Szkraw
