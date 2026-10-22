import Szkraw.ErrorNorm
import Szkraw.RecurrenceNorm
import Szkraw.FiniteRealization
import Szkraw.Krawtchouk

/-!
# Lemma 7.5 (Stability of a reference with a margin)

The proof of Theorem 5.3 with `N` replaced by `M` and the lower bound `1/N` for the upward
coefficients replaced by `α`: the subtracted recurrences give `e_{m+1} ≤ (4e_m + 2e_{m-1} + 12η)/α`,
hence `e_m ≤ η (8/α)^m`.
-/

open scoped Matrix.Norms.Operator

namespace Szkraw

/-- Scalar amplification with `L = 8/α`. -/
theorem amplification_general (M : ℕ) (η α : ℝ) (e : ℕ → ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    (hη : 0 ≤ η) (he0 : e 0 = 0) (he1 : e 1 ≤ 3 * η)
    (hrec : ∀ m, 1 ≤ m → m < M → α * e (m + 1) ≤ 4 * e m + 2 * e (m - 1) + 12 * η) :
    ∀ m, 1 ≤ m → m ≤ M → e m ≤ η * (8 / α) ^ m := by
  set L := 8 / α with hL
  have hL8 : 8 ≤ L := by rw [hL, le_div_iff₀ hα]; linarith
  have hL1 : 1 ≤ L := by linarith
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hm hmM
    rcases Nat.lt_or_ge m 2 with h | h
    · have : m = 1 := by omega
      subst this
      calc e 1 ≤ 3 * η := he1
        _ ≤ η * L := by nlinarith
        _ = η * L ^ 1 := by rw [pow_one]
    · obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      have hr := hrec k (by omega) (by omega)
      have hk := ih k (by omega) (by omega) (by omega)
      have hk1 : e (k - 1) ≤ η * L ^ (k - 1) := by
        rcases Nat.eq_zero_or_pos (k - 1) with h0 | h0
        · rw [h0, he0, pow_zero, mul_one]; exact hη
        · exact ih (k - 1) (by omega) h0 (by omega)
      have hpow : L ^ k = L * L ^ (k - 1) := by
        rw [← pow_succ']; congr 1; omega
      have hp1 : 1 ≤ L ^ (k - 1) := one_le_pow₀ hL1
      -- `4L^k + 2L^{k-1} + 12 ≤ 8L^k`
      have key : 4 * L ^ k + 2 * L ^ (k - 1) + 12 ≤ 8 * L ^ k := by
        rw [hpow]; nlinarith
      have hαL : α * L = 8 := by rw [hL]; field_simp
      have : α * e (k + 1) ≤ α * (η * L ^ (k + 1)) := by
        calc α * e (k + 1) ≤ 4 * e k + 2 * e (k - 1) + 12 * η := hr
          _ ≤ 4 * (η * L ^ k) + 2 * (η * L ^ (k - 1)) + 12 * η := by nlinarith
          _ = η * (4 * L ^ k + 2 * L ^ (k - 1) + 12) := by ring
          _ ≤ η * (8 * L ^ k) := by nlinarith
          _ = α * (η * L ^ (k + 1)) := by rw [pow_succ, ← hαL]; ring
      exact le_of_mul_le_mul_left this hα

/-- **Lemma 7.5** (Stability of a reference with a margin). -/
def Stmt_stability : Prop :=
  ∀ (M : ℕ) (v w : Coefficients M) (α δ η : ℝ) (Sig : ℕ → ℕ → ℕ → Prop),
    Admissible v → MatrixPositivity v → 0 < α → α ≤ 1 → (∀ i, i < M → α ≤ v.a i) →
    0 < δ → (∀ m, m ≤ M → ∀ n k : Fin (M + 1), Sig m n k → δ ≤ productMatrix v m n k) →
    Admissible w → (∀ i, i ≤ M → 0 ≤ w.b i) →
    (∀ i, i ≤ M → |w.a i - v.a i| ≤ η ∧ |w.b i - v.b i| ≤ η ∧ |w.c i - v.c i| ≤ η) →
    η ≤ α / 2 → η * (8 / α) ^ M ≤ δ / 2 →
    (∀ m, m ≤ M → ∀ n k : Fin (M + 1), |productMatrix w m n k - productMatrix v m n k| ≤ δ / 2) ∧
    (∀ m, m ≤ M → ∀ n k : Fin (M + 1), Sig m n k → δ / 2 ≤ productMatrix w m n k)

theorem stability : Stmt_stability := by
  intro M v w α δ η Sig hv hpos hα hα1 hαa hδ hSig hw hwb hcoeff hη hηδ
  have hη0 : 0 ≤ η := le_trans (abs_nonneg _) (hcoeff 0 (by omega)).1
  have hB : ∀ i, i ≤ M → ‖productMatrix v i‖ ≤ 1 := fun i hi =>
    stochastic_norm_le _ (hpos i hi) (fun j => product_row_sum v hv i hi j)
  have hJ : ‖recurrenceMatrix w‖ ≤ 1 := admissible_recurrence_norm w hw hwb
  have hJdiff : ‖recurrenceMatrix w - recurrenceMatrix v‖ ≤ 3 * η :=
    recurrence_difference_norm v w η hη0 hcoeff
  let e : ℕ → ℝ := fun i => ‖productMatrix w i - productMatrix v i‖
  have he0 : e 0 = 0 := by simp [e, productMatrix, matrixPair]
  have hprod1 (z : Coefficients M) (hz : Admissible z) : productMatrix z 1 = recurrenceMatrix z := by
    simp [productMatrix, matrixPair, hz.2.1, hz.2.2.1, hz.2.2.2.1]
  have he1 : e 1 ≤ 3 * η := by simpa only [e, hprod1 v hv, hprod1 w hw] using hJdiff
  have hrec : ∀ i, 1 ≤ i → i < M → α * e (i + 1) ≤ 4 * e i + 2 * e (i - 1) + 12 * η := by
    intro i hi hiM
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0)
    have hsb := admissible_sign_bounds w hw hwb (k + 1) (by omega)
    have hh := product_difference_norm v w hv hw k hiM η hη0 hJ hJdiff
      (hwb (k + 1) (by omega)) hsb.2.2.1 hsb.2.2.2
      (hcoeff (k + 1) (by omega)).1 (hcoeff (k + 1) (by omega)).2.1 (hcoeff (k + 1) (by omega)).2.2
      (hB (k + 1) (by omega)) (hB k (by omega)) (hB (k + 2) (by omega))
    have hwa : α / 2 ≤ w.a (k + 1) := by
      have h1 := hαa (k + 1) hiM
      have h2 := (abs_le.mp (hcoeff (k + 1) (by omega)).1).1
      linarith
    change α * e (k + 2) ≤ _
    have he2 : 0 ≤ e (k + 2) := norm_nonneg _
    calc α * e (k + 2) ≤ 2 * (w.a (k + 1) * e (k + 2)) := by nlinarith
      _ ≤ 2 * (2 * e (k + 1) + e k + 6 * η) := by dsimp [e]; linarith
      _ = _ := by simp only [Nat.succ_sub_one]; ring
  have hamp := amplification_general M η α e hα hα1 hη0 he0 he1 hrec
  have herr : ∀ m, m ≤ M → ∀ n k : Fin (M + 1),
      |productMatrix w m n k - productMatrix v m n k| ≤ δ / 2 := by
    intro m hm n k
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · subst h0; simp only [productMatrix, matrixPair, sub_self, abs_zero]; linarith
    · have hentry := entry_le_row_norm (productMatrix w m - productMatrix v m) n k
      simp only [Matrix.sub_apply] at hentry
      have hL1 : 1 ≤ 8 / α := by rw [le_div_iff₀ hα]; linarith
      have hp := pow_le_pow_right₀ hL1 hm
      calc _ ≤ e m := hentry
        _ ≤ η * (8 / α) ^ m := hamp m h0 hm
        _ ≤ η * (8 / α) ^ M := mul_le_mul_of_nonneg_left hp hη0
        _ ≤ δ / 2 := hηδ
  refine ⟨herr, ?_⟩
  intro m hm n k hs
  have h1 := hSig m hm n k hs
  have h2 := (abs_le.mp (herr m hm n k)).1
  linarith

end Szkraw
