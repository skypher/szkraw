import Szkraw.AbelWeights
import Szkraw.NewtonProduct
import Mathlib.Tactic.FieldSimp

/-!
# Theorem 8.16, key inequality: the algebra in the ratio variables `P`

With `Lin(P) = Σ_k l_k P_k`, `Quad(P) = Σ_{k,m} q_{km} P_k P_m`, `Δc(P) = Σ_m δ_m P_m` and
`Φ = Δc·Lin - F·Quad`, the key `Key = Lin - Quad` equals `(1 - Δc/F) Lin + Φ/F`; and `Φ` has the matrix
`M_{k,m} = β'_k E¹_m + β_k E²_m + [k ≤ 1] D E³_m`. The Abel argument in `P`: `Σ M_{k,m} P_k P_m ≥ 0`
when every central sum of every anti-diagonal is `≥ 0` and `P` is log-concave without internal zeros.
-/

namespace Szkraw

open Finset

/-- Reduction (i): `Key = Lin - Quad ≥ 0` from `Lin ≥ 0`, `Φ = Δc Lin - F Quad ≥ 0` and `Δc ≤ F`. -/
theorem key_of_phi {Lin Quad Dc F : ℝ} (hF : 0 < F) (hLin : 0 ≤ Lin) (hDc : Dc ≤ F)
    (hPhi : 0 ≤ Dc * Lin - F * Quad) : 0 ≤ Lin - Quad := by
  have e : Lin - Quad = (1 - Dc / F) * Lin + (Dc * Lin - F * Quad) / F := by field_simp; ring
  rw [e]
  have h1 : 0 ≤ 1 - Dc / F := by rw [sub_nonneg, div_le_one hF]; exact hDc
  exact add_nonneg (mul_nonneg h1 hLin) (div_nonneg hPhi hF.le)

/-- The matrix of `Φ` (abstract coefficients). -/
theorem phi_matrix (a : ℕ) (P β β' χ χ' δ ζ ν : ℕ → ℝ) (X X' F D Hs : ℝ) :
    (∑ m ∈ range (a + 1), δ m * P m) *
        (∑ k ∈ range (a + 1), (X * β' k + X' * β k - 4 * (if k ≤ 1 then 1 else 0) * D * Hs) * P k) -
      F * (∑ k ∈ range (a + 1), ∑ m ∈ range (a + 1),
        (β' k * χ m + β k * χ' m - (if k ≤ 1 then 1 else 0) * D * (4 * ζ m + 2 * ν m)) * P k * P m) =
    ∑ k ∈ range (a + 1), ∑ m ∈ range (a + 1),
      (β' k * (X * δ m - F * χ m) + β k * (X' * δ m - F * χ' m) +
        (if k ≤ 1 then 1 else 0) * D * (2 * F * ν m - 4 * (Hs * δ m - F * ζ m))) * P k * P m := by
  rw [mul_comm, sum_mul, mul_sum, ← sum_sub_distrib]
  refine sum_congr rfl (fun k _ => ?_)
  rw [mul_sum, mul_sum, ← sum_sub_distrib]
  refine sum_congr rfl (fun m _ => ?_)
  ring

/-- Abel summation over one anti-diagonal of a (not necessarily symmetric) matrix. -/
theorem antidiag_abel {P : ℕ → ℝ} (hP : LCNZ P) (σ : ℕ) (M : ℕ → ℕ → ℝ)
    (hS : ∀ i, 2 * i ≤ σ → 0 ≤ ∑ k ∈ Icc i (σ - i), M k (σ - k)) :
    0 ≤ ∑ k ∈ range (σ + 1), M k (σ - k) * (P k * P (σ - k)) := by
  have hsym : ∀ i ≤ σ, P i * P (σ - i) = P (σ - i) * P (σ - (σ - i)) := by
    intro i hi; rw [Nat.sub_sub_self hi, mul_comm]
  have e : ∑ k ∈ range (σ + 1), M k (σ - k) * (P k * P (σ - k)) =
      ∑ k ∈ range (σ + 1), (P k * P (σ - k)) * M k (σ - k) := sum_congr rfl (fun k _ => mul_comm _ _)
  rw [e, layer_cake σ (fun k => P k * P (σ - k)) (fun k => M k (σ - k)) hsym]
  refine sum_nonneg (fun i hi => mul_nonneg ?_ (hS i (by simp at hi; omega)))
  simp only [mem_range] at hi
  unfold incr
  by_cases h0 : i = 0
  · rw [if_pos h0, sub_zero]; exact mul_nonneg (hP.1 _) (hP.1 _)
  · rw [if_neg h0]
    have := hP.pair_mono (W := σ) (i := i - 1) (by omega)
    rw [show i - 1 + 1 = i by omega] at this
    linarith

/-- **Abel in `P`**: if all central sums of `M` are `≥ 0`, then `Σ_{k,m ≤ a} M_{k,m} P_k P_m ≥ 0`
(with `M` vanishing outside `[0,a]²`). -/
theorem matrix_abel {P : ℕ → ℝ} (hP : LCNZ P) (a : ℕ) (M : ℕ → ℕ → ℝ)
    (hM : ∀ k m, a < k ∨ a < m → M k m = 0)
    (hS : ∀ σ i, 2 * i ≤ σ → 0 ≤ ∑ k ∈ Icc i (σ - i), M k (σ - k)) :
    0 ≤ ∑ k ∈ range (a + 1), ∑ m ∈ range (a + 1), M k m * P k * P m := by
  -- regroup by `σ = k + m`
  have hre : ∑ k ∈ range (a + 1), ∑ m ∈ range (a + 1), M k m * P k * P m =
      ∑ σ ∈ range (2 * a + 1), ∑ k ∈ range (σ + 1), M k (σ - k) * (P k * P (σ - k)) := by
    have hz := pair_reindex (a : ℤ) (fun k m => if 0 ≤ k ∧ 0 ≤ m then M k.toNat m.toNat * P k.toNat * P m.toNat else 0)
      (fun i i' h1 h2 h3 => by
        rw [if_pos ⟨h1, h2⟩, hM i.toNat i'.toNat (by omega)]; ring)
    rw [sum_Icc_zero_eq_range, show 2 * (a : ℤ) = ((2 * a : ℕ) : ℤ) by push_cast; ring, sum_Icc_zero_eq_range] at hz
    simp only [Nat.cast_nonneg, true_and, Int.toNat_natCast] at hz
    rw [show ∑ k ∈ range (a + 1), ∑ m ∈ range (a + 1), M k m * P k * P m =
      ∑ n ∈ range (a + 1), ∑ i' ∈ Icc (0 : ℤ) a,
        (if 0 ≤ i' then M n i'.toNat * P n * P i'.toNat else 0) from ?_]
    · rw [hz]
      refine sum_congr rfl (fun σ hσ => ?_)
      rw [sum_Icc_zero_eq_range]
      refine sum_congr rfl (fun k hk => ?_)
      simp only [mem_range] at hk
      rw [if_pos (by omega), show ((σ : ℤ) - (k : ℤ)).toNat = σ - k by omega]
      simp only [Int.toNat_natCast]
      ring
    · refine sum_congr rfl (fun n _ => ?_)
      rw [sum_Icc_zero_eq_range]
      exact sum_congr rfl (fun m _ => by simp)
  rw [hre]
  exact sum_nonneg (fun σ _ => antidiag_abel hP σ M (hS σ))

end Szkraw
