import Szkraw.ColumnCheck
import Szkraw.CubicLeib

/-!
# P2, Section 6: counterexamples with increasing ratios on the linear profile

Each example is an array with linear profile `d_i = i/N` and ratio `ρ_i = c_i/d_i`. The statement says that the
array exists and is admissible, and that every admissible array with this profile and ratio has nondecreasing `b`
and a negative coefficient `g(m,n;k)`. The negative coefficient is decided by an exact column of the product
table, evaluated in the kernel (`ColCheck.ratio_example`).
-/

namespace Szkraw

open Finset ColCheck

/-! ### Newton coefficients of the ratios -/

theorem newtonCoeff_const_geom (c s x : ℝ) (k : ℕ) :
    newtonCoeff (fun i => c + s * x ^ i) k = c * 0 ^ k + s * (x - 1) ^ k := by
  have h1 : ∑ i ∈ range (k + 1), (-1 : ℝ) ^ (k - i) * (k.choose i : ℝ) = 0 ^ k := by
    have := (add_pow (1 : ℝ) (-1) k).symm
    rw [show (1 : ℝ) + -1 = 0 by ring] at this
    rw [← this]
    exact Finset.sum_congr rfl fun i _ => by ring
  have h2 : ∑ i ∈ range (k + 1), (-1 : ℝ) ^ (k - i) * (k.choose i : ℝ) * x ^ i = (x - 1) ^ k := by
    rw [sub_eq_add_neg, add_pow]
    exact Finset.sum_congr rfl fun i _ => by ring
  unfold newtonCoeff
  simp only [mul_add, Finset.sum_add_distrib]
  rw [← Finset.sum_mul, h1, show ∑ i ∈ range (k + 1), (-1 : ℝ) ^ (k - i) * (k.choose i : ℝ) * (s * x ^ i) =
    s * ∑ i ∈ range (k + 1), (-1 : ℝ) ^ (k - i) * (k.choose i : ℝ) * x ^ i by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring, h2]
  ring

theorem newtonCoeff_top (r κ : ℝ) (N k : ℕ) (hk : k ≤ N) :
    newtonCoeff (fun i => r + κ * if i = N then 1 else 0) k = r * 0 ^ k + if k = N then κ else 0 := by
  have h := newtonCoeff_const_geom r 0 0 k
  simp only [zero_mul, add_zero] at h
  unfold newtonCoeff at h ⊢
  simp only [mul_add, Finset.sum_add_distrib, h]
  congr 1
  split_ifs with hkN
  · subst hkN
    rw [Finset.sum_eq_single k (fun i hi hik => by simp [hik]) (by simp)]
    simp
  · exact Finset.sum_eq_zero fun i hi => by
      have : i ≠ N := by simp at hi; omega
      simp [this]

/-! ### The examples -/

/-- **P2, Section 6, cubic ratio with `t = τ = 0`.** For `N = 48`, the linear profile and
`ρ_i = 9/10 + κ C(i,3)/C(N,3)` with `κ = 1/80`: `b` is nondecreasing and `g(48,48;48) < 0`. -/
theorem cubicBinom48_fails :
    let d : ℕ → ℝ := fun i => i / 48
    let ρ : ℕ → ℝ := fun i => 9 / 10 + 1 / 80 * (i.choose 3 : ℝ) / (Nat.choose 48 3 : ℝ)
    (∃ v : Coefficients 48, Admissible v ∧ (∀ i, i ≤ 48 → profile v i = d i) ∧
      ∀ i, i ≤ 48 → v.c i = ρ i * profile v i) ∧
    ∀ v : Coefficients 48, Admissible v → (∀ i, i ≤ 48 → profile v i = d i) →
      (∀ i, i ≤ 48 → v.c i = ρ i * profile v i) →
      (∀ i, i < 48 → v.b i ≤ v.b (i + 1)) ∧ productMatrix v 48 48 48 < 0 :=
  ratio_example (fun i => i) (fun i => 720 * (Nat.choose 48 3 : ℤ) + 10 * (i.choose 3 : ℤ))
    (800 * (Nat.choose 48 3 : ℤ)) 48 _ _ (by norm_num) (by decide +kernel) rfl (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (fun i _ => by push_cast; ring)
    (fun i _ => by
      have h : (Nat.choose 48 3 : ℝ) = 17296 := by norm_num [Nat.choose]
      push_cast; rw [h]; field_simp; ring) (by decide +kernel) 48 48 48 le_rfl (by norm_num)
    (by norm_num) (by decide +kernel)

/-- **P2, Section 6, cubic ratio `9/10 + κ (i/N)³`.** For `N = 64`, the linear profile and
`ρ_i = 9/10 + κ (i/N)³` with `κ = 1/80`: `b` is nondecreasing and `g(64,64;63) < 0`. In the binomial basis
`ρ(x) = r + t x + τ C(x,2) + σ C(x,3)` with `r = 9/10`, `t = κ/N³`, `τ = σ = 6κ/N³`, and `t τ < r σ`. -/
theorem cubicPow64_fails :
    let d : ℕ → ℝ := fun i => i / 64
    let ρ : ℕ → ℝ := fun i => 9 / 10 + 1 / 80 * ((i : ℝ) / 64) ^ 3
    ((∃ v : Coefficients 64, Admissible v ∧ (∀ i, i ≤ 64 → profile v i = d i) ∧
      ∀ i, i ≤ 64 → v.c i = ρ i * profile v i) ∧
    ∀ v : Coefficients 64, Admissible v → (∀ i, i ≤ 64 → profile v i = d i) →
      (∀ i, i ≤ 64 → v.c i = ρ i * profile v i) →
      (∀ i, i < 64 → v.b i ≤ v.b (i + 1)) ∧ productMatrix v 64 64 63 < 0) ∧
    (∀ i : ℕ, ρ i = 9 / 10 + 1 / 80 / 64 ^ 3 * i + 6 / 80 / 64 ^ 3 * (i.choose 2 : ℝ) +
      6 / 80 / 64 ^ 3 * (i.choose 3 : ℝ)) ∧
    (1 / 80 / 64 ^ 3 : ℝ) * (6 / 80 / 64 ^ 3) < 9 / 10 * (6 / 80 / 64 ^ 3) := by
  refine ⟨ratio_example (fun i => i) (fun i => 720 * 64 ^ 3 + 10 * (i : ℤ) ^ 3) (800 * 64 ^ 3) 64 _ _
    (by norm_num) (by decide +kernel) rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (fun i _ => by push_cast; ring) (fun i _ => by push_cast; field_simp; ring) (by decide +kernel)
    64 64 63 le_rfl (by norm_num) (by norm_num) (by decide +kernel), fun i => ?_, by norm_num⟩
  rw [choose2_real, choose3_real]
  ring

/-- **P2, Section 6, steep ratio.** For `N = 40`, the linear profile and `ρ_i = 1/2 + 10^(i-N)/100`: the Newton
coefficients of `ρ` are nonnegative, `b` is nondecreasing and `g(40,40;40) < 0`. -/
theorem steepRatio40_fails :
    let d : ℕ → ℝ := fun i => i / 40
    let ρ : ℕ → ℝ := fun i => 1 / 2 + (10 : ℝ) ^ ((i : ℤ) - 40) / 100
    (∀ k, 0 ≤ newtonCoeff ρ k) ∧
    (∃ v : Coefficients 40, Admissible v ∧ (∀ i, i ≤ 40 → profile v i = d i) ∧
      ∀ i, i ≤ 40 → v.c i = ρ i * profile v i) ∧
    ∀ v : Coefficients 40, Admissible v → (∀ i, i ≤ 40 → profile v i = d i) →
      (∀ i, i ≤ 40 → v.c i = ρ i * profile v i) →
      (∀ i, i < 40 → v.b i ≤ v.b (i + 1)) ∧ productMatrix v 40 40 40 < 0 := by
  have hρ : ∀ i : ℕ, (1 / 2 + (10 : ℝ) ^ ((i : ℤ) - 40) / 100) = 1 / 2 + 1 / 10 ^ 42 * 10 ^ i := fun i => by
    rw [zpow_sub₀ (by norm_num), zpow_natCast]; ring
  refine ⟨fun k => ?_, ratio_example (fun i => i) (fun i => 10 ^ 42 + 2 * 10 ^ i) (2 * 10 ^ 42) 40 _ _
    (by norm_num) (by decide +kernel) rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (fun i _ => by push_cast; ring) (fun i _ => by rw [hρ]; push_cast; field_simp; ring) (by decide +kernel)
    40 40 40 le_rfl (by norm_num) (by norm_num) (by decide +kernel)⟩
  simp only [hρ]
  rw [newtonCoeff_const_geom]
  positivity

/-- **P2, Section 6, raising only the last ratio, `N = 40`.** For the linear profile, `r = 1/2`, `ρ_i = r` for
`i < N` and `ρ_N = r + (1-r)/N`: the Newton coefficients of `ρ` on `0 ≤ k ≤ N` are nonnegative, `b` is
nondecreasing and `g(40,40;38) < 0`. -/
theorem topRatio40_fails :
    let d : ℕ → ℝ := fun i => i / 40
    let ρ : ℕ → ℝ := fun i => 1 / 2 + (1 - 1 / 2) / 40 * if i = 40 then 1 else 0
    (∀ k, k ≤ 40 → 0 ≤ newtonCoeff ρ k) ∧
    (∃ v : Coefficients 40, Admissible v ∧ (∀ i, i ≤ 40 → profile v i = d i) ∧
      ∀ i, i ≤ 40 → v.c i = ρ i * profile v i) ∧
    ∀ v : Coefficients 40, Admissible v → (∀ i, i ≤ 40 → profile v i = d i) →
      (∀ i, i ≤ 40 → v.c i = ρ i * profile v i) →
      (∀ i, i < 40 → v.b i ≤ v.b (i + 1)) ∧ productMatrix v 40 40 38 < 0 := by
  refine ⟨fun k hk => ?_, ratio_example (fun i => i) (fun i => if i = 40 then 41 else 40) 80 40 _ _
    (by norm_num) (by decide +kernel) rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (fun i _ => by push_cast; ring) (fun i _ => by split_ifs <;> norm_num) (by decide +kernel)
    40 40 38 le_rfl (by norm_num) (by norm_num) (by decide +kernel)⟩
  rw [newtonCoeff_top _ _ 40 k hk]
  split_ifs <;> positivity

/-- **P2, Section 6, raising only the last ratio, `N = 120`** (the convex kinked ratio at `N = 120`). For the
linear profile, `r = 2/5`, `ρ_i = r` for `i < N` and `ρ_N = r + (1-r)/N`: the Newton coefficients of `ρ` on
`0 ≤ k ≤ N` are nonnegative, `b` is nondecreasing and `g(120,120;119) < 0`. -/
theorem topRatio120_fails :
    let d : ℕ → ℝ := fun i => i / 120
    let ρ : ℕ → ℝ := fun i => 2 / 5 + (1 - 2 / 5) / 120 * if i = 120 then 1 else 0
    (∀ k, k ≤ 120 → 0 ≤ newtonCoeff ρ k) ∧
    (∃ v : Coefficients 120, Admissible v ∧ (∀ i, i ≤ 120 → profile v i = d i) ∧
      ∀ i, i ≤ 120 → v.c i = ρ i * profile v i) ∧
    ∀ v : Coefficients 120, Admissible v → (∀ i, i ≤ 120 → profile v i = d i) →
      (∀ i, i ≤ 120 → v.c i = ρ i * profile v i) →
      (∀ i, i < 120 → v.b i ≤ v.b (i + 1)) ∧ productMatrix v 120 120 119 < 0 := by
  refine ⟨fun k hk => ?_, ratio_example (fun i => i) (fun i => if i = 120 then 81 else 80) 200 120 _ _
    (by norm_num) (by decide +kernel) rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (fun i _ => by push_cast; ring) (fun i _ => by split_ifs <;> norm_num) (by decide +kernel)
    120 120 119 le_rfl (by norm_num) (by norm_num) (by decide +kernel)⟩
  rw [newtonCoeff_top _ _ 120 k hk]
  split_ifs <;> positivity

end Szkraw
