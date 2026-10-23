import Szkraw.GenMain
import Szkraw.GenKeyAlgebra

/-!
# Theorem 8.16, key inequality: representation in the variables `u = f(ℓ)` and `P = Δρ(ℓ)`

For a base point `ℓ` put `f k = iterShift ν ℓ k` (the `u_k` of the paper) and `p k = iterShift ρc ℓ k`
(the `P_k`). Every weight of the key is a linear form in `p` (or a product of two such forms), with
coefficients that are explicit in `f`, `a`. The definitions below are those coefficients; the core
lemma `key_core` gives `A₀B₀' + B₀A₀' + 2cc V₁ - 4cc H₁ = Lin(p) - Quad(p)`.
-/

set_option linter.unusedSectionVars false

namespace Szkraw

open Finset

/-- Base-point shift: `Δ^k d(ℓ+m) = Σ_i C(m,i) Δ^{k+i} d(ℓ)`. -/
theorem iterShift_base (v : ℕ → ℝ) (ℓ m k : ℕ) :
    iterShift v (ℓ + m) k = ∑ i ∈ range (m + 1), (m.choose i : ℝ) * iterShift v ℓ (k + i) := by
  rw [iterShift_comp v ℓ m, iterShift_eq]

/-- Binomial sums may be taken over any range containing the support. -/
theorem sum_choose_ext {n a : ℕ} (h : n ≤ a) (q : ℕ → ℝ) :
    ∑ k ∈ range (n + 1), (n.choose k : ℝ) * q k = ∑ k ∈ range (a + 1), (n.choose k : ℝ) * q k := by
  apply Finset.sum_subset
  · intro x hx; simp only [mem_range] at hx ⊢; omega
  · intro x _ hx
    simp only [mem_range] at hx
    rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, zero_mul]

/-- Reindexing of the shifted binomial sum: `Σ_i C(m,i) p(1+i) = Σ_k [1 ≤ k] C(m,k-1) p k`. -/
theorem shift_reindex (p : ℕ → ℝ) {m a : ℕ} (h : m < a) :
    ∑ i ∈ range (m + 1), (m.choose i : ℝ) * p (1 + i) =
      ∑ k ∈ range (a + 1), (if 1 ≤ k then (m.choose (k - 1) : ℝ) else 0) * p k := by
  rw [Finset.sum_range_succ' _ a]
  simp only [show ¬ (1 ≤ 0) by omega, if_false, zero_mul, add_zero]
  have hsub : ∑ i ∈ range (m + 1), (m.choose i : ℝ) * p (1 + i) =
      ∑ i ∈ range a, (m.choose i : ℝ) * p (1 + i) := by
    apply Finset.sum_subset
    · intro x hx; simp only [mem_range] at hx ⊢; omega
    · intro x _ hx
      simp only [mem_range] at hx
      rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, zero_mul]
  rw [hsub]
  refine sum_congr rfl (fun k _ => ?_)
  rw [if_pos (by omega), Nat.add_sub_cancel, add_comm]

/-- `(1:ℕ).choose k` as an indicator. -/
theorem choose_one_ind (k : ℕ) : ((1 : ℕ).choose k : ℝ) = if k ≤ 1 then 1 else 0 := by
  rcases k with _ | _ | k
  · simp
  · simp
  · rw [Nat.choose_eq_zero_of_lt (by omega)]; simp

/-- The coefficient of `w₃(n) = C(n-3+1, 1)` weights in `H₁`. -/
noncomputable def wgtH (n : ℕ) : ℝ := if 3 ≤ n then ((n - 3 + 1).choose 1 : ℝ) else 0

/-- `H_* = Σ_n w_n C(a,n) f_n`. -/
noncomputable def Hstar (f : ℕ → ℝ) (a : ℕ) : ℝ :=
  ∑ n ∈ range (a + 1), wgtH n * (a.choose n : ℝ) * f n

/-- `ζ_k`: coefficient of `P_k` in `-H₁ + H_*`. -/
noncomputable def zetaC (f : ℕ → ℝ) (a k : ℕ) : ℝ :=
  ∑ n ∈ range (a + 1), wgtH n * (a.choose n : ℝ) * f n * (n.choose k : ℝ)

/-- `ν_k`: coefficient of `P_k` in `V₁`. -/
noncomputable def nuC (f : ℕ → ℝ) (a k : ℕ) : ℝ :=
  ∑ n ∈ range (a + 1), wgtH n * (a.choose n : ℝ) * ((n : ℝ) * f (n - 1)) *
    (if 1 ≤ k then ((n - 1).choose (k - 1) : ℝ) else 0)

/-- Coefficient of `P_k` in `c_{ℓ+a} - c_ℓ`-type terms: `χ_k = C(a,k) d_{ℓ+a} - C(0,k) d_ℓ`. -/
noncomputable def chiC (f : ℕ → ℝ) (a k : ℕ) : ℝ :=
  (a.choose k : ℝ) * dd f a - ((0 : ℕ).choose k : ℝ) * dd f 0

/-- `χ'_k = C(a-1,k) d_{ℓ+a-1} - C(1,k) d_{ℓ+1}`. -/
noncomputable def chi'C (f : ℕ → ℝ) (a k : ℕ) : ℝ :=
  ((a - 1).choose k : ℝ) * dd f (a - 1) - ((1 : ℕ).choose k : ℝ) * dd f 1

/-- `β_k`: coefficient of `P_k` in `B₀(ℓ,a)`. -/
noncomputable def betaC (f : ℕ → ℝ) (a k : ℕ) : ℝ :=
  (a.choose k : ℝ) * dd f a - ((0 : ℕ).choose k : ℝ) * dd f 0 -
    (a : ℝ) * (((1 : ℕ).choose k : ℝ) * dd f 1 - ((0 : ℕ).choose k : ℝ) * dd f 0)

/-- `β'_k`: coefficient of `P_k` in `B₀(ℓ+1,a-1)`. -/
noncomputable def beta'C (f : ℕ → ℝ) (a k : ℕ) : ℝ :=
  (a.choose k : ℝ) * dd f a + ((a : ℝ) - 2) * ((1 : ℕ).choose k : ℝ) * dd f 1 -
    ((a : ℝ) - 1) * ((2 : ℕ).choose k : ℝ) * dd f 2

/-- `δ_k`: coefficient of `P_k` in `c_{ℓ+a} - c_{ℓ+a-1}`. -/
noncomputable def deltaC (f : ℕ → ℝ) (a k : ℕ) : ℝ :=
  (a.choose k : ℝ) * dd f a - ((a - 1).choose k : ℝ) * dd f (a - 1)

/-- The coefficients of the linear and quadratic parts of the key, and of `Φ`. -/
noncomputable def linC (f : ℕ → ℝ) (a k : ℕ) : ℝ :=
  (dd f a - dd f 0) * beta'C f a k + (dd f (a - 1) - dd f 1) * betaC f a k -
    4 * (if k ≤ 1 then 1 else 0) * dd f 1 * Hstar f a

noncomputable def quadC (f : ℕ → ℝ) (a k m : ℕ) : ℝ :=
  beta'C f a k * chiC f a m + betaC f a k * chi'C f a m -
    (if k ≤ 1 then 1 else 0) * dd f 1 * (4 * zetaC f a m + 2 * nuC f a m)

noncomputable def MC (f : ℕ → ℝ) (a k m : ℕ) : ℝ :=
  beta'C f a k * ((dd f a - dd f 0) * deltaC f a m - (dd f a - dd f (a - 1)) * chiC f a m) +
    betaC f a k * ((dd f (a - 1) - dd f 1) * deltaC f a m - (dd f a - dd f (a - 1)) * chi'C f a m) +
    (if k ≤ 1 then 1 else 0) * dd f 1 *
      (2 * (dd f a - dd f (a - 1)) * nuC f a m -
        4 * (Hstar f a * deltaC f a m - (dd f a - dd f (a - 1)) * zetaC f a m))

/-- The core algebra: with the expansions of the weights in `p`, the key is `Lin - Quad`. -/
theorem key_core (a : ℕ) (p : ℕ → ℝ) (X X' A0 A0' B0 B0' cc H1 V1 D1 Hs : ℝ)
    (χ χ' β β' ζ ν : ℕ → ℝ)
    (hA0 : A0 = X - ∑ k ∈ range (a + 1), χ k * p k)
    (hA0' : A0' = X' - ∑ k ∈ range (a + 1), χ' k * p k)
    (hB0 : B0 = ∑ k ∈ range (a + 1), β k * p k)
    (hB0' : B0' = ∑ k ∈ range (a + 1), β' k * p k)
    (hcc : cc = D1 * ∑ k ∈ range (a + 1), (if k ≤ 1 then (1 : ℝ) else 0) * p k)
    (hH1 : H1 = Hs - ∑ k ∈ range (a + 1), ζ k * p k)
    (hV1 : V1 = ∑ k ∈ range (a + 1), ν k * p k) :
    A0 * B0' + B0 * A0' + 2 * cc * V1 - 4 * cc * H1 =
      ∑ k ∈ range (a + 1), (X * β' k + X' * β k - 4 * (if k ≤ 1 then 1 else 0) * D1 * Hs) * p k -
        ∑ k ∈ range (a + 1), ∑ m ∈ range (a + 1),
          (β' k * χ m + β k * χ' m - (if k ≤ 1 then 1 else 0) * D1 * (4 * ζ m + 2 * ν m)) * p k * p m := by
  set I : ℕ → ℝ := fun k => if k ≤ 1 then 1 else 0 with hI
  have hL1 : (∑ k ∈ range (a + 1), χ k * p k) * (∑ k ∈ range (a + 1), β' k * p k) =
      ∑ k ∈ range (a + 1), ∑ m ∈ range (a + 1), β' k * χ m * p k * p m := by
    rw [sum_mul_sum, sum_comm]
    exact sum_congr rfl fun k _ => sum_congr rfl fun m _ => by ring
  have hL2 : (∑ k ∈ range (a + 1), β k * p k) * (∑ k ∈ range (a + 1), χ' k * p k) =
      ∑ k ∈ range (a + 1), ∑ m ∈ range (a + 1), β k * χ' m * p k * p m := by
    rw [sum_mul_sum]
    exact sum_congr rfl fun k _ => sum_congr rfl fun m _ => by ring
  have hL3 : (∑ k ∈ range (a + 1), I k * p k) * (∑ k ∈ range (a + 1), ν k * p k) =
      ∑ k ∈ range (a + 1), ∑ m ∈ range (a + 1), I k * ν m * p k * p m := by
    rw [sum_mul_sum]
    exact sum_congr rfl fun k _ => sum_congr rfl fun m _ => by ring
  have hL4 : (∑ k ∈ range (a + 1), I k * p k) * (∑ k ∈ range (a + 1), ζ k * p k) =
      ∑ k ∈ range (a + 1), ∑ m ∈ range (a + 1), I k * ζ m * p k * p m := by
    rw [sum_mul_sum]
    exact sum_congr rfl fun k _ => sum_congr rfl fun m _ => by ring
  have hXb : X * (∑ k ∈ range (a + 1), β' k * p k) = ∑ k ∈ range (a + 1), X * β' k * p k := by
    rw [mul_sum]; exact sum_congr rfl fun k _ => by ring
  have hXb' : X' * (∑ k ∈ range (a + 1), β k * p k) = ∑ k ∈ range (a + 1), X' * β k * p k := by
    rw [mul_sum]; exact sum_congr rfl fun k _ => by ring
  have hH : 4 * D1 * (∑ k ∈ range (a + 1), I k * p k) * Hs =
      ∑ k ∈ range (a + 1), 4 * I k * D1 * Hs * p k := by
    rw [mul_sum, sum_mul]; exact sum_congr rfl fun k _ => by ring
  rw [hA0, hA0', hB0, hB0', hcc, hH1, hV1]
  have hexp : (X - ∑ k ∈ range (a + 1), χ k * p k) * (∑ k ∈ range (a + 1), β' k * p k) +
      (∑ k ∈ range (a + 1), β k * p k) * (X' - ∑ k ∈ range (a + 1), χ' k * p k) +
      2 * (D1 * ∑ k ∈ range (a + 1), I k * p k) * (∑ k ∈ range (a + 1), ν k * p k) -
      4 * (D1 * ∑ k ∈ range (a + 1), I k * p k) * (Hs - ∑ k ∈ range (a + 1), ζ k * p k) =
      X * (∑ k ∈ range (a + 1), β' k * p k) + X' * (∑ k ∈ range (a + 1), β k * p k) -
        (∑ k ∈ range (a + 1), χ k * p k) * (∑ k ∈ range (a + 1), β' k * p k) -
        (∑ k ∈ range (a + 1), β k * p k) * (∑ k ∈ range (a + 1), χ' k * p k) +
        2 * D1 * ((∑ k ∈ range (a + 1), I k * p k) * (∑ k ∈ range (a + 1), ν k * p k)) -
        4 * D1 * (∑ k ∈ range (a + 1), I k * p k) * Hs +
        4 * D1 * ((∑ k ∈ range (a + 1), I k * p k) * (∑ k ∈ range (a + 1), ζ k * p k)) := by ring
  rw [hexp, hL1, hL2, hL3, hL4, hXb, hXb', hH]
  simp only [mul_sum]
  have e1 : ∀ k, (X * β' k + X' * β k - 4 * (if k ≤ 1 then (1 : ℝ) else 0) * D1 * Hs) * p k =
      X * β' k * p k + X' * β k * p k - 4 * (if k ≤ 1 then (1 : ℝ) else 0) * D1 * Hs * p k :=
    fun k => by ring
  have e2 : ∀ k m, (β' k * χ m + β k * χ' m - (if k ≤ 1 then (1 : ℝ) else 0) * D1 * (4 * ζ m + 2 * ν m)) *
      p k * p m = β' k * χ m * p k * p m + β k * χ' m * p k * p m -
        2 * D1 * ((if k ≤ 1 then (1 : ℝ) else 0) * ν m * p k * p m) -
        4 * D1 * ((if k ≤ 1 then (1 : ℝ) else 0) * ζ m * p k * p m) := fun k m => by ring
  simp only [e1, e2, sum_sub_distrib, sum_add_distrib, hI]
  ring


/-! ### Value lemmas in a `GenSetting` -/

theorem dd_shift_eq (v : ℕ → ℝ) (ℓ n : ℕ) :
    dd v (ℓ + n) = dd (Szkraw.iterShift v ℓ) n := by
  rw [dd_split]
  unfold dd
  rw [iterShift_eq]
  simp only [zero_add]

theorem dd_shift_zero (v : ℕ → ℝ) (ℓ : ℕ) : dd v ℓ = dd (Szkraw.iterShift v ℓ) 0 := by
  have := dd_shift_eq v ℓ 0
  rw [add_zero] at this
  exact this

theorem Wt_two_eq (v : ℕ → ℝ) (ℓ m : ℕ) :
    Wt v 2 0 ℓ m = dd v (ℓ + m) - dd v ℓ - (m : ℝ) * (dd v (ℓ + 1) - dd v ℓ) := by
  have h1 := Wt_one_split v ℓ m
  have h2 := Wt_one_zero v ℓ m
  have h3 : dd v (ℓ + 1) = dd v ℓ + Szkraw.iterShift v ℓ 1 := rfl
  rw [h2] at h1
  have h4 : (m : ℝ) * Szkraw.iterShift v ℓ 1 = (m : ℝ) * (dd v (ℓ + 1) - dd v ℓ) := by
    rw [h3]; ring
  linarith

theorem dd_quadW (ν u : ℕ → ℝ) (x : ℕ) : dd (quadW ν u) x = dd ν x - dd u x := by
  unfold dd quadW; rw [iterShift_sub]

section Values

variable {N : ℕ} {ρc ν u : ℕ → ℝ} (S : GenSetting N ρc ν u)
include S

/-- `c_{ℓ+n}` expanded in `P_k = iterShift ρc ℓ k`, for `n ≤ a`. -/
theorem GenSetting.cexp {ℓ a n : ℕ} (h : ℓ + n ≤ N) (hna : n ≤ a) :
    dd u (ℓ + n) = dd (Szkraw.iterShift ν ℓ) n *
      ∑ k ∈ range (a + 1), (n.choose k : ℝ) * Szkraw.iterShift ρc ℓ k := by
  rw [S.dd_u h, dd_split ρc ℓ n, dd_shift_eq ν ℓ n, sum_choose_ext hna, mul_comm]

theorem GenSetting.A0_expand {ℓ a : ℕ} (h : ℓ + a ≤ N) :
    wA (quadW ν u) 0 ℓ a = (dd (Szkraw.iterShift ν ℓ) a - dd (Szkraw.iterShift ν ℓ) 0) -
      ∑ k ∈ range (a + 1), chiC (Szkraw.iterShift ν ℓ) a k * Szkraw.iterShift ρc ℓ k := by
  unfold wA
  show Wt (quadW ν u) 1 0 ℓ a = _
  have c0 : dd u ℓ = dd (Szkraw.iterShift ν ℓ) 0 *
      ∑ k ∈ range (a + 1), ((0 : ℕ).choose k : ℝ) * Szkraw.iterShift ρc ℓ k := by
    have := S.cexp (ℓ := ℓ) (a := a) (n := 0) (by omega) (by omega)
    rwa [add_zero] at this
  rw [Wt_one_zero, dd_quadW, dd_quadW, dd_shift_eq ν ℓ a, S.cexp (a := a) (n := a) h le_rfl,
    c0, dd_shift_zero ν ℓ]
  have hch : ∑ k ∈ range (a + 1), chiC (Szkraw.iterShift ν ℓ) a k * Szkraw.iterShift ρc ℓ k =
      dd (Szkraw.iterShift ν ℓ) a * ∑ k ∈ range (a + 1), (a.choose k : ℝ) * Szkraw.iterShift ρc ℓ k -
      dd (Szkraw.iterShift ν ℓ) 0 * ∑ k ∈ range (a + 1), ((0 : ℕ).choose k : ℝ) * Szkraw.iterShift ρc ℓ k := by
    rw [mul_sum, mul_sum, ← sum_sub_distrib]
    exact sum_congr rfl fun k _ => by unfold chiC; ring
  rw [hch]
  ring


end Values

theorem wgtH_eq (n : ℕ) : (if 2 * 1 + 1 ≤ n then ((n - (2 * 1 + 1) + 1).choose 1 : ℝ) else 0) = wgtH n := by
  unfold wgtH; norm_num

section Values2

variable {N : ℕ} {ρc ν u : ℕ → ℝ} (S : GenSetting N ρc ν u)
include S

theorem GenSetting.c1 {ℓ a : ℕ} (h : ℓ + 1 ≤ N) (ha : 1 ≤ a) :
    dd u (ℓ + 1) = dd (Szkraw.iterShift ν ℓ) 1 *
      ∑ k ∈ range (a + 1), ((1 : ℕ).choose k : ℝ) * Szkraw.iterShift ρc ℓ k :=
  S.cexp (a := a) (n := 1) h ha

theorem GenSetting.A0p_expand {ℓ a : ℕ} (h : ℓ + a ≤ N) (ha : 3 ≤ a) :
    wA (quadW ν u) 0 (ℓ + 1) (a - 2) = (dd (Szkraw.iterShift ν ℓ) (a - 1) - dd (Szkraw.iterShift ν ℓ) 1) -
      ∑ k ∈ range (a + 1), chi'C (Szkraw.iterShift ν ℓ) a k * Szkraw.iterShift ρc ℓ k := by
  unfold wA
  show Wt (quadW ν u) 1 0 (ℓ + 1) (a - 2) = _
  rw [Wt_one_zero, show ℓ + 1 + (a - 2) = ℓ + (a - 1) by omega, dd_quadW, dd_quadW,
    dd_shift_eq ν ℓ (a - 1), dd_shift_eq ν ℓ 1, S.c1 (a := a) (by omega) (by omega),
    S.cexp (a := a) (n := a - 1) (by omega) (by omega)]
  have hch : ∑ k ∈ range (a + 1), chi'C (Szkraw.iterShift ν ℓ) a k * Szkraw.iterShift ρc ℓ k =
      dd (Szkraw.iterShift ν ℓ) (a - 1) * ∑ k ∈ range (a + 1), ((a - 1).choose k : ℝ) * Szkraw.iterShift ρc ℓ k -
      dd (Szkraw.iterShift ν ℓ) 1 * ∑ k ∈ range (a + 1), ((1 : ℕ).choose k : ℝ) * Szkraw.iterShift ρc ℓ k := by
    rw [mul_sum, mul_sum, ← sum_sub_distrib]
    exact sum_congr rfl fun k _ => by unfold chi'C; ring
  rw [hch]
  ring

theorem GenSetting.B0_expand {ℓ a : ℕ} (h : ℓ + a ≤ N) (ha : 1 ≤ a) :
    Wt u 2 0 ℓ a = ∑ k ∈ range (a + 1), betaC (Szkraw.iterShift ν ℓ) a k * Szkraw.iterShift ρc ℓ k := by
  have c0 : dd u ℓ = dd (Szkraw.iterShift ν ℓ) 0 *
      ∑ k ∈ range (a + 1), ((0 : ℕ).choose k : ℝ) * Szkraw.iterShift ρc ℓ k := by
    have := S.cexp (ℓ := ℓ) (a := a) (n := 0) (by omega) (by omega)
    rwa [add_zero] at this
  rw [Wt_two_eq, S.cexp (a := a) (n := a) h le_rfl, c0, S.c1 (a := a) (by omega) (by omega)]
  simp only [mul_sum, ← sum_sub_distrib]
  refine sum_congr rfl fun k _ => ?_
  unfold betaC
  ring

theorem GenSetting.B0p_expand {ℓ a : ℕ} (h : ℓ + a ≤ N) (ha : 3 ≤ a) :
    Wt u 2 0 (ℓ + 1) (a - 1) = ∑ k ∈ range (a + 1), beta'C (Szkraw.iterShift ν ℓ) a k * Szkraw.iterShift ρc ℓ k := by
  rw [Wt_two_eq, show ℓ + 1 + (a - 1) = ℓ + a by omega, show ℓ + 1 + 1 = ℓ + 2 from rfl,
    Nat.cast_sub (by omega : 1 ≤ a), Nat.cast_one, S.cexp (a := a) (n := a) h le_rfl,
    S.c1 (a := a) (by omega) (by omega), S.cexp (a := a) (n := 2) (by omega) (by omega)]
  simp only [mul_sum, ← sum_sub_distrib]
  refine sum_congr rfl fun k _ => ?_
  unfold beta'C
  ring

theorem GenSetting.Dc_expand {ℓ a : ℕ} (h : ℓ + a ≤ N) :
    ∑ k ∈ range (a + 1), deltaC (Szkraw.iterShift ν ℓ) a k * Szkraw.iterShift ρc ℓ k =
      dd u (ℓ + a) - dd u (ℓ + (a - 1)) := by
  rw [S.cexp (a := a) (n := a) h le_rfl, S.cexp (a := a) (n := a - 1) (by omega) (by omega)]
  simp only [mul_sum, ← sum_sub_distrib]
  refine sum_congr rfl fun k _ => ?_
  unfold deltaC
  ring

theorem GenSetting.F_pos {ℓ a : ℕ} (h : ℓ + a ≤ N) (ha : 1 ≤ a) :
    0 < dd (Szkraw.iterShift ν ℓ) a - dd (Szkraw.iterShift ν ℓ) (a - 1) := by
  have e : dd (Szkraw.iterShift ν ℓ) a - dd (Szkraw.iterShift ν ℓ) (a - 1) =
      Szkraw.iterShift ν (ℓ + (a - 1)) 1 := by
    rw [← dd_shift_eq ν ℓ a, ← dd_shift_eq ν ℓ (a - 1), show ℓ + a = (ℓ + (a - 1)) + 1 by omega]
    have h1 : dd ν (ℓ + (a - 1) + 1) = dd ν (ℓ + (a - 1)) + Szkraw.iterShift ν (ℓ + (a - 1)) 1 := rfl
    linarith
  rw [e]
  exact S.f1_pos _

theorem GenSetting.Dc_le {ℓ a : ℕ} (h : ℓ + a ≤ N) (ha : 1 ≤ a) :
    dd u (ℓ + a) - dd u (ℓ + (a - 1)) ≤
      dd (Szkraw.iterShift ν ℓ) a - dd (Szkraw.iterShift ν ℓ) (a - 1) := by
  have hb := S.hb (ℓ + (a - 1)) (by omega)
  rw [show ℓ + (a - 1) + 1 = ℓ + a by omega, dd_quadW, dd_quadW, dd_shift_eq ν ℓ a,
    dd_shift_eq ν ℓ (a - 1)] at hb
  linarith


end Values2

section Values3

variable {N : ℕ} {ρc ν u : ℕ → ℝ} (S : GenSetting N ρc ν u)
include S

theorem GenSetting.dd_rho {ℓ a n : ℕ} (hna : n ≤ a) :
    dd ρc (ℓ + n) = ∑ k ∈ range (a + 1), (n.choose k : ℝ) * Szkraw.iterShift ρc ℓ k := by
  rw [dd_split ρc ℓ n, sum_choose_ext hna]

theorem GenSetting.H1_expand {ℓ a : ℕ} (ha : 1 ≤ a) :
    genH ρc ν 1 ℓ a = Hstar (Szkraw.iterShift ν ℓ) a -
      ∑ k ∈ range (a + 1), zetaC (Szkraw.iterShift ν ℓ) a k * Szkraw.iterShift ρc ℓ k := by
  unfold genH WtF hG
  simp only [wgtH_eq]
  have hterm : ∀ n ∈ range (a + 1), wgtH n * (a.choose n : ℝ) *
      ((1 - dd ρc (ℓ + n)) * Szkraw.iterShift ν ℓ n) =
      wgtH n * (a.choose n : ℝ) * Szkraw.iterShift ν ℓ n -
        ∑ k ∈ range (a + 1), (wgtH n * (a.choose n : ℝ) * Szkraw.iterShift ν ℓ n * (n.choose k : ℝ)) *
          Szkraw.iterShift ρc ℓ k := by
    intro n hn
    have hna : n ≤ a := by have := mem_range.mp hn; omega
    have e : (1 - dd ρc (ℓ + n)) * Szkraw.iterShift ν ℓ n =
        Szkraw.iterShift ν ℓ n - ∑ k ∈ range (a + 1), (Szkraw.iterShift ν ℓ n * (n.choose k : ℝ)) *
          Szkraw.iterShift ρc ℓ k := by
      rw [S.dd_rho (ℓ := ℓ) hna, sub_mul, one_mul, sum_mul]
      congr 1
      exact sum_congr rfl fun k _ => by ring
    rw [e, mul_sub, mul_sum]
    congr 1
    exact sum_congr rfl fun k _ => by ring
  rw [sum_congr rfl hterm, sum_sub_distrib]
  congr 1
  rw [sum_comm]
  refine sum_congr rfl fun k _ => ?_
  unfold zetaC
  rw [sum_mul]

theorem GenSetting.V1_expand {ℓ a : ℕ} (ha : 3 ≤ a) :
    genV ρc ν 1 ℓ a = ∑ k ∈ range (a + 1), nuC (Szkraw.iterShift ν ℓ) a k * Szkraw.iterShift ρc ℓ k := by
  unfold genV WtF vG
  simp only [wgtH_eq]
  have hterm : ∀ n ∈ range (a + 1), wgtH n * (a.choose n : ℝ) *
      ((n : ℝ) * Szkraw.iterShift ρc (ℓ + (n - 1)) 1 * Szkraw.iterShift ν ℓ (n - 1)) =
      ∑ k ∈ range (a + 1), (wgtH n * (a.choose n : ℝ) * ((n : ℝ) * Szkraw.iterShift ν ℓ (n - 1)) *
        (if 1 ≤ k then ((n - 1).choose (k - 1) : ℝ) else 0)) * Szkraw.iterShift ρc ℓ k := by
    intro n hn
    have hna : n ≤ a := by have := mem_range.mp hn; omega
    rw [iterShift_base ρc ℓ (n - 1) 1, shift_reindex (Szkraw.iterShift ρc ℓ) (by omega : n - 1 < a)]
    simp only [Finset.mul_sum, Finset.sum_mul]
    exact sum_congr rfl fun k _ => by ring
  rw [sum_congr rfl hterm, sum_comm]
  refine sum_congr rfl fun k _ => ?_
  unfold nuC
  rw [sum_mul]

end Values3

theorem MC_zero {f : ℕ → ℝ} {a : ℕ} (ha : 3 ≤ a) (k m : ℕ) (hkm : a < k ∨ a < m) :
    MC f a k m = 0 := by
  rcases hkm with hk | hm
  · have c1 : (a.choose k : ℝ) = 0 := by rw [Nat.choose_eq_zero_of_lt hk]; simp
    have c2 : ((1 : ℕ).choose k : ℝ) = 0 := by rw [Nat.choose_eq_zero_of_lt (by omega)]; simp
    have c3 : ((2 : ℕ).choose k : ℝ) = 0 := by rw [Nat.choose_eq_zero_of_lt (by omega)]; simp
    have c4 : ((0 : ℕ).choose k : ℝ) = 0 := by rw [Nat.choose_eq_zero_of_lt (by omega)]; simp
    have hk1 : ¬ k ≤ 1 := by omega
    simp [MC, beta'C, betaC, c1, c2, c3, c4, hk1]
  · have c1 : (a.choose m : ℝ) = 0 := by rw [Nat.choose_eq_zero_of_lt hm]; simp
    have c1' : ((a - 1).choose m : ℝ) = 0 := by rw [Nat.choose_eq_zero_of_lt (by omega)]; simp
    have c2 : ((1 : ℕ).choose m : ℝ) = 0 := by rw [Nat.choose_eq_zero_of_lt (by omega)]; simp
    have c4 : ((0 : ℕ).choose m : ℝ) = 0 := by rw [Nat.choose_eq_zero_of_lt (by omega)]; simp
    have hz : zetaC f a m = 0 := by
      unfold zetaC
      refine sum_eq_zero fun n hn => ?_
      have : n ≤ a := by have := mem_range.mp hn; omega
      rw [Nat.choose_eq_zero_of_lt (show n < m by omega)]; simp
    have hn : nuC f a m = 0 := by
      unfold nuC
      refine sum_eq_zero fun n hn => ?_
      have hna : n ≤ a := by have := mem_range.mp hn; omega
      rcases Nat.eq_zero_or_pos n with h0 | hpos
      · subst h0; simp
      · rw [if_pos (show 1 ≤ m by omega), Nat.choose_eq_zero_of_lt (show n - 1 < m - 1 by omega)]; simp
    have hd : deltaC f a m = 0 := by unfold deltaC; rw [c1, c1']; ring
    have hc : chiC f a m = 0 := by unfold chiC; rw [c1, c4]; ring
    have hc' : chi'C f a m = 0 := by unfold chi'C; rw [c1', c2]; ring
    simp [MC, hd, hc, hc', hz, hn]


/-! ### The two remaining analytic inputs, and `GenKeyStmt` from them -/

/-- Linear coefficients `l_k ≥ 0` for `k ≤ a` (paper step (ii)): for every log-concave `f` with
`f 1 > 0`. -/
def LinCoefStmt : Prop :=
  ∀ (f : ℕ → ℝ), LCNZ f → 0 < f 1 → ∀ a : ℕ, 3 ≤ a → ∀ k : ℕ, k ≤ a → 0 ≤ linC f a k

/-- Central sums of the matrix `MC` are nonnegative (paper steps (iii)-(v)). -/
def CentralStmt : Prop :=
  ∀ (f : ℕ → ℝ), LCNZ f → 0 < f 1 → ∀ a : ℕ, 3 ≤ a → ∀ σ i : ℕ, 2 * i ≤ σ →
    0 ≤ ∑ k ∈ Icc i (σ - i), MC f a k (σ - k)

theorem genKey_of_props (hLin : LinCoefStmt) (hCen : CentralStmt) : GenKeyStmt := by
  intro N ρc ν u S ℓ a h ha
  have ha3 : 3 ≤ a := ha
  have hf : LCNZ (Szkraw.iterShift ν ℓ) := S.hν.iterShift ℓ
  have hp : LCNZ (Szkraw.iterShift ρc ℓ) := S.hρc.iterShift ℓ
  have f1 : 0 < Szkraw.iterShift ν ℓ 1 := S.f1_pos ℓ
  set f := Szkraw.iterShift ν ℓ with hfdef
  set p := Szkraw.iterShift ρc ℓ with hpdef
  have hP0 : ∀ k, 0 ≤ p k := fun k => hp.1 k
  -- the pieces
  have hA0 := S.A0_expand h
  have hA0' := S.A0p_expand h ha3
  have hB0 : wB u 0 ℓ a = ∑ k ∈ range (a + 1), betaC f a k * p k := S.B0_expand h (by omega)
  have hB0' : wB u 0 (ℓ + 1) (a - 1) = ∑ k ∈ range (a + 1), beta'C f a k * p k :=
    S.B0p_expand h ha3
  have hcc : dd u (ℓ + 1) = dd f 1 * ∑ k ∈ range (a + 1), (if k ≤ 1 then (1 : ℝ) else 0) * p k := by
    rw [S.c1 (a := a) (by omega) (by omega)]
    congr 1
    exact sum_congr rfl fun k _ => by rw [choose_one_ind]
  have hH1 : genH ρc ν 1 ℓ a = Hstar f a - ∑ k ∈ range (a + 1), zetaC f a k * p k :=
    S.H1_expand (by omega)
  have hV1 : genV ρc ν 1 ℓ a = ∑ k ∈ range (a + 1), nuC f a k * p k := S.V1_expand ha3
  have hcore := key_core a p (dd f a - dd f 0) (dd f (a - 1) - dd f 1) (wA (quadW ν u) 0 ℓ a)
    (wA (quadW ν u) 0 (ℓ + 1) (a - 2)) (wB u 0 ℓ a) (wB u 0 (ℓ + 1) (a - 1)) (dd u (ℓ + 1))
    (genH ρc ν 1 ℓ a) (genV ρc ν 1 ℓ a) (dd f 1) (Hstar f a) (chiC f a) (chi'C f a) (betaC f a)
    (beta'C f a) (zetaC f a) (nuC f a) hA0 hA0' hB0 hB0' hcc hH1 hV1
  -- the Abel argument in `p`
  set F := dd f a - dd f (a - 1) with hFdef
  have hFpos : 0 < F := S.F_pos h (by omega)
  have hDc : ∑ k ∈ range (a + 1), deltaC f a k * p k ≤ F := by
    rw [S.Dc_expand h]; exact S.Dc_le h (by omega)
  have hLinNN : 0 ≤ ∑ k ∈ range (a + 1), ((dd f a - dd f 0) * beta'C f a k +
      (dd f (a - 1) - dd f 1) * betaC f a k - 4 * (if k ≤ 1 then (1 : ℝ) else 0) * dd f 1 * Hstar f a) * p k :=
    sum_nonneg fun k hk => mul_nonneg (hLin f hf f1 a ha3 k (by simp only [mem_range] at hk; omega))
      (hP0 k)
  have hPhiM : 0 ≤ ∑ k ∈ range (a + 1), ∑ m ∈ range (a + 1), MC f a k m * p k * p m :=
    matrix_abel hp a (MC f a) (fun k m hkm => MC_zero ha3 k m hkm)
      (fun σ i hi => hCen f hf f1 a ha3 σ i hi)
  have hPhi : 0 ≤ (∑ k ∈ range (a + 1), deltaC f a k * p k) *
      (∑ k ∈ range (a + 1), ((dd f a - dd f 0) * beta'C f a k + (dd f (a - 1) - dd f 1) * betaC f a k -
        4 * (if k ≤ 1 then (1 : ℝ) else 0) * dd f 1 * Hstar f a) * p k) -
      F * ∑ k ∈ range (a + 1), ∑ m ∈ range (a + 1),
        (beta'C f a k * chiC f a m + betaC f a k * chi'C f a m -
          (if k ≤ 1 then (1 : ℝ) else 0) * dd f 1 * (4 * zetaC f a m + 2 * nuC f a m)) * p k * p m := by
    have hphi := phi_matrix a p (betaC f a) (beta'C f a) (chiC f a) (chi'C f a) (deltaC f a)
      (zetaC f a) (nuC f a) (dd f a - dd f 0) (dd f (a - 1) - dd f 1) F (dd f 1) (Hstar f a)
    rw [hphi]
    exact hPhiM
  have hkey0 := key_of_phi hFpos hLinNN hDc hPhi
  have hT := hcore
  linarith [hT, hkey0]

end Szkraw
