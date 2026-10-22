import Szkraw.LCInduction
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination

/-!
# Polynomial tools for the kernel identity (F4)

Polynomials in two variables `X 0`, `X 1`. On the `(z, w)` side they are read as `z = X 0`,
`w = X 1`, with `S = z + w` and `Z = z w`; on the symmetric side `X 0 = S` and `X 1 = Z`, and
`ι` substitutes `S ↦ z + w`, `Z ↦ z w`.
-/

namespace Szkraw

open MvPolynomial Finset

/-- Polynomials in two variables. -/
abbrev P2 := MvPolynomial (Fin 2) ℝ

/-- The coefficient of `X0^m X1^n`. -/
noncomputable def cf (p : P2) (m n : ℕ) : ℝ := coeff (Finsupp.single 0 m + Finsupp.single 1 n) p

theorem single_add_single_eq {p q m n : ℕ} :
    (Finsupp.single (0 : Fin 2) p + Finsupp.single 1 q = Finsupp.single 0 m + Finsupp.single 1 n) ↔
      p = m ∧ q = n := by
  constructor
  · intro h
    have h0 := DFunLike.congr_fun h 0
    have h1 := DFunLike.congr_fun h 1
    simp at h0 h1
    exact ⟨h0, h1⟩
  · rintro ⟨rfl, rfl⟩; rfl

theorem cf_XX (p q m n : ℕ) : cf (X 0 ^ p * X 1 ^ q) m n = if p = m ∧ q = n then 1 else 0 := by
  unfold cf
  rw [X_pow_eq_monomial, X_pow_eq_monomial, monomial_mul, one_mul, coeff_monomial]
  simp only [single_add_single_eq]

theorem cf_add (p q : P2) (m n : ℕ) : cf (p + q) m n = cf p m n + cf q m n := coeff_add _ _ _
theorem cf_sub (p q : P2) (m n : ℕ) : cf (p - q) m n = cf p m n - cf q m n := by simp [cf]
theorem cf_neg (p : P2) (m n : ℕ) : cf (-p) m n = -cf p m n := by simp [cf]
theorem cf_zero (m n : ℕ) : cf 0 m n = 0 := coeff_zero _
theorem cf_C_mul (c : ℝ) (p : P2) (m n : ℕ) : cf (C c * p) m n = c * cf p m n := coeff_C_mul _ _ _
theorem cf_sum {ι : Type*} (s : Finset ι) (f : ι → P2) (m n : ℕ) :
    cf (∑ i ∈ s, f i) m n = ∑ i ∈ s, cf (f i) m n := coeff_sum _ _ _

theorem P2_ext {p q : P2} (h : ∀ m n, cf p m n = cf q m n) : p = q := by
  ext d
  have : d = Finsupp.single 0 (d 0) + Finsupp.single 1 (d 1) := by
    ext i; fin_cases i <;> simp
  rw [this]; exact h _ _

theorem cf_X0_mul (p : P2) (m n : ℕ) : cf (X 0 * p) m n = if 1 ≤ m then cf p (m - 1) n else 0 := by
  unfold cf
  rw [coeff_X_mul']
  have hs : (0 : Fin 2) ∈ (Finsupp.single (0 : Fin 2) m + Finsupp.single (1 : Fin 2) n : Fin 2 →₀ ℕ).support ↔ 1 ≤ m := by
    simp [Finsupp.mem_support_iff]; omega
  have he : Finsupp.single (0 : Fin 2) m + Finsupp.single 1 n - Finsupp.single 0 1 =
      Finsupp.single 0 (m - 1) + Finsupp.single 1 n := by
    ext i; fin_cases i <;> simp
  by_cases h : 1 ≤ m
  · rw [if_pos (hs.mpr h), if_pos h, he]
  · rw [if_neg (fun h' => h (hs.mp h')), if_neg h]

theorem cf_X1_mul (p : P2) (m n : ℕ) : cf (X 1 * p) m n = if 1 ≤ n then cf p m (n - 1) else 0 := by
  unfold cf
  rw [coeff_X_mul']
  have hs : (1 : Fin 2) ∈ (Finsupp.single (0 : Fin 2) m + Finsupp.single (1 : Fin 2) n : Fin 2 →₀ ℕ).support ↔ 1 ≤ n := by
    simp [Finsupp.mem_support_iff]; omega
  have he : Finsupp.single (0 : Fin 2) m + Finsupp.single 1 n - Finsupp.single 1 1 =
      Finsupp.single 0 m + Finsupp.single 1 (n - 1) := by
    ext i; fin_cases i <;> simp
  by_cases h : 1 ≤ n
  · rw [if_pos (hs.mpr h), if_pos h, he]
  · rw [if_neg (fun h' => h (hs.mp h')), if_neg h]

/-- Coefficient of `z^i w^j (z+w)^b (zw)^r` at `z^m w^n`. -/
noncomputable def Ecf (i j b r m n : ℕ) : ℝ :=
  if i + r ≤ m ∧ j + r ≤ n ∧ m + n = i + j + b + 2 * r then (b.choose (m - i - r) : ℝ) else 0

theorem Ecf_pascal (i j b r m n : ℕ) :
    Ecf (i + 1) j b r m n + Ecf i (j + 1) b r m n = Ecf i j (b + 1) r m n := by
  unfold Ecf
  by_cases h3 : i + r ≤ m ∧ j + r ≤ n ∧ m + n = i + j + (b + 1) + 2 * r
  · rw [if_pos h3]
    by_cases h1 : i + 1 + r ≤ m ∧ j + r ≤ n ∧ m + n = i + 1 + j + b + 2 * r
    · rw [if_pos h1]
      by_cases h2 : i + r ≤ m ∧ j + 1 + r ≤ n ∧ m + n = i + (j + 1) + b + 2 * r
      · rw [if_pos h2]
        have e : m - i - r = (m - (i + 1) - r) + 1 := by omega
        rw [e, Nat.choose_succ_succ', Nat.cast_add]
      · rw [if_neg h2, add_zero]
        have e : m - i - r = b + 1 := by omega
        have e' : m - (i + 1) - r = b := by omega
        rw [e, e', Nat.choose_self, Nat.choose_self]
    · rw [if_neg h1, zero_add]
      have hm : m = i + r := by omega
      rw [if_pos (by omega)]
      have e : m - i - r = 0 := by omega
      rw [e, Nat.choose_zero_right, Nat.choose_zero_right]
  · rw [if_neg h3, if_neg (by omega), if_neg (by omega), add_zero]

theorem cf_mono (i j b r m n : ℕ) :
    cf (X 0 ^ i * X 1 ^ j * (X 0 + X 1) ^ b * (X 0 * X 1) ^ r) m n = Ecf i j b r m n := by
  induction b generalizing i j with
  | zero =>
    have : (X 0 : P2) ^ i * X 1 ^ j * (X 0 + X 1) ^ 0 * (X 0 * X 1) ^ r =
        X 0 ^ (i + r) * X 1 ^ (j + r) := by ring
    rw [this, cf_XX]; unfold Ecf
    by_cases h : i + r = m ∧ j + r = n
    · rw [if_pos h, if_pos (by omega)]
      have e : m - i - r = 0 := by omega
      rw [e]; simp
    · rw [if_neg h, if_neg (by omega)]
  | succ b ih =>
    have : (X 0 : P2) ^ i * X 1 ^ j * (X 0 + X 1) ^ (b + 1) * (X 0 * X 1) ^ r =
        X 0 ^ (i + 1) * X 1 ^ j * (X 0 + X 1) ^ b * (X 0 * X 1) ^ r +
        X 0 ^ i * X 1 ^ (j + 1) * (X 0 + X 1) ^ b * (X 0 * X 1) ^ r := by ring
    rw [this, cf_add, ih, ih, Ecf_pascal]

theorem Ecf_swap (i j b r m n : ℕ) : Ecf i j b r m n = Ecf j i b r n m := by
  unfold Ecf
  by_cases h : i + r ≤ m ∧ j + r ≤ n ∧ m + n = i + j + b + 2 * r
  · rw [if_pos h, if_pos (by omega)]
    have e : n - j - r = b - (m - i - r) := by omega
    rw [e, Nat.choose_symm (by omega)]
  · rw [if_neg h, if_neg (by omega)]

theorem Ecf_nonneg (i j b r m n : ℕ) : 0 ≤ Ecf i j b r m n := by
  unfold Ecf; split_ifs <;> positivity

/-! ### The polynomials `h_n` on the symmetric side -/

/-- `h_n = Σ_l (-1)^l C(n-l,l) S^(n-2l) Z^l` with `S = X 0`, `Z = X 1`. -/
noncomputable def hh (n : ℕ) : P2 :=
  ∑ l ∈ range (n + 1), C ((-1 : ℝ) ^ l * ((n - l).choose l : ℝ)) * (X 0 ^ (n - 2 * l) * X 1 ^ l)

theorem cf_hh (n x y : ℕ) :
    cf (hh n) x y = if x + 2 * y = n then (-1 : ℝ) ^ y * ((n - y).choose y : ℝ) else 0 := by
  unfold hh
  rw [cf_sum]
  simp only [cf_C_mul, cf_XX]
  by_cases hy : y ≤ n
  · rw [Finset.sum_eq_single y]
    · by_cases h : x + 2 * y = n
      · rw [if_pos ⟨by omega, rfl⟩, if_pos h, mul_one]
      · rw [if_neg h]
        by_cases h' : n - 2 * y = x
        · rw [if_pos ⟨h', rfl⟩, mul_one, Nat.choose_eq_zero_of_lt (by omega)]; simp
        · rw [if_neg (fun h'' => h' h''.1), mul_zero]
    · intro l _ hl; rw [if_neg (fun h => hl h.2), mul_zero]
    · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h
  · rw [if_neg (by omega)]
    apply Finset.sum_eq_zero
    intro l hl
    rw [Finset.mem_range] at hl
    rw [if_neg (by omega), mul_zero]

theorem hh_rec (n : ℕ) : hh (n + 2) = X 0 * hh (n + 1) - X 1 * hh n := by
  apply P2_ext; intro x y
  rw [cf_sub, cf_X0_mul, cf_X1_mul, cf_hh]
  by_cases h : x + 2 * y = n + 2
  · rw [if_pos h]
    rcases Nat.eq_zero_or_pos y with hy | hy
    · subst hy
      rw [if_pos (by omega), cf_hh, if_pos (by omega), if_neg (by omega)]
      simp
    rcases Nat.eq_zero_or_pos x with hx | hx
    · subst hx
      rw [if_neg (by omega), if_pos (by omega), cf_hh, if_pos (by omega)]
      obtain ⟨y', rfl⟩ : ∃ y', y = y' + 1 := ⟨y - 1, by omega⟩
      have e1 : n + 2 - (y' + 1) = y' + 1 := by omega
      have e2 : n - (y' + 1 - 1) = y' := by omega
      rw [e1, e2]
      simp only [Nat.add_sub_cancel, Nat.choose_self, pow_succ]
      ring
    · rw [if_pos (by omega), if_pos (by omega), cf_hh, cf_hh, if_pos (by omega), if_pos (by omega)]
      obtain ⟨y', rfl⟩ : ∃ y', y = y' + 1 := ⟨y - 1, by omega⟩
      have e1 : n + 2 - (y' + 1) = (n - y') + 1 := by omega
      have e2 : n + 1 - (y' + 1) = n - y' := by omega
      have e3 : n - (y' + 1 - 1) = n - y' := by omega
      rw [e1, e2, e3, Nat.add_sub_cancel, Nat.choose_succ_succ', Nat.cast_add, pow_succ]
      ring
  · rw [if_neg h]
    have a1 : (if 1 ≤ x then cf (hh (n + 1)) (x - 1) y else 0) = 0 := by
      split_ifs
      · rw [cf_hh, if_neg (by omega)]
      · rfl
    have a2 : (if 1 ≤ y then cf (hh n) x (y - 1) else 0) = 0 := by
      split_ifs
      · rw [cf_hh, if_neg (by omega)]
      · rfl
    rw [a1, a2, sub_zero]

/-- Substitution `S ↦ z + w`, `Z ↦ z w`. -/
noncomputable def ι : P2 →ₐ[ℝ] P2 := aeval (fun i : Fin 2 => if i = 0 then X 0 + X 1 else X 0 * X 1)

theorem ι_X0 : ι (X 0) = X 0 + X 1 := by simp [ι]
theorem ι_X1 : ι (X 1) = X 0 * X 1 := by simp [ι]

theorem hh_zero : hh 0 = 1 := by simp [hh]
theorem hh_one : hh 1 = X 0 := by simp [hh, Finset.sum_range_succ]

/-- `(z - w) h_n(z+w, zw) = z^(n+1) - w^(n+1)`. -/
theorem hh_spec (n : ℕ) : (X 0 - X 1) * ι (hh n) = X 0 ^ (n + 1) - X 1 ^ (n + 1) := by
  have pair : ∀ n, (X 0 - X 1) * ι (hh n) = (X 0 : P2) ^ (n + 1) - X 1 ^ (n + 1) ∧
      (X 0 - X 1) * ι (hh (n + 1)) = (X 0 : P2) ^ (n + 2) - X 1 ^ (n + 2) := by
    intro n
    induction n with
    | zero => exact ⟨by simp [hh_zero], by rw [show (0 : ℕ) + 1 = 1 from rfl, hh_one, ι_X0]; ring⟩
    | succ n ih =>
      refine ⟨ih.2, ?_⟩
      rw [hh_rec, map_sub, map_mul, map_mul, ι_X0, ι_X1]
      linear_combination (X 0 + X 1) * ih.2 - X 0 * X 1 * ih.1
  exact (pair n).1

/-! ### The Vandermonde step: `D(θ_z)` on `S^a Z^r` -/

theorem iterShift_comp (u : ℕ → ℝ) (r : ℕ) :
    ∀ p, Szkraw.iterShift u (r + p) = Szkraw.iterShift (Szkraw.iterShift u r) p
  | 0 => rfl
  | p + 1 => by
    show Szkraw.shiftSum (Szkraw.iterShift u (r + p)) =
      Szkraw.shiftSum (Szkraw.iterShift (Szkraw.iterShift u r) p)
    rw [iterShift_comp u r p]

/-- `D_{r+p} = Σ_i C(p,i) f_i(r)`. -/
theorem dd_split (u : ℕ → ℝ) (r p : ℕ) :
    dd u (r + p) = ∑ i ∈ range (p + 1), (p.choose i : ℝ) * Szkraw.iterShift u r i := by
  unfold dd
  rw [iterShift_comp, iterShift_eq]
  simp only [zero_add]

/-- `Σ_i f_i(r) C(a,i) [z^m w^n] z^i S^(a-i) Z^r = D_m [z^m w^n] S^a Z^r`. -/
theorem theta_z (u : ℕ → ℝ) (a r m n : ℕ) :
    ∑ i ∈ range (a + 1), Szkraw.iterShift u r i * (a.choose i : ℝ) * Ecf i 0 (a - i) r m n =
      dd u m * Ecf 0 0 a r m n := by
  by_cases h : r ≤ m ∧ r ≤ n ∧ m + n = a + 2 * r
  · obtain ⟨p, rfl⟩ : ∃ p, m = r + p := ⟨m - r, by omega⟩
    have hp : p ≤ a := by omega
    have hE : Ecf 0 0 a r (r + p) n = (a.choose p : ℝ) := by
      unfold Ecf; rw [if_pos (by omega)]
      have e : r + p - 0 - r = p := by omega
      rw [e]
    have hterm : ∀ i ∈ range (a + 1),
        Szkraw.iterShift u r i * (a.choose i : ℝ) * Ecf i 0 (a - i) r (r + p) n =
          (a.choose p : ℝ) * ((p.choose i : ℝ) * Szkraw.iterShift u r i) := by
      intro i hi
      rw [Finset.mem_range] at hi
      unfold Ecf
      by_cases hip : i ≤ p
      · rw [if_pos (by omega)]
        have e : r + p - i - r = p - i := by omega
        rw [e]
        have hc : (a.choose p : ℝ) * (p.choose i : ℝ) = (a.choose i : ℝ) * ((a - i).choose (p - i) : ℝ) := by
          exact_mod_cast Nat.choose_mul hip
        linear_combination (Szkraw.iterShift u r i) * hc.symm
      · rw [if_neg (by omega), Nat.choose_eq_zero_of_lt (by omega : p < i)]; simp
    rw [hE, dd_split, sum_congr rfl hterm, ← mul_sum, mul_comm]
    congr 1
    symm
    apply Finset.sum_subset (Finset.range_subset_range.mpr (by omega))
    intro i hi hni
    simp only [Finset.mem_range] at hi hni
    rw [Nat.choose_eq_zero_of_lt (by omega)]; simp
  · have h0 : Ecf 0 0 a r m n = 0 := by unfold Ecf; rw [if_neg (by omega)]
    rw [h0, mul_zero]
    apply sum_eq_zero
    intro i hi
    rw [Finset.mem_range] at hi
    have h1 : Ecf i 0 (a - i) r m n = 0 := by unfold Ecf; rw [if_neg (by omega)]
    rw [h1, mul_zero]

theorem Ecf_succ_left (i j b r m n : ℕ) :
    Ecf (i + 1) j b r m n = if 1 ≤ m then Ecf i j b r (m - 1) n else 0 := by
  unfold Ecf
  by_cases hm : 1 ≤ m
  · rw [if_pos hm]
    by_cases h : i + 1 + r ≤ m ∧ j + r ≤ n ∧ m + n = i + 1 + j + b + 2 * r
    · rw [if_pos h, if_pos (by omega)]
      have e : m - (i + 1) - r = m - 1 - i - r := by omega
      rw [e]
    · rw [if_neg h, if_neg (by omega)]
  · rw [if_neg hm, if_neg (by omega)]

theorem Ecf_zero_one (a r m n : ℕ) : Ecf 0 1 a r m n = Ecf 0 0 a (r + 1) (m + 1) n := by
  unfold Ecf
  by_cases h : 0 + r ≤ m ∧ 1 + r ≤ n ∧ m + n = 0 + 1 + a + 2 * r
  · rw [if_pos h, if_pos (by omega)]
    have e : m + 1 - 0 - (r + 1) = m - 0 - r := by omega
    rw [e]
  · rw [if_neg h, if_neg (by omega)]

/-! ### The operators `ℒ_z`, `ℒ_w` on coefficient arrays and their images on `S^a Z^r` -/

/-- The coefficient of `z^m w^n` in `ℒ_z F`, `ℒ_z = (z⁻¹ + t - z) D(θ_z) + T z`. -/
noncomputable def Lz (D : ℕ → ℝ) (t T : ℝ) (F : ℕ → ℕ → ℝ) (m n : ℕ) : ℝ :=
  D (m + 1) * F (m + 1) n + t * D m * F m n +
    (if 1 ≤ m then (T - D (m - 1)) * F (m - 1) n else 0)

/-- The coefficient of `z^m w^n` in `ℒ_w F`. -/
noncomputable def Lw (D : ℕ → ℝ) (t T : ℝ) (F : ℕ → ℕ → ℝ) (m n : ℕ) : ℝ :=
  D (n + 1) * F m (n + 1) + t * D n * F m n +
    (if 1 ≤ n then (T - D (n - 1)) * F m (n - 1) else 0)

/-- `z^i w^j (z+w)^b (zw)^r`. -/
noncomputable def mono (i j b r : ℕ) : P2 := X 0 ^ i * X 1 ^ j * (X 0 + X 1) ^ b * (X 0 * X 1) ^ r

theorem cf_mono' (i j b r m n : ℕ) : cf (mono i j b r) m n = Ecf i j b r m n := cf_mono i j b r m n

variable (u : ℕ → ℝ) (t T : ℝ)

/-- `z⁻¹ z^i S^(a-i) Z^r` (for `i = 0`, `w S^a Z^(r-1)`). -/
noncomputable def zinv (r a i : ℕ) : P2 := if i = 0 then mono 0 1 a (r - 1) else mono (i - 1) 0 (a - i) r
noncomputable def winv (r a i : ℕ) : P2 := if i = 0 then mono 1 0 a (r - 1) else mono 0 (i - 1) (a - i) r

/-- `ℒ_z (S^a Z^r)`. -/
noncomputable def LzImg (r a : ℕ) : P2 :=
  ∑ i ∈ range (a + 1), C (Szkraw.iterShift u r i * (a.choose i : ℝ)) *
    (zinv r a i + C t * mono i 0 (a - i) r - mono (i + 1) 0 (a - i) r) + C T * mono 1 0 a r

/-- `ℒ_w (S^a Z^r)`. -/
noncomputable def LwImg (r a : ℕ) : P2 :=
  ∑ i ∈ range (a + 1), C (Szkraw.iterShift u r i * (a.choose i : ℝ)) *
    (winv r a i + C t * mono 0 i (a - i) r - mono 0 (i + 1) (a - i) r) + C T * mono 0 1 a r

theorem cf_LzImg (r a m n : ℕ) :
    cf (LzImg u t T r a) m n =
      ∑ i ∈ range (a + 1), Szkraw.iterShift u r i * (a.choose i : ℝ) * cf (zinv r a i) m n +
      t * ∑ i ∈ range (a + 1), Szkraw.iterShift u r i * (a.choose i : ℝ) * Ecf i 0 (a - i) r m n -
      ∑ i ∈ range (a + 1), Szkraw.iterShift u r i * (a.choose i : ℝ) * Ecf (i + 1) 0 (a - i) r m n +
      T * Ecf 1 0 a r m n := by
  unfold LzImg
  rw [cf_add, cf_sum, cf_C_mul, cf_mono', mul_sum, ← sum_add_distrib, ← sum_sub_distrib]
  congr 1
  apply sum_congr rfl
  intro i _
  rw [cf_C_mul, cf_sub, cf_add, cf_C_mul, cf_mono', cf_mono']
  ring

theorem cf_LwImg (r a m n : ℕ) :
    cf (LwImg u t T r a) m n =
      ∑ i ∈ range (a + 1), Szkraw.iterShift u r i * (a.choose i : ℝ) * cf (winv r a i) m n +
      t * ∑ i ∈ range (a + 1), Szkraw.iterShift u r i * (a.choose i : ℝ) * Ecf 0 i (a - i) r m n -
      ∑ i ∈ range (a + 1), Szkraw.iterShift u r i * (a.choose i : ℝ) * Ecf 0 (i + 1) (a - i) r m n +
      T * Ecf 0 1 a r m n := by
  unfold LwImg
  rw [cf_add, cf_sum, cf_C_mul, cf_mono', mul_sum, ← sum_add_distrib, ← sum_sub_distrib]
  congr 1
  apply sum_congr rfl
  intro i _
  rw [cf_C_mul, cf_sub, cf_add, cf_C_mul, cf_mono', cf_mono']
  ring

theorem cf_winv_swap (r a i m n : ℕ) : cf (winv r a i) m n = cf (zinv r a i) n m := by
  unfold winv zinv
  split_ifs <;> rw [cf_mono', cf_mono', Ecf_swap]

/-- The `ℒ_z` image of `S^a Z^r`, coefficientwise. Needs `u 0 = 0` (so `D_0 = 0`). -/
theorem Lz_mono (hu0 : u 0 = 0) (r a m n : ℕ) :
    Lz (dd u) t T (fun m n => Ecf 0 0 a r m n) m n = cf (LzImg u t T r a) m n := by
  have h1 : ∑ i ∈ range (a + 1), Szkraw.iterShift u r i * (a.choose i : ℝ) * cf (zinv r a i) m n =
      dd u (m + 1) * Ecf 0 0 a r (m + 1) n := by
    rw [← theta_z]
    apply sum_congr rfl
    intro i _
    unfold zinv
    by_cases hi : i = 0
    · subst hi
      rw [if_pos rfl, cf_mono']
      rcases Nat.eq_zero_or_pos r with hr | hr
      · subst hr
        have : Szkraw.iterShift u 0 0 = 0 := hu0
        rw [this]; ring
      · obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
        rw [Nat.add_sub_cancel, Ecf_zero_one, Nat.sub_zero]
    · rw [if_neg hi, cf_mono']
      obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
      rw [Ecf_succ_left, if_pos (by omega), Nat.add_sub_cancel, Nat.add_sub_cancel]
  have h2 := theta_z u a r m n
  have h3 : ∑ i ∈ range (a + 1), Szkraw.iterShift u r i * (a.choose i : ℝ) * Ecf (i + 1) 0 (a - i) r m n =
      if 1 ≤ m then dd u (m - 1) * Ecf 0 0 a r (m - 1) n else 0 := by
    simp_rw [Ecf_succ_left]
    split_ifs
    · exact theta_z u a r (m - 1) n
    · simp
  rw [cf_LzImg, h1, h2, h3, Ecf_succ_left]
  unfold Lz
  split_ifs <;> ring

theorem Lw_mono (hu0 : u 0 = 0) (r a m n : ℕ) :
    Lw (dd u) t T (fun m n => Ecf 0 0 a r m n) m n = cf (LwImg u t T r a) m n := by
  have hz := Lz_mono u t T hu0 r a n m
  have hs : (fun m n => Ecf 0 0 a r n m) = (fun m n => Ecf 0 0 a r m n) := by
    funext m n; rw [Ecf_swap]
  have hL : Lw (dd u) t T (fun m n => Ecf 0 0 a r m n) m n =
      Lz (dd u) t T (fun m n => Ecf 0 0 a r n m) n m := rfl
  rw [hL, hs, hz, cf_LzImg, cf_LwImg]
  simp_rw [cf_winv_swap]
  have e1 : ∑ i ∈ range (a + 1), Szkraw.iterShift u r i * (a.choose i : ℝ) * Ecf i 0 (a - i) r n m =
      ∑ i ∈ range (a + 1), Szkraw.iterShift u r i * (a.choose i : ℝ) * Ecf 0 i (a - i) r m n :=
    sum_congr rfl (fun i _ => by rw [Ecf_swap])
  have e2 : ∑ i ∈ range (a + 1), Szkraw.iterShift u r i * (a.choose i : ℝ) * Ecf (i + 1) 0 (a - i) r n m =
      ∑ i ∈ range (a + 1), Szkraw.iterShift u r i * (a.choose i : ℝ) * Ecf 0 (i + 1) (a - i) r m n :=
    sum_congr rfl (fun i _ => by rw [Ecf_swap])
  rw [e1, e2, Ecf_swap 1 0 a r n m]

/-! ### The symmetric-side image `M = (ℒ_z - ℒ_w)/(z - w)` of `S^a Z^r` -/

/-- Term `i` of `M(S^a Z^r)` (with `X 0 = S`, `X 1 = Z`). -/
noncomputable def Mterm (r a i : ℕ) : P2 :=
  (if i = 0 then -(X 0 ^ a * X 1 ^ (r - 1)) else if i = 1 then 0 else X 0 ^ (a - i) * X 1 ^ r * hh (i - 2)) +
  C t * (if i = 0 then 0 else X 0 ^ (a - i) * X 1 ^ r * hh (i - 1)) - X 0 ^ (a - i) * X 1 ^ r * hh i

/-- `M(S^a Z^r)`. -/
noncomputable def Mu (r a : ℕ) : P2 :=
  C T * (X 0 ^ a * X 1 ^ r) +
    ∑ i ∈ range (a + 1), C (Szkraw.iterShift u r i * (a.choose i : ℝ)) * Mterm t r a i

theorem ι_C (c : ℝ) : ι (C c) = C c := by simp [ι, MvPolynomial.algebraMap_eq]

theorem Mterm_spec (r a i : ℕ) :
    (X 0 - X 1) * ι (Mterm t r a i) =
      (zinv r a i + C t * mono i 0 (a - i) r - mono (i + 1) 0 (a - i) r) -
      (winv r a i + C t * mono 0 i (a - i) r - mono 0 (i + 1) (a - i) r) := by
  unfold Mterm zinv winv mono
  by_cases h0 : i = 0
  · subst h0
    simp only [if_true, map_add, map_sub, map_neg, map_mul, map_pow, ι_X0, ι_X1, hh_zero,
      map_one, map_zero, Nat.sub_zero, mul_zero]
    ring
  by_cases h1 : i = 1
  · subst h1
    simp only [if_neg (show (1 : ℕ) ≠ 0 by omega), if_true, map_add, map_sub, map_mul, map_pow,
      ι_X0, ι_X1, ι_C, map_zero, Nat.sub_self, hh_zero, hh_one, map_one]
    ring
  obtain ⟨k, rfl⟩ : ∃ k, i = k + 2 := ⟨i - 2, by omega⟩
  have e1 : k + 2 - 2 = k := by omega
  have e2 : k + 2 - 1 = k + 1 := by omega
  simp only [show k + 2 ≠ 0 by omega, show k + 2 ≠ 1 by omega, if_false, map_add, map_sub,
    map_mul, map_pow, ι_X0, ι_X1, ι_C, e1, e2]
  have s0 := hh_spec k
  have s1 := hh_spec (k + 1)
  have s2 := hh_spec (k + 2)
  linear_combination ((X 0 + X 1) ^ (a - (k + 2)) * (X 0 * X 1) ^ r) * s0 +
    (C t * ((X 0 + X 1) ^ (a - (k + 2)) * (X 0 * X 1) ^ r)) * s1 -
    ((X 0 + X 1) ^ (a - (k + 2)) * (X 0 * X 1) ^ r) * s2

/-- `ℒ_z(S^aZ^r) - ℒ_w(S^aZ^r) = (z - w) M(S^aZ^r)`. -/
theorem image_diff (r a : ℕ) :
    LzImg u t T r a - LwImg u t T r a = (X 0 - X 1) * ι (Mu u t T r a) := by
  unfold LzImg LwImg Mu
  rw [map_add, map_mul ι, ι_C, map_sum ι, mul_add, mul_sum]
  have hT : C T * mono 1 0 a r - C T * mono 0 1 a r = (X 0 - X 1) * (C T * ι (X 0 ^ a * X 1 ^ r)) := by
    unfold mono; simp only [map_mul, map_pow, ι_X0, ι_X1]; ring
  have hs : ∀ i ∈ range (a + 1),
      C (Szkraw.iterShift u r i * (a.choose i : ℝ)) *
          (zinv r a i + C t * mono i 0 (a - i) r - mono (i + 1) 0 (a - i) r) -
        C (Szkraw.iterShift u r i * (a.choose i : ℝ)) *
          (winv r a i + C t * mono 0 i (a - i) r - mono 0 (i + 1) (a - i) r) =
      (X 0 - X 1) * ι (C (Szkraw.iterShift u r i * (a.choose i : ℝ)) * Mterm t r a i) := by
    intro i _
    rw [map_mul ι, ι_C, mul_left_comm, Mterm_spec]; ring
  rw [← sum_congr rfl hs, sum_sub_distrib, ← hT]
  ring

/-! ### Coefficients of `M(S^a Z^r)` on the symmetric side -/

theorem cf_X0pow_mul (p : ℕ) (P : P2) (x y : ℕ) :
    cf (X 0 ^ p * P) x y = if p ≤ x then cf P (x - p) y else 0 := by
  induction p generalizing x with
  | zero => simp
  | succ p ih =>
    rw [pow_succ, mul_comm (X 0 ^ p) (X 0), mul_assoc, cf_X0_mul]
    by_cases hx : 1 ≤ x
    · rw [if_pos hx, ih]
      by_cases hp : p ≤ x - 1
      · rw [if_pos hp, if_pos (by omega)]
        congr 1; omega
      · rw [if_neg hp, if_neg (by omega)]
    · rw [if_neg hx, if_neg (by omega)]

theorem cf_X1pow_mul (q : ℕ) (P : P2) (x y : ℕ) :
    cf (X 1 ^ q * P) x y = if q ≤ y then cf P x (y - q) else 0 := by
  induction q generalizing y with
  | zero => simp
  | succ q ih =>
    rw [pow_succ, mul_comm (X 1 ^ q) (X 1), mul_assoc, cf_X1_mul]
    by_cases hy : 1 ≤ y
    · rw [if_pos hy, ih]
      by_cases hq : q ≤ y - 1
      · rw [if_pos hq, if_pos (by omega)]
        congr 1; omega
      · rw [if_neg hq, if_neg (by omega)]
    · rw [if_neg hy, if_neg (by omega)]

theorem cf_shift_hh (b r n x y : ℕ) :
    cf (X 0 ^ b * X 1 ^ r * hh n) x y =
      if b ≤ x ∧ r ≤ y ∧ (x - b) + 2 * (y - r) = n then
        (-1 : ℝ) ^ (y - r) * ((n - (y - r)).choose (y - r) : ℝ) else 0 := by
  rw [mul_assoc, cf_X0pow_mul, cf_X1pow_mul, cf_hh]
  by_cases h1 : b ≤ x <;> by_cases h2 : r ≤ y <;> simp [h1, h2]

/-- The `s`-shifted part of term `i`: `[z^x w^y] S^(a-i) Z^r h_(i-s)` (zero for `i < s`). -/
noncomputable def Gi (r a s i x y : ℕ) : ℝ :=
  if s ≤ i then cf (X 0 ^ (a - i) * X 1 ^ r * hh (i - s)) x y else 0

theorem cf_Mterm (r a i x y : ℕ) :
    cf (Mterm t r a i) x y =
      (if i = 0 then -(if a = x ∧ r - 1 = y then 1 else 0) else 0) +
        Gi r a 2 i x y + t * Gi r a 1 i x y - Gi r a 0 i x y := by
  unfold Mterm Gi
  by_cases h0 : i = 0
  · subst h0
    simp only [if_true, cf_sub, cf_add, cf_neg, cf_XX, cf_zero, mul_zero, Nat.sub_zero,
      Nat.zero_le, show ¬(2 ≤ 0) by omega, show ¬(1 ≤ 0) by omega, if_false]
    ring
  by_cases h1 : i = 1
  · subst h1
    simp only [show (1 : ℕ) ≠ 0 by omega, if_true, if_false, cf_sub, cf_add, cf_C_mul, cf_zero,
      Nat.zero_le, show ¬(2 ≤ 1) by omega, show (1 ≤ 1) by omega, Nat.sub_zero]
    ring
  · rw [if_neg h0, if_neg h0, if_neg h1, if_neg h0, if_pos (by omega), if_pos (by omega),
      if_pos (by omega), cf_sub, cf_add, cf_C_mul, Nat.sub_zero]
    ring

/-- Summing the `s`-shifted parts against `f_i(r) C(a,i)` gives one `W` weight. -/
theorem sum_Gi (r a s x y : ℕ) :
    ∑ i ∈ range (a + 1), Szkraw.iterShift u r i * (a.choose i : ℝ) * Gi r a s i x y =
      if r ≤ y ∧ x + 2 * (y - r) + s = a then
        (-1 : ℝ) ^ (y - r) * Wt u (2 * (y - r) + s) (y - r) r a else 0 := by
  unfold Gi
  simp_rw [cf_shift_hh]
  by_cases h : r ≤ y ∧ x + 2 * (y - r) + s = a
  · rw [if_pos h]
    unfold Wt
    rw [mul_sum]
    apply sum_congr rfl
    intro i hi
    rw [Finset.mem_range] at hi
    by_cases hi2 : 2 * (y - r) + s ≤ i
    · rw [if_pos (by omega), if_pos (by omega), if_pos hi2]
      have e : i - s - (y - r) = i - (2 * (y - r) + s) + (y - r) := by omega
      rw [e]; ring
    · rw [if_neg hi2]
      by_cases hs : s ≤ i
      · rw [if_pos hs, if_neg (by omega)]; ring
      · rw [if_neg hs]; ring
  · rw [if_neg h]
    apply sum_eq_zero
    intro i hi
    rw [Finset.mem_range] at hi
    by_cases hs : s ≤ i
    · rw [if_pos hs, if_neg (by omega), mul_zero]
    · rw [if_neg hs, mul_zero]

theorem cf_Mu (r a x y : ℕ) :
    cf (Mu u t T r a) x y =
      T * (if a = x ∧ r = y then 1 else 0) - Szkraw.iterShift u r 0 * (if a = x ∧ r - 1 = y then 1 else 0) +
      (if r ≤ y ∧ x + 2 * (y - r) + 2 = a then
        (-1 : ℝ) ^ (y - r) * Wt u (2 * (y - r) + 2) (y - r) r a else 0) +
      t * (if r ≤ y ∧ x + 2 * (y - r) + 1 = a then
        (-1 : ℝ) ^ (y - r) * Wt u (2 * (y - r) + 1) (y - r) r a else 0) -
      (if r ≤ y ∧ x + 2 * (y - r) + 0 = a then
        (-1 : ℝ) ^ (y - r) * Wt u (2 * (y - r) + 0) (y - r) r a else 0) := by
  unfold Mu
  rw [cf_add, cf_C_mul, cf_XX, cf_sum]
  simp only [cf_C_mul, cf_Mterm, mul_add, mul_sub, sum_add_distrib, sum_sub_distrib]
  rw [← sum_Gi u r a 2 x y, ← sum_Gi u r a 1 x y, ← sum_Gi u r a 0 x y, mul_sum]
  have h0 : ∑ i ∈ range (a + 1), Szkraw.iterShift u r i * (a.choose i : ℝ) *
      (if i = 0 then -(if a = x ∧ r - 1 = y then (1 : ℝ) else 0) else 0) =
      -(Szkraw.iterShift u r 0 * (if a = x ∧ r - 1 = y then 1 else 0)) := by
    rw [Finset.sum_eq_single 0]
    · simp
    · intro i _ hi; rw [if_neg hi, mul_zero]
    · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h
  rw [h0]
  have e : ∀ i ∈ range (a + 1), Szkraw.iterShift u r i * (a.choose i : ℝ) * (t * Gi r a 1 i x y) =
      t * (Szkraw.iterShift u r i * (a.choose i : ℝ) * Gi r a 1 i x y) := fun i _ => by ring
  rw [sum_congr rfl e]
  ring

/-! ### Assembly: the kernel recurrence (8.1) gives the coefficient relation `ℒ_z K = ℒ_w K` -/

theorem box_point (N : ℕ) (ω : ℕ → ℕ → ℝ) (hsupp : ∀ r a, N < r + a → ω r a = 0) (c : ℝ) (x y : ℕ) :
    ∑ r ∈ range (N + 1), ∑ a ∈ range (N + 1), ω r a * (c * if a = x ∧ r = y then 1 else 0) =
      ω y x * c := by
  by_cases hin : y ≤ N ∧ x ≤ N
  · rw [Finset.sum_eq_single y]
    · rw [Finset.sum_eq_single x]
      · simp
      · intro a _ ha; rw [if_neg (fun h => ha h.1)]; simp
      · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h
    · intro r _ hr; apply sum_eq_zero; intro a _; rw [if_neg (fun h => hr h.2)]; simp
    · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h
  · rw [hsupp y x (by omega), zero_mul]
    apply sum_eq_zero; intro r hr; apply sum_eq_zero; intro a ha
    rw [Finset.mem_range] at hr ha
    rw [if_neg (by omega)]; simp

theorem box_line (N : ℕ) (ω : ℕ → ℕ → ℝ) (hsupp : ∀ r a, N < r + a → ω r a = 0)
    (g : ℕ → ℕ → ℝ) (x y s : ℕ) :
    ∑ r ∈ range (N + 1), ∑ a ∈ range (N + 1),
        ω r a * (if r ≤ y ∧ x + 2 * (y - r) + s = a then g r a else 0) =
      ∑ l ∈ range (y + 1), ω (y - l) (x + 2 * l + s) * g (y - l) (x + 2 * l + s) := by
  set F : ℕ → ℝ := fun r => ω r (x + 2 * (y - r) + s) * g r (x + 2 * (y - r) + s) with hF
  have inner : ∀ r ∈ range (N + 1), ∑ a ∈ range (N + 1),
      ω r a * (if r ≤ y ∧ x + 2 * (y - r) + s = a then g r a else 0) = if r ≤ y then F r else 0 := by
    intro r _
    by_cases hry : r ≤ y
    · rw [if_pos hry]
      by_cases hc : x + 2 * (y - r) + s ≤ N
      · rw [Finset.sum_eq_single (x + 2 * (y - r) + s)]
        · rw [if_pos ⟨hry, rfl⟩]
        · intro a _ ha; rw [if_neg (fun h => ha h.2.symm), mul_zero]
        · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h
      · rw [hF]; simp only
        rw [hsupp r _ (by omega), zero_mul]
        apply sum_eq_zero; intro a ha; rw [Finset.mem_range] at ha
        rw [if_neg (by omega), mul_zero]
    · rw [if_neg hry]; apply sum_eq_zero; intro a _; rw [if_neg (fun h => hry h.1), mul_zero]
  rw [sum_congr rfl inner]
  have hFz : ∀ r, N < r → F r = 0 := fun r hr => by rw [hF]; simp only; rw [hsupp r _ (by omega), zero_mul]
  have e1 : ∑ r ∈ range (N + 1), (if r ≤ y then F r else 0) =
      ∑ r ∈ range (N + y + 2), (if r ≤ y then F r else 0) := by
    apply Finset.sum_subset (Finset.range_subset_range.mpr (by omega))
    intro r _ hr; rw [Finset.mem_range] at hr
    split_ifs
    · exact hFz r (by omega)
    · rfl
  have e2 : ∑ r ∈ range (y + 1), F r = ∑ r ∈ range (N + y + 2), (if r ≤ y then F r else 0) := by
    rw [← Finset.sum_subset (Finset.range_subset_range.mpr (by omega : y + 1 ≤ N + y + 2))]
    · apply sum_congr rfl; intro r hr; rw [Finset.mem_range] at hr; rw [if_pos (by omega)]
    · intro r _ hr; rw [Finset.mem_range] at hr; rw [if_neg (by omega)]
  rw [e1, ← e2, ← Finset.sum_range_reflect]
  apply sum_congr rfl
  intro l hl
  rw [Finset.mem_range] at hl
  rw [hF]
  simp only
  have e3 : y + 1 - 1 - l = y - l := by omega
  have e4 : y - (y - l) = l := by omega
  rw [e3, e4]

variable {u t T}

theorem Wt_zero_zero (r a : ℕ) : Wt u 0 0 r a = dd u (r + a) := by
  unfold Wt
  rw [dd_split]
  apply sum_congr rfl
  intro n _
  simp [mul_comm]

/-- Recurrence (8.1) makes `Σ ω_{r,a} M(S^a Z^r)` vanish. -/
theorem kernel_poly_zero (hu0 : u 0 = 0) (N : ℕ) (ω : ℕ → ℕ → ℝ) (hrec : KernelRec u t ω T)
    (hsupp : ∀ r a, N < r + a → ω r a = 0) :
    ∑ r ∈ range (N + 1), ∑ a ∈ range (N + 1), C (ω r a) * Mu u t T r a = 0 := by
  apply P2_ext; intro x y
  rw [cf_zero, cf_sum]
  simp only [cf_sum, cf_C_mul, cf_Mu]
  have hf0 : ∀ r a, ω r a * (Szkraw.iterShift u r 0 * if a = x ∧ r - 1 = y then 1 else 0) =
      ω r a * (Szkraw.iterShift u (y + 1) 0 * if a = x ∧ r = y + 1 then 1 else 0) := by
    intro r a
    by_cases hr : r = 0
    · subst hr
      have : Szkraw.iterShift u 0 0 = 0 := hu0
      rw [this, if_neg (show ¬(a = x ∧ (0 : ℕ) = y + 1) by omega)]; ring
    · by_cases h : a = x ∧ r = y + 1
      · rw [if_pos ⟨h.1, by omega⟩, if_pos h, h.2]
      · rw [if_neg (by omega), if_neg h]; ring
  simp only [mul_add, mul_sub, sum_add_distrib, sum_sub_distrib]
  simp only [hf0]
  rw [box_point N ω hsupp, box_point N ω hsupp]
  have ht : ∀ r a, ω r a * (t * if r ≤ y ∧ x + 2 * (y - r) + 1 = a then
      (-1 : ℝ) ^ (y - r) * Wt u (2 * (y - r) + 1) (y - r) r a else 0) =
      t * (ω r a * if r ≤ y ∧ x + 2 * (y - r) + 1 = a then
      (-1 : ℝ) ^ (y - r) * Wt u (2 * (y - r) + 1) (y - r) r a else 0) := fun r a => by ring
  simp only [ht, ← mul_sum]
  rw [box_line N ω hsupp _ x y 2, box_line N ω hsupp _ x y 1, box_line N ω hsupp _ x y 0]
  -- normalize `y - (y - l) = l`
  have norm : ∀ s : ℕ, ∑ l ∈ range (y + 1), ω (y - l) (x + 2 * l + s) *
      ((-1 : ℝ) ^ (y - (y - l)) * Wt u (2 * (y - (y - l)) + s) (y - (y - l)) (y - l) (x + 2 * l + s)) =
      ∑ l ∈ range (y + 1), (-1 : ℝ) ^ l * (Wt u (2 * l + s) l (y - l) (x + 2 * l + s) *
        ω (y - l) (x + 2 * l + s)) := by
    intro s
    apply sum_congr rfl; intro l hl; rw [Finset.mem_range] at hl
    have e : y - (y - l) = l := by omega
    rw [e]; ring
  rw [norm 2, norm 1, norm 0]
  -- the kernel recurrence at `(y, x)`
  have hr := hrec y x
  unfold grp moveA moveB moveC at hr
  simp only [mul_add, sum_add_distrib] at hr
  -- C-moves against the shifted zero-part
  have hC : ∑ j ∈ range (y + 1), (-1 : ℝ) ^ j * (if j < y then
        Wt u (2 * j + 2) (j + 1) (y - j - 1) (x + 2 * j + 2) * ω (y - j - 1) (x + 2 * j + 2) else 0) =
      -(∑ l ∈ range (y + 1), (-1 : ℝ) ^ l * (Wt u (2 * l + 0) l (y - l) (x + 2 * l + 0) *
        ω (y - l) (x + 2 * l + 0))) + dd u (y + x) * ω y x := by
    rw [Finset.sum_range_succ, if_neg (lt_irrefl y), mul_zero, add_zero, Finset.sum_range_succ']
    have h0 : (-1 : ℝ) ^ 0 * (Wt u (2 * 0 + 0) 0 (y - 0) (x + 2 * 0 + 0) * ω (y - 0) (x + 2 * 0 + 0)) =
        dd u (y + x) * ω y x := by
      simp only [pow_zero, one_mul, mul_zero, add_zero, Nat.sub_zero]; rw [Wt_zero_zero]
    rw [h0, neg_add, neg_add_cancel_right, ← sum_neg_distrib]
    apply sum_congr rfl; intro j hj; rw [Finset.mem_range] at hj
    rw [if_pos hj]
    have e1 : 2 * (j + 1) + 0 = 2 * j + 2 := by ring
    have e2 : y - (j + 1) = y - j - 1 := by omega
    have e3 : x + 2 * (j + 1) + 0 = x + 2 * j + 2 := by ring
    rw [e1, e2, e3, pow_succ]; ring
  have hA : ∑ j ∈ range (y + 1), (-1 : ℝ) ^ j * (t * Wt u (2 * j + 1) j (y - j) (x + 2 * j + 1) *
        ω (y - j) (x + 2 * j + 1)) =
      t * ∑ l ∈ range (y + 1), (-1 : ℝ) ^ l * (Wt u (2 * l + 1) l (y - l) (x + 2 * l + 1) *
        ω (y - l) (x + 2 * l + 1)) := by
    rw [mul_sum]; apply sum_congr rfl; intro j _; ring
  rw [hC, hA] at hr
  unfold dd at hr
  linear_combination -hr

/-- The coefficient array `L(m,n) = [z^m w^n] Σ ω_{r,a} S^a Z^r`. -/
noncomputable def Lker (N : ℕ) (ω : ℕ → ℕ → ℝ) (m n : ℕ) : ℝ :=
  ∑ r ∈ range (N + 1), ∑ a ∈ range (N + 1), ω r a * Ecf 0 0 a r m n

theorem Lz_sum {ι : Type*} (D : ℕ → ℝ) (t T : ℝ) (s : Finset ι) (F : ι → ℕ → ℕ → ℝ) (m n : ℕ) :
    Lz D t T (fun m n => ∑ x ∈ s, F x m n) m n = ∑ x ∈ s, Lz D t T (F x) m n := by
  unfold Lz; split_ifs <;> simp [mul_sum, sum_add_distrib]

theorem Lw_sum {ι : Type*} (D : ℕ → ℝ) (t T : ℝ) (s : Finset ι) (F : ι → ℕ → ℕ → ℝ) (m n : ℕ) :
    Lw D t T (fun m n => ∑ x ∈ s, F x m n) m n = ∑ x ∈ s, Lw D t T (F x) m n := by
  unfold Lw; split_ifs <;> simp [mul_sum, sum_add_distrib]

theorem Lz_smul (D : ℕ → ℝ) (t T c : ℝ) (F : ℕ → ℕ → ℝ) (m n : ℕ) :
    Lz D t T (fun m n => c * F m n) m n = c * Lz D t T F m n := by
  unfold Lz; split_ifs <;> ring

theorem Lw_smul (D : ℕ → ℝ) (t T c : ℝ) (F : ℕ → ℕ → ℝ) (m n : ℕ) :
    Lw D t T (fun m n => c * F m n) m n = c * Lw D t T F m n := by
  unfold Lw; split_ifs <;> ring

/-- F4: for a solution of (8.1) with the support property, the coefficient array of
`Σ ω_{r,a} S^a Z^r` satisfies `ℒ_z L = ℒ_w L` coefficientwise. -/
theorem kernel_star (hu0 : u 0 = 0) (N : ℕ) (ω : ℕ → ℕ → ℝ) (hrec : KernelRec u t ω T)
    (hsupp : ∀ r a, N < r + a → ω r a = 0) (m n : ℕ) :
    Lz (dd u) t T (Lker N ω) m n = Lw (dd u) t T (Lker N ω) m n := by
  have hz : Lz (dd u) t T (Lker N ω) m n = ∑ r ∈ range (N + 1), ∑ a ∈ range (N + 1),
      ω r a * Lz (dd u) t T (fun m n => Ecf 0 0 a r m n) m n := by
    unfold Lker
    rw [Lz_sum]; apply sum_congr rfl; intro r _
    rw [Lz_sum]; apply sum_congr rfl; intro a _
    rw [Lz_smul]
  have hw : Lw (dd u) t T (Lker N ω) m n = ∑ r ∈ range (N + 1), ∑ a ∈ range (N + 1),
      ω r a * Lw (dd u) t T (fun m n => Ecf 0 0 a r m n) m n := by
    unfold Lker
    rw [Lw_sum]; apply sum_congr rfl; intro r _
    rw [Lw_sum]; apply sum_congr rfl; intro a _
    rw [Lw_smul]
  rw [← sub_eq_zero, hz, hw, ← sum_sub_distrib]
  have hpoly := congrArg (fun p => cf ((X 0 - X 1) * ι p) m n) (kernel_poly_zero hu0 N ω hrec hsupp)
  simp only [map_zero, mul_zero, cf_zero, map_sum, mul_sum, cf_sum, map_mul ι, ι_C] at hpoly
  rw [← hpoly]
  apply sum_congr rfl; intro r _
  rw [← sum_sub_distrib]
  apply sum_congr rfl; intro a _
  rw [← mul_sub, Lz_mono u t T hu0, Lw_mono u t T hu0, ← cf_sub, image_diff, mul_left_comm, cf_C_mul]

end Szkraw
