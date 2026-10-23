import Szkraw.SignPattern
import Szkraw.RuleCounterexamples
import Szkraw.AllProducts
import Szkraw.Reversal
import Szkraw.ParitySplit

/-!
# P3: exact remarks outside the numbered results

* `g111`, `g222`: closed forms of `g(1,1;1)` and `g(2,2;2)` for any array.
* After Corollary 8.4 (heavy top): the bound `d_{N-1} ≤ 1/2` is sharp (`heavy_top_sharp`), the corollary contains the
  arrays (eq:parameters) with `q ≥ 2` but not the Krawtchouk arrays with `N ≥ 3`, the profile need not be convex
  (`heavy_top_scope`), and convex profiles with `d_0 = 0` are superadditive (`convex_superadditive`).
* After Corollary 7.7: perturbing `K_{2,1}` by `c_1 = 1/2 + ε`, `a_1 = 1/2 - ε` keeps the positive coefficients
  positive but gives `g(2,2;2) = -2ε/(1/2 - ε)` (`k21_perturbation`).
* End of Section 8: reversal obstructions (`reversal_obstruction_kraw`, `reversal_obstruction_szwarc`) and the
  failure of Miclo's monotonicity condition for the symmetric Krawtchouk chain (`miclo_condition_fails`).
* Section 9: along the terminal row, `g(N,N;N)` is a polynomial in the perturbation (`terminal_polynomial`).
-/

namespace Szkraw

open Finset

variable {N : ℕ}

/-! ### `g(1,1;1)` and `g(2,2;2)` -/

theorem g111 (v : Coefficients N) (hN : 1 ≤ N) :
    productMatrix v 1 ⟨1, by omega⟩ ⟨1, by omega⟩ = (v.b 1 - v.b 0) / v.a 0 := by
  rw [show productMatrix v 1 = (v.a 0)⁻¹ • ((recurrenceMatrix v - v.b 0 • (1 : Matrix _ _ ℝ)) * 1 -
    v.c 0 • (0 : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)) from rfl]
  simp [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, recurrenceMatrix]
  ring

theorem g222 (v : Coefficients N) (hN : 2 ≤ N) (ha0 : v.a 0 ≠ 0) (ha1 : v.a 1 ≠ 0) :
    productMatrix v 2 ⟨2, by omega⟩ ⟨2, by omega⟩ =
      ((if 3 ≤ N then v.a 2 * v.c 3 else 0) + (v.b 2 - v.b 1) * (v.b 2 - v.b 0) + v.c 2 * v.a 1 -
        v.a 0 * v.c 1) / (v.a 0 * v.a 1) := by
  have hP1 : ∀ l : Fin (N + 1), productMatrix v 1 l ⟨2, by omega⟩ =
      (v.a 0)⁻¹ * ((if 2 = l.val + 1 then v.a l else 0) + (if 2 = l.val then v.b l else 0) +
        (if 2 + 1 = l.val then v.c l else 0) - (if l.val = 2 then v.b 0 else 0)) := by
    intro l
    rw [show productMatrix v 1 = (v.a 0)⁻¹ • ((recurrenceMatrix v - v.b 0 • (1 : Matrix _ _ ℝ)) * 1 -
      v.c 0 • (0 : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)) from rfl]
    simp only [Matrix.mul_one, smul_zero, sub_zero, Matrix.smul_apply, Matrix.sub_apply, Matrix.one_apply,
      smul_eq_mul, J_entry]
    congr 1
    have e : (l = ⟨2, by omega⟩) ↔ l.val = 2 := by rw [Fin.ext_iff]
    by_cases h : l.val = 2
    · rw [if_pos (e.2 h), if_pos h]; ring
    · rw [if_neg (fun h' => h (e.1 h')), if_neg h]; ring
  rw [show productMatrix v 2 = (v.a 1)⁻¹ • ((recurrenceMatrix v - v.b 1 • (1 : Matrix _ _ ℝ)) * productMatrix v 1 -
    v.c 1 • (matrixPair v 1).1) from rfl]
  have h0 : (matrixPair v 1).1 = 1 := rfl
  simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul, smul_eq_mul,
    h0, Matrix.one_apply_eq]
  rw [J_mul_apply v _ (fun l : ℕ => (v.a 0)⁻¹ * ((if 2 = l + 1 then v.a l else 0) + (if 2 = l then v.b l else 0) +
      (if 2 + 1 = l then v.c l else 0) - (if l = 2 then v.b 0 else 0))) ⟨2, by omega⟩ ⟨2, by omega⟩ hP1,
    hP1 ⟨2, by omega⟩]
  simp only [Fin.val_mk, show (2 : ℕ) - 1 = 1 by rfl]
  split_ifs <;> first | omega | (field_simp; ring)

/-! ### Heavy top (P3, after Corollary 8.4) -/

/-- The constant-ratio array with `N = 2`, `r = 1` and `d_1 = x`. -/
noncomputable def heavyEx (x : ℝ) : Coefficients 2 where
  a i := if i = 0 then 1 else if i = 1 then 1 - x else 0
  b _ := 0
  c i := if i = 0 then 0 else if i = 1 then x else 1

/-- **Sharpness of `d_{N-1} ≤ 1/2`**: for `N = 2`, `r = 1`, `g(2,2;2) = (1 - 2 d_1)/(1 - d_1)`, negative when
`1/2 < d_1 < 1`. -/
theorem heavy_top_sharp (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1) :
    Admissible (heavyEx x) ∧ (∀ i, i ≤ 2 → (heavyEx x).c i = 1 * profile (heavyEx x) i) ∧
    productMatrix (heavyEx x) 2 2 2 = (1 - 2 * x) / (1 - x) ∧ (1 / 2 < x → productMatrix (heavyEx x) 2 2 2 < 0) := by
  have h1x : 1 - x ≠ 0 := by linarith
  have hg : productMatrix (heavyEx x) 2 2 2 = (1 - 2 * x) / (1 - x) := by
    rw [show (2 : Fin 3) = ⟨2, by omega⟩ from rfl, g222 _ le_rfl (by simp [heavyEx]) (by simp [heavyEx]; linarith)]
    simp [heavyEx]
    field_simp
    ring
  refine ⟨⟨by norm_num, by simp [heavyEx], rfl, by simp [heavyEx], by simp [heavyEx], fun i hi => ?_,
    fun i hi => ?_, fun i hi hi2 => ?_⟩, fun i hi => by simp [heavyEx, profile], hg, fun hx => ?_⟩
  · interval_cases i <;> simp [heavyEx]
  · interval_cases i <;> simp [heavyEx] <;> linarith
  · interval_cases i <;> simp [heavyEx] <;> linarith
  · rw [hg]; exact div_neg_of_neg_of_pos (by linarith) (by linarith)

/-- **Scope of Corollary 8.4**: it contains the arrays (eq:parameters) with `q ≥ 2` (`d_{N-1} ≤ 1/2`) but not the
Krawtchouk arrays with `N ≥ 3` (`d_{N-1} = (N-1)/N > 1/2`); the profile need not be convex. -/
theorem heavy_top_scope :
    (∀ N : ℕ, 1 ≤ N → ∀ p q : ℝ, 1 ≤ p → 2 ≤ q → profile (geometricCoefficients N p q) (N - 1) ≤ 1 / 2) ∧
    (∀ N : ℕ, 3 ≤ N → ∀ r : ℝ, 0 < r → 1 / 2 < profile (krawCoefficients N r) (N - 1)) ∧
    (∃ v : Coefficients 3, Admissible v ∧ HeavyTop v ∧
      profile v 2 - profile v 1 < profile v 1 - profile v 0 ∧ MatrixPositivity v) := by
  refine ⟨fun N hN p q hp hq => ?_, fun N hN r hr => ?_, ?_⟩
  · have hp0 : 0 < p := by linarith
    rw [profile_geometric N p q hp0]
    have hq1 : (0 : ℝ) < q - 1 := by linarith
    have a1 := qInteger_mul q (N - 1)
    have a2 := qInteger_mul q N
    have hpos : 0 < qInteger q N := qInteger_pos q (by linarith) N (by omega)
    rw [div_le_iff₀ hpos]
    have hqN : q ^ N = q * q ^ (N - 1) := by rw [← pow_succ', Nat.sub_add_cancel hN]
    have h1 : 1 ≤ q ^ (N - 1) := one_le_pow₀ (by linarith)
    nlinarith
  · simp only [profile, krawCoefficients]
    have hN' : (3 : ℝ) ≤ N := by exact_mod_cast hN
    rw [Nat.cast_sub (by omega)]
    push_cast
    rw [show (1 - r) * ((N : ℝ) - 1) / N + r * ((N : ℝ) - 1) / N = ((N : ℝ) - 1) / N by ring, lt_div_iff₀ (by linarith)]
    linarith
  · let v : Coefficients 3 :=
      ⟨fun i => 1 - (if i = 0 then 0 else if i = 1 then 2 / 5 else if i = 2 then 9 / 20 else 1),
       fun i => (1 - 1 / 2) * (if i = 0 then 0 else if i = 1 then 2 / 5 else if i = 2 then 9 / 20 else 1),
       fun i => 1 / 2 * (if i = 0 then 0 else if i = 1 then 2 / 5 else if i = 2 then 9 / 20 else 1)⟩
    have hadm : Admissible v := by
      refine ⟨by norm_num, by simp [v], by simp [v], by simp [v], by simp [v], fun i _ => by simp only [v]; ring,
        fun i hi => ?_, fun i hi hi3 => ?_⟩
      · interval_cases i <;> simp [v] <;> norm_num
      · interval_cases i <;> simp [v] <;> norm_num
    have hprof : ∀ i, profile v i = if i = 0 then 0 else if i = 1 then 2 / 5 else if i = 2 then 9 / 20 else 1 :=
      fun i => by simp only [profile, v]; ring
    have hh : HeavyTop v := ⟨1 / 2, by norm_num, by norm_num, fun i _ => by rw [hprof],
      fun i hi => by interval_cases i <;> simp [hprof] <;> norm_num, by rw [hprof]; norm_num⟩
    exact ⟨v, hadm, hh, by simp only [hprof]; norm_num, heavy_top 3 v hadm hh⟩

/-- Convex sequences with `d_0 = 0` are superadditive: `d_i + d_j ≤ d_{i+j}`. -/
theorem convex_superadditive (d : ℕ → ℝ) (hd0 : d 0 = 0)
    (hconv : ∀ n, d (n + 1) - d n ≤ d (n + 2) - d (n + 1)) (i j : ℕ) : d i + d j ≤ d (i + j) := by
  have hinc : ∀ a b, a ≤ b → d (a + 1) - d a ≤ d (b + 1) - d b := by
    intro a b hab
    induction b, hab using Nat.le_induction with
    | base => exact le_rfl
    | succ b _ ih => exact ih.trans (hconv b)
  induction j with
  | zero => simp [hd0]
  | succ j ih =>
    have h1 : d (j + 1) - d j ≤ d (i + j + 1) - d (i + j) := hinc j (i + j) (by omega)
    rw [show i + (j + 1) = i + j + 1 by omega]
    linarith

/-! ### `K_{2,1}` perturbed (P3, after Corollary 7.7) -/

/-- `K_{2,1}` with `c_1 = 1/2 + ε`, `a_1 = 1/2 - ε`, `b ≡ 0`, `c_2 = 1`. -/
noncomputable def k21Pert (ε : ℝ) : Coefficients 2 where
  a i := if i = 0 then 1 else if i = 1 then 1 / 2 - ε else 0
  b _ := 0
  c i := if i = 0 then 0 else if i = 1 then 1 / 2 + ε else 1

theorem k21Pert_zero : ∀ m, m ≤ 2 + 1 → productMatrix (k21Pert 0) m = productMatrix (krawCoefficients 2 1) m :=
  product_congr _ _ (fun i hi => by interval_cases i <;> simp [k21Pert, krawCoefficients] <;> norm_num)
    (fun i hi => by interval_cases i <;> simp [k21Pert, krawCoefficients])
    (fun i hi => by interval_cases i <;> simp [k21Pert, krawCoefficients] <;> norm_num)

theorem k21Pert_table (ε : ℝ) (hε : ε < 1 / 2) (m : ℕ) (hm : m ≤ 2) (n k : Fin 3) :
    productMatrix (k21Pert ε) m n k =
      if m = 0 then (if n = k then 1 else 0)
      else if m = 1 then (if n.val = 0 ∧ k.val = 1 then 1 else if n.val = 1 ∧ k.val = 0 then 1 / 2 + ε
        else if n.val = 1 ∧ k.val = 2 then 1 / 2 - ε else if n.val = 2 ∧ k.val = 1 then 1 else 0)
      else (if n.val = 0 ∧ k.val = 2 then 1 else if n.val = 1 ∧ k.val = 1 then 1
        else if n.val = 2 ∧ k.val = 0 then (1 / 2 + ε) / (1 / 2 - ε)
        else if n.val = 2 ∧ k.val = 2 then -2 * ε / (1 / 2 - ε) else 0) := by
  have h1 : (1 : ℝ) / 2 - ε ≠ 0 := by linarith
  have h2 : (1 : ℝ) - ε * 2 ≠ 0 := by linarith
  have h3 : (2 : ℝ)⁻¹ - ε ≠ 0 := by norm_num; linarith
  interval_cases m <;> fin_cases n <;> fin_cases k <;>
    simp [productMatrix, matrixPair, k21Pert, Matrix.mul_apply, Fin.sum_univ_three, Matrix.sub_apply,
      Matrix.smul_apply, Matrix.one_apply, recurrenceMatrix] <;> field_simp <;> ring_nf
  all_goals linear_combination mul_inv_cancel₀ h2

/-- **P3, after Corollary 7.7**: for `0 < ε < 1/2`, every coefficient that is positive at `K_{2,1}` stays positive,
but `g(2,2;2) = -2ε/(1/2 - ε) < 0`. -/
theorem k21_perturbation (ε : ℝ) (hε0 : 0 < ε) (hε : ε < 1 / 2) :
    (∀ m, m ≤ 2 → ∀ n k : Fin 3, 0 < productMatrix (krawCoefficients 2 1) m n k →
      0 < productMatrix (k21Pert ε) m n k) ∧
    productMatrix (k21Pert ε) 2 2 2 = -2 * ε / (1 / 2 - ε) ∧ productMatrix (k21Pert ε) 2 2 2 < 0 := by
  have hpos : (0 : ℝ) < 1 / 2 - ε := by linarith
  refine ⟨fun m hm n k h => ?_, ?_, ?_⟩
  · rw [← k21Pert_zero m (by omega), k21Pert_table 0 (by norm_num) m hm] at h
    rw [k21Pert_table ε hε m hm]
    split_ifs at h ⊢ <;> first | positivity | (norm_num at h) | skip
    all_goals first | exact div_pos (by linarith) hpos | linarith
  · rw [k21Pert_table ε hε 2 le_rfl]; simp
  · rw [k21Pert_table ε hε 2 le_rfl]; simp
    exact div_neg_of_neg_of_pos (by linarith) (by norm_num; linarith)

/-! ### Reversal obstructions and Miclo's condition (P3, end of Section 8) -/

/-- If `b_{N-1} < b_N`, the reversed array has `g'(1,1;1) = (b_{N-1} - b_N)/c_N < 0`; so condition (b) of the
deep reduction fails for `N ≥ 3`. In particular for `K_{N,r}`, `0 < r < 1`. -/
theorem reversal_obstruction_kraw (N : ℕ) (hN : 3 ≤ N) (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) :
    productMatrix (revCoeff (krawCoefficients N r)) 1 ⟨1, by omega⟩ ⟨1, by omega⟩ =
      ((krawCoefficients N r).b (N - 1) - (krawCoefficients N r).b N) / (krawCoefficients N r).c N ∧
    productMatrix (revCoeff (krawCoefficients N r)) 1 ⟨1, by omega⟩ ⟨1, by omega⟩ < 0 ∧
    ¬ (∀ i j, (h : i + j < N) → ∀ t : Fin (N + 1),
      0 ≤ productMatrix (revCoeff (krawCoefficients N r)) i ⟨j, by omega⟩ t) := by
  have hN' : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have hval : productMatrix (revCoeff (krawCoefficients N r)) 1 ⟨1, by omega⟩ ⟨1, by omega⟩ = -(1 - r) / (r * N) := by
    rw [g111 _ (by omega)]
    simp only [revCoeff, krawCoefficients, Nat.sub_zero]
    rw [Nat.cast_sub (by omega)]
    push_cast
    field_simp
    ring
  have hneg : -(1 - r) / (r * N) < 0 := div_neg_of_neg_of_pos (by linarith) (by positivity)
  refine ⟨by rw [hval]; simp only [krawCoefficients]; rw [Nat.cast_sub (by omega)]; push_cast; field_simp; ring,
    hval ▸ hneg, fun h => ?_⟩
  have := h 1 1 (by omega) ⟨1, by omega⟩
  rw [hval] at this
  linarith

/-- Szwarc's array (eq:qarray) reversed: `g'(2,2;2) = (2p₀ - 1)/(N p₀) < 0` for `0 < p₀ < 1/2`, which violates
condition (b) of the deep reduction for the array of length `2N + 1` when `N ≥ 3`. -/
theorem reversal_obstruction_szwarc (N : ℕ) (hN : 3 ≤ N) (p : ℝ) (hp0 : 0 < p) (hp : p < 1 / 2) :
    productMatrix (revCoeff (szwarcCoefficients N p)) 2 ⟨2, by omega⟩ ⟨2, by omega⟩ = (2 * p - 1) / (N * p) ∧
    (2 * p - 1) / (N * p) < 0 ∧
    ¬ (∀ i j, (h : i + j < 2 * N) → ∀ t : Fin (2 * N + 1),
      0 ≤ productMatrix (revCoeff (szwarcCoefficients N p)) i ⟨j, by omega⟩ t) := by
  have hN' : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have hval : productMatrix (revCoeff (szwarcCoefficients N p)) 2 ⟨2, by omega⟩ ⟨2, by omega⟩ =
      (2 * p - 1) / (N * p) := by
    have hNpos : (0 : ℝ) < N := by linarith
    have ha0 : (revCoeff (szwarcCoefficients N p)).a 0 = 1 := by
      simp only [revCoeff, szwarcCoefficients, Nat.sub_zero, if_pos (show (2 * N) % 2 = 0 by omega),
        show 2 * N / 2 = N by omega]
      exact div_self hNpos.ne'
    have ha1 : (revCoeff (szwarcCoefficients N p)).a 1 = p := by
      simp only [revCoeff, szwarcCoefficients, if_neg (show ¬ (2 * N - 1) % 2 = 0 by omega)]
    rw [g222 _ (by omega) (by rw [ha0]; norm_num) (by rw [ha1]; exact hp0.ne'), if_pos (by omega)]
    simp only [revCoeff, szwarcCoefficients]
    have e0 : (2 * N - 0) % 2 = 0 := by omega
    have e1 : (2 * N - 1) % 2 = 1 := by omega
    have e2 : (2 * N - 2) % 2 = 0 := by omega
    have e3 : (2 * N - 3) % 2 = 1 := by omega
    have f0 : (2 * N - 0) / 2 = N := by omega
    have f2 : (2 * N - 2) / 2 = N - 1 := by omega
    simp only [e0, e1, e2, e3, f0, f2, if_true, show (1 : ℕ) % 2 = 0 ↔ False by decide, if_false,
      show ¬ ((1 : ℕ) = 0) by decide]
    rw [Nat.cast_sub (by omega)]
    push_cast
    field_simp
    ring
  have hneg : (2 * p - 1) / (N * p) < 0 := div_neg_of_neg_of_pos (by linarith) (by positivity)
  refine ⟨hval, hneg, fun h => ?_⟩
  have := h 2 2 (by omega) ⟨2, by omega⟩
  rw [hval] at this
  linarith

/-- Miclo's palindromic criterion requires `2^n P(n, n+1)` to be nonincreasing on `[0, N/2]`; for the symmetric
Krawtchouk chain `P(n, n+1) = a_n = (N - n)/N`, this fails for `N > 2` (already at `n = 0`). -/
theorem miclo_condition_fails (N : ℕ) (hN : 2 < N) :
    ∃ n : ℕ, ((n : ℝ) + 1 ≤ N / 2) ∧
      (2 : ℝ) ^ n * (krawCoefficients N 1).a n < 2 ^ (n + 1) * (krawCoefficients N 1).a (n + 1) := by
  refine ⟨0, ?_, ?_⟩
  · have : (3 : ℝ) ≤ N := by exact_mod_cast hN
    push_cast; linarith
  · simp only [krawCoefficients]
    have hN' : (3 : ℝ) ≤ N := by exact_mod_cast hN
    have hNpos : (0 : ℝ) < N := by linarith
    push_cast
    simp only [pow_zero, one_mul, zero_add, pow_one, sub_zero]
    rw [div_self hNpos.ne', show (2 : ℝ) * (((N : ℝ) - 1) / N) = 2 - 2 / N by field_simp; try ring]
    have : 2 / (N : ℝ) < 1 := by rw [div_lt_one hNpos]; linarith
    linarith

/-! ### Terminal row: polynomial dependence (P3, Section 9) -/

/-- Functions of `e` that are polynomials. -/
def IsPolyFun (f : ℝ → ℝ) : Prop := ∃ P : Polynomial ℝ, ∀ e, f e = P.eval e

theorem IsPolyFun.const (c : ℝ) : IsPolyFun fun _ => c := ⟨Polynomial.C c, fun _ => by simp⟩
theorem IsPolyFun.id : IsPolyFun fun e => e := ⟨Polynomial.X, fun _ => by simp⟩
theorem IsPolyFun.add {f g : ℝ → ℝ} (hf : IsPolyFun f) (hg : IsPolyFun g) : IsPolyFun fun e => f e + g e := by
  obtain ⟨P, hP⟩ := hf; obtain ⟨Q, hQ⟩ := hg; exact ⟨P + Q, fun e => by simp [hP, hQ]⟩
theorem IsPolyFun.mul {f g : ℝ → ℝ} (hf : IsPolyFun f) (hg : IsPolyFun g) : IsPolyFun fun e => f e * g e := by
  obtain ⟨P, hP⟩ := hf; obtain ⟨Q, hQ⟩ := hg; exact ⟨P * Q, fun e => by simp [hP, hQ]⟩
theorem IsPolyFun.sub {f g : ℝ → ℝ} (hf : IsPolyFun f) (hg : IsPolyFun g) : IsPolyFun fun e => f e - g e := by
  obtain ⟨P, hP⟩ := hf; obtain ⟨Q, hQ⟩ := hg; exact ⟨P - Q, fun e => by simp [hP, hQ]⟩
theorem IsPolyFun.neg {f : ℝ → ℝ} (hf : IsPolyFun f) : IsPolyFun fun e => -f e := by
  obtain ⟨P, hP⟩ := hf; exact ⟨-P, fun e => by simp [hP]⟩

theorem IsPolyFun.div {f : ℝ → ℝ} (hf : IsPolyFun f) (c : ℝ) : IsPolyFun fun e => f e / c := by
  obtain ⟨P, hP⟩ := hf; exact ⟨P * Polynomial.C c⁻¹, fun e => by simp [hP, div_eq_mul_inv]⟩

/-- Closure of `IsPolyFun` under constants, the identity, `+`, `-`, `*` and division by constants. -/
macro "polyfun" : tactic => `(tactic| repeat (first
  | exact IsPolyFun.const _ | exact IsPolyFun.id | apply IsPolyFun.add | apply IsPolyFun.sub
  | apply IsPolyFun.mul | apply IsPolyFun.div | apply IsPolyFun.neg))

theorem IsPolyFun.sum {ι : Type*} (s : Finset ι) {f : ι → ℝ → ℝ} (h : ∀ i ∈ s, IsPolyFun (f i)) :
    IsPolyFun fun e => ∑ i ∈ s, f i e := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using IsPolyFun.const 0
  | insert x s hx ih =>
    simp only [Finset.sum_insert hx]
    exact (h x (by simp)).add (ih fun i hi => h i (by simp [hi]))

/-- **P3, Section 9**: along the terminal direction `c_N ↦ c_N + e`, `b_N ↦ b_N - e` at `K_{N,r}`, every product
coefficient `g(m,n;k)`, `m ≤ N`, in particular `g(N,N;N)`, is a polynomial in `e`. -/
theorem terminal_polynomial (N : ℕ) (hN : 1 ≤ N) (r : ℝ) :
    ∀ m, m ≤ N → ∀ n k : Fin (N + 1), IsPolyFun fun e => productMatrix (termArray N r e) m n k := by
  have ha : ∀ m, m < N → ∀ e, (termArray N r e).a m = (termArray N r 0).a m := fun m hm e => by
    simp only [termArray, krawDir, stochArray]
    split_ifs <;> simp_all
  have hJ : ∀ i j : Fin (N + 1), IsPolyFun fun e => recurrenceMatrix (termArray N r e) i j := by
    intro i j
    simp only [recurrenceMatrix, termArray, krawDir, stochArray]
    split_ifs <;> polyfun
  have hb : ∀ m, IsPolyFun fun e => (termArray N r e).b m := fun m => by
    simp only [termArray, krawDir, stochArray]
    split_ifs <;> polyfun
  have hc : ∀ m, IsPolyFun fun e => (termArray N r e).c m := fun m => by
    simp only [termArray, krawDir, stochArray]
    split_ifs <;> polyfun
  have key : ∀ m, m ≤ N → ∀ n k : Fin (N + 1),
      IsPolyFun (fun e => (matrixPair (termArray N r e) m).1 n k) ∧
      IsPolyFun (fun e => (matrixPair (termArray N r e) m).2 n k) := by
    intro m
    induction m with
    | zero =>
      intro _ n k
      exact ⟨by simpa [matrixPair] using IsPolyFun.const 0, by
        simp only [matrixPair]; exact IsPolyFun.const _⟩
    | succ m ih =>
      intro hm n k
      refine ⟨(ih (by omega) n k).2, ?_⟩
      have e : (fun e => (matrixPair (termArray N r e) (m + 1)).2 n k) = fun e =>
          ((termArray N r 0).a m)⁻¹ * ((∑ l, (recurrenceMatrix (termArray N r e) n l -
            (termArray N r e).b m * (1 : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) n l) *
              (matrixPair (termArray N r e) m).2 l k) - (termArray N r e).c m * (matrixPair (termArray N r e) m).1 n k) := by
        funext e
        show ((termArray N r e).a m)⁻¹ * _ = _
        rw [ha m (by omega) e]
        simp only [Matrix.sub_apply, Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul]
      rw [e]
      refine (IsPolyFun.const _).mul (IsPolyFun.sub (IsPolyFun.sum _ fun l _ => ?_) ((hc m).mul (ih (by omega) n k).1))
      exact ((hJ n l).sub ((hb m).mul (IsPolyFun.const _))).mul (ih (by omega) l k).2
  exact fun m hm n k => (key m hm n k).2

end Szkraw
