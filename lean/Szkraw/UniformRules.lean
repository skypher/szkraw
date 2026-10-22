import Szkraw.CornerIdentity
import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# Definition 9.3 and Theorem 9.4: forced equalities for uniform criteria

A uniform rule `(β, γ)` defines for each `N` the direction `v_N` with `δb_n = β(n/N)`,
`δc_n = γ(n/N)`. If a set of arrays with property (P) admits a polynomial rule at the symmetric
endpoint, then `L_even = L_odd = 0`; conversely, when both vanish the first-order change of
`g(N,N;N)` along `v_N` vanishes for every `N` above the degrees of `β` and `γ`.
-/

namespace Szkraw

open Finset Filter Topology Polynomial

/-- `K_{N,1} + ε v_N` for the uniform rule `(β, γ)`. -/
noncomputable def ruleArray (β γ : ℝ → ℝ) (N : ℕ) (ε : ℝ) : Coefficients N :=
  krawDir N (fun n => β (n / N)) (fun n => γ (n / N)) 1 ε

/-- **Definition 9.3**: a family of sets of arrays admits the rule `(β, γ)` at the symmetric
endpoint if for all large `N` there is `ε_N > 0` with `K_{N,1} + ε v_N` in the set for
`0 < ε < ε_N`. -/
def AdmitsRule (S : (N : ℕ) → Set (Coefficients N)) (β γ : ℝ → ℝ) : Prop :=
  ∃ N₀, ∀ N, N₀ ≤ N → ∃ εN > 0, ∀ ε, 0 < ε → ε < εN → ruleArray β γ N ε ∈ S N

/-- `L_even = β(0) + 2γ(0) + β(1) + γ(1)`. -/
def Leven (β γ : ℝ → ℝ) : ℝ := β 0 + 2 * γ 0 + β 1 + γ 1

/-- `L_odd = β(0) - β(1) - γ(1)`. -/
def Lodd (β γ : ℝ → ℝ) : ℝ := β 0 - β 1 - γ 1

/-- `Σ_{n=0}^N (-1)^n C(N,n) p(n/N) = 0` for a polynomial of degree less than `N`. -/
theorem alt_sum_poly (p : ℝ[X]) {N : ℕ} (hp : p.natDegree < N) :
    ∑ n ∈ range (N + 1), (-1 : ℝ) ^ n * (N.choose n : ℝ) * p.eval ((n : ℝ) / N) = 0 := by
  set q := p.comp (C ((N : ℝ)⁻¹) * X)
  have hq : q.natDegree < N := by
    refine lt_of_le_of_lt (natDegree_comp_le) ?_
    have : (C ((N : ℝ)⁻¹) * X).natDegree ≤ 1 := (natDegree_C_mul_le _ _).trans natDegree_X_le
    calc p.natDegree * (C ((N : ℝ)⁻¹) * X).natDegree ≤ p.natDegree * 1 := Nat.mul_le_mul_left _ this
      _ < N := by rw [mul_one]; exact hp
  have h := congrFun (Polynomial.fwdDiff_iter_eq_zero_of_degree_lt hq) 0
  rw [fwdDiff_iter_eq_sum_shift] at h
  have e : ∀ k ∈ range (N + 1), ((-1 : ℤ) ^ (N - k) * N.choose k) • q.eval (0 + k • (1 : ℝ)) =
      (-1 : ℝ) ^ N * ((-1 : ℝ) ^ k * (N.choose k : ℝ) * p.eval ((k : ℝ) / N)) := by
    intro k hk
    rw [mem_range] at hk
    rw [zsmul_eq_mul, Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one, Int.cast_natCast,
      neg_one_pow_sub_eq (by omega : k ≤ N), nsmul_eq_mul, mul_one, zero_add, eval_comp]
    simp only [eval_mul, eval_C, eval_X]
    rw [inv_mul_eq_div]
    ring
  rw [sum_congr rfl e, ← mul_sum] at h
  exact (mul_eq_zero.mp h).resolve_left (pow_ne_zero _ (by norm_num))

theorem natDegree_add_two_mul_lt {β γ : ℝ[X]} {N : ℕ} (hβ : β.natDegree < N) (hγ : γ.natDegree < N) :
    (β + C 2 * γ).natDegree < N :=
  lt_of_le_of_lt (natDegree_add_le _ _) (max_lt hβ (lt_of_le_of_lt (natDegree_C_mul_le _ _) hγ))

/-- Along a polynomial rule the alternating sum of Lemma 9.2 is `-L_even` or `-L_odd`. -/
theorem rule_sum (β γ : ℝ[X]) {N : ℕ} (hN : 2 ≤ N) (hβ : β.natDegree < N) (hγ : γ.natDegree < N) :
    ∑ n ∈ range (N + 1), (-1 : ℝ) ^ n * (N.choose n : ℝ) *
        cornerF N (fun n => β.eval ((n : ℝ) / N)) (fun n => γ.eval ((n : ℝ) / N)) n =
      -(if N % 2 = 0 then Leven β.eval γ.eval else Lodd β.eval γ.eval) := by
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  by_cases hpar : N % 2 = 0
  · set p := β + C 2 * γ
    have term : ∀ n ∈ range (N + 1), (-1 : ℝ) ^ n * (N.choose n : ℝ) *
        cornerF N (fun n => β.eval ((n : ℝ) / N)) (fun n => γ.eval ((n : ℝ) / N)) n =
        (-1 : ℝ) ^ n * (N.choose n : ℝ) * p.eval ((n : ℝ) / N) +
          (if n = 0 then -(β.eval 0 + 2 * γ.eval 0) else 0) +
            (if n = N then (-1 : ℝ) ^ N * (-(β.eval 1) - γ.eval 1) else 0) := by
      intro n hn
      rw [mem_range] at hn
      simp only [cornerF, if_pos hpar, stochDir, p, eval_add, eval_mul, eval_C]
      rcases Nat.eq_zero_or_pos n with h0 | hpos
      · subst h0; simp [show ¬(0 = N) by omega]
      by_cases hnN : n = N
      · subst hnN; simp [show n ≠ 0 by omega]; ring
      · simp [show n ≠ 0 by omega, hnN]
    rw [sum_congr rfl term, sum_add_distrib, sum_add_distrib, alt_sum_poly p (natDegree_add_two_mul_lt hβ hγ),
      sum_ite_eq' (range (N + 1)) 0, sum_ite_eq' (range (N + 1)) N, if_pos (by simp), if_pos (by simp),
      if_pos hpar, (Even.neg_one_pow ⟨N / 2, by omega⟩ : (-1 : ℝ) ^ N = 1), Leven]
    ring
  · have term : ∀ n ∈ range (N + 1), (-1 : ℝ) ^ n * (N.choose n : ℝ) *
        cornerF N (fun n => β.eval ((n : ℝ) / N)) (fun n => γ.eval ((n : ℝ) / N)) n =
        (-1 : ℝ) ^ n * (N.choose n : ℝ) * β.eval ((n : ℝ) / N) +
          (if n = 0 then -(β.eval 0) else 0) +
            (if n = N then (-1 : ℝ) ^ N * (-(β.eval 1) - γ.eval 1) else 0) := by
      intro n hn
      rw [mem_range] at hn
      simp only [cornerF, if_neg hpar, stochDir]
      rcases Nat.eq_zero_or_pos n with h0 | hpos
      · subst h0; simp [show ¬(0 = N) by omega]
      by_cases hnN : n = N
      · subst hnN; simp [show n ≠ 0 by omega]; ring
      · simp [show n ≠ 0 by omega, hnN]
    rw [sum_congr rfl term, sum_add_distrib, sum_add_distrib, alt_sum_poly β hβ,
      sum_ite_eq' (range (N + 1)) 0, sum_ite_eq' (range (N + 1)) N, if_pos (by simp), if_pos (by simp),
      if_neg hpar, (Odd.neg_one_pow ⟨N / 2, by omega⟩ : (-1 : ℝ) ^ N = -1), Lodd]
    ring

/-- The first-order change of `g(N,N;N)` along a polynomial rule, for `N` above the degrees. -/
theorem rule_deriv (β γ : ℝ[X]) {N : ℕ} (hN : 2 ≤ N) (hβ : β.natDegree < N) (hγ : γ.natDegree < N) :
    HasDerivAt (fun ε => productMatrix (ruleArray β.eval γ.eval N ε) N (Fin.last N) (Fin.last N))
      (sN N * -(if N % 2 = 0 then Leven β.eval γ.eval else Lodd β.eval γ.eval)) 0 := by
  have h := corner_identity (δb := fun n => β.eval ((n : ℝ) / N)) (δc := fun n => γ.eval ((n : ℝ) / N)) hN
  rw [rule_sum β γ hN hβ hγ] at h
  exact h

/-- `g(N,N;N) = 0` at `K_{N,1}` (Lemma 9.1 with `r = 1`). -/
theorem rule_corner_zero (β γ : ℝ → ℝ) {N : ℕ} (hN : 1 ≤ N) :
    productMatrix (ruleArray β γ N 0) N (Fin.last N) (Fin.last N) = 0 := by
  rw [ruleArray, krawDir_zero hN 1 N (by omega)]
  have := corner_value N hN 1 (by norm_num) le_rfl
  rw [sub_self, zero_pow (by omega)] at this
  exact this

/-- A negative derivative at a zero gives negative values just to the right. -/
theorem neg_right_of_deriv {f : ℝ → ℝ} {d : ℝ} (hf : HasDerivAt f d 0) (h0 : f 0 = 0) (hd : d < 0) :
    ∃ ε₀ > 0, ∀ ε, 0 < ε → ε < ε₀ → f ε < 0 := by
  have h := (hasDerivAt_iff_tendsto_slope_zero.mp hf).eventually (gt_mem_nhds hd)
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp (eventually_nhdsWithin_iff.mp h)
  refine ⟨δ, hδ, fun ε hε hεδ => ?_⟩
  have := hball (show dist ε 0 < δ by rw [Real.dist_eq, sub_zero, abs_of_pos hε]; exact hεδ) hε.ne'
  simp only [zero_add, h0, sub_zero, smul_eq_mul] at this
  by_contra hc
  exact absurd this (not_lt.mpr (mul_nonneg (inv_nonneg.mpr hε.le) (not_lt.mp hc)))

theorem sN_even {h : ℕ} (hh : 1 ≤ h) : sN (2 * h) = (-1) ^ (h + 1) / ((2 * h - 1).choose (h - 1) : ℝ) := by
  rw [sN, show 2 * h / 2 = h by omega, show (2 * h - 1) / 2 = h - 1 by omega]

theorem sN_odd (h : ℕ) : sN (2 * h + 1) = (-1) ^ (h + 1) / ((2 * h).choose h : ℝ) := by
  rw [sN, show (2 * h + 1) / 2 = h by omega, show 2 * h + 1 - 1 = 2 * h by omega,
    show 2 * h / 2 = h by omega]

theorem exists_sign_index (L : ℝ) (hL : L ≠ 0) (M : ℕ) : ∃ h, M ≤ h ∧ 1 ≤ h ∧ (-1 : ℝ) ^ h * L < 0 := by
  rcases lt_or_gt_of_ne hL with hneg | hpos
  · exact ⟨2 * M + 2, by omega, by omega, by rw [pow_add, pow_mul]; norm_num; exact hneg⟩
  · exact ⟨2 * M + 1, by omega, by omega, by rw [pow_succ, pow_mul]; norm_num; exact hpos⟩

/-- **Theorem 9.4** (Forced equalities for uniform criteria), first part: if a set of arrays with
property (P) admits a polynomial rule `(β, γ)` at the symmetric endpoint, then
`L_even = L_odd = 0`. -/
theorem forced_equalities (β γ : ℝ[X]) (S : (N : ℕ) → Set (Coefficients N))
    (hS : ∀ N, ∀ v ∈ S N, MatrixPositivity v) (hadm : AdmitsRule S β.eval γ.eval) :
    Leven β.eval γ.eval = 0 ∧ Lodd β.eval γ.eval = 0 := by
  obtain ⟨N₀, hN₀⟩ := hadm
  set M := N₀ + β.natDegree + γ.natDegree + 2
  -- for all large `N` the derivative is nonnegative
  have key : ∀ N, M ≤ N →
      0 ≤ sN N * -(if N % 2 = 0 then Leven β.eval γ.eval else Lodd β.eval γ.eval) := by
    intro N hN
    by_contra hneg'
    have hneg := lt_of_not_ge hneg'
    obtain ⟨εN, hεN, hmem⟩ := hN₀ N (by omega)
    obtain ⟨ε₀, hε₀, hlt⟩ := neg_right_of_deriv (rule_deriv β γ (by omega) (by omega) (by omega))
      (rule_corner_zero _ _ (by omega)) hneg
    set ε := min εN ε₀ / 2 with hεdef
    have hmin : 0 < min εN ε₀ := lt_min hεN hε₀
    have hε : 0 < ε := by rw [hεdef]; linarith
    have h1 : ε < εN := by have := min_le_left εN ε₀; rw [hεdef]; linarith
    have h2 : ε < ε₀ := by have := min_le_right εN ε₀; rw [hεdef]; linarith
    have hP := hS N _ (hmem ε hε h1) N le_rfl (Fin.last N) (Fin.last N)
    exact absurd (hlt ε hε h2) (not_lt.mpr hP)
  constructor
  · by_contra hL
    obtain ⟨h, hMh, h1, hsign⟩ := exists_sign_index _ hL M
    have hk := key (2 * h) (by omega)
    rw [if_pos (by omega), sN_even h1] at hk
    have hC : (0 : ℝ) < (2 * h - 1).choose (h - 1) := by exact_mod_cast Nat.choose_pos (by omega)
    have : (-1 : ℝ) ^ (h + 1) / ((2 * h - 1).choose (h - 1) : ℝ) * -Leven β.eval γ.eval =
        (-1) ^ h * Leven β.eval γ.eval / ((2 * h - 1).choose (h - 1) : ℝ) := by rw [pow_succ]; ring
    rw [this] at hk
    exact absurd (div_neg_of_neg_of_pos hsign hC) (not_lt.mpr hk)
  · by_contra hL
    obtain ⟨h, hMh, h1, hsign⟩ := exists_sign_index _ hL M
    have hk := key (2 * h + 1) (by omega)
    rw [if_neg (by omega), sN_odd] at hk
    have hC : (0 : ℝ) < (2 * h).choose h := by exact_mod_cast Nat.choose_pos (by omega)
    have : (-1 : ℝ) ^ (h + 1) / ((2 * h).choose h : ℝ) * -Lodd β.eval γ.eval =
        (-1) ^ h * Lodd β.eval γ.eval / ((2 * h).choose h : ℝ) := by rw [pow_succ]; ring
    rw [this] at hk
    exact absurd (div_neg_of_neg_of_pos hsign hC) (not_lt.mpr hk)

/-- **Theorem 9.4**, second part: if `L_even = L_odd = 0`, the first-order change of `g(N,N;N)`
along `v_N` vanishes for every `N` above the degrees of `β` and `γ`. -/
theorem forced_vanishing (β γ : ℝ[X]) (hL : Leven β.eval γ.eval = 0 ∧ Lodd β.eval γ.eval = 0)
    {N : ℕ} (hβ : β.natDegree < N) (hγ : γ.natDegree < N) :
    HasDerivAt (fun ε => productMatrix (ruleArray β.eval γ.eval N ε) N (Fin.last N) (Fin.last N)) 0 0 := by
  rcases Nat.lt_or_ge N 2 with hN | hN
  · -- `N = 1`: `β` and `γ` are constants and `g(1,1;1) = b_1 = -ε γ(1)`
    have hN1 : N = 1 := by omega
    subst hN1
    have hβc := eq_C_of_natDegree_eq_zero (show β.natDegree = 0 by omega)
    have hγ1 : γ.eval 1 = 0 := by
      have := hL.2
      rw [Lodd, hβc] at this
      simpa using this
    have hfun : (fun ε => productMatrix (ruleArray β.eval γ.eval 1 ε) 1 (Fin.last 1) (Fin.last 1)) =
        fun ε => -(ε * γ.eval 1) := by
      funext ε
      simp [productMatrix, matrixPair, ruleArray, krawDir, stochArray, recurrenceMatrix]
    rw [hfun, hγ1]
    simpa using hasDerivAt_const (0 : ℝ) (0 : ℝ)
  · have h := rule_deriv β γ hN hβ hγ
    split_ifs at h with hpar
    · rwa [hL.1, neg_zero, mul_zero] at h
    · rwa [hL.2, neg_zero, mul_zero] at h

end Szkraw
