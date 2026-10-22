import Szkraw.TopMass

/-!
# Proposition 9.12: raising the top mass of `K_{N,r}`

The measure of `K_{N,r}` has nodes `x_n = 1 - (1+r) n / N` and masses
`w_n = C(N,n) r^{N-n} / (1+r)^N` (`binomialNode`, `binomialMass` with `p = 1/r`). Raising the mass at
`x_0 = 1` to `(1 + τ) w_0` gives, after the affine normalization of Section 2, the array
`epsNorm … (τ w_0)` of `TopMass.lean`. This file evaluates its corner coefficient
`g(N,N;N) = ((1+τ)^2 (I - w_0) + w_0) / ((1+τ)(h - w_0) + w_0)` with `I = (r(1-r))^N`, `h = r^N`,
locates its sign change at `τ_N^* = (1 - (1-r^2)^N)^{-1/2} - 1`, and bounds the change of the
coefficients by `3 τ max_n w_n`.
-/

namespace Szkraw

open Finset

variable {N : ℕ} {r : ℝ}

/-- The array of `K_{N,r}` in the parametrization (2.3), `p = 1/r`. -/
noncomputable abbrev kv (N : ℕ) (r : ℝ) : Coefficients N := geometricCoefficients N (1 / r) 1

/-- The nodes `x_n = 1 - (1 + r) n / N`. -/
noncomputable def kx (N : ℕ) (r : ℝ) (j : Fin (N + 1)) : ℝ := binomialNode (1 / r) N j.val

/-- The masses `w_n = C(N,n) r^{N-n} / (1+r)^N`. -/
noncomputable def kw (N : ℕ) (r : ℝ) (j : Fin (N + 1)) : ℝ := binomialMass (1 / r) N j.val

theorem one_le_inv_r (hr : 0 < r) (hr1 : r ≤ 1) : 1 ≤ 1 / r := by
  rw [le_div_iff₀ hr]; linarith

theorem kv_admissible (hN : 1 ≤ N) (hr : 0 < r) (hr1 : r ≤ 1) : Admissible (kv N r) :=
  geometric_coefficients_admissible N hN _ 1 (one_le_inv_r hr hr1) le_rfl

theorem kx_zero : kx N r 0 = 1 := by simp [kx, binomialNode]

theorem k_act (hN : 1 ≤ N) (hr : 0 < r) (hr1 : r ≤ 1) (t i : Fin (N + 1)) :
    kx N r t * uval (kv N r) (kx N r) i t = ∑ k, recurrenceMatrix (kv N r) i k * uval (kv N r) (kx N r) k t :=
  binomial_node_action _ (one_le_inv_r hr hr1) N hN t i

theorem k_orth (hN : 1 ≤ N) (hr : 0 < r) (hr1 : r ≤ 1) (m n : ℕ) (hm : m ≤ N) (hn : n ≤ N) (hmn : m ≠ n) :
    ∑ t, kw N r t * uval (kv N r) (kx N r) m t * uval (kv N r) (kx N r) n t = 0 :=
  binomial_orthogonal _ (one_le_inv_r hr hr1) N hN m n hm hn hmn

theorem k_nrm_pos (hN : 1 ≤ N) (hr : 0 < r) (hr1 : r ≤ 1) (n : ℕ) (hn : n ≤ N) :
    0 < nrm (kv N r) (kx N r) (kw N r) n :=
  binomial_norm_pos _ (one_le_inv_r hr hr1) N hN n hn

theorem k_w_pos (hr : 0 < r) (hr1 : r ≤ 1) (t : Fin (N + 1)) : 0 < kw N r t :=
  binomial_mass_pos _ (one_le_inv_r hr hr1) N t

theorem kv_a (i : ℕ) (hi : i ≤ N) : (kv N r).a i = ((N : ℝ) - i) / N := by
  simp only [kv, geometricCoefficients, one_pow, one_mul, qInteger_at_one, Nat.cast_sub hi]

theorem kv_c (i : ℕ) : (kv N r).c i = r * i / N := by
  simp only [kv, geometricCoefficients, qInteger_at_one]
  rcases eq_or_ne r 0 with h | h
  · subst h; simp
  · field_simp

/-- `π_n = C(N,n) / r^n`. -/
theorem k_piw (hN : 1 ≤ N) (hr : 0 < r) (hr1 : r ≤ 1) :
    ∀ n, n ≤ N → piw (kv N r) (kx N r) (kw N r) n = (N.choose n : ℝ) / r ^ n := by
  have hv := kv_admissible hN hr hr1
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  intro n hn
  induction n with
  | zero =>
    have : nrm (kv N r) (kx N r) (kw N r) 0 = 1 := by
      simp only [nrm, uval_zero, one_pow, mul_one]
      exact binomial_mass_sum _ (one_le_inv_r hr hr1) N hN
    simp [piw, this]
  | succ n ih =>
    have hb := piw_balance (k_act hN hr hr1) (k_orth hN hr hr1) (k_nrm_pos hN hr hr1) (n + 1) (by omega) hn
    rw [Nat.add_sub_cancel, ih (by omega), kv_a n (by omega), kv_c] at hb
    have hc : (r * ((n + 1 : ℕ) : ℝ) / N) ≠ 0 := by positivity
    have hch : (N.choose (n + 1) : ℝ) * ((n + 1 : ℕ) : ℝ) = N.choose n * ((N - n : ℕ) : ℝ) := by
      exact_mod_cast Nat.choose_succ_right_eq N n
    rw [Nat.cast_sub (by omega : n ≤ N)] at hch
    have hr0 := hr.ne'
    rw [eq_div_iff (pow_ne_zero _ hr0)]
    have := eq_div_of_mul_eq hc hb.symm
    rw [this]
    field_simp
    push_cast at hch ⊢
    linear_combination -(r ^ n * r) * hch

theorem k_nrm_N (hN : 1 ≤ N) (hr : 0 < r) (hr1 : r ≤ 1) : nrm (kv N r) (kx N r) (kw N r) N = r ^ N := by
  have h := k_piw hN hr hr1 N le_rfl
  rw [piw, Nat.choose_self, Nat.cast_one, one_div] at h
  have := (k_nrm_pos hN hr hr1 N le_rfl).ne'
  rw [← inv_inv (nrm _ _ _ N), h, inv_inv]

theorem k_w0 (hr : 0 < r) : kw N r 0 = (r / (1 + r)) ^ N := by
  simp only [kw, binomialMass, Fin.val_zero, Nat.choose_zero_right, Nat.cast_one, Nat.sub_zero, pow_zero,
    mul_one, one_mul]
  congr 1
  field_simp

/-- `w_n = w_0 π_n`. -/
theorem k_w_eq (hN : 1 ≤ N) (hr : 0 < r) (hr1 : r ≤ 1) (t : Fin (N + 1)) :
    kw N r t = kw N r 0 * piw (kv N r) (kx N r) (kw N r) t := by
  rw [k_piw hN hr hr1 t (by omega), k_w0 hr]
  simp only [kw, binomialMass]
  have hr0 := hr.ne'
  have ht := t.isLt
  obtain ⟨k, hk⟩ : ∃ k, N = t.val + k := ⟨N - t.val, by omega⟩
  have hNk : (r / (1 + r)) ^ N = (r / (1 + r)) ^ (t : ℕ) * (r / (1 + r)) ^ k := by rw [← pow_add, ← hk]
  have e1 : 1 / (1 / r + 1) = r / (1 + r) := by field_simp
  have e2 : 1 / r / (1 / r + 1) = 1 / (1 + r) := by field_simp
  have h1r : (1 + r) ≠ 0 := by linarith
  rw [show N - t.val = k by omega, hNk, e1, e2, div_pow, div_pow, div_pow, one_pow]
  field_simp

/-- `Σ_t w_t R_N(x_t)^3 = (r(1-r))^N` (Lemma 9.1). -/
theorem k_cube (hN : 1 ≤ N) (hr : 0 < r) (hr1 : r ≤ 1) :
    ∑ t, kw N r t * uval (kv N r) (kx N r) N t ^ 3 = (r * (1 - r)) ^ N := by
  have hp := one_le_inv_r hr hr1
  have hprod := fun t : Fin (N + 1) => binomial_product_identity (1 / r) hp N hN N (Fin.last N) t
  have e : ∑ t, kw N r t * uval (kv N r) (kx N r) N t ^ 3 =
      ∑ k : Fin (N + 1), productMatrix (kv N r) N (Fin.last N) k *
        ∑ t, kw N r t * uval (kv N r) (kx N r) k t * uval (kv N r) (kx N r) N t := by
    have : ∀ t : Fin (N + 1), kw N r t * uval (kv N r) (kx N r) N t ^ 3 =
        ∑ k : Fin (N + 1), productMatrix (kv N r) N (Fin.last N) k *
          (kw N r t * uval (kv N r) (kx N r) k t * uval (kv N r) (kx N r) N t) := by
      intro t
      have h := hprod t
      simp only [Fin.val_last] at h
      rw [show uval (kv N r) (kx N r) N t ^ 3 =
        (uval (kv N r) (kx N r) N t * uval (kv N r) (kx N r) N t) * uval (kv N r) (kx N r) N t by ring]
      rw [show uval (kv N r) (kx N r) N t * uval (kv N r) (kx N r) N t =
        ∑ k : Fin (N + 1), productMatrix (kv N r) N (Fin.last N) k * uval (kv N r) (kx N r) k t from h,
        sum_mul, mul_sum]
      exact sum_congr rfl fun k _ => by ring
    rw [sum_congr rfl fun t _ => this t, sum_comm]
    exact sum_congr rfl fun k _ => by rw [mul_sum]
  rw [e, sum_eq_single (Fin.last N)]
  · have hg : productMatrix (kv N r) N (Fin.last N) (Fin.last N) = (1 - r) ^ N := by
      have hc := product_congr (krawCoefficients N r) (kv N r)
        (fun i hi => (kraw_geometric_prefix N r hr i hi).1) (fun i hi => (kraw_geometric_prefix N r hr i hi).2.1)
        (fun i hi => (kraw_geometric_prefix N r hr i hi).2.2) N (by omega)
      rw [← hc]
      exact corner_value N hN r hr hr1
    have hn : ∑ t, kw N r t * uval (kv N r) (kx N r) (Fin.last N) t * uval (kv N r) (kx N r) N t =
        nrm (kv N r) (kx N r) (kw N r) N := by
      rw [nrm]; exact sum_congr rfl fun t _ => by simp only [Fin.val_last]; ring
    rw [hg, hn, k_nrm_N hN hr hr1, mul_pow]; ring
  · intro k _ hk
    rw [k_orth hN hr hr1 k N (by omega) le_rfl (fun h => hk (Fin.ext (by simp [h]))), mul_zero]
  · intro h; exact absurd (mem_univ _) h

/-- The normalized array of `K_{N,r}` with the top mass raised to `(1 + τ) w_0`. -/
noncomputable def raisedKraw (N : ℕ) (r τ : ℝ) : Coefficients N :=
  epsNorm (kv N r) (kx N r) (kw N r) (τ * kw N r 0)

theorem k_Ssum_nonneg (hN : 1 ≤ N) (hr : 0 < r) (hr1 : r ≤ 1) (n : ℕ) (hn : n ≤ N + 1) :
    0 ≤ Ssum (kv N r) (kx N r) (kw N r) n :=
  sum_nonneg fun k hk => by
    rw [mem_range] at hk
    exact (inv_pos.mpr (k_nrm_pos hN hr hr1 k (by omega))).le

theorem k_Aeps_pos (hN : 1 ≤ N) (hr : 0 < r) (hr1 : r ≤ 1) {ε : ℝ} (hε : 0 ≤ ε) (n : ℕ) (hn : n ≤ N + 1) :
    0 < Aeps (kv N r) (kx N r) (kw N r) ε n := by
  rw [Aeps]; have := k_Ssum_nonneg hN hr hr1 n hn; nlinarith

/-- **Proposition 9.12**, corner formula: the raised measure has
`g(N,N;N) = ((1+τ)^2 (I - w_0) + w_0) / ((1+τ)(h - w_0) + w_0)`, `I = (r(1-r))^N`, `h = r^N`,
`w_0 = (r/(1+r))^N`. -/
theorem raise_corner (hN : 1 ≤ N) (hr : 0 < r) (hr1 : r < 1) {τ : ℝ} (hτ : 0 < τ) :
    productMatrix (raisedKraw N r τ) N (Fin.last N) (Fin.last N) =
      ((1 + τ) ^ 2 * ((r * (1 - r)) ^ N - (r / (1 + r)) ^ N) + (r / (1 + r)) ^ N) /
        ((1 + τ) * (r ^ N - (r / (1 + r)) ^ N) + (r / (1 + r)) ^ N) := by
  have hr1' := hr1.le
  have hw0 : 0 < kw N r 0 := k_w_pos hr hr1' 0
  have hε : 0 ≤ τ * kw N r 0 := by positivity
  have hτε : τ * kw N r 0 / kw N r 0 = τ := by field_simp
  have h := eps_corner_value (kv_admissible hN hr hr1') kx_zero (k_act hN hr hr1') (k_orth hN hr hr1')
    (k_nrm_pos hN hr hr1') (k_w_pos hr hr1') (by rw [hτε]; linarith) (by linarith)
    (fun n hn => (k_Aeps_pos hN hr hr1' hε n hn).ne')
  rw [hτε, k_nrm_N hN hr hr1', k_cube hN hr hr1', k_w0 hr] at h
  have hden : 0 < (1 + τ) * (r ^ N - (r / (1 + r)) ^ N) + (r / (1 + r)) ^ N := by
    have h1 : (r / (1 + r)) ^ N ≤ r ^ N :=
      pow_le_pow_left₀ (by positivity) (div_le_self hr.le (by linarith)) N
    have h2 : 0 < (r / (1 + r)) ^ N := by positivity
    nlinarith
  rw [eq_div_iff hden.ne', raisedKraw, k_w0 hr]
  exact h

/-- `(r(1-r))^N = (r/(1+r))^N (1 - r^2)^N`. -/
theorem cube_eq (hr : 0 < r) : (r * (1 - r)) ^ N = (r / (1 + r)) ^ N * (1 - r ^ 2) ^ N := by
  rw [← mul_pow]; congr 1; field_simp; ring

/-- **Proposition 9.12**, sign: the corner coefficient of the raised measure is negative exactly
when `τ > τ_N^* = (1 - (1 - r^2)^N)^{-1/2} - 1`. -/
theorem raise_sign (hN : 1 ≤ N) (hr : 0 < r) (hr1 : r < 1) {τ : ℝ} (hτ : 0 < τ) :
    productMatrix (raisedKraw N r τ) N (Fin.last N) (Fin.last N) < 0 ↔
      (Real.sqrt (1 - (1 - r ^ 2) ^ N))⁻¹ - 1 < τ := by
  have hr1' := hr1.le
  rw [raise_corner hN hr hr1 hτ, cube_eq hr]
  set w0 := (r / (1 + r)) ^ N with hw0def
  set q := (1 - r ^ 2) ^ N with hqdef
  have hw0 : 0 < w0 := by positivity
  have hq0 : 0 < q := pow_pos (by nlinarith) N
  have hq1 : q < 1 := pow_lt_one₀ (by nlinarith) (by nlinarith) (by omega)
  have hden : 0 < (1 + τ) * (r ^ N - w0) + w0 := by
    have h1 : w0 ≤ r ^ N := pow_le_pow_left₀ (by positivity) (div_le_self hr.le (by linarith)) N
    nlinarith
  rw [div_neg_iff, or_iff_right (fun h => absurd h.2 (not_lt.mpr hden.le)), and_iff_left hden]
  set s := Real.sqrt (1 - q) with hs
  have hs0 : 0 < s := Real.sqrt_pos.mpr (by linarith)
  have hs2 : s ^ 2 = 1 - q := Real.sq_sqrt (by linarith)
  have hnum : (1 + τ) ^ 2 * (w0 * q - w0) + w0 = w0 * (1 - ((1 + τ) * s) ^ 2) := by
    rw [mul_pow, hs2]; ring
  rw [hnum]
  constructor
  · intro h
    have h1 : 1 < ((1 + τ) * s) ^ 2 := by
      by_contra hc; push Not at hc; nlinarith
    have h2 : 1 < (1 + τ) * s :=
      lt_of_pow_lt_pow_left₀ 2 (by positivity) (by rw [one_pow]; exact h1)
    rw [inv_eq_one_div, sub_lt_iff_lt_add, div_lt_iff₀ hs0]; linarith
  · intro h
    rw [inv_eq_one_div, sub_lt_iff_lt_add, div_lt_iff₀ hs0] at h
    have h2 : 1 < ((1 + τ) * s) ^ 2 := by nlinarith
    nlinarith

theorem k_piw_zero (hN : 1 ≤ N) (hr : 0 < r) (hr1 : r ≤ 1) : piw (kv N r) (kx N r) (kw N r) 0 = 1 := by
  rw [k_piw hN hr hr1 0 (by omega)]; simp

theorem k_Aeps_ge (hN : 1 ≤ N) (hr : 0 < r) (hr1 : r ≤ 1) {ε : ℝ} (hε : 0 ≤ ε) (n : ℕ) (h1 : 1 ≤ n)
    (hn : n ≤ N + 1) : 1 + ε ≤ Aeps (kv N r) (kx N r) (kw N r) ε n := by
  have hS : 1 ≤ Ssum (kv N r) (kx N r) (kw N r) n := by
    rw [Ssum, ← add_sum_erase _ _ (mem_range.mpr (by omega : 0 < n)), k_piw_zero hN hr hr1]
    have : 0 ≤ ∑ k ∈ (range n).erase 0, piw (kv N r) (kx N r) (kw N r) k :=
      sum_nonneg fun k hk => by
        have := mem_range.mp (mem_of_mem_erase hk)
        exact (inv_pos.mpr (k_nrm_pos hN hr hr1 k (by omega))).le
    linarith
  rw [Aeps]; nlinarith

/-- **Proposition 9.12**, the raised measure: the raised array satisfies (2.1), and its
polynomials are orthogonal for the measure with masses `w_t + τ w_0 [t = 0]` at the nodes
`y_t = (1 + ε) x_t - ε` (`ε = τ w_0`), with value `1` at the top node `y_0 = 1`. -/
theorem raise_measure (hN : 1 ≤ N) (hr : 0 < r) (hr1 : r < 1) {τ : ℝ} (hτ : 0 < τ) :
    Admissible (raisedKraw N r τ) ∧
      (∀ n, n ≤ N → (recurrencePolynomial (raisedKraw N r τ) n).eval
        ((1 + τ * kw N r 0) * kx N r 0 - τ * kw N r 0) = 1) ∧
      ∀ m n, m ≤ N → n ≤ N → m ≠ n →
        ∑ t, (kw N r t + if t = 0 then τ * kw N r 0 else 0) *
          (recurrencePolynomial (raisedKraw N r τ) m).eval ((1 + τ * kw N r 0) * kx N r t - τ * kw N r 0) *
          (recurrencePolynomial (raisedKraw N r τ) n).eval ((1 + τ * kw N r 0) * kx N r t - τ * kw N r 0) = 0 := by
  have hr1' := hr1.le
  have hv := kv_admissible hN hr hr1'
  have hw0 : 0 < kw N r 0 := k_w_pos hr hr1' 0
  set ε := τ * kw N r 0 with hεdef
  have hε : 0 < ε := by positivity
  have hA := fun n hn => (k_Aeps_pos hN hr hr1' hε.le n hn).ne'
  have hev := fun m hm t => ueps_eval hv (k_act hN hr hr1') (k_orth hN hr hr1') (k_nrm_pos hN hr hr1')
    (by linarith : 1 + ε ≠ 0) hA m hm t
  refine ⟨?_, fun n hn => ?_, fun m n hm hn hmn => ?_⟩
  · obtain ⟨_, ha0, hb0, hc0, haN, hsum, hapos, hcpos⟩ := hv
    have hA0 : Aeps (kv N r) (kx N r) (kw N r) ε 0 = 1 := by simp [Aeps, Ssum]
    have hA1 : Aeps (kv N r) (kx N r) (kw N r) ε 1 = 1 + ε := by
      simp [Aeps, Ssum, k_piw_zero hN hr hr1']
    have h1ε : (1 + ε) ≠ 0 := by linarith
    refine ⟨hN, ?_, ?_, ?_, ?_, fun i hi => ?_, fun i hi => ?_, fun i hi1 hi2 => ?_⟩
    · simp only [raisedKraw, epsNorm, epsRaw, ← hεdef, hA0, zero_add, hA1, ha0]; field_simp
    · simp only [raisedKraw, epsNorm, epsRaw, ← hεdef, hA0, zero_add, hA1, ha0, hc0]; field_simp; ring
    · simp only [raisedKraw, epsNorm, epsRaw, ← hεdef, hc0]; simp
    · simp only [raisedKraw, epsNorm, epsRaw, ← hεdef, haN]; simp
    · simp only [raisedKraw, epsNorm, epsRaw, ← hεdef]; ring
    · simp only [raisedKraw, epsNorm, epsRaw, ← hεdef]
      have := hapos i hi
      have := k_Aeps_pos hN hr hr1' hε.le i (by omega)
      have := k_Aeps_pos hN hr hr1' hε.le (i + 1) (by omega)
      positivity
    · simp only [raisedKraw, epsNorm, epsRaw, ← hεdef]
      have := hcpos i hi1 hi2
      have := k_Aeps_pos hN hr hr1' hε.le i (by omega)
      have := k_Aeps_pos hN hr hr1' hε.le (i + 1) (by omega)
      positivity
  · rw [show raisedKraw N r τ = epsNorm (kv N r) (kx N r) (kw N r) ε from rfl, hev n hn 0]
    exact ueps_top hv kx_zero ε n hn
  · simp only [show raisedKraw N r τ = epsNorm (kv N r) (kx N r) (kw N r) ε from rfl, hev m hm, hev n hn]
    exact ueps_orth hv kx_zero (k_orth hN hr hr1') (k_nrm_pos hN hr hr1') ε m n hm hn hmn

/-- The coefficient bounds behind Proposition 9.12. -/
theorem raise_bound_alg {a c ε t A B : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c) (hac : a + c ≤ 1) (hε : 0 ≤ ε)
    (ht : 0 ≤ t) (hA : 0 < A) (hB : B = A + t) (hBε : 1 + ε ≤ B) (hAε : c = 0 ∨ 1 + ε ≤ A) :
    |(1 + ε) * (a * A / B) - a| ≤ ε + t ∧
      |(1 + ε) * (1 - a * A / B - c * B / A) - ε - (1 - a - c)| ≤ ε + t ∧
        |(1 + ε) * (c * B / A) - c| ≤ ε + t := by
  have hB0 : 0 < B := by linarith
  -- `X = (1+ε) a / B ∈ [0, a]`, `Y = (1+ε) c / A ∈ [0, c]`
  have hX0 : 0 ≤ (1 + ε) * a / B := by positivity
  have hX1 : (1 + ε) * a / B ≤ a := by
    rw [div_le_iff₀ hB0]; nlinarith
  have hY0 : 0 ≤ (1 + ε) * c / A := by positivity
  have hY1 : (1 + ε) * c / A ≤ c := by
    rcases hAε with h | h
    · rw [h]; simp
    · rw [div_le_iff₀ hA]; nlinarith
  have ea : (1 + ε) * (a * A / B) - a = ε * a - t * ((1 + ε) * a / B) := by
    rw [hB]; field_simp; ring
  have ec : (1 + ε) * (c * B / A) - c = ε * c + t * ((1 + ε) * c / A) := by
    rw [hB]; field_simp; ring
  have eb : (1 + ε) * (1 - a * A / B - c * B / A) - ε - (1 - a - c) =
      -(ε * (a + c)) + t * ((1 + ε) * a / B - (1 + ε) * c / A) := by
    have : (1 + ε) * (1 - a * A / B - c * B / A) - ε - (1 - a - c) =
        -((1 + ε) * (a * A / B) - a) - ((1 + ε) * (c * B / A) - c) := by ring
    rw [this, ea, ec]; ring
  refine ⟨?_, ?_, ?_⟩
  · rw [ea, abs_le]; constructor <;> nlinarith
  · rw [eb, abs_le]; constructor <;> nlinarith
  · rw [ec, abs_le]; constructor <;> nlinarith

/-- **Proposition 9.12**, coefficients: after the affine normalization the coefficients of the
raised measure differ from those of `K_{N,r}` by at most `3 τ max_n w_n`. -/
theorem raise_bound (hN : 1 ≤ N) (hr : 0 < r) (hr1 : r < 1) {τ : ℝ} (hτ : 0 < τ) (n : ℕ) (hn : n ≤ N) :
    |(raisedKraw N r τ).a n - (krawCoefficients N r).a n| ≤ 3 * τ * univ.sup' univ_nonempty (kw N r) ∧
      |(raisedKraw N r τ).b n - (krawCoefficients N r).b n| ≤ 3 * τ * univ.sup' univ_nonempty (kw N r) ∧
        |(raisedKraw N r τ).c n - (krawCoefficients N r).c n| ≤ 3 * τ * univ.sup' univ_nonempty (kw N r) := by
  have hr1' := hr1.le
  have hv := kv_admissible hN hr hr1'
  obtain ⟨_, _, _, hc0, _, hsum, _, _⟩ := hv
  set W := univ.sup' univ_nonempty (kw N r)
  have hw0 : 0 < kw N r 0 := k_w_pos hr hr1' 0
  set ε := τ * kw N r 0 with hεdef
  have hε : 0 < ε := by positivity
  set A := Aeps (kv N r) (kx N r) (kw N r) ε n
  set B := Aeps (kv N r) (kx N r) (kw N r) ε (n + 1)
  set t := ε * piw (kv N r) (kx N r) (kw N r) n
  have hA : 0 < A := k_Aeps_pos hN hr hr1' hε.le n (by omega)
  have hB : B = A + t := by simp only [B, A, t, Aeps, Ssum_succ]; ring
  have hBε : 1 + ε ≤ B := k_Aeps_ge hN hr hr1' hε.le (n + 1) (by omega) (by omega)
  have hAε : (kv N r).c n = 0 ∨ 1 + ε ≤ A := by
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · left; rw [h0]; exact hc0
    · right; exact k_Aeps_ge hN hr hr1' hε.le n hpos (by omega)
  have hpi : 0 < piw (kv N r) (kx N r) (kw N r) n := inv_pos.mpr (k_nrm_pos hN hr hr1' n hn)
  have ht : 0 ≤ t := by positivity
  have hta : 0 ≤ (kv N r).a n := by rw [kv_a n hn]; have : (n : ℝ) ≤ N := by exact_mod_cast hn
                                    exact div_nonneg (by linarith) (by positivity)
  have htc : 0 ≤ (kv N r).c n := by rw [kv_c]; positivity
  have htb : 0 ≤ (kv N r).b n := by
    simp only [kv, geometricCoefficients, qInteger_at_one]
    have : (1 : ℝ) ≤ 1 / r := one_le_inv_r hr hr1'
    positivity
  have hac : (kv N r).a n + (kv N r).c n ≤ 1 := by linarith [hsum n hn]
  obtain ⟨b1, b2, b3⟩ := raise_bound_alg hta htc hac hε.le ht hA hB hBε hAε
  -- `ε ≤ τ W` and `t = τ w_n ≤ τ W`
  have hεW : ε ≤ τ * W := mul_le_mul_of_nonneg_left (le_sup' (kw N r) (mem_univ 0)) hτ.le
  have htW : t ≤ τ * W := by
    have : t = τ * kw N r ⟨n, by omega⟩ := by
      rw [k_w_eq hN hr hr1' ⟨n, by omega⟩]; simp only [t, ε]; ring
    rw [this]; exact mul_le_mul_of_nonneg_left (le_sup' (kw N r) (mem_univ _)) hτ.le
  have hW : 0 ≤ τ * W := le_trans hε.le hεW
  have hK := kraw_geometric_prefix N r hr n hn
  have hbK : (krawCoefficients N r).b n = 1 - (kv N r).a n - (kv N r).c n := by
    rw [hK.2.1]; linarith [hsum n hn]
  simp only [raisedKraw, epsNorm, epsRaw, ← hεdef]
  rw [hK.1, hK.2.2, hbK]
  refine ⟨by linarith, by linarith, by linarith⟩

end Szkraw
