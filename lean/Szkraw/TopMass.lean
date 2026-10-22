import Szkraw.CornerIdentity
import Szkraw.BinomialMeasure

/-!
# Changing the top mass of a finite orthogonality measure

Let `v` be an admissible array with a discrete orthogonality measure: nodes `x_t`, weights
`w_t > 0` summing to one, a top node `x_{t₀} = 1`, the eigen relation
`x_t u_i(t) = Σ_k J_{ik} u_k(t)` for the values `u_n(t) = R_n(x_t)`, and orthogonality.
Put `π_n = 1 / Σ_t w_t u_n(t)^2`, `S_n = Σ_{k<n} π_k` and `K_n(t) = Σ_{k<n} π_k u_k(t)`.

Changing the mass at `x_{t₀}` by `ε` gives the polynomials
`ũ_n = (1 + ε S_n) u_n - ε K_n` (Lemma 9.7 for `ε < 0`, Proposition 9.12 for `ε > 0`).
This file proves the identities behind both: detailed balance, the Christoffel–Darboux identity
at the top node, and dual orthogonality.
-/

namespace Szkraw

open Finset

variable {N : ℕ}

/-- The vector form of a row of the recurrence matrix. -/
theorem J_vec_apply (v : Coefficients N) (F : ℕ → ℝ) (i : Fin (N + 1)) :
    ∑ k : Fin (N + 1), recurrenceMatrix v i k * F k.val =
      (if i.val + 1 ≤ N then v.a i * F (i + 1) else 0) + v.b i * F i +
        (if 1 ≤ i.val then v.c i * F (i - 1) else 0) := by
  have h := J_mul_apply v (Matrix.of fun (l : Fin (N + 1)) (_ : Fin (N + 1)) => F l.val) F i i (fun l => rfl)
  rw [Matrix.mul_apply] at h
  exact h

section spectral

variable (v : Coefficients N) (x w : Fin (N + 1) → ℝ)

/-- The values `u_n(t) = R_n(x_t)`. -/
noncomputable def uval (n : ℕ) (t : Fin (N + 1)) : ℝ := (recurrencePolynomial v n).eval (x t)

/-- `‖R_n‖² = Σ_t w_t u_n(t)^2`. -/
noncomputable def nrm (n : ℕ) : ℝ := ∑ t, w t * uval v x n t ^ 2

/-- `π_n = 1/‖R_n‖²`. -/
noncomputable def piw (n : ℕ) : ℝ := (nrm v x w n)⁻¹

/-- `K_n(t) = Σ_{k<n} π_k u_k(t)`. -/
noncomputable def kerT (n : ℕ) (t : Fin (N + 1)) : ℝ := ∑ k ∈ range n, piw v x w k * uval v x k t

/-- `S_n = Σ_{k<n} π_k`. -/
noncomputable def Ssum (n : ℕ) : ℝ := ∑ k ∈ range n, piw v x w k

variable {v x w}

/-- The row `i` of the eigen relation. -/
theorem row_rel (hact : ∀ t (i : Fin (N + 1)), x t * uval v x i t = ∑ k, recurrenceMatrix v i k * uval v x k t)
    (t : Fin (N + 1)) (i : ℕ) (hi : i ≤ N) :
    x t * uval v x i t = (if i + 1 ≤ N then v.a i * uval v x (i + 1) t else 0) + v.b i * uval v x i t +
      (if 1 ≤ i then v.c i * uval v x (i - 1) t else 0) := by
  have h := hact t ⟨i, by omega⟩
  rw [J_vec_apply v (fun k => uval v x k t) ⟨i, by omega⟩] at h
  exact h

/-- `a_{n-1} ‖R_n‖² = c_n ‖R_{n-1}‖²`. -/
theorem norm_balance (hact : ∀ t (i : Fin (N + 1)), x t * uval v x i t = ∑ k, recurrenceMatrix v i k * uval v x k t)
    (horth : ∀ m n, m ≤ N → n ≤ N → m ≠ n → ∑ t, w t * uval v x m t * uval v x n t = 0)
    (n : ℕ) (h1 : 1 ≤ n) (hn : n ≤ N) :
    v.a (n - 1) * nrm v x w n = v.c n * nrm v x w (n - 1) := by
  -- `Σ_t w_t x_t u_{n-1} u_n` computed from rows `n - 1` and `n`
  have e1 : ∑ t, w t * (x t * uval v x (n - 1) t) * uval v x n t = v.a (n - 1) * nrm v x w n := by
    simp_rw [row_rel hact _ (n - 1) (by omega), show n - 1 + 1 = n by omega, if_pos (show n ≤ N from hn)]
    simp only [add_mul, mul_add, sum_add_distrib]
    have o1 : ∑ t, w t * (v.b (n - 1) * uval v x (n - 1) t) * uval v x n t = 0 := by
      rw [← mul_zero (v.b (n - 1)), ← horth (n - 1) n (by omega) hn (by omega), mul_sum]
      exact sum_congr rfl fun t _ => by ring
    have o2 : ∑ t, w t * (if 1 ≤ n - 1 then v.c (n - 1) * uval v x (n - 1 - 1) t else 0) * uval v x n t = 0 := by
      split_ifs with h
      · rw [← mul_zero (v.c (n - 1)), ← horth (n - 1 - 1) n (by omega) hn (by omega), mul_sum]
        exact sum_congr rfl fun t _ => by ring
      · simp
    rw [o1, o2, add_zero, add_zero, nrm, mul_sum]
    exact sum_congr rfl fun t _ => by ring
  have e2 : ∑ t, w t * (x t * uval v x n t) * uval v x (n - 1) t = v.c n * nrm v x w (n - 1) := by
    simp_rw [row_rel hact _ n hn, if_pos h1]
    simp only [add_mul, mul_add, sum_add_distrib]
    have o1 : ∑ t, w t * (if n + 1 ≤ N then v.a n * uval v x (n + 1) t else 0) * uval v x (n - 1) t = 0 := by
      split_ifs with h
      · rw [← mul_zero (v.a n), ← horth (n + 1) (n - 1) h (by omega) (by omega), mul_sum]
        exact sum_congr rfl fun t _ => by ring
      · simp
    have o2 : ∑ t, w t * (v.b n * uval v x n t) * uval v x (n - 1) t = 0 := by
      rw [← mul_zero (v.b n), ← horth n (n - 1) hn (by omega) (by omega), mul_sum]
      exact sum_congr rfl fun t _ => by ring
    rw [o1, o2, zero_add, zero_add, nrm, mul_sum]
    exact sum_congr rfl fun t _ => by ring
  rw [← e1, ← e2]
  exact sum_congr rfl fun t _ => by ring

theorem uval_zero (t : Fin (N + 1)) : uval v x 0 t = 1 := by
  simp [uval, recurrencePolynomial, polynomialPair]

/-- Detailed balance `π_{n-1} a_{n-1} = π_n c_n`. -/
theorem piw_balance (hact : ∀ t (i : Fin (N + 1)), x t * uval v x i t = ∑ k, recurrenceMatrix v i k * uval v x k t)
    (horth : ∀ m n, m ≤ N → n ≤ N → m ≠ n → ∑ t, w t * uval v x m t * uval v x n t = 0)
    (hnrm : ∀ n, n ≤ N → 0 < nrm v x w n) (n : ℕ) (h1 : 1 ≤ n) (hn : n ≤ N) :
    piw v x w (n - 1) * v.a (n - 1) = piw v x w n * v.c n := by
  have hb := norm_balance hact horth n h1 hn
  have h0 := (hnrm n hn).ne'
  have h0' := (hnrm (n - 1) (by omega)).ne'
  rw [piw, piw]
  field_simp
  linarith

/-- Christoffel–Darboux at the top node: `(x_t - 1) K_n(t) = π_{n-1} a_{n-1} (u_n(t) - u_{n-1}(t))`. -/
theorem kerT_cd (hv : Admissible v)
    (hact : ∀ t (i : Fin (N + 1)), x t * uval v x i t = ∑ k, recurrenceMatrix v i k * uval v x k t)
    (horth : ∀ m n, m ≤ N → n ≤ N → m ≠ n → ∑ t, w t * uval v x m t * uval v x n t = 0)
    (hnrm : ∀ n, n ≤ N → 0 < nrm v x w n) (t : Fin (N + 1)) :
    ∀ n, 1 ≤ n → n ≤ N →
      (x t - 1) * kerT v x w n t = piw v x w (n - 1) * v.a (n - 1) * (uval v x n t - uval v x (n - 1) t) := by
  obtain ⟨hN, ha0, hb0, hc0, haN, hsum, hapos, hcpos⟩ := hv
  intro n h1 hn
  induction n with
  | zero => omega
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · subst h0
      have r0 := row_rel hact t 0 (by omega)
      rw [if_pos (by omega), if_neg (by omega), uval_zero] at r0
      simp only [zero_add] at r0 ⊢
      simp only [kerT, range_one, sum_singleton, uval_zero, Nat.sub_self, mul_one]
      have := hsum 0 (by omega)
      rw [hc0] at this
      linear_combination (piw v x w 0) * r0 + (piw v x w 0) * this
    · have ih' := ih (by omega) (by omega)
      have rn := row_rel hact t n (by omega)
      rw [if_pos (by omega), if_pos (show 1 ≤ n by omega)] at rn
      have hbal := piw_balance hact horth hnrm n hpos (by omega)
      have hs := hsum n (by omega)
      have hk : kerT v x w (n + 1) t = kerT v x w n t + piw v x w n * uval v x n t := sum_range_succ _ _
      rw [hk, mul_add, ih', Nat.add_sub_cancel]
      linear_combination (piw v x w n) * rn + (uval v x n t - uval v x (n - 1) t) * hbal +
        (piw v x w n * uval v x n t) * hs

/-- Dual orthogonality: `Σ_{k ≤ N} π_k u_k(s) u_k(t) = δ_{st} / w_t`. -/
theorem dual_orth (horth : ∀ m n, m ≤ N → n ≤ N → m ≠ n → ∑ t, w t * uval v x m t * uval v x n t = 0)
    (hnrm : ∀ n, n ≤ N → 0 < nrm v x w n) (hw : ∀ t, 0 < w t) (s t : Fin (N + 1)) :
    ∑ k : Fin (N + 1), piw v x w k * uval v x k s * uval v x k t = if s = t then (w t)⁻¹ else 0 := by
  set A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ := Matrix.of fun k t => piw v x w k * uval v x k t
  set B : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ := Matrix.of fun t k => w t * uval v x k t
  have hAB : A * B = 1 := by
    ext m n
    simp only [A, B, Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply]
    by_cases hmn : m = n
    · subst hmn
      rw [if_pos rfl]
      have := (hnrm m (by omega)).ne'
      have e : ∑ t, piw v x w m * uval v x m t * (w t * uval v x m t) = piw v x w m * nrm v x w m := by
        rw [nrm, mul_sum]; exact sum_congr rfl fun t _ => by ring
      rw [e, piw, inv_mul_cancel₀ this]
    · rw [if_neg hmn]
      have h := horth m n (by omega) (by omega) (fun h => hmn (Fin.ext h))
      have e : ∑ t, piw v x w m * uval v x m t * (w t * uval v x n t) =
          piw v x w m * ∑ t, w t * uval v x m t * uval v x n t := by
        rw [mul_sum]; exact sum_congr rfl fun t _ => by ring
      rw [e, h, mul_zero]
  have hBA := mul_eq_one_comm.mp hAB
  have h := congrFun (congrFun hBA s) t
  simp only [A, B, Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply] at h
  have hw0 := (hw s).ne'
  have e : ∑ k : Fin (N + 1), w s * uval v x k s * (piw v x w k * uval v x k t) =
      w s * ∑ k : Fin (N + 1), piw v x w k * uval v x k s * uval v x k t := by
    rw [mul_sum]; exact sum_congr rfl fun k _ => by ring
  rw [e] at h
  split_ifs with hst
  · subst hst; rw [if_pos rfl] at h; exact eq_inv_of_mul_eq_one_right h
  · rw [if_neg hst] at h; exact (mul_eq_zero.mp h).resolve_left hw0

/-- At the top node: `Σ_{k ≤ N} π_k u_k(t) = δ_{t t₀} / w_{t₀}`. -/
theorem kerT_top (hv : Admissible v) {t₀ : Fin (N + 1)} (hx0 : x t₀ = 1)
    (horth : ∀ m n, m ≤ N → n ≤ N → m ≠ n → ∑ t, w t * uval v x m t * uval v x n t = 0)
    (hnrm : ∀ n, n ≤ N → 0 < nrm v x w n) (hw : ∀ t, 0 < w t) (t : Fin (N + 1)) :
    kerT v x w (N + 1) t = if t₀ = t then (w t)⁻¹ else 0 := by
  have h := dual_orth horth hnrm hw t₀ t
  have hu : ∀ k : Fin (N + 1), uval v x k t₀ = 1 := fun k => by
    rw [uval, hx0]; exact recurrence_normalized v hv k (by omega)
  simp only [hu, mul_one] at h
  rw [kerT, ← h, Fin.sum_univ_eq_sum_range (fun k => piw v x w k * uval v x k t) (N + 1)]

/-! ### The system with the top mass changed by `ε` -/

variable (v x w)

/-- `A_n = 1 + ε S_n`. -/
noncomputable def Aeps (ε : ℝ) (n : ℕ) : ℝ := 1 + ε * Ssum v x w n

/-- `ũ_n(t) = A_n u_n(t) - ε K_n(t)`. -/
noncomputable def ueps (ε : ℝ) (n : ℕ) (t : Fin (N + 1)) : ℝ :=
  Aeps v x w ε n * uval v x n t - ε * kerT v x w n t

/-- The recurrence coefficients of the changed measure in the coordinate `x`:
`a'_n = a_n A_n / A_{n+1}`, `c'_n = c_n A_{n+1} / A_n`, `b'_n = 1 - a'_n - c'_n`. -/
noncomputable def epsRaw (ε : ℝ) : Coefficients N where
  a n := v.a n * Aeps v x w ε n / Aeps v x w ε (n + 1)
  b n := 1 - v.a n * Aeps v x w ε n / Aeps v x w ε (n + 1) - v.c n * Aeps v x w ε (n + 1) / Aeps v x w ε n
  c n := v.c n * Aeps v x w ε (n + 1) / Aeps v x w ε n

variable {v x w}

/-- The row identity behind the changed recurrence. -/
theorem eps_row_alg {xt α ε πn an bn cn um u up K : ℝ} (hα : α ≠ 0) (hβ : α + ε * πn ≠ 0)
    (rn : xt * u = an * up + bn * u + cn * um) (hs : an + bn + cn = 1)
    (cd : (xt - 1) * K = πn * cn * (u - um)) :
    xt * (α * u - ε * K) = an * α / (α + ε * πn) * ((α + ε * πn) * up - ε * (K + πn * u)) +
      (1 - an * α / (α + ε * πn) - cn * (α + ε * πn) / α) * (α * u - ε * K) +
        cn * (α + ε * πn) / α * (α * um - ε * K) := by
  have key : an * α / (α + ε * πn) * ((α + ε * πn) * up - ε * (K + πn * u)) +
      (1 - an * α / (α + ε * πn) - cn * (α + ε * πn) / α) * (α * u - ε * K) +
        cn * (α + ε * πn) / α * (α * um - ε * K) =
      an * α * up - ε * K + (α - an * α - cn * (α + ε * πn)) * u + cn * (α + ε * πn) * um := by
    field_simp
    ring
  rw [key]
  linear_combination α * rn + α * u * hs - ε * cd

theorem Ssum_succ (n : ℕ) : Ssum v x w (n + 1) = Ssum v x w n + piw v x w n := sum_range_succ _ _

theorem kerT_succ (n : ℕ) (t : Fin (N + 1)) :
    kerT v x w (n + 1) t = kerT v x w n t + piw v x w n * uval v x n t := sum_range_succ _ _

/-- The changed polynomials satisfy the changed recurrence at every node, including the
terminal row. -/
theorem ueps_rel (hv : Admissible v)
    (hact : ∀ t (i : Fin (N + 1)), x t * uval v x i t = ∑ k, recurrenceMatrix v i k * uval v x k t)
    (horth : ∀ m n, m ≤ N → n ≤ N → m ≠ n → ∑ t, w t * uval v x m t * uval v x n t = 0)
    (hnrm : ∀ n, n ≤ N → 0 < nrm v x w n) {ε : ℝ} (hA : ∀ n, n ≤ N + 1 → Aeps v x w ε n ≠ 0)
    (t : Fin (N + 1)) (i : Fin (N + 1)) :
    x t * ueps v x w ε i t = ∑ k, recurrenceMatrix (epsRaw v x w ε) i k * ueps v x w ε k t := by
  have hv' := hv
  obtain ⟨hN, ha0, hb0, hc0, haN, hsum, hapos, hcpos⟩ := hv'
  rw [J_vec_apply (epsRaw v x w ε) (fun k => ueps v x w ε k t) i]
  set n := i.val with hn
  have hiN : n ≤ N := by omega
  have hα := hA n (by omega)
  have hβ : Aeps v x w ε n + ε * piw v x w n ≠ 0 := by
    rw [Aeps, add_assoc, ← mul_add, ← Ssum_succ]; exact hA (n + 1) (by omega)
  have hAs : Aeps v x w ε (n + 1) = Aeps v x w ε n + ε * piw v x w n := by
    rw [Aeps, Aeps, Ssum_succ]; ring
  -- the neighbours in terms of `A_n`, `K_n`
  have hup : ueps v x w ε (n + 1) t = (Aeps v x w ε n + ε * piw v x w n) * uval v x (n + 1) t -
      ε * (kerT v x w n t + piw v x w n * uval v x n t) := by
    rw [ueps, hAs, kerT_succ]
  have hs := hsum n hiN
  have hK0 : kerT v x w 0 t = 0 := by simp [kerT]
  -- uniform row relation `x u_n = a_n u_{n+1} + b_n u_n + c_n u_{n-1}`
  have rn : x t * uval v x n t = v.a n * uval v x (n + 1) t + v.b n * uval v x n t +
      v.c n * uval v x (n - 1) t := by
    have r := row_rel hact t n hiN
    by_cases h1 : n + 1 ≤ N
    · rw [if_pos h1] at r
      rcases Nat.eq_zero_or_pos n with h0 | hpos
      · rw [if_neg (by omega)] at r; rw [r, h0, hc0]; ring
      · rw [if_pos (by omega)] at r; exact r
    · rw [if_neg h1, if_pos (by omega)] at r
      rw [r, show n = N by omega, haN]; ring
  -- uniform `(x - 1) K_n = π_n c_n (u_n - u_{n-1})`
  have cd : (x t - 1) * kerT v x w n t = piw v x w n * v.c n * (uval v x n t - uval v x (n - 1) t) := by
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · rw [h0, hK0, hc0]; ring
    · rw [kerT_cd hv hact horth hnrm t n hpos hiN, piw_balance hact horth hnrm n hpos hiN]
  -- uniform `ũ_{n-1} = A_n u_{n-1} - ε K_n`
  have hdown : ueps v x w ε (n - 1) t = Aeps v x w ε n * uval v x (n - 1) t - ε * kerT v x w n t := by
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · rw [h0]; rfl
    · have hAm : Aeps v x w ε n = Aeps v x w ε (n - 1) + ε * piw v x w (n - 1) := by
        rw [Aeps, Aeps, show n = n - 1 + 1 from (Nat.sub_add_cancel hpos).symm, Ssum_succ,
          Nat.add_sub_cancel]; ring
      have hk : kerT v x w n t = kerT v x w (n - 1) t + piw v x w (n - 1) * uval v x (n - 1) t := by
        conv_lhs => rw [show n = n - 1 + 1 from (Nat.sub_add_cancel hpos).symm]
        exact kerT_succ _ _
      rw [ueps, hk, hAm]; ring
  -- the guarded terms are the plain ones
  have ga : (if n + 1 ≤ N then (epsRaw v x w ε).a n * ueps v x w ε (n + 1) t else 0) =
      (epsRaw v x w ε).a n * ueps v x w ε (n + 1) t := by
    split_ifs with h
    · rfl
    · simp [epsRaw, show v.a n = 0 by rw [show n = N by omega]; exact haN]
  have gc : (if 1 ≤ n then (epsRaw v x w ε).c n * ueps v x w ε (n - 1) t else 0) =
      (epsRaw v x w ε).c n * ueps v x w ε (n - 1) t := by
    split_ifs with h
    · rfl
    · simp [epsRaw, show v.c n = 0 by rw [show n = 0 by omega]; exact hc0]
  rw [ga, gc]
  have e := eps_row_alg (xt := x t) (α := Aeps v x w ε n) (ε := ε) (πn := piw v x w n) (an := v.a n)
    (bn := v.b n) (cn := v.c n) (um := uval v x (n - 1) t) (u := uval v x n t) (up := uval v x (n + 1) t)
    (K := kerT v x w n t) hα hβ rn hs cd
  simp only [epsRaw]
  rw [hup, hdown, hAs, show ueps v x w ε n t = Aeps v x w ε n * uval v x n t - ε * kerT v x w n t from rfl]
  linear_combination e

/-- `ũ_n(t₀) = 1`. -/
theorem ueps_top (hv : Admissible v) {t₀ : Fin (N + 1)} (hx0 : x t₀ = 1) (ε : ℝ) (n : ℕ) (hn : n ≤ N) :
    ueps v x w ε n t₀ = 1 := by
  have hu : ∀ k, k ≤ N → uval v x k t₀ = 1 := fun k hk => by
    rw [uval, hx0]; exact recurrence_normalized v hv k hk
  have hK : kerT v x w n t₀ = Ssum v x w n := by
    rw [kerT, Ssum]
    exact sum_congr rfl fun k hk => by rw [mem_range] at hk; rw [hu k (by omega), mul_one]
  rw [ueps, hK, hu n hn, Aeps]; ring

/-- `Σ_t w_t ũ_k(t) u_j(t) = A_k ‖R_k‖² δ_{jk} - ε [j < k]`. -/
theorem ueps_inner (horth : ∀ m n, m ≤ N → n ≤ N → m ≠ n → ∑ t, w t * uval v x m t * uval v x n t = 0)
    (hnrm : ∀ n, n ≤ N → 0 < nrm v x w n) (ε : ℝ) (k j : ℕ) (hk : k ≤ N) (hj : j ≤ N) :
    ∑ t, w t * ueps v x w ε k t * uval v x j t =
      (if j = k then Aeps v x w ε k * nrm v x w k else 0) - (if j < k then ε else 0) := by
  have hinner : ∀ i, i ≤ N → ∑ t, w t * uval v x i t * uval v x j t = if i = j then nrm v x w j else 0 := by
    intro i hi
    split_ifs with h
    · subst h; rw [nrm]; exact sum_congr rfl fun t _ => by ring
    · exact horth i j hi hj h
  have e : ∑ t, w t * ueps v x w ε k t * uval v x j t =
      Aeps v x w ε k * (∑ t, w t * uval v x k t * uval v x j t) -
        ε * ∑ i ∈ range k, piw v x w i * (∑ t, w t * uval v x i t * uval v x j t) := by
    simp only [ueps, kerT, mul_sum, sum_mul, mul_sub, sub_mul, sum_sub_distrib]
    congr 1
    · exact sum_congr rfl fun t _ => by ring
    · rw [sum_comm]
      exact sum_congr rfl fun i _ => sum_congr rfl fun t _ => by ring
  rw [e, hinner k hk]
  have hs : ∑ i ∈ range k, piw v x w i * (∑ t, w t * uval v x i t * uval v x j t) = if j < k then 1 else 0 := by
    rw [sum_congr rfl fun i hi => by rw [hinner i (by rw [mem_range] at hi; omega)]]
    simp only [mul_ite, mul_zero]
    rw [sum_ite_eq' (range k) j]
    simp only [mem_range]
    split_ifs with h
    · rw [piw, inv_mul_cancel₀ (hnrm j hj).ne']
    · rfl
  rw [hs]
  by_cases hjk : j = k
  · subst hjk; simp
  · rw [if_neg (Ne.symm hjk), if_neg hjk]
    split_ifs <;> ring

/-- Orthogonality of the changed polynomials for the measure `w + ε δ_{t₀}`. -/
theorem ueps_orth (hv : Admissible v) {t₀ : Fin (N + 1)} (hx0 : x t₀ = 1)
    (horth : ∀ m n, m ≤ N → n ≤ N → m ≠ n → ∑ t, w t * uval v x m t * uval v x n t = 0)
    (hnrm : ∀ n, n ≤ N → 0 < nrm v x w n) (ε : ℝ) (k n : ℕ) (hk : k ≤ N) (hn : n ≤ N) (hkn : k ≠ n) :
    ∑ t, (w t + if t = t₀ then ε else 0) * ueps v x w ε k t * ueps v x w ε n t = 0 := by
  -- reduce to `k < n`
  wlog hlt : k < n generalizing k n
  · have h := this n k hn hk (Ne.symm hkn) (by omega)
    have hsym : ∑ t, (w t + if t = t₀ then ε else 0) * ueps v x w ε k t * ueps v x w ε n t =
        ∑ t, (w t + if t = t₀ then ε else 0) * ueps v x w ε n t * ueps v x w ε k t :=
      sum_congr rfl fun t _ => by ring
    rw [hsym]; exact h
  have hsplit : ∑ t, (w t + if t = t₀ then ε else 0) * ueps v x w ε k t * ueps v x w ε n t =
      ∑ t, w t * ueps v x w ε k t * ueps v x w ε n t + ε * ueps v x w ε k t₀ * ueps v x w ε n t₀ := by
    simp only [add_mul, sum_add_distrib, ite_mul, zero_mul, sum_ite_eq' univ t₀, mem_univ, if_true]
  rw [hsplit, ueps_top hv hx0 ε k hk, ueps_top hv hx0 ε n hn]
  have e : ∑ t, w t * ueps v x w ε k t * ueps v x w ε n t =
      Aeps v x w ε n * (∑ t, w t * ueps v x w ε k t * uval v x n t) -
        ε * ∑ j ∈ range n, piw v x w j * (∑ t, w t * ueps v x w ε k t * uval v x j t) := by
    have ht : ∀ t, w t * ueps v x w ε k t * ueps v x w ε n t =
        Aeps v x w ε n * (w t * ueps v x w ε k t * uval v x n t) -
          ε * ∑ j ∈ range n, piw v x w j * (w t * ueps v x w ε k t * uval v x j t) := by
      intro t
      rw [show ueps v x w ε n t = Aeps v x w ε n * uval v x n t - ε * kerT v x w n t from rfl, kerT,
        mul_sub, mul_sum, mul_sum]
      congr 1
      · ring
      · rw [mul_sum]; exact sum_congr rfl fun j _ => by ring
    rw [sum_congr rfl fun t _ => ht t, sum_sub_distrib, ← mul_sum, ← mul_sum, sum_comm]
    congr 2
    exact sum_congr rfl fun j _ => by rw [mul_sum]
  rw [e, ueps_inner horth hnrm ε k n hk hn, if_neg (by omega), if_neg (by omega)]
  have hs : ∑ j ∈ range n, piw v x w j * (∑ t, w t * ueps v x w ε k t * uval v x j t) = 1 := by
    rw [sum_congr rfl fun j hj => by rw [ueps_inner horth hnrm ε k j hk (by rw [mem_range] at hj; omega)]]
    have : ∀ j ∈ range n, piw v x w j * ((if j = k then Aeps v x w ε k * nrm v x w k else 0) -
        (if j < k then ε else 0)) = (if j = k then Aeps v x w ε k else 0) - (if j < k then ε * piw v x w j else 0) := by
      intro j hj
      split_ifs with h1 h2 h2
      · omega
      · subst h1; rw [piw]; field_simp [(hnrm j (by rw [mem_range] at hj; omega)).ne']; ring
      · ring
      · ring
    rw [sum_congr rfl this, sum_sub_distrib, sum_ite_eq' (range n) k, if_pos (mem_range.mpr hlt)]
    have : ∑ j ∈ range n, (if j < k then ε * piw v x w j else 0) = ε * Ssum v x w k := by
      rw [Ssum, mul_sum, ← sum_filter]
      congr 1
      ext j; simp only [mem_filter, mem_range]; omega
    rw [this, Aeps]; ring
  rw [hs]; ring

variable (v x w) in
/-- The changed system after the affine normalization `y = (1 + ε) x - ε`. -/
noncomputable def epsNorm (ε : ℝ) : Coefficients N where
  a n := (1 + ε) * (epsRaw v x w ε).a n
  b n := (1 + ε) * (epsRaw v x w ε).b n - ε
  c n := (1 + ε) * (epsRaw v x w ε).c n

theorem epsNorm_recurrence (ε : ℝ) :
    recurrenceMatrix (epsNorm v x w ε) = (1 + ε) • recurrenceMatrix (epsRaw v x w ε) - ε • (1 : Matrix _ _ ℝ) := by
  ext i j
  simp only [recurrenceMatrix, epsNorm, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul,
    Fin.ext_iff]
  split_ifs <;> first | (exfalso; omega) | ring

/-- The normalized eigen relation at the nodes `y_t = (1 + ε) x_t - ε`. -/
theorem ueps_rel_norm (hv : Admissible v)
    (hact : ∀ t (i : Fin (N + 1)), x t * uval v x i t = ∑ k, recurrenceMatrix v i k * uval v x k t)
    (horth : ∀ m n, m ≤ N → n ≤ N → m ≠ n → ∑ t, w t * uval v x m t * uval v x n t = 0)
    (hnrm : ∀ n, n ≤ N → 0 < nrm v x w n) {ε : ℝ} (hA : ∀ n, n ≤ N + 1 → Aeps v x w ε n ≠ 0)
    (t i : Fin (N + 1)) :
    ((1 + ε) * x t - ε) * ueps v x w ε i t =
      ∑ k, recurrenceMatrix (epsNorm v x w ε) i k * ueps v x w ε k t := by
  rw [epsNorm_recurrence]
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, sub_mul, sum_sub_distrib]
  rw [show ∑ k, (1 + ε) * recurrenceMatrix (epsRaw v x w ε) i k * ueps v x w ε k t =
    (1 + ε) * ∑ k, recurrenceMatrix (epsRaw v x w ε) i k * ueps v x w ε k t by
      rw [mul_sum]; exact sum_congr rfl fun k _ => by ring,
    ← ueps_rel hv hact horth hnrm hA t i]
  simp only [mul_ite, mul_one, mul_zero, ite_mul, zero_mul, sum_ite_eq, mem_univ, if_true]
  ring

/-- The changed polynomials are the polynomials of the normalized changed system:
`R̃_m(y_t) = ũ_m(t)`. -/
theorem ueps_eval (hv : Admissible v)
    (hact : ∀ t (i : Fin (N + 1)), x t * uval v x i t = ∑ k, recurrenceMatrix v i k * uval v x k t)
    (horth : ∀ m n, m ≤ N → n ≤ N → m ≠ n → ∑ t, w t * uval v x m t * uval v x n t = 0)
    (hnrm : ∀ n, n ≤ N → 0 < nrm v x w n) {ε : ℝ} (h1ε : 1 + ε ≠ 0) (hA : ∀ n, n ≤ N + 1 → Aeps v x w ε n ≠ 0)
    (m : ℕ) (hm : m ≤ N) (t : Fin (N + 1)) :
    (recurrencePolynomial (epsNorm v x w ε) m).eval ((1 + ε) * x t - ε) = ueps v x w ε m t := by
  have hJ := ueps_rel_norm hv hact horth hnrm hA t
  have hrep := representation_product (epsNorm v x w ε) (fun k => ueps v x w ε k t)
    ((1 + ε) * x t - ε) (fun i => by simpa only [smul_eq_mul] using hJ i) m 0
  have ha : ∀ k, k < N → (epsNorm v x w ε).a k ≠ 0 := by
    intro k hk
    simp only [epsNorm, epsRaw]
    have := hv.2.2.2.2.2.2.1 k hk
    exact mul_ne_zero h1ε (div_ne_zero (mul_ne_zero this.ne' (hA k (by omega))) (hA (k + 1) (by omega)))
  have h0 : ueps v x w ε 0 t = 1 := by simp [ueps, Aeps, Ssum, kerT, uval_zero]
  simp only [smul_eq_mul, Fin.val_zero] at hrep
  rw [h0, mul_one] at hrep
  rw [← Polynomial.coe_aeval_eq_eval, hrep, sum_eq_single ⟨m, by omega⟩]
  · rw [row_zero _ ha m hm]; simp
  · intro k _ hk; rw [row_zero _ ha m hm, if_neg (fun h => hk (Fin.ext h)), zero_mul]
  · intro h; exact absurd (mem_univ _) h

/-- The product identity for the changed system at every node. -/
theorem ueps_product (hv : Admissible v)
    (hact : ∀ t (i : Fin (N + 1)), x t * uval v x i t = ∑ k, recurrenceMatrix v i k * uval v x k t)
    (horth : ∀ m n, m ≤ N → n ≤ N → m ≠ n → ∑ t, w t * uval v x m t * uval v x n t = 0)
    (hnrm : ∀ n, n ≤ N → 0 < nrm v x w n) {ε : ℝ} (h1ε : 1 + ε ≠ 0) (hA : ∀ n, n ≤ N + 1 → Aeps v x w ε n ≠ 0)
    (m : ℕ) (hm : m ≤ N) (t i : Fin (N + 1)) :
    ueps v x w ε m t * ueps v x w ε i t = ∑ k, productMatrix (epsNorm v x w ε) m i k * ueps v x w ε k t := by
  have hJ := ueps_rel_norm hv hact horth hnrm hA t
  have hrep := fun j => representation_product (epsNorm v x w ε) (fun k => ueps v x w ε k t)
    ((1 + ε) * x t - ε) (fun i => by simpa only [smul_eq_mul] using hJ i) m j
  have ha : ∀ k, k < N → (epsNorm v x w ε).a k ≠ 0 := by
    intro k hk
    simp only [epsNorm, epsRaw]
    have := hv.2.2.2.2.2.2.1 k hk
    exact mul_ne_zero h1ε (div_ne_zero (mul_ne_zero this.ne' (hA k (by omega))) (hA (k + 1) (by omega)))
  have h0 : ueps v x w ε 0 t = 1 := by simp [ueps, Aeps, Ssum, kerT, uval_zero]
  -- `R̃_m(y_t) = ũ_m(t)`
  have hm' : Polynomial.aeval ((1 + ε) * x t - ε) (recurrencePolynomial (epsNorm v x w ε) m) = ueps v x w ε m t := by
    have := hrep 0
    simp only [smul_eq_mul, Fin.val_zero] at this
    rw [h0, mul_one] at this
    rw [this, sum_eq_single ⟨m, by omega⟩]
    · rw [row_zero _ ha m hm]; simp
    · intro k _ hk; rw [row_zero _ ha m hm, if_neg (fun h => hk (Fin.ext h)), zero_mul]
    · intro h; exact absurd (mem_univ _) h
  have := hrep i
  simp only [smul_eq_mul] at this
  rw [← hm']
  exact this

/-- `g̃(N,N;N) Σ_t m_t ũ_N(t)^2 = Σ_t m_t ũ_N(t)^3` for the measure `m = w + ε δ_{t₀}`. -/
theorem eps_corner (hv : Admissible v) {t₀ : Fin (N + 1)} (hx0 : x t₀ = 1)
    (hact : ∀ t (i : Fin (N + 1)), x t * uval v x i t = ∑ k, recurrenceMatrix v i k * uval v x k t)
    (horth : ∀ m n, m ≤ N → n ≤ N → m ≠ n → ∑ t, w t * uval v x m t * uval v x n t = 0)
    (hnrm : ∀ n, n ≤ N → 0 < nrm v x w n) {ε : ℝ} (h1ε : 1 + ε ≠ 0) (hA : ∀ n, n ≤ N + 1 → Aeps v x w ε n ≠ 0) :
    productMatrix (epsNorm v x w ε) N (Fin.last N) (Fin.last N) *
        ∑ t, (w t + if t = t₀ then ε else 0) * ueps v x w ε N t ^ 2 =
      ∑ t, (w t + if t = t₀ then ε else 0) * ueps v x w ε N t ^ 3 := by
  have hp := fun t => ueps_product hv hact horth hnrm h1ε hA N le_rfl t (Fin.last N)
  have e : ∑ t, (w t + if t = t₀ then ε else 0) * ueps v x w ε N t ^ 3 =
      ∑ k : Fin (N + 1), productMatrix (epsNorm v x w ε) N (Fin.last N) k *
        ∑ t, (w t + if t = t₀ then ε else 0) * ueps v x w ε k t * ueps v x w ε N t := by
    have : ∀ t, (w t + if t = t₀ then ε else 0) * ueps v x w ε N t ^ 3 =
        ∑ k : Fin (N + 1), productMatrix (epsNorm v x w ε) N (Fin.last N) k *
          ((w t + if t = t₀ then ε else 0) * ueps v x w ε k t * ueps v x w ε N t) := by
      intro t
      have h := hp t
      simp only [Fin.val_last] at h
      rw [show ueps v x w ε N t ^ 3 = (ueps v x w ε N t * ueps v x w ε N t) * ueps v x w ε N t by ring, h,
        sum_mul, mul_sum]
      exact sum_congr rfl fun k _ => by ring
    rw [sum_congr rfl fun t _ => this t, sum_comm]
    exact sum_congr rfl fun k _ => by rw [mul_sum]
  have hsingle : ∑ k : Fin (N + 1), productMatrix (epsNorm v x w ε) N (Fin.last N) k *
      ∑ t, (w t + if t = t₀ then ε else 0) * ueps v x w ε k t * ueps v x w ε N t =
      productMatrix (epsNorm v x w ε) N (Fin.last N) (Fin.last N) *
        ∑ t, (w t + if t = t₀ then ε else 0) * ueps v x w ε N t * ueps v x w ε N t := by
    rw [sum_eq_single (Fin.last N)]
    · rfl
    · intro k _ hk
      rw [ueps_orth hv hx0 horth hnrm ε k N (by omega) le_rfl (fun h => hk (Fin.ext (by simp [h]))), mul_zero]
    · intro h; exact absurd (mem_univ _) h
  rw [e, hsingle]
  congr 1
  exact sum_congr rfl fun t _ => by ring

/-- Off the top node `ũ_N = (1 + ε/w_{t₀}) u_N`. -/
theorem ueps_N_off (hv : Admissible v) {t₀ : Fin (N + 1)} (hx0 : x t₀ = 1)
    (horth : ∀ m n, m ≤ N → n ≤ N → m ≠ n → ∑ t, w t * uval v x m t * uval v x n t = 0)
    (hnrm : ∀ n, n ≤ N → 0 < nrm v x w n) (hw : ∀ t, 0 < w t) (ε : ℝ) (t : Fin (N + 1)) (ht : t ≠ t₀) :
    ueps v x w ε N t = (1 + ε / w t₀) * uval v x N t := by
  have hK := kerT_top hv hx0 horth hnrm hw t
  have hK0 := kerT_top hv hx0 horth hnrm hw t₀
  rw [if_neg (Ne.symm ht)] at hK
  rw [if_pos rfl] at hK0
  have hS : Ssum v x w (N + 1) = (w t₀)⁻¹ := by
    have hu : ∀ k, k ≤ N → uval v x k t₀ = 1 := fun k hk => by
      rw [uval, hx0]; exact recurrence_normalized v hv k hk
    rw [← hK0, kerT, Ssum]
    exact sum_congr rfl fun k hk => by rw [mem_range] at hk; rw [hu k (by omega), mul_one]
  rw [kerT_succ] at hK
  rw [Ssum_succ] at hS
  rw [ueps, Aeps, show kerT v x w N t = -(piw v x w N * uval v x N t) by linarith, div_eq_mul_inv, ← hS]
  ring

/-- **The corner after changing the top mass**: with `τ = ε / w_{t₀}`, `I = Σ_t w_t u_N^3`,
`h = Σ_t w_t u_N^2` and `w₀ = w_{t₀}`,
`g̃(N,N;N) ((1+τ)(h - w₀) + w₀) = (1+τ)^2 (I - w₀) + w₀`. -/
theorem eps_corner_value (hv : Admissible v) {t₀ : Fin (N + 1)} (hx0 : x t₀ = 1)
    (hact : ∀ t (i : Fin (N + 1)), x t * uval v x i t = ∑ k, recurrenceMatrix v i k * uval v x k t)
    (horth : ∀ m n, m ≤ N → n ≤ N → m ≠ n → ∑ t, w t * uval v x m t * uval v x n t = 0)
    (hnrm : ∀ n, n ≤ N → 0 < nrm v x w n) (hw : ∀ t, 0 < w t) {ε : ℝ} (h1ε : 0 < 1 + ε / w t₀)
    (h1ε' : 1 + ε ≠ 0) (hA : ∀ n, n ≤ N + 1 → Aeps v x w ε n ≠ 0) :
    productMatrix (epsNorm v x w ε) N (Fin.last N) (Fin.last N) *
        ((1 + ε / w t₀) * (nrm v x w N - w t₀) + w t₀) =
      (1 + ε / w t₀) ^ 2 * (∑ t, w t * uval v x N t ^ 3 - w t₀) + w t₀ := by
  set τ := ε / w t₀ with hτ
  have hw0 := (hw t₀).ne'
  have hε : ε = τ * w t₀ := by rw [hτ]; field_simp
  have hu0 : uval v x N t₀ = 1 := by rw [uval, hx0]; exact recurrence_normalized v hv N le_rfl
  have htop := ueps_top (w := w) hv hx0 ε N le_rfl
  -- `Σ_t m_t ũ_N^p = (1+τ)^p (Σ_t w_t u_N^p - w₀) + (1+τ) w₀`
  have hpow : ∀ p : ℕ, ∑ t, (w t + if t = t₀ then ε else 0) * ueps v x w ε N t ^ p =
      (1 + τ) ^ p * (∑ t, w t * uval v x N t ^ p - w t₀) + (1 + τ) * w t₀ := by
    intro p
    rw [← add_sum_erase _ _ (mem_univ t₀), ← add_sum_erase _ _ (mem_univ t₀), if_pos rfl, htop, hu0]
    have hrest : ∑ t ∈ univ.erase t₀, (w t + if t = t₀ then ε else 0) * ueps v x w ε N t ^ p =
        (1 + τ) ^ p * ∑ t ∈ univ.erase t₀, w t * uval v x N t ^ p := by
      rw [mul_sum]
      refine sum_congr rfl fun t ht => ?_
      have htt := ne_of_mem_erase ht
      rw [if_neg htt, ueps_N_off hv hx0 horth hnrm hw ε t htt, mul_pow]
      ring
    rw [hrest, hε]
    ring
  have hc := eps_corner hv hx0 hact horth hnrm h1ε' hA
  rw [hpow 2, hpow 3] at hc
  have hnrm2 : ∑ t, w t * uval v x N t ^ 2 = nrm v x w N := rfl
  rw [hnrm2] at hc
  have h1τ : (1 + τ) ≠ 0 := h1ε.ne'
  apply mul_left_cancel₀ h1τ
  linear_combination hc

end spectral
