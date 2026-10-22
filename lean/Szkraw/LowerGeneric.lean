import Szkraw.LowerTopMass

/-!
# Lemma 9.7 (2) for any orthogonality data, and the first-order change of `g`

The proof of `lower_triple` uses only the eigen relation, orthogonality and a top node. Here it is
restated for arbitrary data `(x, w)` and combined with the product identity of the lowered system:
if `g(m,n;k) = 0`, then lowering the top mass changes `g(m,n;k)` at the rate
`π_k (2 - T_m(n,k) - T_n(m,k) - T_k(m,n))`.
-/

namespace Szkraw

open Finset Filter Topology

variable {N : ℕ} (v : Coefficients N) (hv : Admissible v) {x w : Fin (N + 1) → ℝ}
  (hact : ∀ t (i : Fin (N + 1)), x t * uval v x i t = ∑ k, recurrenceMatrix v i k * uval v x k t)
  (horth : ∀ m n, m ≤ N → n ≤ N → m ≠ n → ∑ t, w t * uval v x m t * uval v x n t = 0)
  (hnrm : ∀ n, n ≤ N → 0 < nrm v x w n)

include hv hact in
theorem gen_product (m : ℕ) (hm : m ≤ N) (n t : Fin (N + 1)) :
    uval v x m t * uval v x n t = ∑ k, productMatrix v m n k * uval v x k t := by
  have hrep := representation_product v (fun j => uval v x j t) (x t)
    (fun i => by simpa only [smul_eq_mul] using hact t i)
  have hm' : Polynomial.aeval (x t) (recurrencePolynomial v m) = uval v x m t := by
    have h := hrep m 0
    have ha : ∀ i, i < N → v.a i ≠ 0 := fun i hi => (hv.2.2.2.2.2.2.1 i hi).ne'
    simp only [smul_eq_mul, Fin.val_zero, uval_zero, mul_one] at h
    rw [h, sum_eq_single ⟨m, by omega⟩]
    · rw [row_zero _ ha m hm]; simp
    · intro k _ hk; rw [row_zero _ ha m hm, if_neg (fun h => hk (Fin.ext h)), zero_mul]
    · intro h; exact absurd (mem_univ _) h
  have h := hrep m n
  simp only [smul_eq_mul] at h
  rw [← hm']; exact h

include hv hact horth in
theorem gen_triple (l : Fin (N + 1)) (j : ℕ) (hj : j ≤ N) (k : Fin (N + 1)) :
    ∑ t, w t * uval v x l t * (uval v x j t * uval v x k t) = productMatrix v j k l * nrm v x w l := by
  simp_rw [gen_product v hv hact j hj k, mul_sum]
  rw [sum_comm, sum_eq_single l]
  · rw [nrm, mul_sum]; exact sum_congr rfl fun t _ => by ring
  · intro m _ hml
    have := horth l m (by omega) (by omega) (fun h => hml (Fin.ext h.symm))
    rw [← mul_zero (productMatrix v j k m), ← this, mul_sum]
    exact sum_congr rfl fun t _ => by ring
  · intro h; exact absurd (mem_univ _) h

include hv hact horth hnrm in
theorem gen_Qsum (a b c : Fin (N + 1))
    (h0 : ∑ t, w t * uval v x a t * uval v x b t * uval v x c t = 0) :
    ∑ t, w t * (kerT v x w a t - Ssum v x w a * uval v x a t) * uval v x b t * uval v x c t =
      1 - tailG v a b c := by
  have e1 : ∑ t, w t * (kerT v x w a t - Ssum v x w a * uval v x a t) * uval v x b t * uval v x c t =
      ∑ t, w t * kerT v x w a t * uval v x b t * uval v x c t -
        Ssum v x w a * ∑ t, w t * uval v x a t * uval v x b t * uval v x c t := by
    rw [mul_sum, ← sum_sub_distrib]; exact sum_congr rfl fun t _ => by ring
  rw [e1, h0, mul_zero, sub_zero]
  have e2 : ∑ t, w t * kerT v x w a t * uval v x b t * uval v x c t =
      ∑ l : Fin (N + 1), if l.val < a.val then productMatrix v b c l else 0 := by
    have hk : ∀ t, kerT v x w a t = ∑ l : Fin (N + 1), if l.val < a.val then piw v x w l * uval v x l t else 0 := by
      intro t
      rw [kerT, Fin.sum_univ_eq_sum_range (fun l => if l < a.val then piw v x w l * uval v x l t else 0) (N + 1),
        ← sum_filter]
      congr 1; ext l; simp only [mem_filter, mem_range]; omega
    simp_rw [hk, mul_sum, sum_mul]
    rw [sum_comm]
    refine sum_congr rfl fun l _ => ?_
    split_ifs with hl
    · have := gen_triple v hv hact horth l b.val (by omega) c
      have hpn : piw v x w l * nrm v x w l = 1 := inv_mul_cancel₀ (hnrm l (by omega)).ne'
      calc ∑ t, w t * (piw v x w l * uval v x l t) * uval v x b t * uval v x c t
          = piw v x w l * ∑ t, w t * uval v x l t * (uval v x b t * uval v x c t) := by
            rw [mul_sum]; exact sum_congr rfl fun t _ => by ring
        _ = productMatrix v b c l := by rw [this, mul_comm (productMatrix v b c l), ← mul_assoc, hpn, one_mul]
    · simp
  rw [e2, tailG]
  have hrow := product_row_sum v hv b.val (by omega) c
  rw [← hrow, ← sum_sub_distrib]
  exact sum_congr rfl fun l _ => by split_ifs <;> first | omega | ring

include hv hact horth hnrm in
/-- Lemma 9.7 (2) for any data, in terms of the changed values `ũ = ueps (-ε)`. -/
theorem gen_triple_deriv {t₀ : Fin (N + 1)} (hx0 : x t₀ = 1) (i j k : Fin (N + 1))
    (h0 : ∑ t, w t * uval v x i t * uval v x j t * uval v x k t = 0) :
    HasDerivAt (fun ε => ∑ t, (w t - if t = t₀ then ε else 0) * ueps v x w (-ε) i t * ueps v x w (-ε) j t *
      ueps v x w (-ε) k t) (2 - tailG v i j k - tailG v j i k - tailG v k i j) 0 := by
  set Q : ℕ → Fin (N + 1) → ℝ := fun m t => kerT v x w m t - Ssum v x w m * uval v x m t
  have hU : ∀ (m : ℕ) t, HasDerivAt (fun ε : ℝ => ueps v x w (-ε) m t) (Q m t) 0 := by
    intro m t
    have hA := ((hasDerivAt_neg (0 : ℝ)).mul_const (Ssum v x w m)).const_add 1
    have h := (hA.mul_const (uval v x m t)).sub ((hasDerivAt_neg (0 : ℝ)).mul_const (kerT v x w m t))
    exact h.congr_deriv (by simp only [Q]; ring)
  have hval : ∀ (m : ℕ) t, ueps v x w (-0) m t = uval v x m t := fun m t => by simp [ueps, Aeps]
  have hW : ∀ t, HasDerivAt (fun ε : ℝ => w t - if t = t₀ then ε else 0) (-(if t = t₀ then 1 else 0)) 0 := by
    intro t
    by_cases h : t = t₀
    · simp only [h, if_true]
      exact ((hasDerivAt_const (0 : ℝ) (w t₀)).sub (hasDerivAt_id' (0 : ℝ))).congr_deriv (by ring)
    · simp only [h, if_false, sub_zero, neg_zero]
      exact hasDerivAt_const (0 : ℝ) (w t)
  have hG := HasDerivAt.fun_sum (u := univ) fun t _ =>
    (((hW t).mul (hU i t)).mul (hU j t)).mul (hU k t)
  have hsym1 : ∑ t, w t * uval v x j t * uval v x i t * uval v x k t = 0 := by
    rw [← h0]; exact sum_congr rfl fun t _ => by ring
  have hsym2 : ∑ t, w t * uval v x k t * uval v x i t * uval v x j t = 0 := by
    rw [← h0]; exact sum_congr rfl fun t _ => by ring
  have q1 := gen_Qsum v hv hact horth hnrm i j k h0
  have q2 := gen_Qsum v hv hact horth hnrm j i k hsym1
  have q3 := gen_Qsum v hv hact horth hnrm k i j hsym2
  have hu0 : ∀ m : Fin (N + 1), uval v x m t₀ = 1 := fun m => by
    rw [uval, hx0]; exact recurrence_normalized v hv m (by omega)
  have hD : ∑ t, ((((-(if t = t₀ then (1 : ℝ) else 0)) * ueps v x w (-0) i t +
      (w t - if t = t₀ then (0 : ℝ) else 0) * Q i t) * ueps v x w (-0) j t +
      ((w t - if t = t₀ then (0 : ℝ) else 0) * ueps v x w (-0) i t) * Q j t) * ueps v x w (-0) k t +
      ((w t - if t = t₀ then (0 : ℝ) else 0) * ueps v x w (-0) i t * ueps v x w (-0) j t) * Q k t) =
      2 - tailG v i j k - tailG v j i k - tailG v k i j := by
    simp only [hval, ite_self, sub_zero]
    have e : ∀ t, ((((-(if t = t₀ then (1 : ℝ) else 0)) * uval v x i t + w t * Q i t) * uval v x j t +
        (w t * uval v x i t) * Q j t) * uval v x k t + (w t * uval v x i t * uval v x j t) * Q k t) =
        -(if t = t₀ then uval v x i t * uval v x j t * uval v x k t else 0) +
          w t * Q i t * uval v x j t * uval v x k t + w t * Q j t * uval v x i t * uval v x k t +
          w t * Q k t * uval v x i t * uval v x j t := by
      intro t; split_ifs <;> ring
    rw [sum_congr rfl fun t _ => e t, sum_add_distrib, sum_add_distrib, sum_add_distrib, sum_neg_distrib,
      sum_ite_eq' univ t₀, if_pos (mem_univ _), hu0, hu0, hu0]
    simp only [Q] at q1 q2 q3 ⊢
    rw [q1, q2, q3]; ring
  exact hG.congr_deriv hD

include hv hact horth hnrm in
/-- `g^ε(m,n;k) Σ_t m_t ũ_k^2 = Σ_t m_t ũ_m ũ_n ũ_k` for the measure `m = w + ε δ_{t₀}`. -/
theorem gen_raw_g {t₀ : Fin (N + 1)} (hx0 : x t₀ = 1) {ε : ℝ} (hA : ∀ n, n ≤ N + 1 → Aeps v x w ε n ≠ 0)
    (m : ℕ) (hm : m ≤ N) (n k : Fin (N + 1)) :
    productMatrix (epsRaw v x w ε) m n k * ∑ t, (w t + if t = t₀ then ε else 0) * ueps v x w ε k t ^ 2 =
      ∑ t, (w t + if t = t₀ then ε else 0) * ueps v x w ε m t * ueps v x w ε n t * ueps v x w ε k t := by
  have hprod : ∀ t, ueps v x w ε m t * ueps v x w ε n t =
      ∑ l, productMatrix (epsRaw v x w ε) m n l * ueps v x w ε l t := by
    intro t
    have hJ := ueps_rel hv hact horth hnrm hA t
    have hrep := representation_product (epsRaw v x w ε) (fun l => ueps v x w ε l t) (x t)
      (fun i => by simpa only [smul_eq_mul] using hJ i) m n
    simp only [smul_eq_mul] at hrep
    rw [Polynomial.coe_aeval_eq_eval, ueps_eval_raw v hv hact horth hnrm hA m hm t] at hrep
    exact hrep
  have e : ∑ t, (w t + if t = t₀ then ε else 0) * ueps v x w ε m t * ueps v x w ε n t * ueps v x w ε k t =
      ∑ l : Fin (N + 1), productMatrix (epsRaw v x w ε) m n l *
        ∑ t, (w t + if t = t₀ then ε else 0) * ueps v x w ε l t * ueps v x w ε k t := by
    have : ∀ t, (w t + if t = t₀ then ε else 0) * ueps v x w ε m t * ueps v x w ε n t * ueps v x w ε k t =
        ∑ l : Fin (N + 1), productMatrix (epsRaw v x w ε) m n l *
          ((w t + if t = t₀ then ε else 0) * ueps v x w ε l t * ueps v x w ε k t) := by
      intro t
      have e1 : (w t + if t = t₀ then ε else 0) * ueps v x w ε m t * ueps v x w ε n t * ueps v x w ε k t =
          ((w t + if t = t₀ then ε else 0) * ueps v x w ε k t) * (ueps v x w ε m t * ueps v x w ε n t) := by ring
      rw [e1, hprod t, mul_sum]
      exact sum_congr rfl fun l _ => by ring
    rw [sum_congr rfl fun t _ => this t, sum_comm]
    exact sum_congr rfl fun l _ => by rw [mul_sum]
  have hsingle : ∑ l : Fin (N + 1), productMatrix (epsRaw v x w ε) m n l *
      ∑ t, (w t + if t = t₀ then ε else 0) * ueps v x w ε l t * ueps v x w ε k t =
      productMatrix (epsRaw v x w ε) m n k *
        ∑ t, (w t + if t = t₀ then ε else 0) * ueps v x w ε k t * ueps v x w ε k t := by
    rw [sum_eq_single k]
    · intro l _ hl
      rw [ueps_orth hv hx0 horth hnrm ε l k (by omega) (by omega) (fun h => hl (Fin.ext h)), mul_zero]
    · intro h; exact absurd (mem_univ _) h
  rw [e, hsingle]
  congr 1
  exact sum_congr rfl fun t _ => by ring

include hv in
theorem epsRaw_zero_product (m : ℕ) (hm : m ≤ N + 1) :
    productMatrix (epsRaw v x w (-0)) m = productMatrix v m := by
  obtain ⟨_, _, _, _, _, hsum, _, _⟩ := hv
  have hA : ∀ n, Aeps v x w (-0) n = 1 := fun n => by simp [Aeps]
  apply product_congr _ _ _ _ _ m hm
  · intro i _; simp only [epsRaw, hA, div_one, mul_one]
  · intro i hi; simp only [epsRaw, hA, div_one, mul_one]; linarith [hsum i hi]
  · intro i _; simp only [epsRaw, hA, div_one, mul_one]

include hv hact horth hnrm in
/-- **The first-order change of a vanishing coefficient** under lowering the top mass:
if `g(m,n;k) = 0` and `G'` is the derivative of `g^ε(m,n;k)` at `0`, then
`G' ‖R_k‖² = 2 - T_m(n,k) - T_n(m,k) - T_k(m,n)`. -/
theorem gen_g_deriv {t₀ : Fin (N + 1)} (hx0 : x t₀ = 1) (m : ℕ) (hm : m ≤ N) (n k : Fin (N + 1))
    (hz : productMatrix v m n k = 0) {G' : ℝ}
    (hG : HasDerivAt (fun ε => productMatrix (epsRaw v x w (-ε)) m n k) G' 0) :
    G' * nrm v x w k = 2 - tailG v ⟨m, by omega⟩ n k - tailG v n ⟨m, by omega⟩ k - tailG v k ⟨m, by omega⟩ n := by
  set i : Fin (N + 1) := ⟨m, by omega⟩
  have h0 : ∑ t, w t * uval v x i t * uval v x n t * uval v x k t = 0 := by
    have := gen_triple v hv hact horth k m hm n
    rw [hz, zero_mul] at this
    rw [← this]; exact sum_congr rfl fun t _ => by ring
  have hF := gen_triple_deriv v hv hact horth hnrm hx0 i n k h0
  -- `N_k(ε) = Σ_t m_t ũ_k^2`
  have hU : ∀ (l : ℕ) t, HasDerivAt (fun ε : ℝ => ueps v x w (-ε) l t)
      (kerT v x w l t - Ssum v x w l * uval v x l t) 0 := by
    intro l t
    have hA := ((hasDerivAt_neg (0 : ℝ)).mul_const (Ssum v x w l)).const_add 1
    have h := (hA.mul_const (uval v x l t)).sub ((hasDerivAt_neg (0 : ℝ)).mul_const (kerT v x w l t))
    exact h.congr_deriv (by ring)
  have hW : ∀ t, HasDerivAt (fun ε : ℝ => w t - if t = t₀ then ε else 0) (-(if t = t₀ then 1 else 0)) 0 := by
    intro t
    by_cases h : t = t₀
    · simp only [h, if_true]
      exact ((hasDerivAt_const (0 : ℝ) (w t₀)).sub (hasDerivAt_id' (0 : ℝ))).congr_deriv (by ring)
    · simp only [h, if_false, sub_zero, neg_zero]
      exact hasDerivAt_const (0 : ℝ) (w t)
  have hNk := HasDerivAt.fun_sum (u := univ) fun t _ => (hW t).mul ((hU k t).pow 2)
  have hprod := hG.mul hNk
  -- `g^ε N_k = F` near `0`
  have hev : ∀ᶠ ε in nhds (0 : ℝ), ∀ l ∈ range (N + 2), Aeps v x w (-ε) l ≠ 0 := by
    refine (Filter.eventually_all_finset _).mpr fun l _ => ?_
    have hc : Continuous fun ε : ℝ => Aeps v x w (-ε) l := by
      simp only [Aeps]; fun_prop
    exact hc.continuousAt.eventually_ne (by simp [Aeps])
  have heq : (fun ε => ∑ t, (w t - if t = t₀ then ε else 0) * ueps v x w (-ε) i t * ueps v x w (-ε) n t *
      ueps v x w (-ε) k t) =ᶠ[nhds 0]
      fun ε => productMatrix (epsRaw v x w (-ε)) m n k * ∑ t, (w t - if t = t₀ then ε else 0) *
        ueps v x w (-ε) k t ^ 2 := by
    filter_upwards [hev] with ε hε
    have hA : ∀ l, l ≤ N + 1 → Aeps v x w (-ε) l ≠ 0 := fun l hl => hε l (mem_range.mpr (by omega))
    have h := gen_raw_g v hv hact horth hnrm hx0 hA m hm n k
    have e1 : ∀ t, (w t + if t = t₀ then -ε else 0) = (w t - if t = t₀ then ε else 0) := fun t => by
      split_ifs <;> ring
    simp only [e1] at h
    exact h.symm
  have hF' := hprod.congr_of_eventuallyEq heq
  have huniq := hF.unique hF'
  have hG0 : productMatrix (epsRaw v x w (-0)) m n k = 0 := by
    rw [epsRaw_zero_product v hv m (by omega)]; exact hz
  have hN0 : ∑ t, (w t - if t = t₀ then (0 : ℝ) else 0) * ueps v x w (-0) k t ^ 2 = nrm v x w k := by
    rw [nrm]; exact sum_congr rfl fun t _ => by simp [ueps, Aeps]
  simp only [hG0, zero_mul, add_zero, Pi.mul_apply, Pi.pow_apply] at huniq
  rw [hN0] at huniq
  exact huniq.symm

include hv hact horth hnrm in
/-- The lowered measure, for any data: the polynomials of `epsRaw v x w (-ε)` are orthogonal for
`w - ε δ_{t₀}` and equal `1` at `x_{t₀} = 1`. -/
theorem gen_lower_measure {t₀ : Fin (N + 1)} (hx0 : x t₀ = 1) {ε : ℝ}
    (hA : ∀ n, n ≤ N + 1 → Aeps v x w (-ε) n ≠ 0) :
    (∀ n, n ≤ N → (recurrencePolynomial (epsRaw v x w (-ε)) n).eval 1 = 1) ∧
      ∀ m n, m ≤ N → n ≤ N → m ≠ n →
        ∑ t, (w t - if t = t₀ then ε else 0) * (recurrencePolynomial (epsRaw v x w (-ε)) m).eval (x t) *
          (recurrencePolynomial (epsRaw v x w (-ε)) n).eval (x t) = 0 := by
  have hev := fun m hm t => ueps_eval_raw v hv hact horth hnrm hA m hm t
  refine ⟨fun n hn => ?_, fun m n hm hn hmn => ?_⟩
  · have h := hev n hn t₀
    rw [hx0] at h
    rw [h]; exact ueps_top (w := w) hv hx0 (-ε) n hn
  · have e : ∀ t, (w t - if t = t₀ then ε else 0) * (recurrencePolynomial (epsRaw v x w (-ε)) m).eval (x t) *
        (recurrencePolynomial (epsRaw v x w (-ε)) n).eval (x t) =
        (w t + if t = t₀ then -ε else 0) * ueps v x w (-ε) m t * ueps v x w (-ε) n t := by
      intro t; rw [hev m hm t, hev n hn t]; split_ifs <;> ring
    rw [sum_congr rfl fun t _ => e t]
    exact ueps_orth hv hx0 horth hnrm (-ε) m n hm hn hmn

end Szkraw
