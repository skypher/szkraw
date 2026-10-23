import Szkraw.GenFormR
import Szkraw.CubicLeib

/-!
# Theorem 8.17: the σ-part `Φ₃^loc` of the key inequality

With `u = f(ℓ)` log-concave, `s = C(a-1,2)`, `D = u₀ + u₁`, `T₃ = Σ (n-2)(C(a,3) - C(n,3)) y_n`,
`E₃ = Σ (n-2) C(a,n) C(n,3)(3u_{n-1} + 3u_{n-2} + u_{n-3})`:
`Φ̃₃ = u₁ [-C(a,3) u₀ Y' + Y (s X' - C(a-1,3) D) - D (4T₃ - E₃)] + s u₀ [X Y' + Y X' - 4 D H_*] ≥ 0`.
Proof: `Φ̃₃ ≥ u₁² Σ eA_n u_n + u₀u₁ Σ eB_n u_n` by the edge bounds (`LCNZ.edge_prod`) and `u₀ H_* ≤ u₁ H_*^{shift}`,
with `eA_n, eB_n ≥ 0` (generic certificates by `runs/lean_plan/gen_phi3_arith.py`).
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Szkraw

open Finset

theorem choose4_real : ∀ n : ℕ, (n.choose 4 : ℝ) = (n : ℝ) * ((n : ℝ) - 1) * ((n : ℝ) - 2) * ((n : ℝ) - 3) / 24
  | 0 => by simp
  | n + 1 => by
    have h : (n + 1).choose 4 = n.choose 3 + n.choose 4 := Nat.choose_succ_succ' n 3
    rw [h]; push_cast; rw [choose4_real n, choose3_real n]; ring

theorem choose5_real : ∀ n : ℕ,
    (n.choose 5 : ℝ) = (n : ℝ) * ((n : ℝ) - 1) * ((n : ℝ) - 2) * ((n : ℝ) - 3) * ((n : ℝ) - 4) / 120
  | 0 => by simp
  | n + 1 => by
    have h : (n + 1).choose 5 = n.choose 4 + n.choose 5 := Nat.choose_succ_succ' n 4
    rw [h]; push_cast; rw [choose5_real n, choose4_real n]; ring

theorem choose6_real : ∀ n : ℕ,
    (n.choose 6 : ℝ) = (n : ℝ) * ((n : ℝ) - 1) * ((n : ℝ) - 2) * ((n : ℝ) - 3) * ((n : ℝ) - 4) * ((n : ℝ) - 5) / 720
  | 0 => by simp
  | n + 1 => by
    have h : (n + 1).choose 6 = n.choose 5 + n.choose 6 := Nat.choose_succ_succ' n 5
    rw [h]; push_cast; rw [choose6_real n, choose5_real n]; ring

/-- `C(A,k+1)(k+1) = C(A,k)(A-k)` for every `k`. -/
theorem choose_succ_real' (A k : ℕ) : ((A.choose (k + 1) : ℕ) : ℝ) * ((k : ℝ) + 1) = (A.choose k : ℝ) * ((A : ℝ) - k) := by
  rcases Nat.lt_or_ge A k with h | h
  · rw [Nat.choose_eq_zero_of_lt h, Nat.choose_eq_zero_of_lt (by omega)]; simp
  · exact choose_succ_real A k h

theorem rel_cp2 (p K : ℕ) :
    (((p + 4 + K).choose (p + 4 + 2) : ℕ) : ℝ) * ((p : ℝ) + 6) =
      ((p + 4 + K).choose (p + 4 + 1) : ℝ) * ((K : ℝ) - 1) := by
  have := choose_succ_real' (p + 4 + K) (p + 4 + 1)
  rw [show p + 4 + 1 + 1 = p + 4 + 2 from rfl] at this
  push_cast at this ⊢; linarith

theorem rel_cp3 (p K : ℕ) :
    (((p + 4 + K).choose (p + 4 + 3) : ℕ) : ℝ) * ((p : ℝ) + 7) =
      ((p + 4 + K).choose (p + 4 + 2) : ℝ) * ((K : ℝ) - 2) := by
  have := choose_succ_real' (p + 4 + K) (p + 4 + 2)
  rw [show p + 4 + 2 + 1 = p + 4 + 3 from rfl] at this
  push_cast at this ⊢; linarith

/-- `T₃` coefficients: `(n-2) C(a,n) (C(a,3) - C(n,3))`. -/
noncomputable def cfT3 (a n : ℕ) : ℝ := cfH a n * ((a.choose 3 : ℝ) - (n.choose 3 : ℝ))
/-- `w_k = (k-2) C(a,k) C(k,3)`. -/
noncomputable def cfW3 (a k : ℕ) : ℝ := cfH a k * (k.choose 3 : ℝ)
/-- `E₃` coefficients for `n ≥ 1`: `3 w_{n+1} + 3 w_{n+2} + w_{n+3}` (the `u₀` coefficient `C(a,3)` is separate). -/
noncomputable def cfE3 (a n : ℕ) : ℝ :=
  if 1 ≤ n then 3 * cfW3 a (n + 1) + 3 * cfW3 a (n + 2) + cfW3 a (n + 3) else 0

/-- `C(a-1,2)`, `C(a,3)`, `C(a-1,3)` as real polynomials. -/
noncomputable def sC (a : ℕ) : ℝ := ((a : ℝ) - 1) * ((a : ℝ) - 2) / 2
noncomputable def c3 (a : ℕ) : ℝ := (a : ℝ) * ((a : ℝ) - 1) * ((a : ℝ) - 2) / 6
noncomputable def c3' (a : ℕ) : ℝ := ((a : ℝ) - 1) * ((a : ℝ) - 2) * ((a : ℝ) - 3) / 6

noncomputable def eA (a n : ℕ) : ℝ :=
  sC a * edgeCoef (cfY a) (cfXp a) n - c3' a * cfY a n - 4 * cfT3 a n + cfE3 a n

noncomputable def eB (a n : ℕ) : ℝ :=
  sC a * (edgeCoef (cfX a) (cfYp a) n + edgeCoef (cfY a) (cfXp a) n) - 4 * sC a * (cfH a n + cfH a (n + 1)) -
    c3 a * cfYp a n - c3' a * cfY a n - 4 * cfT3 a n + cfE3 a n + (if n = 1 then c3 a else 0)

section Values

variable {a : ℕ}

theorem cfT3_le2 {n : ℕ} (hn : n ≤ 2) : cfT3 a n = 0 := by unfold cfT3; rw [cfH_le2 hn, zero_mul]
theorem cfW3_le2 {k : ℕ} (hk : k ≤ 2) : cfW3 a k = 0 := by unfold cfW3; rw [cfH_le2 hk, zero_mul]
theorem cfE3_zero : cfE3 a 0 = 0 := by simp [cfE3]
theorem cfE3_pos {n : ℕ} (hn : 1 ≤ n) : cfE3 a n = 3 * cfW3 a (n + 1) + 3 * cfW3 a (n + 2) + cfW3 a (n + 3) := by
  unfold cfE3; rw [if_pos hn]
theorem cfW3_ge3 {k : ℕ} (hk : 3 ≤ k) : cfW3 a k = ((k : ℝ) - 2) * (a.choose k : ℝ) * (k.choose 3 : ℝ) := by
  unfold cfW3; rw [cfH_ge3 hk]

theorem cfT3_three : cfT3 a 3 = c3 a * (c3 a - 1) := by
  unfold cfT3 c3; rw [cfH_ge3 le_rfl, choose3_real a]; norm_num <;> ring
theorem cfE3_one : cfE3 a 1 = 3 * c3 a + 8 * ((a.choose 4 : ℕ) : ℝ) := by
  rw [cfE3_pos le_rfl, cfW3_le2 (by norm_num), cfW3_ge3 (by norm_num), cfW3_ge3 (by norm_num)]
  unfold c3; rw [choose3_real a]; norm_num [Nat.choose] <;> ring
theorem cfE3_two : cfE3 a 2 = 3 * c3 a + 24 * ((a.choose 4 : ℕ) : ℝ) + 30 * ((a.choose 5 : ℕ) : ℝ) := by
  rw [cfE3_pos (by norm_num), cfW3_ge3 (by norm_num), cfW3_ge3 (by norm_num), cfW3_ge3 (by norm_num)]
  unfold c3; rw [choose3_real a]; norm_num [Nat.choose] <;> ring
theorem cfE3_three :
    cfE3 a 3 = 24 * ((a.choose 4 : ℕ) : ℝ) + 90 * ((a.choose 5 : ℕ) : ℝ) + 80 * ((a.choose 6 : ℕ) : ℝ) := by
  rw [cfE3_pos (by norm_num), cfW3_ge3 (by norm_num), cfW3_ge3 (by norm_num), cfW3_ge3 (by norm_num)]
  norm_num [Nat.choose] <;> ring

theorem cfE3_nonneg (n : ℕ) : 0 ≤ cfE3 a n := by
  unfold cfE3 cfW3; split_ifs
  · have h1 := cfH_nonneg (a := a) (n + 1); have h2 := cfH_nonneg (a := a) (n + 2)
    have h3 := cfH_nonneg (a := a) (n + 3)
    have := mul_nonneg h1 (Nat.cast_nonneg ((n + 1).choose 3))
    have := mul_nonneg h2 (Nat.cast_nonneg ((n + 2).choose 3))
    have := mul_nonneg h3 (Nat.cast_nonneg ((n + 3).choose 3))
    linarith
  · exact le_rfl

theorem cfT3_vanish {n : ℕ} (ha : 3 ≤ a) (hn : a + 1 ≤ n) : cfT3 a n = 0 := by
  unfold cfT3; rw [(cf_vanish ha hn).2.2.2.2, zero_mul]
theorem cfE3_vanish {n : ℕ} (ha : 3 ≤ a) (hn : a + 1 ≤ n) : cfE3 a n = 0 := by
  unfold cfE3 cfW3
  rw [(cf_vanish (a := a) ha (n := n + 1) (by omega)).2.2.2.2, (cf_vanish (a := a) ha (n := n + 2) (by omega)).2.2.2.2,
    (cf_vanish (a := a) ha (n := n + 3) (by omega)).2.2.2.2]
  simp

end Values

theorem eA_arith (p K c cm cp cp2 cp3 d e : ℝ) (hp : 0 ≤ p) (hK : 0 ≤ K) (hc : 0 ≤ c)
    (h1 : cm * (K + 1) = c * (p + 4)) (h2 : cp * (p + 5) = c * K) (h3 : d * (p + 4 + K) = c * (p + 4))
    (h4 : e * (p + 4 + K) = c * K) (h5 : cp2 * (p + 6) = cp * (K - 1)) (h6 : cp3 * (p + 7) = cp2 * (K - 2)) :
    0 ≤ ((p + 4 + K) - 1) * ((p + 4 + K) - 2) / 2 * (0 * e + (p + 4 + K) * ((p + 4 + K) - 1) / 2 * d + ((p + 4 + K) - 2) * c + ((p + 4 + K) - 1) * ((p + 4 + K) - 2) / 2 * cm) - ((p + 4 + K) - 1) * ((p + 4 + K) - 2) * ((p + 4 + K) - 3) / 6 * c - 4 * (((p + 4) - 2) * c * ((p + 4 + K) * ((p + 4 + K) - 1) * ((p + 4 + K) - 2) / 6 - ((p + 4)) * (((p + 4)) - 1) * (((p + 4)) - 2) / 6)) + (3 * (((p + 4) + 1 - 2) * cp * ((p + 4) + 1) * (((p + 4) + 1) - 1) * (((p + 4) + 1) - 2) / 6) + 3 * (((p + 4) + 2 - 2) * cp2 * ((p + 4) + 2) * (((p + 4) + 2) - 1) * (((p + 4) + 2) - 2) / 6) + (((p + 4) + 3 - 2) * cp3 * ((p + 4) + 3) * (((p + 4) + 3) - 1) * (((p + 4) + 3) - 2) / 6)) := by
  have hK1 : 0 < K + 1 := by linarith
  have hp5 : 0 < p + 5 := by linarith
  have hp6 : 0 < p + 6 := by linarith
  have hp7 : 0 < p + 7 := by linarith
  have ha : 0 < p + 4 + K := by linarith
  have ecm : cm = c * (p + 4) / (K + 1) := by field_simp; linarith
  have ecp : cp = c * K / (p + 5) := by field_simp; linarith
  have ecp2 : cp2 = c * K * (K - 1) / ((p + 5) * (p + 6)) := by rw [ecp] at h5; field_simp at h5 ⊢; linarith
  have ecp3 : cp3 = c * K * (K - 1) * (K - 2) / ((p + 5) * (p + 6) * (p + 7)) := by
    rw [ecp2] at h6; field_simp at h6 ⊢; linarith
  have ed : d = c * (p + 4) / (p + 4 + K) := by field_simp; linarith
  have ee : e = c * K / (p + 4 + K) := by field_simp; linarith
  rw [ecm, ecp3, ecp2, ecp, ed, ee]
  have hN : 0 ≤ c * (3 * p ^ 5 + 15 * p ^ 4 * K ^ 1 + 45 * p ^ 4 + 9 * p ^ 3 * K ^ 2 + 169 * p ^ 3 * K ^ 1 + 271 * p ^ 3 + 3 * p ^ 2 * K ^ 3 + 111 * p ^ 2 * K ^ 2 + 729 * p ^ 2 * K ^ 1 + 813 * p ^ 2 + 69 * p ^ 1 * K ^ 3 + 438 * p ^ 1 * K ^ 2 + 1421 * p ^ 1 * K ^ 1 + 1208 * p ^ 1 + 22 * K ^ 4 + 178 * K ^ 3 + 542 * K ^ 2 + 1046 * K ^ 1 + 708) / (12*(K + 1)) := by positivity
  exact le_of_le_of_eq hN (by field_simp; ring)

theorem eB_arith (p K c cm cp cp2 cp3 d e : ℝ) (hp : 0 ≤ p) (hK : 0 ≤ K) (hc : 0 ≤ c)
    (h1 : cm * (K + 1) = c * (p + 4)) (h2 : cp * (p + 5) = c * K) (h3 : d * (p + 4 + K) = c * (p + 4))
    (h4 : e * (p + 4 + K) = c * K) (h5 : cp2 * (p + 6) = cp * (K - 1)) (h6 : cp3 * (p + 7) = cp2 * (K - 2)) :
    0 ≤ ((p + 4 + K) - 1) * ((p + 4 + K) - 2) / 2 * (((p + 4 + K) * c + (p + 4 + K) * ((p + 4 + K) - 1) / 2 * cm + 0 * c + ((p + 4 + K) * ((p + 4 + K) - 1) / 2 - ((p + 4 + K) - 1)) * cm) + (0 * e + (p + 4 + K) * ((p + 4 + K) - 1) / 2 * d + ((p + 4 + K) - 2) * c + ((p + 4 + K) - 1) * ((p + 4 + K) - 2) / 2 * cm)) - 4 * ((p + 4 + K) - 1) * ((p + 4 + K) - 2) / 2 * ((((p + 4) - 2) * c) + (((p + 4) + 1 - 2) * cp)) - (p + 4 + K) * ((p + 4 + K) - 1) * ((p + 4 + K) - 2) / 6 * c - ((p + 4 + K) - 1) * ((p + 4 + K) - 2) * ((p + 4 + K) - 3) / 6 * c - 4 * (((p + 4) - 2) * c * ((p + 4 + K) * ((p + 4 + K) - 1) * ((p + 4 + K) - 2) / 6 - ((p + 4)) * (((p + 4)) - 1) * (((p + 4)) - 2) / 6)) + (3 * (((p + 4) + 1 - 2) * cp * ((p + 4) + 1) * (((p + 4) + 1) - 1) * (((p + 4) + 1) - 2) / 6) + 3 * (((p + 4) + 2 - 2) * cp2 * ((p + 4) + 2) * (((p + 4) + 2) - 1) * (((p + 4) + 2) - 2) / 6) + (((p + 4) + 3 - 2) * cp3 * ((p + 4) + 3) * (((p + 4) + 3) - 1) * (((p + 4) + 3) - 2) / 6)) := by
  have hK1 : 0 < K + 1 := by linarith
  have hp5 : 0 < p + 5 := by linarith
  have hp6 : 0 < p + 6 := by linarith
  have hp7 : 0 < p + 7 := by linarith
  have ha : 0 < p + 4 + K := by linarith
  have ecm : cm = c * (p + 4) / (K + 1) := by field_simp; linarith
  have ecp : cp = c * K / (p + 5) := by field_simp; linarith
  have ecp2 : cp2 = c * K * (K - 1) / ((p + 5) * (p + 6)) := by rw [ecp] at h5; field_simp at h5 ⊢; linarith
  have ecp3 : cp3 = c * K * (K - 1) * (K - 2) / ((p + 5) * (p + 6) * (p + 7)) := by
    rw [ecp2] at h6; field_simp at h6 ⊢; linarith
  have ed : d = c * (p + 4) / (p + 4 + K) := by field_simp; linarith
  have ee : e = c * K / (p + 4 + K) := by field_simp; linarith
  rw [ecm, ecp3, ecp2, ecp, ed, ee]
  have hN : 0 ≤ c * (9 * p ^ 6 + 39 * p ^ 5 * K ^ 1 + 180 * p ^ 5 + 45 * p ^ 4 * K ^ 2 + 638 * p ^ 4 * K ^ 1 + 1460 * p ^ 4 + 27 * p ^ 3 * K ^ 3 + 618 * p ^ 3 * K ^ 2 + 4084 * p ^ 3 * K ^ 1 + 6172 * p ^ 3 + 6 * p ^ 2 * K ^ 4 + 306 * p ^ 2 * K ^ 3 + 3189 * p ^ 2 * K ^ 2 + 12916 * p ^ 2 * K ^ 1 + 14431 * p ^ 2 + 56 * p ^ 1 * K ^ 4 + 1241 * p ^ 1 * K ^ 3 + 7426 * p ^ 1 * K ^ 2 + 20373 * p ^ 1 * K ^ 1 + 17792 * p ^ 1 + 178 * K ^ 4 + 1738 * K ^ 3 + 6578 * K ^ 2 + 12878 * K ^ 1 + 9060) / (12*(K + 1)*(p + 5)) := by positivity
  exact le_of_le_of_eq hN (by field_simp; ring)

set_option hygiene false in
/-- The extra small-index values for `eA`, `eB` (needs `3 ≤ a` in scope); run after `small_vals`. -/
macro "phi3_vals" : tactic =>
  `(tactic| (simp only [cfX_pos (a := a) (n := 1) (by norm_num), cfX_pos (a := a) (n := 2) (by norm_num),
    cfX_pos (a := a) (n := 3) (by norm_num), Nat.choose_one_right, cast_choose_two, cast_choose_three a (by omega),
    cfT3_le2 (a := a) (n := 0) (by norm_num), cfT3_le2 (a := a) (n := 1) (by norm_num),
    cfT3_le2 (a := a) (n := 2) (by norm_num), cfT3_three, cfE3_zero, cfE3_one, cfE3_two, cfE3_three,
    choose4_real, choose5_real, choose6_real, sC, c3, c3', if_true, if_false]; push_cast))

theorem eA_nonneg {a : ℕ} (ha : 3 ≤ a) (n : ℕ) : 0 ≤ eA a n := by
  have hA : (3 : ℝ) ≤ a := by exact_mod_cast ha
  rcases (show n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ (4 ≤ n ∧ n ≤ a) ∨ a + 1 ≤ n by omega) with
    rfl | rfl | rfl | rfl | ⟨_h4, hna⟩ | hbig
  · unfold eA; small_vals; phi3_vals; try norm_num
  · unfold eA; small_vals; phi3_vals; poly_nonneg (a : ℝ) ≥ 3
  · unfold eA; small_vals; phi3_vals; poly_nonneg (a : ℝ) ≥ 3
  · unfold eA; small_vals; phi3_vals; poly_nonneg (a : ℝ) ≥ 3
  · obtain ⟨p, rfl⟩ : ∃ p, n = p + 4 := ⟨n - 4, by omega⟩
    obtain ⟨K, rfl⟩ : ∃ K, a = p + 4 + K := ⟨a - (p + 4), by omega⟩
    unfold eA cfT3
    rw [edgeCoef_ge4 _ _ (by omega : 4 ≤ p + 4), cfE3_pos (by omega)]
    simp only [show p + 4 - 1 = p + 3 by omega]
    rw [cfY_one, cfY_two', cfY_ge2 (a := p + 4 + K) (n := p + 4) (by omega),
      cfY_ge2 (a := p + 4 + K) (n := p + 3) (by omega), cfXp_one (by omega), cfXp_two' (by omega),
      cfXp_ge2 (a := p + 4 + K) (n := p + 4) (by omega), cfXp_ge2 (a := p + 4 + K) (n := p + 3) (by omega),
      cfH_ge3 (a := p + 4 + K) (n := p + 4) (by omega), cfW3_ge3 (a := p + 4 + K) (k := p + 4 + 1) (by omega),
      cfW3_ge3 (a := p + 4 + K) (k := p + 4 + 2) (by omega), cfW3_ge3 (a := p + 4 + K) (k := p + 4 + 3) (by omega)]
    simp only [choose3_real, sC, c3, c3']
    have := eA_arith (p : ℝ) (K : ℝ) _ _ _ _ _ _ _ (by positivity) (by positivity) (by positivity)
      (rel_cm p K) (rel_cp p K) (rel_d p K) (rel_e p K) (rel_cp2 p K) (rel_cp3 p K)
    push_cast at this ⊢; linarith
  · unfold eA
    rw [(cf_vanish ha hbig).2.2.1, cfT3_vanish ha hbig, cfE3_vanish ha hbig]
    have hs : 0 ≤ sC a := by unfold sC; nlinarith
    have := mul_nonneg hs (edgeCoef_nonneg (cfY_nonneg (a := a)) (cfXp_nonneg (a := a) (by omega)) n)
    linarith

theorem eB_nonneg {a : ℕ} (ha : 3 ≤ a) (n : ℕ) : 0 ≤ eB a n := by
  have hA : (3 : ℝ) ≤ a := by exact_mod_cast ha
  rcases (show n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ (4 ≤ n ∧ n ≤ a) ∨ a + 1 ≤ n by omega) with
    rfl | rfl | rfl | rfl | ⟨_h4, hna⟩ | hbig
  · unfold eB; small_vals; phi3_vals; try norm_num
  · unfold eB; small_vals; phi3_vals; poly_nonneg (a : ℝ) ≥ 3
  · unfold eB; small_vals; phi3_vals; poly_nonneg (a : ℝ) ≥ 3
  · unfold eB; small_vals; phi3_vals; poly_nonneg (a : ℝ) ≥ 3
  · obtain ⟨p, rfl⟩ : ∃ p, n = p + 4 := ⟨n - 4, by omega⟩
    obtain ⟨K, rfl⟩ : ∃ K, a = p + 4 + K := ⟨a - (p + 4), by omega⟩
    unfold eB cfT3
    rw [edgeCoef_ge4 _ _ (by omega : 4 ≤ p + 4), edgeCoef_ge4 _ _ (by omega : 4 ≤ p + 4), cfE3_pos (by omega),
      if_neg (by omega)]
    simp only [show p + 4 - 1 = p + 3 by omega]
    rw [cfX_pos (a := p + 4 + K) (n := 1) le_rfl, cfX_pos (a := p + 4 + K) (n := 2) (by norm_num),
      cfX_pos (a := p + 4 + K) (n := p + 4) (by omega), cfX_pos (a := p + 4 + K) (n := p + 3) (by omega),
      cfYp_one, cfYp_two', cfYp_ge3 (a := p + 4 + K) (n := p + 4) (by omega),
      cfYp_ge3 (a := p + 4 + K) (n := p + 3) (by omega), cfY_one, cfY_two',
      cfY_ge2 (a := p + 4 + K) (n := p + 4) (by omega), cfY_ge2 (a := p + 4 + K) (n := p + 3) (by omega),
      cfXp_one (by omega), cfXp_two' (by omega), cfXp_ge2 (a := p + 4 + K) (n := p + 4) (by omega),
      cfXp_ge2 (a := p + 4 + K) (n := p + 3) (by omega),
      cfH_ge3 (a := p + 4 + K) (n := p + 4) (by omega), cfH_ge3 (a := p + 4 + K) (n := p + 4 + 1) (by omega),
      cfW3_ge3 (a := p + 4 + K) (k := p + 4 + 1) (by omega), cfW3_ge3 (a := p + 4 + K) (k := p + 4 + 2) (by omega),
      cfW3_ge3 (a := p + 4 + K) (k := p + 4 + 3) (by omega)]
    simp only [choose3_real, sC, c3, c3', Nat.choose_one_right, cast_choose_two]
    have := eB_arith (p : ℝ) (K : ℝ) _ _ _ _ _ _ _ (by positivity) (by positivity) (by positivity)
      (rel_cm p K) (rel_cp p K) (rel_d p K) (rel_e p K) (rel_cp2 p K) (rel_cp3 p K)
    push_cast at this ⊢; linarith
  · unfold eB
    have hv := cf_vanish ha hbig
    have hv1 := cf_vanish (a := a) ha (n := n + 1) (by omega)
    rw [hv.2.2.1, hv.2.2.2.1, hv.2.2.2.2, hv1.2.2.2.2, cfT3_vanish ha hbig, cfE3_vanish ha hbig, if_neg (by omega)]
    have hs : 0 ≤ sC a := by unfold sC; nlinarith
    have := mul_nonneg hs (add_nonneg (edgeCoef_nonneg (cfX_nonneg (a := a)) (cfYp_nonneg (a := a) (by omega)) n)
      (edgeCoef_nonneg (cfY_nonneg (a := a)) (cfXp_nonneg (a := a) (by omega)) n))
    linarith

/-- **`Φ₃^loc ≥ 0`** (times `u₁`), for `u = f` log-concave without internal zeros. -/
theorem Phi3_nonneg (f : ℕ → ℝ) (hf : LCNZ f) {a : ℕ} (ha : 3 ≤ a) :
    0 ≤ f 1 * (-(c3 a) * f 0 * lf (a + 1) (cfYp a) f +
        lf (a + 1) (cfY a) f * (sC a * lf (a + 1) (cfXp a) f - c3' a * (f 0 + f 1)) -
        (f 0 + f 1) * (4 * lf (a + 1) (cfT3 a) f - (c3 a * f 0 + lf (a + 1) (cfE3 a) f))) +
      sC a * f 0 * (lf (a + 1) (cfX a) f * lf (a + 1) (cfYp a) f + lf (a + 1) (cfY a) f * lf (a + 1) (cfXp a) f -
        4 * (f 0 + f 1) * lf (a + 1) (cfH a) f) := by
  have hv := fun n (hn : a + 1 ≤ n) => cf_vanish (a := a) ha hn
  have hA3 : (3 : ℝ) ≤ a := by exact_mod_cast ha
  have hs : 0 ≤ sC a := by unfold sC; nlinarith
  have hc3 : 0 ≤ c3 a := by unfold c3; have : (0 : ℝ) ≤ (a : ℝ) * ((a : ℝ) - 1) := by nlinarith
                            nlinarith
  have hf0 := hf.1 0
  have hf1 := hf.1 1
  have E1 := hf.edge_prod (R := a + 1) (by omega) (x := cfY a) (y := cfXp a) cfY_nonneg (cfXp_nonneg (by omega))
    cfY_zero cfXp_zero (fun n hn => (hv n hn).2.2.1) (fun n hn => (hv n hn).2.1)
  have E2 := hf.edge_prod (R := a + 1) (by omega) (x := cfX a) (y := cfYp a) cfX_nonneg (cfYp_nonneg (by omega))
    cfX_zero cfYp_zero (fun n hn => (hv n hn).1) (fun n hn => (hv n hn).2.2.2.1)
  have N0 := u0H_le f hf ha
  have eY : lf (a + 1) (cfY a) f = lf (a + 2) (cfY a) f := lf_extend (by omega) (fun n hn => (hv n hn).2.2.1)
  have eYp : lf (a + 1) (cfYp a) f = lf (a + 2) (cfYp a) f := lf_extend (by omega) (fun n hn => (hv n hn).2.2.2.1)
  have eH : lf (a + 1) (cfH a) f = lf (a + 2) (cfH a) f := lf_extend (by omega) (fun n hn => (hv n hn).2.2.2.2)
  have eT : lf (a + 1) (cfT3 a) f = lf (a + 2) (cfT3 a) f := lf_extend (by omega) (fun n hn => cfT3_vanish ha hn)
  have eE : lf (a + 1) (cfE3 a) f = lf (a + 2) (cfE3 a) f := lf_extend (by omega) (fun n hn => cfE3_vanish ha hn)
  have hind : lf (a + 2) (fun n => if n = 1 then c3 a else 0) f = c3 a * f 1 := by
    unfold lf; simp only [ite_mul, zero_mul]; rw [sum_ite_eq', if_pos (mem_range.2 (by omega))]
  have hA : lf (a + 2) (eA a) f = sC a * lf (a + 2) (edgeCoef (cfY a) (cfXp a)) f - c3' a * lf (a + 2) (cfY a) f -
      4 * lf (a + 2) (cfT3 a) f + lf (a + 2) (cfE3 a) f := by
    unfold lf eA; simp only [mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
    exact sum_congr rfl fun n _ => by ring
  have hB : lf (a + 2) (eB a) f = sC a * (lf (a + 2) (edgeCoef (cfX a) (cfYp a)) f +
      lf (a + 2) (edgeCoef (cfY a) (cfXp a)) f) - 4 * sC a * (lf (a + 2) (cfH a) f +
      lf (a + 2) (fun n => cfH a (n + 1)) f) - c3 a * lf (a + 2) (cfYp a) f - c3' a * lf (a + 2) (cfY a) f -
      4 * lf (a + 2) (cfT3 a) f + lf (a + 2) (cfE3 a) f + lf (a + 2) (fun n => if n = 1 then c3 a else 0) f := by
    unfold lf eB; simp only [mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
    exact sum_congr rfl fun n _ => by ring
  rw [hind] at hB
  rw [eY, eYp, eH, eT, eE]
  rw [eY] at E1; rw [eYp] at E2; rw [eH] at N0
  have pA := lf_nonneg hf (fun n _ => eA_nonneg ha n) (R := a + 2)
  have pB := lf_nonneg hf (fun n _ => eB_nonneg ha n) (R := a + 2)
  have k1 := mul_nonneg (mul_nonneg hs hf1) (sub_nonneg.2 E1)
  have k2 := mul_nonneg (mul_nonneg hs hf0) (sub_nonneg.2 E2)
  have k3 := mul_nonneg (mul_nonneg hs hf0) (sub_nonneg.2 E1)
  have k4 := mul_nonneg (mul_nonneg hs hf0) (sub_nonneg.2 N0)
  have k5 := mul_nonneg (mul_nonneg hc3 (mul_nonneg hf0 hf0)) hf1
  have k6 := mul_nonneg (mul_nonneg hf1 hf1) pA
  have k7 := mul_nonneg (mul_nonneg hf0 hf1) pB
  rw [hA] at k6; rw [hB] at k7
  nlinarith [k1, k2, k3, k4, k5, k6, k7]

end Szkraw
