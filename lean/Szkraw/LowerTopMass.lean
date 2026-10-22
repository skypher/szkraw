import Szkraw.TopMass
import Szkraw.SymmetricMeasure
import Szkraw.FiniteRealization
import Mathlib.Analysis.Calculus.Deriv.Inv

/-!
# Lemma 9.7: lowering the top mass

For every admissible array the point `x = 1`, where all `R_n` equal `1`, is a node of the spectral
measure (`spectral_top_node`). Lowering its mass by `ε` gives the system `ueps v x w (-ε)` of
`TopMass.lean`, with recurrence coefficients `epsRaw v x w (-ε)` in the fixed coordinate `x`.
Lemma 9.7 computes their first-order changes and the first-order change of
`∫ R_x R_y R_z dμ_ε`.
-/

namespace Szkraw

open Finset Polynomial

variable {N : ℕ}

/-- The point `1` is a node of the spectral measure of every admissible array. -/
theorem spectral_top_node (v : Coefficients N) (hv : Admissible v) : ∃ t₀, spectralNode v hv t₀ = 1 := by
  have ha : ∀ i, i < N → v.a i ≠ 0 := fun i hi => (hv.2.2.2.2.2.2.1 i hi).ne'
  have hN := hv.1
  have hco := poly_coeff v ha
  have hQ : (polynomialPair v N).1 = recurrencePolynomial v (N - 1) := by
    exact congrArg (fun k => (polynomialPair v k).1) (show N = N - 1 + 1 by omega)
  set T : ℝ[X] := (X - C (v.b N)) * recurrencePolynomial v N - C (v.c N) * (polynomialPair v N).1 with hT
  have hTeval : ∀ y, T.eval y = (y - v.b N) * (recurrencePolynomial v N).eval y -
      v.c N * (recurrencePolynomial v (N - 1)).eval y := by
    intro y; rw [hT, ← hQ]; simp [eval_mul, eval_sub]
  obtain ⟨hP0', hPN0', hQc⟩ := hco N le_rfl
  have hP0 : ∀ j, N < j → (recurrencePolynomial v N).coeff j = 0 := hP0'
  have hPN0 : (recurrencePolynomial v N).coeff N ≠ 0 := hPN0'
  have hTc : ∀ j, T.coeff (j + 1) = (recurrencePolynomial v N).coeff j -
      v.b N * (recurrencePolynomial v N).coeff (j + 1) - v.c N * (polynomialPair v N).1.coeff (j + 1) := by
    intro j; rw [hT, coeff_sub, sub_mul, coeff_sub, coeff_X_mul, coeff_C_mul, coeff_C_mul]
  have hT0 : T ≠ 0 := by
    intro h
    have := hTc N
    rw [h, coeff_zero, hP0 (N + 1) (by omega), hQc (N + 1) (by omega)] at this
    apply hPN0; linarith
  have hroot : ∀ t, T.eval (spectralNode v hv t) = 0 := fun t => by rw [hTeval]; exact spectral_terminal v hv t
  have hroot1 : T.eval 1 = 0 := by
    rw [hTeval, recurrence_normalized v hv N le_rfl, recurrence_normalized v hv (N - 1) (by omega)]
    have := hv.2.2.2.2.2.1 N le_rfl
    rw [hv.2.2.2.2.1] at this
    linarith
  by_contra hne
  push Not at hne
  have hnot : (1 : ℝ) ∉ univ.image (spectralNode v hv) := by
    simp only [Finset.mem_image, Finset.mem_univ, true_and, not_exists]; exact hne
  have hsub : insert (1 : ℝ) (univ.image (spectralNode v hv)) ⊆ T.roots.toFinset := by
    intro y hy
    rw [Multiset.mem_toFinset, mem_roots hT0]
    rcases Finset.mem_insert.mp hy with h | h
    · rw [h]; exact hroot1
    · obtain ⟨s, _, rfl⟩ := Finset.mem_image.mp h; exact hroot s
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem hnot, Finset.card_image_of_injective _ (spectral_nodes_injective v hv),
    Finset.card_univ, Fintype.card_fin] at hcard
  have hTdeg : T.natDegree ≤ N + 1 := by
    rw [natDegree_le_iff_coeff_eq_zero]
    intro j hj
    obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    rw [hTc, hP0 j' (by omega), hP0 (j' + 1) (by omega), hQc (j' + 1) (by omega)]; ring
  have := (Multiset.toFinset_card_le T.roots).trans (card_roots' T)
  omega

section lower

variable (v : Coefficients N) (hv : Admissible v)

/-- The spectral data of an admissible array satisfy the hypotheses of `TopMass.lean`. -/
theorem spec_act (t i : Fin (N + 1)) :
    spectralNode v hv t * uval v (spectralNode v hv) i t =
      ∑ k, recurrenceMatrix v i k * uval v (spectralNode v hv) k t :=
  spectral_node_action v hv t i

theorem spec_orth (m n : ℕ) (hm : m ≤ N) (hn : n ≤ N) (hmn : m ≠ n) :
    ∑ t, spectralWeight v hv t * uval v (spectralNode v hv) m t * uval v (spectralNode v hv) n t = 0 :=
  spectral_orthogonal v hv ⟨m, by omega⟩ ⟨n, by omega⟩ (fun h => hmn (congrArg Fin.val h))

theorem spec_nrm (n : ℕ) (hn : n ≤ N) : 0 < nrm v (spectralNode v hv) (spectralWeight v hv) n :=
  spectral_norm_pos v hv ⟨n, by omega⟩

include hv in
/-- The raw changed polynomials are the polynomials of `epsRaw`: `R^ε_m(x_t) = ũ_m(t)`. -/
theorem ueps_eval_raw {x w : Fin (N + 1) → ℝ}
    (hact : ∀ t (i : Fin (N + 1)), x t * uval v x i t = ∑ k, recurrenceMatrix v i k * uval v x k t)
    (horth : ∀ m n, m ≤ N → n ≤ N → m ≠ n → ∑ t, w t * uval v x m t * uval v x n t = 0)
    (hnrm : ∀ n, n ≤ N → 0 < nrm v x w n) {ε : ℝ} (hA : ∀ n, n ≤ N + 1 → Aeps v x w ε n ≠ 0)
    (m : ℕ) (hm : m ≤ N) (t : Fin (N + 1)) :
    (recurrencePolynomial (epsRaw v x w ε) m).eval (x t) = ueps v x w ε m t := by
  have hJ := ueps_rel hv hact horth hnrm hA t
  have hrep := representation_product (epsRaw v x w ε) (fun k => ueps v x w ε k t) (x t)
    (fun i => by simpa only [smul_eq_mul] using hJ i) m 0
  have ha : ∀ k, k < N → (epsRaw v x w ε).a k ≠ 0 := by
    intro k hk
    simp only [epsRaw]
    exact div_ne_zero (mul_ne_zero (hv.2.2.2.2.2.2.1 k hk).ne' (hA k (by omega))) (hA (k + 1) (by omega))
  have h0 : ueps v x w ε 0 t = 1 := by simp [ueps, Aeps, Ssum, kerT, uval_zero]
  simp only [smul_eq_mul, Fin.val_zero] at hrep
  rw [h0, mul_one] at hrep
  rw [← Polynomial.coe_aeval_eq_eval, hrep, sum_eq_single ⟨m, by omega⟩]
  · rw [row_zero _ ha m hm]; simp
  · intro k _ hk; rw [row_zero _ ha m hm, if_neg (fun h => hk (Fin.ext h)), zero_mul]
  · intro h; exact absurd (mem_univ _) h

/-- The product identity at the spectral nodes. -/
theorem spec_product (m : ℕ) (hm : m ≤ N) (n t : Fin (N + 1)) :
    uval v (spectralNode v hv) m t * uval v (spectralNode v hv) n t =
      ∑ k, productMatrix v m n k * uval v (spectralNode v hv) k t := by
  have hrep := representation_product v (fun j => uval v (spectralNode v hv) j t) (spectralNode v hv t)
    (fun i => by simpa only [smul_eq_mul] using spec_act v hv t i)
  have hm' : Polynomial.aeval (spectralNode v hv t) (recurrencePolynomial v m) = uval v (spectralNode v hv) m t := by
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

/-- `Σ_t w_t R_l R_j R_k = g(j,k;l) ‖R_l‖²`. -/
theorem spec_triple (l : Fin (N + 1)) (j : ℕ) (hj : j ≤ N) (k : Fin (N + 1)) :
    ∑ t, spectralWeight v hv t * uval v (spectralNode v hv) l t *
        (uval v (spectralNode v hv) j t * uval v (spectralNode v hv) k t) =
      productMatrix v j k l * nrm v (spectralNode v hv) (spectralWeight v hv) l := by
  simp_rw [spec_product v hv j hj k, mul_sum]
  rw [sum_comm, sum_eq_single l]
  · rw [nrm, mul_sum]; exact sum_congr rfl fun t _ => by ring
  · intro m _ hml
    have := spec_orth v hv l m (by omega) (by omega) (fun h => hml (Fin.ext h.symm))
    rw [← mul_zero (productMatrix v j k m), ← this, mul_sum]
    exact sum_congr rfl fun t _ => by ring
  · intro h; exact absurd (mem_univ _) h

/-- The tail `T_x(y, z) = Σ_{l ≥ x} g(y, z; l)`. -/
noncomputable def tailG (v : Coefficients N) (x y z : Fin (N + 1)) : ℝ :=
  ∑ l : Fin (N + 1), if x.val ≤ l.val then productMatrix v y z l else 0

/-- **Lemma 9.7 (1)**: lowering the top mass changes the recurrence coefficients, in the fixed
coordinate `x`, at the rates `(ȧ_n, ḃ_n, ċ_n) = π_n (a_n, c_n - a_n, -c_n)`. -/
theorem lower_rates (n : ℕ) :
    let x := spectralNode v hv; let w := spectralWeight v hv
    HasDerivAt (fun ε => (epsRaw v x w (-ε)).a n) (piw v x w n * v.a n) 0 ∧
      HasDerivAt (fun ε => (epsRaw v x w (-ε)).b n) (piw v x w n * (v.c n - v.a n)) 0 ∧
        HasDerivAt (fun ε => (epsRaw v x w (-ε)).c n) (-(piw v x w n * v.c n)) 0 := by
  intro x w
  have hA : ∀ m, HasDerivAt (fun ε : ℝ => Aeps v x w (-ε) m) (-Ssum v x w m) 0 := by
    intro m
    have h := ((hasDerivAt_neg (0 : ℝ)).mul_const (Ssum v x w m)).const_add 1
    exact h.congr_deriv (by ring)
  have hA0 : ∀ m, Aeps v x w (-0) m = 1 := fun m => by simp [Aeps]
  have hSs : Ssum v x w (n + 1) - Ssum v x w n = piw v x w n := by rw [Ssum_succ]; ring
  have ha : HasDerivAt (fun ε => (epsRaw v x w (-ε)).a n) (piw v x w n * v.a n) 0 := by
    have h := ((hasDerivAt_const (0 : ℝ) (v.a n)).mul (hA n)).div (hA (n + 1)) (by rw [hA0]; norm_num)
    exact h.congr_deriv (by simp only [Pi.mul_apply]; rw [hA0, hA0, ← hSs]; ring)
  have hc : HasDerivAt (fun ε => (epsRaw v x w (-ε)).c n) (-(piw v x w n * v.c n)) 0 := by
    have h := ((hasDerivAt_const (0 : ℝ) (v.c n)).mul (hA (n + 1))).div (hA n) (by rw [hA0]; norm_num)
    exact h.congr_deriv (by simp only [Pi.mul_apply]; rw [hA0, hA0, ← hSs]; ring)
  refine ⟨ha, ?_, hc⟩
  have h := ((hasDerivAt_const (0 : ℝ) (1 : ℝ)).sub ha).sub hc
  exact h.congr_deriv (by ring)

theorem spec_Ssum_top {t₀ : Fin (N + 1)} (hx0 : spectralNode v hv t₀ = 1) :
    Ssum v (spectralNode v hv) (spectralWeight v hv) (N + 1) = (spectralWeight v hv t₀)⁻¹ := by
  have hK := kerT_top hv hx0 (spec_orth v hv) (spec_nrm v hv) (spectral_weight_pos v hv) t₀
  rw [if_pos rfl] at hK
  have hu : ∀ k, k ≤ N → uval v (spectralNode v hv) k t₀ = 1 := fun k hk => by
    rw [uval, hx0]; exact recurrence_normalized v hv k hk
  rw [← hK, kerT, Ssum]
  exact sum_congr rfl fun k hk => by rw [mem_range] at hk; rw [hu k (by omega), mul_one]

theorem spec_Aeps_pos {t₀ : Fin (N + 1)} (hx0 : spectralNode v hv t₀ = 1) {ε : ℝ} (hε0 : 0 ≤ ε)
    (hε : ε < spectralWeight v hv t₀) (n : ℕ) (hn : n ≤ N + 1) :
    0 < Aeps v (spectralNode v hv) (spectralWeight v hv) (-ε) n := by
  have hw0 : 0 < spectralWeight v hv t₀ := spectral_weight_pos v hv t₀
  have hmono : Ssum v (spectralNode v hv) (spectralWeight v hv) n ≤
      Ssum v (spectralNode v hv) (spectralWeight v hv) (N + 1) := by
    apply sum_le_sum_of_subset_of_nonneg (Finset.range_mono hn)
    intro k hk _
    rw [mem_range] at hk
    exact (inv_pos.mpr (spec_nrm v hv k (by omega))).le
  rw [spec_Ssum_top v hv hx0] at hmono
  have h1 : ε * Ssum v (spectralNode v hv) (spectralWeight v hv) n < 1 := by
    calc ε * Ssum v (spectralNode v hv) (spectralWeight v hv) n ≤ ε * (spectralWeight v hv t₀)⁻¹ :=
          mul_le_mul_of_nonneg_left hmono hε0
      _ < 1 := by rw [← div_eq_mul_inv, div_lt_one hw0]; exact hε
  rw [Aeps]; linarith

/-- **Lemma 9.7**, the lowered measure: for `0 ≤ ε < μ({x₀})` the polynomials of the coefficients
`epsRaw v x w (-ε)` are orthogonal for `μ - ε δ_{x₀}` and equal `1` at `x₀ = 1`. -/
theorem lower_measure {t₀ : Fin (N + 1)} (hx0 : spectralNode v hv t₀ = 1) {ε : ℝ} (hε0 : 0 ≤ ε)
    (hε : ε < spectralWeight v hv t₀) :
    (∀ t, 0 < spectralWeight v hv t - if t = t₀ then ε else 0) ∧
      (∀ n, n ≤ N →
        (recurrencePolynomial (epsRaw v (spectralNode v hv) (spectralWeight v hv) (-ε)) n).eval 1 = 1) ∧
      ∀ m n, m ≤ N → n ≤ N → m ≠ n →
        ∑ t, (spectralWeight v hv t - if t = t₀ then ε else 0) *
          (recurrencePolynomial (epsRaw v (spectralNode v hv) (spectralWeight v hv) (-ε)) m).eval
            (spectralNode v hv t) *
          (recurrencePolynomial (epsRaw v (spectralNode v hv) (spectralWeight v hv) (-ε)) n).eval
            (spectralNode v hv t) = 0 := by
  have hA := fun n hn => (spec_Aeps_pos v hv hx0 hε0 hε n hn).ne'
  have hev := fun m hm t => ueps_eval_raw v hv (spec_act v hv) (spec_orth v hv) (spec_nrm v hv) hA m hm t
  refine ⟨fun t => ?_, fun n hn => ?_, fun m n hm hn hmn => ?_⟩
  · split_ifs with h
    · rw [h]; linarith
    · rw [sub_zero]; exact spectral_weight_pos v hv t
  · have h := hev n hn t₀
    rw [hx0] at h
    rw [h]; exact ueps_top (w := spectralWeight v hv) hv hx0 (-ε) n hn
  · have e : ∀ t, (spectralWeight v hv t - if t = t₀ then ε else 0) *
        (recurrencePolynomial (epsRaw v (spectralNode v hv) (spectralWeight v hv) (-ε)) m).eval
          (spectralNode v hv t) *
        (recurrencePolynomial (epsRaw v (spectralNode v hv) (spectralWeight v hv) (-ε)) n).eval
          (spectralNode v hv t) =
        (spectralWeight v hv t + if t = t₀ then -ε else 0) *
          ueps v (spectralNode v hv) (spectralWeight v hv) (-ε) m t *
          ueps v (spectralNode v hv) (spectralWeight v hv) (-ε) n t := by
      intro t; rw [hev m hm t, hev n hn t]; split_ifs <;> ring
    rw [sum_congr rfl fun t _ => e t]
    exact ueps_orth hv hx0 (spec_orth v hv) (spec_nrm v hv) (-ε) m n hm hn hmn

/-- `Q_a = K_a - S_a R_a`: `Σ_t w_t Q_a R_b R_c = Σ_{l<a} g(b,c;l) = 1 - T_a(b,c)` when
`∫ R_a R_b R_c dμ = 0`. -/
theorem lower_Qsum (a b c : Fin (N + 1))
    (h0 : ∑ t, spectralWeight v hv t * uval v (spectralNode v hv) a t * uval v (spectralNode v hv) b t *
      uval v (spectralNode v hv) c t = 0) :
    ∑ t, spectralWeight v hv t * (kerT v (spectralNode v hv) (spectralWeight v hv) a t -
        Ssum v (spectralNode v hv) (spectralWeight v hv) a * uval v (spectralNode v hv) a t) *
        uval v (spectralNode v hv) b t * uval v (spectralNode v hv) c t = 1 - tailG v a b c := by
  set x := spectralNode v hv
  set w := spectralWeight v hv
  have e1 : ∑ t, w t * (kerT v x w a t - Ssum v x w a * uval v x a t) * uval v x b t * uval v x c t =
      ∑ t, w t * kerT v x w a t * uval v x b t * uval v x c t -
        Ssum v x w a * ∑ t, w t * uval v x a t * uval v x b t * uval v x c t := by
    rw [mul_sum, ← sum_sub_distrib]; exact sum_congr rfl fun t _ => by ring
  rw [e1, h0, mul_zero, sub_zero]
  -- `Σ_t w K_a R_b R_c = Σ_{l < a} π_l Σ_t w R_l R_b R_c`
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
    · have := spec_triple v hv l b.val (by omega) c
      have hpn : piw v x w l * nrm v x w l = 1 := inv_mul_cancel₀ (spec_nrm v hv l (by omega)).ne'
      calc ∑ t, w t * (piw v x w l * uval v x l t) * uval v x b t * uval v x c t
          = piw v x w l * ∑ t, w t * uval v x l t * (uval v x b t * uval v x c t) := by
            rw [mul_sum]; exact sum_congr rfl fun t _ => by ring
        _ = productMatrix v b c l := by rw [this, mul_comm (productMatrix v b c l), ← mul_assoc, hpn, one_mul]
    · simp
  rw [e2, tailG]
  have hrow := product_row_sum v hv b.val (by omega) c
  rw [← hrow, ← sum_sub_distrib]
  exact sum_congr rfl fun l _ => by split_ifs <;> first | omega | ring

/-- **Lemma 9.7 (2)**: if `∫ R_x R_y R_z dμ = 0`, then lowering the top mass changes
`∫ R^ε_x R^ε_y R^ε_z dμ_ε` at the rate `2 - T_x(y,z) - T_y(x,z) - T_z(x,y)`,
`T_x(y,z) = Σ_{k ≥ x} g(y,z;k)`. -/
theorem lower_triple {t₀ : Fin (N + 1)} (hx0 : spectralNode v hv t₀ = 1) (i j k : Fin (N + 1))
    (h0 : ∑ t, spectralWeight v hv t * uval v (spectralNode v hv) i t * uval v (spectralNode v hv) j t *
      uval v (spectralNode v hv) k t = 0) :
    HasDerivAt (fun ε => ∑ t, (spectralWeight v hv t - if t = t₀ then ε else 0) *
        (recurrencePolynomial (epsRaw v (spectralNode v hv) (spectralWeight v hv) (-ε)) i).eval (spectralNode v hv t) *
        (recurrencePolynomial (epsRaw v (spectralNode v hv) (spectralWeight v hv) (-ε)) j).eval (spectralNode v hv t) *
        (recurrencePolynomial (epsRaw v (spectralNode v hv) (spectralWeight v hv) (-ε)) k).eval (spectralNode v hv t))
      (2 - tailG v i j k - tailG v j i k - tailG v k i j) 0 := by
  set x := spectralNode v hv
  set w := spectralWeight v hv
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
  -- the derivative
  have hsym1 : ∑ t, w t * uval v x j t * uval v x i t * uval v x k t = 0 := by
    rw [← h0]; exact sum_congr rfl fun t _ => by ring
  have hsym2 : ∑ t, w t * uval v x k t * uval v x i t * uval v x j t = 0 := by
    rw [← h0]; exact sum_congr rfl fun t _ => by ring
  have q1 := lower_Qsum v hv i j k h0
  have q2 := lower_Qsum v hv j i k hsym1
  have q3 := lower_Qsum v hv k i j hsym2
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
  have hG' := hG.congr_deriv hD
  -- the polynomials of the lowered system are the `ũ` near `0`
  have hev : ∀ᶠ ε in nhds (0 : ℝ), ∀ n ∈ range (N + 2), Aeps v x w (-ε) n ≠ 0 := by
    refine (Filter.eventually_all_finset _).mpr fun n _ => ?_
    have hc : Continuous fun ε : ℝ => Aeps v x w (-ε) n := by
      simp only [Aeps]; fun_prop
    exact hc.continuousAt.eventually_ne (by simp [Aeps])
  refine hG'.congr_of_eventuallyEq ?_
  filter_upwards [hev] with ε hε
  have hA : ∀ n, n ≤ N + 1 → Aeps v x w (-ε) n ≠ 0 := fun n hn => hε n (mem_range.mpr (by omega))
  have hr := fun (m : Fin (N + 1)) t =>
    ueps_eval_raw v hv (spec_act v hv) (spec_orth v hv) (spec_nrm v hv) hA m (by omega) t
  show ∑ t, _ = ∑ t, _
  exact sum_congr rfl fun t _ => by rw [hr i t, hr j t, hr k t]; rfl

end lower

end Szkraw
