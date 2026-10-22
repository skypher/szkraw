import Szkraw.Families
import Szkraw.Norlund
import Mathlib.Analysis.Polynomial.Basic
import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Corollary 9.6 (analytic rules) and Proposition 9.9 (2) (boundary layers)

A rule `β` is analytic on an open set containing `Ω = {U ≤ -1}` if it extends from `[0,1]` to a
function holomorphic there. By Lemma 9.5 the alternating sums `D_N β = Σ (-1)^n C(N,n) β(n/N)`
are `O(√N e^{-ηN})`.

* Corollary 9.6: a set of arrays with property (P) admitting an analytic rule forces
  `L_even = L_odd = 0`; when these hold, the first-order change of `g(N,N;N)` along `v_N` is
  `O(|s_N| √N e^{-ηN})`, and the rule `β(x) = e^x - 1 - (e - 1)x`, `γ = 0` shows that it need not
  vanish.
* Proposition 9.9 (2): for `δb_n = β(n/N) + p_n + q_{N-n}`, `δc_n = γ(n/N) + p'_n + q'_{N-n}` with
  finitely supported boundary layers, `q'_0 = L_even = L_odd`, `p_k = q_k` and `p'_k + q'_k = -p_k`
  for `k ≥ 1`.
-/

namespace Szkraw

open Finset Filter Topology Polynomial

/-- A rule `β` on `[0,1]` that extends to a function holomorphic on an open set containing
`Ω = {U ≤ -1}`. -/
def AnalyticOnOmega (β : ℝ → ℝ) : Prop :=
  ∃ (F : ℂ → ℂ) (D : Set ℂ), IsOpen D ∧ {x : ℂ | Ulog x ≤ -1} ⊆ D ∧ DifferentiableOn ℂ F D ∧
    ∀ t ∈ Set.Icc (0 : ℝ) 1, F t = β t

theorem AnalyticOnOmega.add_two_mul {β γ : ℝ → ℝ} (hβ : AnalyticOnOmega β) (hγ : AnalyticOnOmega γ) :
    AnalyticOnOmega fun x => β x + 2 * γ x := by
  obtain ⟨F, D, hD, hΩ, hF, hFβ⟩ := hβ
  obtain ⟨G, E, hE, hΩ', hG, hGγ⟩ := hγ
  refine ⟨fun z => F z + 2 * G z, D ∩ E, hD.inter hE, Set.subset_inter hΩ hΩ', ?_, fun t ht => ?_⟩
  · exact (hF.mono Set.inter_subset_left).add ((hG.mono Set.inter_subset_right).const_mul 2)
  · simp only [hFβ t ht, hGγ t ht]; push_cast; ring

/-- `D_N φ = Σ_{n=0}^N (-1)^n C(N,n) φ(n/N)`. -/
noncomputable def DN (N : ℕ) (φ : ℝ → ℝ) : ℝ :=
  ∑ n ∈ range (N + 1), (-1 : ℝ) ^ n * (N.choose n : ℝ) * φ (n / N)

/-- Lemma 9.5 for analytic rules. -/
theorem DN_bound {φ : ℝ → ℝ} (hφ : AnalyticOnOmega φ) :
    ∃ η > 0, ∃ C ≥ 0, ∀ N : ℕ, 1 ≤ N → |DN N φ| ≤ C * Real.sqrt N * Real.exp (-(η * N)) := by
  obtain ⟨F, D, hD, hΩ, hF, hFφ⟩ := hφ
  obtain ⟨η, hη, C, hC⟩ := norlund_rice F D hD hF hΩ
  refine ⟨η, hη, max C 0, le_max_right _ _, fun N hN => ?_⟩
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have e : altBinom N F = (DN N φ : ℂ) := by
    rw [altBinom, DN]
    push_cast
    refine sum_congr rfl fun n hn => ?_
    have hn' : n ≤ N := Nat.lt_succ_iff.mp (mem_range.mp hn)
    rw [show (n : ℂ) / N = ((n / N : ℝ) : ℂ) by push_cast; rfl,
      hFφ _ ⟨by positivity, by rw [div_le_one hN0]; exact_mod_cast hn'⟩]
  have := hC N hN
  rw [e, Complex.norm_real, Real.norm_eq_abs] at this
  exact this.trans (by gcongr; exact le_max_left _ _)

theorem tendsto_sqrt_mul_exp {η : ℝ} (hη : 0 < η) :
    Tendsto (fun N : ℕ => Real.sqrt N * Real.exp (-(η * N))) atTop (𝓝 0) := by
  have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (1 / 2) η hη).comp tendsto_natCast_atTop_atTop
  refine h.congr fun N => ?_
  simp only [Function.comp, Real.sqrt_eq_rpow, neg_mul]

theorem DN_tendsto {φ : ℝ → ℝ} (hφ : AnalyticOnOmega φ) : Tendsto (fun N => DN N φ) atTop (𝓝 0) := by
  obtain ⟨η, hη, C, -, hbd⟩ := DN_bound hφ
  have h := (tendsto_sqrt_mul_exp hη).const_mul C
  rw [mul_zero] at h
  refine squeeze_zero_norm' ?_ h
  filter_upwards [eventually_ge_atTop 1] with N hN
  rw [Real.norm_eq_abs, ← mul_assoc]
  exact hbd N hN

/-! ### The alternating sum of Lemma 9.2 for general directions -/

/-- `Σ_{n=0}^N (-1)^n C(N,n) φ_n`. -/
noncomputable def altN (N : ℕ) (φ : ℕ → ℝ) : ℝ := ∑ n ∈ range (N + 1), (-1 : ℝ) ^ n * (N.choose n : ℝ) * φ n

theorem altN_add (N : ℕ) (f g : ℕ → ℝ) : altN N (fun n => f n + g n) = altN N f + altN N g := by
  simp only [altN, mul_add, sum_add_distrib]

theorem altN_supp {N K : ℕ} {f : ℕ → ℝ} (hf : ∀ k, K < k → f k = 0) (hKN : K ≤ N) :
    altN N f = ∑ k ∈ range (K + 1), (-1 : ℝ) ^ k * (N.choose k : ℝ) * f k := by
  refine (sum_subset (range_subset_range.mpr (by omega)) fun k _ hk => ?_).symm
  rw [hf k (by simp at hk; omega), mul_zero]

theorem neg_one_pow_sub {N j : ℕ} (hj : j ≤ N) : (-1 : ℝ) ^ (N - j) = (-1) ^ N * (-1) ^ j := by
  rw [← pow_add, show N + j = (N - j) + 2 * j by omega, pow_add, pow_mul, neg_one_sq, one_pow, mul_one]

theorem altN_refl (N : ℕ) (f : ℕ → ℝ) : altN N (fun n => f (N - n)) = (-1) ^ N * altN N f := by
  rw [altN, altN, ← sum_range_reflect, mul_sum]
  refine sum_congr rfl fun j hj => ?_
  have hj' : j ≤ N := Nat.lt_succ_iff.mp (mem_range.mp hj)
  rw [show N + 1 - 1 - j = N - j by omega, show N - (N - j) = j by omega, Nat.choose_symm hj',
    neg_one_pow_sub hj']
  ring

/-- `Σ (-1)^n C(N,n) F_n` in terms of the full direction: the boundary values `n = 0, N` are
corrected. -/
theorem corner_sum_gen (δb δc : ℕ → ℝ) {N : ℕ} (hN : 2 ≤ N) :
    ∑ n ∈ range (N + 1), (-1 : ℝ) ^ n * (N.choose n : ℝ) * cornerF N δb δc n =
      if N % 2 = 0 then altN N (fun n => δb n + 2 * δc n) - (δb 0 + 2 * δc 0) - (δb N + δc N)
      else altN N δb - δb 0 + (δb N + δc N) := by
  by_cases hpar : N % 2 = 0
  · have term : ∀ n ∈ range (N + 1), (-1 : ℝ) ^ n * (N.choose n : ℝ) * cornerF N δb δc n =
        (-1 : ℝ) ^ n * (N.choose n : ℝ) * (δb n + 2 * δc n) +
          (if n = 0 then -(δb 0 + 2 * δc 0) else 0) +
            (if n = N then (-1 : ℝ) ^ N * (-(δb N) - δc N) else 0) := by
      intro n hn
      rw [mem_range] at hn
      simp only [cornerF, if_pos hpar, stochDir]
      rcases Nat.eq_zero_or_pos n with h0 | hpos
      · subst h0; simp [show ¬(0 = N) by omega]
      by_cases hnN : n = N
      · subst hnN; simp [show n ≠ 0 by omega]; ring
      · simp [show n ≠ 0 by omega, hnN]
    rw [sum_congr rfl term, sum_add_distrib, sum_add_distrib, sum_ite_eq' (range (N + 1)) 0,
      sum_ite_eq' (range (N + 1)) N, if_pos (by simp), if_pos (by simp), if_pos hpar,
      (Even.neg_one_pow ⟨N / 2, by omega⟩ : (-1 : ℝ) ^ N = 1), altN]
    ring
  · have term : ∀ n ∈ range (N + 1), (-1 : ℝ) ^ n * (N.choose n : ℝ) * cornerF N δb δc n =
        (-1 : ℝ) ^ n * (N.choose n : ℝ) * δb n + (if n = 0 then -(δb 0) else 0) +
          (if n = N then (-1 : ℝ) ^ N * (-(δb N) - δc N) else 0) := by
      intro n hn
      rw [mem_range] at hn
      simp only [cornerF, if_neg hpar, stochDir]
      rcases Nat.eq_zero_or_pos n with h0 | hpos
      · subst h0; simp [show ¬(0 = N) by omega]
      by_cases hnN : n = N
      · subst hnN; simp [show n ≠ 0 by omega]; ring
      · simp [show n ≠ 0 by omega, hnN]
    rw [sum_congr rfl term, sum_add_distrib, sum_add_distrib, sum_ite_eq' (range (N + 1)) 0,
      sum_ite_eq' (range (N + 1)) N, if_pos (by simp), if_pos (by simp), if_neg hpar,
      (Odd.neg_one_pow ⟨N / 2, by omega⟩ : (-1 : ℝ) ^ N = -1), altN]
    ring

/-- `F` only depends on `δb_1, …, δb_{N-1}` and `δc_1, …, δc_N`. -/
theorem cornerF_congr {N : ℕ} {δb δc δb' δc' : ℕ → ℝ} (hb : ∀ n, 1 ≤ n → n < N → δb n = δb' n)
    (hc : ∀ n, 1 ≤ n → n ≤ N → δc n = δc' n) {n : ℕ} (hn : n ≤ N) :
    cornerF N δb δc n = cornerF N δb' δc' n := by
  simp only [cornerF, stochDir]
  by_cases h0 : n = 0
  · simp [h0]
  by_cases hN : n = N
  · subst hN; simp [h0, hc n (by omega) le_rfl]
  · simp [h0, hN, hb n (by omega) (by omega), hc n (by omega) hn]

/-- Along a uniform rule the alternating sum is `D_N(β + 2γ) - L_even` or `D_N β - L_odd`. -/
theorem rule_sum_analytic (β γ : ℝ → ℝ) {N : ℕ} (hN : 2 ≤ N) :
    ∑ n ∈ range (N + 1), (-1 : ℝ) ^ n * (N.choose n : ℝ) *
        cornerF N (fun n => β (n / N)) (fun n => γ (n / N)) n =
      if N % 2 = 0 then DN N (fun x => β x + 2 * γ x) - Leven β γ else DN N β - Lodd β γ := by
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  rw [corner_sum_gen _ _ hN]
  simp only [Nat.cast_zero, zero_div, div_self hN0]
  split_ifs
  · simp only [altN, DN, Leven]; ring
  · simp only [altN, DN, Lodd]; ring

/-- The first-order change of `g(N,N;N)` along a general uniform rule. -/
theorem analytic_rule_deriv (β γ : ℝ → ℝ) {N : ℕ} (hN : 2 ≤ N) :
    HasDerivAt (fun ε => productMatrix (ruleArray β γ N ε) N (Fin.last N) (Fin.last N))
      (sN N * (if N % 2 = 0 then DN N (fun x => β x + 2 * γ x) - Leven β γ else DN N β - Lodd β γ)) 0 := by
  have h := corner_identity (δb := fun n => β (n / N)) (δc := fun n => γ (n / N)) hN
  rw [rule_sum_analytic β γ hN] at h
  exact h

/-! ### Binomial polynomials -/

/-- The polynomial `Σ_{k ≤ K} a_k C(X,k) - c`. -/
noncomputable def binomPoly (a : ℕ → ℝ) (K : ℕ) (c : ℝ) : ℝ[X] :=
  ∑ k ∈ range (K + 1), Polynomial.C (a k / k.factorial) * descPochhammer ℝ k - Polynomial.C c

theorem binomPoly_eval (a : ℕ → ℝ) (K : ℕ) (c : ℝ) (N : ℕ) :
    (binomPoly a K c).eval (N : ℝ) = ∑ k ∈ range (K + 1), a k * (N.choose k : ℝ) - c := by
  rw [binomPoly, eval_sub, eval_C, eval_finsetSum]
  congr 1
  refine sum_congr rfl fun k _ => ?_
  rw [eval_mul, eval_C, descPochhammer_eval_eq_descFactorial, Nat.descFactorial_eq_factorial_mul_choose]
  have : (k.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  push_cast
  field_simp

/-- The binomial polynomials `C(X,k)` are linearly independent. -/
theorem binom_indep {a : ℕ → ℝ} {K : ℕ} (h : ∀ m : ℕ, ∑ k ∈ range (K + 1), a k * (m.choose k : ℝ) = 0) :
    ∀ k ≤ K, a k = 0 := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    have hm := h k
    rw [sum_eq_single k (fun j hj hjk => ?_) (fun h' => absurd (mem_range.mpr (by omega)) h')] at hm
    · simpa using hm
    · rcases lt_or_gt_of_ne hjk with hlt | hgt
      · rw [ih j hlt (by have := mem_range.mp hj; omega), zero_mul]
      · rw [Nat.choose_eq_zero_of_lt hgt, Nat.cast_zero, mul_zero]

theorem binomPoly_eq_zero {a : ℕ → ℝ} {K : ℕ} {c : ℝ} (h : binomPoly a K c = 0) :
    a 0 = c ∧ ∀ k, 1 ≤ k → k ≤ K → a k = 0 := by
  set a' : ℕ → ℝ := fun k => if k = 0 then a 0 - c else a k
  have h' : ∀ m : ℕ, ∑ k ∈ range (K + 1), a' k * (m.choose k : ℝ) = 0 := by
    intro m
    have := binomPoly_eval a K c m
    rw [h, eval_zero] at this
    rw [sum_range_succ'] at this ⊢
    simp only [a', if_neg (Nat.succ_ne_zero _), if_pos rfl, Nat.choose_zero_right, Nat.cast_one, mul_one] at this ⊢
    linarith
  have hz := binom_indep h'
  refine ⟨?_, fun k hk1 hkK => ?_⟩
  · have := hz 0 (Nat.zero_le _); simp only [a', if_pos rfl] at this; linarith
  · have := hz k hkK; simpa [a', show k ≠ 0 by omega] using this

/-- A nonzero polynomial has an eventual strict sign, bounded away from `0`. -/
theorem poly_eventual_sign {Q : ℝ[X]} (hQ : Q ≠ 0) :
    ∃ c > 0, (∀ᶠ x in atTop, c ≤ Q.eval x) ∨ ∀ᶠ x in atTop, Q.eval x ≤ -c := by
  rcases Nat.eq_zero_or_pos Q.natDegree with hd | hd
  · have hQc := eq_C_of_natDegree_eq_zero hd
    have h0 : Q.coeff 0 ≠ 0 := fun h => hQ (by rw [hQc, h, C_0])
    have hev : ∀ x, Q.eval x = Q.coeff 0 := fun x => by conv_lhs => rw [hQc]
                                                        rw [eval_C]
    rcases lt_or_gt_of_ne h0 with hn | hp
    · exact ⟨-Q.coeff 0, by linarith, Or.inr (Eventually.of_forall fun x => by rw [hev]; linarith)⟩
    · exact ⟨Q.coeff 0, hp, Or.inl (Eventually.of_forall fun x => by rw [hev])⟩
  · have hdeg : 0 < Q.degree := natDegree_pos_iff_degree_pos.mp hd
    rcases le_or_gt 0 Q.leadingCoeff with hl | hl
    · exact ⟨1, one_pos, Or.inl ((Q.tendsto_atTop_of_leadingCoeff_nonneg hdeg hl).eventually_ge_atTop 1)⟩
    · exact ⟨1, one_pos, Or.inr ((Q.tendsto_atBot_of_leadingCoeff_nonpos hdeg hl.le).eventually_le_atBot (-1))⟩

/-- If `A_N = D_N + Q(N)` on a parity class with `D_N → 0`, and `A_N` is neither eventually
strictly positive nor eventually strictly negative there, then `Q = 0`. -/
theorem poly_zero_of_no_sign {A D : ℕ → ℝ} {Q : ℝ[X]} {par N₁ : ℕ} (hD : Tendsto D atTop (𝓝 0))
    (hA : ∀ N, N₁ ≤ N → N % 2 = par → A N = D N + Q.eval (N : ℝ))
    (hpos : ¬∃ M, ∀ N, M ≤ N → N % 2 = par → 0 < A N) (hneg : ¬∃ M, ∀ N, M ≤ N → N % 2 = par → A N < 0) :
    Q = 0 := by
  by_contra hne
  obtain ⟨c, hc, hsign⟩ := poly_eventual_sign hne
  have hD' := hD.eventually (Metric.ball_mem_nhds 0 hc)
  rcases hsign with hs | hs
  · obtain ⟨M, hM⟩ := eventually_atTop.mp
      ((hD'.and (tendsto_natCast_atTop_atTop.eventually hs)).and (eventually_ge_atTop N₁))
    refine hpos ⟨M, fun N hNM hpar => ?_⟩
    obtain ⟨⟨h1, h2⟩, h3⟩ := hM N hNM
    rw [Real.dist_eq, sub_zero] at h1
    rw [hA N h3 hpar]
    linarith [(abs_lt.mp h1).1]
  · obtain ⟨M, hM⟩ := eventually_atTop.mp
      ((hD'.and (tendsto_natCast_atTop_atTop.eventually hs)).and (eventually_ge_atTop N₁))
    refine hneg ⟨M, fun N hNM hpar => ?_⟩
    obtain ⟨⟨h1, h2⟩, h3⟩ := hM N hNM
    rw [Real.dist_eq, sub_zero] at h1
    rw [hA N h3 hpar]
    linarith [(abs_lt.mp h1).2]

/-! ### Proposition 9.9 (2) -/

/-- **Proposition 9.9 (2)** (boundary layers): let `δb_n = β(n/N) + p_n + q_{N-n}` for
`1 ≤ n ≤ N - 1` and `δc_n = γ(n/N) + p'_n + q'_{N-n}` for `1 ≤ n ≤ N`, for all large `N`, with `β, γ` analytic on an
open set containing `Ω` and finitely supported boundary layers `p, q, p', q'` independent of `N`.
If a set with property (P) contains `K_{N,1} + ε v_N` for all large `N` and small `ε > 0`, then
`q'_0 = L_even = L_odd`, `p_k = q_k` and `p'_k + q'_k = -p_k` for `k ≥ 1`. -/
theorem families_boundary_layers (S : (N : ℕ) → Set (Coefficients N))
    (hS : ∀ N, ∀ v ∈ S N, MatrixPositivity v) {β γ : ℝ → ℝ} (hβ : AnalyticOnOmega β)
    (hγ : AnalyticOnOmega γ) {p q p' q' : ℕ → ℝ} {K : ℕ} (hp : ∀ k, K < k → p k = 0)
    (hq : ∀ k, K < k → q k = 0) (hp' : ∀ k, K < k → p' k = 0) (hq' : ∀ k, K < k → q' k = 0)
    {vb vc : ℕ → ℕ → ℝ} (hvb : ∃ N₁, ∀ N, N₁ ≤ N → ∀ n, 1 ≤ n → n < N → vb N n = β (n / N) + p n + q (N - n))
    (hvc : ∃ N₁, ∀ N, N₁ ≤ N → ∀ n, 1 ≤ n → n ≤ N → vc N n = γ (n / N) + p' n + q' (N - n))
    (hfam : ContainsFamily S vb vc) :
    q' 0 = Leven β γ ∧ q' 0 = Lodd β γ ∧ (∀ k, 1 ≤ k → p k = q k) ∧ ∀ k, 1 ≤ k → p' k + q' k = -p k := by
  obtain ⟨N₁, hvb⟩ := hvb
  obtain ⟨N₂, hvc⟩ := hvc
  set ae : ℕ → ℝ := fun k => (-1) ^ k * (p k + 2 * p' k + q k + 2 * q' k)
  set ce : ℝ := β 0 + p 0 + 2 * γ 0 + 2 * p' 0 + (β 1 + q 0 + γ 1 + q' 0)
  set ao : ℕ → ℝ := fun k => (-1) ^ k * (p k - q k)
  set co : ℝ := β 0 + p 0 - (β 1 + q 0 + γ 1 + q' 0)
  -- the alternating sum for large `N`
  have hA : ∀ N, max (max 2 (K + 1)) (max N₁ N₂) ≤ N → altSum vb vc N =
      if N % 2 = 0 then DN N (fun x => β x + 2 * γ x) + (binomPoly ae K ce).eval (N : ℝ)
      else DN N β + (binomPoly ao K co).eval (N : ℝ) := by
    intro N hN
    have hN2 : 2 ≤ N := by have := le_max_left (max 2 (K + 1)) (max N₁ N₂); omega
    have hKN : K + 1 ≤ N := by have := le_max_left (max 2 (K + 1)) (max N₁ N₂); omega
    have hN₁ : N₁ ≤ N := by have := le_max_right (max 2 (K + 1)) (max N₁ N₂); omega
    have hN₂ : N₂ ≤ N := by have := le_max_right (max 2 (K + 1)) (max N₁ N₂); omega
    have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
    set fb : ℕ → ℝ := fun n => β (n / N) + p n + q (N - n)
    set fc : ℕ → ℝ := fun n => γ (n / N) + p' n + q' (N - n)
    have hcongr : altSum vb vc N =
        ∑ n ∈ range (N + 1), (-1 : ℝ) ^ n * (N.choose n : ℝ) * cornerF N fb fc n := by
      refine sum_congr rfl fun n hn => ?_
      rw [cornerF_congr (δb' := fb) (δc' := fc) (fun m h1 h2 => hvb N hN₁ m h1 h2) (fun m h1 h2 => hvc N hN₂ m h1 h2)
        (Nat.lt_succ_iff.mp (mem_range.mp hn))]
    have hqN : q N = 0 := hq N (by omega)
    have hq'N : q' N = 0 := hq' N (by omega)
    have hpN : p N = 0 := hp N (by omega)
    have hp'N : p' N = 0 := hp' N (by omega)
    have hfb0 : fb 0 = β 0 + p 0 := by simp [fb, hqN]
    have hfc0 : fc 0 = γ 0 + p' 0 := by simp [fc, hq'N]
    have hfbN : fb N = β 1 + q 0 := by simp [fb, div_self hN0, hpN]
    have hfcN : fc N = γ 1 + q' 0 := by simp [fc, div_self hN0, hp'N]
    rw [hcongr, corner_sum_gen fb fc hN2, binomPoly_eval, binomPoly_eval]
    split_ifs with hpar
    · have e1 : altN N (fun n => p n + 2 * p' n) =
          ∑ k ∈ range (K + 1), (-1 : ℝ) ^ k * (N.choose k : ℝ) * (p k + 2 * p' k) :=
        altN_supp (fun k hk => by rw [hp k hk, hp' k hk]; ring) (by omega)
      have e2 : altN N (fun n => q (N - n) + 2 * q' (N - n)) =
          ∑ k ∈ range (K + 1), (-1 : ℝ) ^ k * (N.choose k : ℝ) * (q k + 2 * q' k) := by
        refine (altN_refl N (fun k => q k + 2 * q' k)).trans ?_
        rw [(Even.neg_one_pow ⟨N / 2, by omega⟩ : (-1 : ℝ) ^ N = 1), one_mul]
        exact altN_supp (fun k hk => by rw [hq k hk, hq' k hk]; ring) (by omega)
      have hAlt : altN N (fun n => fb n + 2 * fc n) = DN N (fun x => β x + 2 * γ x) +
          altN N (fun n => p n + 2 * p' n) + altN N (fun n => q (N - n) + 2 * q' (N - n)) := by
        simp only [altN, DN, fb, fc, ← sum_add_distrib]
        exact sum_congr rfl fun n _ => by ring
      rw [hAlt, e1, e2, hfb0, hfc0, hfbN, hfcN]
      have e3 : ∑ k ∈ range (K + 1), ae k * (N.choose k : ℝ) =
          ∑ k ∈ range (K + 1), (-1 : ℝ) ^ k * (N.choose k : ℝ) * (p k + 2 * p' k) +
            ∑ k ∈ range (K + 1), (-1 : ℝ) ^ k * (N.choose k : ℝ) * (q k + 2 * q' k) := by
        rw [← sum_add_distrib]; exact sum_congr rfl fun k _ => by simp only [ae]; ring
      rw [e3]
      simp only [ce]
      ring
    · have e1 : altN N p = ∑ k ∈ range (K + 1), (-1 : ℝ) ^ k * (N.choose k : ℝ) * p k := altN_supp hp (by omega)
      have e2 : altN N (fun n => q (N - n)) = -∑ k ∈ range (K + 1), (-1 : ℝ) ^ k * (N.choose k : ℝ) * q k := by
        refine (altN_refl N q).trans ?_
        rw [(Odd.neg_one_pow ⟨N / 2, by omega⟩ : (-1 : ℝ) ^ N = -1), neg_one_mul]
        exact congrArg _ (altN_supp hq (by omega))
      have hAlt : altN N fb = DN N β + altN N p + altN N (fun n => q (N - n)) := by
        simp only [altN, DN, fb, ← sum_add_distrib]
        exact sum_congr rfl fun n _ => by ring
      rw [hAlt, e1, e2, hfb0, hfbN, hfcN]
      have e3 : ∑ k ∈ range (K + 1), ao k * (N.choose k : ℝ) =
          ∑ k ∈ range (K + 1), (-1 : ℝ) ^ k * (N.choose k : ℝ) * p k -
            ∑ k ∈ range (K + 1), (-1 : ℝ) ^ k * (N.choose k : ℝ) * q k := by
        rw [← sum_sub_distrib]; exact sum_congr rfl fun k _ => by simp only [ao]; ring
      rw [e3]
      simp only [co]
      ring
  -- both polynomial parts vanish
  have hns0 := families_no_strict_sign S hS hfam 0 (by norm_num)
  have hns1 := families_no_strict_sign S hS hfam 1 (by norm_num)
  have hQe : binomPoly ae K ce = 0 := poly_zero_of_no_sign (DN_tendsto (hβ.add_two_mul hγ))
    (fun N hN hpar => by rw [hA N hN, if_pos hpar]) hns0.1 hns0.2
  have hQo : binomPoly ao K co = 0 := poly_zero_of_no_sign (DN_tendsto hβ)
    (fun N hN hpar => by rw [hA N hN, if_neg (by omega)]) hns1.1 hns1.2
  obtain ⟨he0, hek⟩ := binomPoly_eq_zero hQe
  obtain ⟨ho0, hok⟩ := binomPoly_eq_zero hQo
  simp only [ae, ce, ao, co, pow_zero, one_mul] at he0 ho0
  have hpow : ∀ k : ℕ, (-1 : ℝ) ^ k ≠ 0 := fun k => pow_ne_zero _ (by norm_num)
  have hpq : ∀ k, 1 ≤ k → p k = q k := by
    intro k hk
    by_cases hkK : k ≤ K
    · have := (mul_eq_zero.mp (hok k hk hkK)).resolve_left (hpow k); linarith
    · rw [hp k (by omega), hq k (by omega)]
  refine ⟨by rw [Leven]; linarith, by rw [Lodd]; linarith, hpq, fun k hk => ?_⟩
  by_cases hkK : k ≤ K
  · have := (mul_eq_zero.mp (hek k hk hkK)).resolve_left (hpow k)
    have := hpq k hk
    linarith
  · rw [hp k (by omega), hp' k (by omega), hq' k (by omega)]; ring

/-! ### Corollary 9.6 -/

/-- **Corollary 9.6**, first statement: if a set of arrays with property (P) admits an analytic
rule `(β, γ)` at the symmetric endpoint, then `L_even = L_odd = 0`. -/
theorem analytic_forced_equalities (S : (N : ℕ) → Set (Coefficients N))
    (hS : ∀ N, ∀ v ∈ S N, MatrixPositivity v) {β γ : ℝ → ℝ} (hβ : AnalyticOnOmega β)
    (hγ : AnalyticOnOmega γ) (hadm : AdmitsRule S β γ) : Leven β γ = 0 ∧ Lodd β γ = 0 := by
  have h := families_boundary_layers S hS hβ hγ (p := fun _ => 0) (q := fun _ => 0) (p' := fun _ => 0)
    (q' := fun _ => 0) (K := 0) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (vb := fun N n => β (n / N)) (vc := fun N n => γ (n / N)) ⟨0, fun _ _ _ _ _ => by ring⟩
    ⟨0, fun _ _ _ _ _ => by ring⟩ hadm
  exact ⟨h.1.symm, h.2.1.symm⟩

/-- **Corollary 9.6**, second statement: when `L_even = L_odd = 0`, the first-order change of
`g(N,N;N)` along `v_N` is `O(|s_N| √N e^{-ηN})`. -/
theorem analytic_rule_small {β γ : ℝ → ℝ} (hβ : AnalyticOnOmega β) (hγ : AnalyticOnOmega γ)
    (hL : Leven β γ = 0 ∧ Lodd β γ = 0) :
    ∃ η > 0, ∃ C, ∀ N : ℕ, 2 ≤ N → ∃ d,
      HasDerivAt (fun ε => productMatrix (ruleArray β γ N ε) N (Fin.last N) (Fin.last N)) d 0 ∧
        |d| ≤ |sN N| * (C * Real.sqrt N * Real.exp (-(η * N))) := by
  obtain ⟨η₁, hη₁, C₁, hC₁, h₁⟩ := DN_bound hβ
  obtain ⟨η₂, hη₂, C₂, hC₂, h₂⟩ := DN_bound (hβ.add_two_mul hγ)
  refine ⟨min η₁ η₂, lt_min hη₁ hη₂, max C₁ C₂, fun N hN => ⟨_, analytic_rule_deriv β γ hN, ?_⟩⟩
  rw [abs_mul]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  have hmono : ∀ η C, 0 < η → 0 ≤ C → min η₁ η₂ ≤ η → C ≤ max C₁ C₂ →
      C * Real.sqrt N * Real.exp (-(η * N)) ≤ max C₁ C₂ * Real.sqrt N * Real.exp (-(min η₁ η₂ * N)) := by
    intro η C _ hC hη hCle
    have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    gcongr
  split_ifs
  · rw [hL.1, sub_zero]
    exact (h₂ N (by omega)).trans (hmono η₂ C₂ hη₂ hC₂ (min_le_right _ _) (le_max_right _ _))
  · rw [hL.2, sub_zero]
    exact (h₁ N (by omega)).trans (hmono η₁ C₁ hη₁ hC₁ (min_le_left _ _) (le_max_left _ _))

/-- The rule `β(x) = e^x - 1 - (e - 1)x` of Corollary 9.6. -/
noncomputable def expRule (x : ℝ) : ℝ := Real.exp x - 1 - (Real.exp 1 - 1) * x

theorem expRule_analytic : AnalyticOnOmega expRule := by
  refine ⟨fun z => Complex.exp z - 1 - ((Real.exp 1 - 1 : ℝ) : ℂ) * z, Set.univ, isOpen_univ,
    Set.subset_univ _, ?_, fun t _ => ?_⟩
  · exact ((Complex.differentiable_exp.sub_const 1).sub (differentiable_id.const_mul _)).differentiableOn
  · simp only [expRule]; push_cast; rfl

theorem expRule_L : Leven expRule (fun _ => 0) = 0 ∧ Lodd expRule (fun _ => 0) = 0 := by
  simp only [Leven, Lodd, expRule, Real.exp_zero]
  constructor <;> ring

theorem alt_pow (N : ℕ) (x : ℝ) : ∑ n ∈ range (N + 1), (-1 : ℝ) ^ n * (N.choose n : ℝ) * x ^ n = (1 - x) ^ N := by
  rw [show (1 - x) = -x + 1 by ring, add_pow]
  refine sum_congr rfl fun n _ => ?_
  rw [one_pow, mul_one, neg_pow]
  ring

theorem DN_expRule {N : ℕ} (hN : 2 ≤ N) : DN N expRule = (1 - Real.exp (1 / N)) ^ N := by
  have hpoly := alt_sum_poly (Polynomial.C 1 + Polynomial.C (Real.exp 1 - 1) * Polynomial.X) (N := N)
    (lt_of_le_of_lt (natDegree_add_le _ _) (max_lt (by simp; omega)
      (lt_of_le_of_lt (natDegree_C_mul_le _ _) (by simp; omega))))
  simp only [eval_add, eval_C, eval_mul, eval_X] at hpoly
  rw [← alt_pow, DN]
  have e : ∀ n ∈ range (N + 1), (-1 : ℝ) ^ n * (N.choose n : ℝ) * expRule (n / N) =
      (-1 : ℝ) ^ n * (N.choose n : ℝ) * Real.exp (1 / N) ^ n -
        (-1 : ℝ) ^ n * (N.choose n : ℝ) * (1 + (Real.exp 1 - 1) * (n / N)) := by
    intro n _
    rw [expRule, ← Real.exp_nat_mul, mul_one_div]
    ring
  rw [sum_congr rfl e, sum_sub_distrib, hpoly, sub_zero]

/-- **Corollary 9.6**, third statement: the rule `β(x) = e^x - 1 - (e - 1)x`, `γ = 0` is analytic
(entire), has `L_even = L_odd = 0`, and the first-order change of `g(N,N;N)` along it is
`s_N (1 - e^{1/N})^N ≠ 0`. -/
theorem expRule_deriv {N : ℕ} (hN : 2 ≤ N) :
    HasDerivAt (fun ε => productMatrix (ruleArray expRule (fun _ => 0) N ε) N (Fin.last N) (Fin.last N))
      (sN N * (1 - Real.exp (1 / N)) ^ N) 0 ∧ sN N * (1 - Real.exp (1 / N)) ^ N ≠ 0 := by
  constructor
  · have h := analytic_rule_deriv expRule (fun _ => 0) hN
    rw [expRule_L.1, expRule_L.2] at h
    simp only [mul_zero, add_zero, sub_zero, ite_self] at h
    rwa [DN_expRule hN] at h
  · have hC : (0 : ℝ) < (N - 1).choose ((N - 1) / 2) := by exact_mod_cast Nat.choose_pos (by omega)
    have hs : sN N ≠ 0 := by
      rw [sN]; exact div_ne_zero (pow_ne_zero _ (by norm_num)) hC.ne'
    have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
    have he : 1 - Real.exp (1 / N) ≠ 0 := by
      have := Real.one_lt_exp_iff.mpr (one_div_pos.mpr hN0); linarith
    exact mul_ne_zero hs (pow_ne_zero _ he)

end Szkraw
