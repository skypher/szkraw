import Szkraw.NorlundU
import Szkraw.NorlundResidue
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.NumberTheory.Real.Irrational

/-!
# Lemma 9.5: the Nörlund–Rice bound

Let `U(x) = ∫_0^1 log|x - t| dt` and `Ω = {U ≤ -1}`. If `f` is holomorphic on an open set
containing `Ω`, then `Σ_{n=0}^N (-1)^n C(N,n) f(n/N) = O(√N e^{-ηN})` for some `η > 0`.

The cycle `Γ` of the paper is the boundary of a finite union `S` of squares of a fixed grid whose
origin has irrational coordinates, so that no node `k/N` lies on a grid line. The squares of `S` are
those meeting `{U ≤ -1 + η}`; the edges between `S` and its complement lie in `{U ≥ -1 + η}`.
-/

namespace Szkraw

open Complex MeasureTheory intervalIntegral Set Finset Metric
open scoped Interval

/-- **Margin**: there are `δ > 0` and `0 < η ≤ 1` such that every point within `δ` of
`{U ≤ -1 + η}` lies in `D`. -/
theorem exists_margin {D : Set ℂ} (hD : IsOpen D) (hΩ : {x : ℂ | Ulog x ≤ -1} ⊆ D) :
    ∃ δ > 0, ∃ η, 0 < η ∧ η ≤ 1 ∧ ∀ y, Ulog y ≤ -1 + η → ∀ z, dist z y < δ → z ∈ D := by
  have hbdd : ∀ c : ℝ, Bornology.IsBounded {x : ℂ | Ulog x ≤ c} := fun c =>
    isBounded_closedBall.subset fun x hx => by
      rw [mem_closedBall, dist_zero_right]; exact norm_le_of_Ulog_le hx
  have hcl : ∀ c : ℝ, IsClosed {x : ℂ | Ulog x ≤ c} := fun c => isClosed_le continuous_Ulog continuous_const
  set K := {x : ℂ | Ulog x ≤ -1}
  have hK : IsCompact K := isCompact_of_isClosed_isBounded (hcl _) (hbdd _)
  obtain ⟨δ₀, hδ₀, hsub⟩ := hK.exists_cthickening_subset_open hD hΩ
  set L := {x : ℂ | Ulog x ≤ 0} ∩ (thickening (δ₀ / 2) K)ᶜ
  have hL : IsCompact L := isCompact_of_isClosed_isBounded ((hcl 0).inter isOpen_thickening.isClosed_compl)
    ((hbdd 0).subset inter_subset_left)
  -- a level `η` with `{U ≤ -1 + η} ⊆ thickening (δ₀/2) K`
  obtain ⟨η, hη, hη1, hηK⟩ : ∃ η, 0 < η ∧ η ≤ 1 ∧ ∀ y, Ulog y ≤ -1 + η → y ∈ thickening (δ₀ / 2) K := by
    rcases L.eq_empty_or_nonempty with hE | hne
    · refine ⟨1, one_pos, le_rfl, fun y hy => ?_⟩
      by_contra hy'
      have : y ∈ L := ⟨by simp only [mem_ofPred_eq]; linarith, hy'⟩
      rw [hE] at this; exact this
    · obtain ⟨y₀, hy₀, hmin⟩ := hL.exists_isMinOn hne continuous_Ulog.continuousOn
      have hm : -1 < Ulog y₀ := by
        by_contra hle
        exact hy₀.2 (self_subset_thickening (half_pos hδ₀) K (not_lt.mp hle))
      refine ⟨min 1 ((Ulog y₀ + 1) / 2), lt_min one_pos (by linarith), min_le_left _ _, fun y hy => ?_⟩
      by_contra hy'
      have h1 : min 1 ((Ulog y₀ + 1) / 2) ≤ (Ulog y₀ + 1) / 2 := min_le_right _ _
      have hyL : y ∈ L := ⟨by simp only [mem_ofPred_eq]; linarith [min_le_left 1 ((Ulog y₀ + 1) / 2)], hy'⟩
      have := hmin hyL
      simp only [mem_ofPred_eq] at this
      linarith
  refine ⟨δ₀ / 2, half_pos hδ₀, η, hη, hη1, fun y hy z hz => hsub ?_⟩
  obtain ⟨k, hk, hyk⟩ := mem_thickening_iff.mp (hηK y hy)
  exact mem_cthickening_of_dist_le z k δ₀ K hk (by linarith [dist_triangle z y k])

variable {c : ℂ} {h : ℝ}

theorem mem_sqSet_iff (hh : 0 < h) {p : ℤ × ℤ} {x : ℂ} :
    x ∈ sqSet c h p ↔ (c.re + p.1 * h ≤ x.re ∧ x.re ≤ c.re + p.1 * h + h) ∧
      (c.im + p.2 * h ≤ x.im ∧ x.im ≤ c.im + p.2 * h + h) := by
  simp only [sqSet, mem_reProdIm, sqLo_re, sqLo_im, Int.cast_add, Int.cast_one]
  rw [Set.uIcc_of_le (by nlinarith), Set.uIcc_of_le (by nlinarith)]
  simp only [Set.mem_Icc]
  constructor <;> rintro ⟨⟨h1, h2⟩, h3, h4⟩ <;> refine ⟨⟨h1, ?_⟩, h3, ?_⟩ <;> linarith

/-- A grid square has diameter at most `2h`. -/
theorem sq_dist_le (hh : 0 < h) {p : ℤ × ℤ} {y z : ℂ} (hy : y ∈ sqSet c h p) (hz : z ∈ sqSet c h p) :
    dist z y ≤ 2 * h := by
  rw [mem_sqSet_iff hh] at hy hz
  rw [dist_eq_norm]
  refine (norm_le_abs_re_add_abs_im _).trans ?_
  rw [sub_re, sub_im]
  have h1 : |z.re - y.re| ≤ h := abs_le.mpr ⟨by linarith, by linarith⟩
  have h2 : |z.im - y.im| ≤ h := abs_le.mpr ⟨by linarith, by linarith⟩
  linarith

/-- Stirling's upper bound `N! ≤ e √N N^N e^{-N}`. -/
theorem factorial_le_stirling {N : ℕ} (hN : 1 ≤ N) :
    (N.factorial : ℝ) ≤ Real.exp 1 * Real.sqrt N * ((N : ℝ) ^ N * Real.exp (-N)) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have h1 : Stirling.stirlingSeq N ≤ Real.exp 1 / Real.sqrt 2 := by
    rw [← Stirling.stirlingSeq_one]
    have := Stirling.stirlingSeq'_antitone (Nat.zero_le (N - 1))
    simp only [Function.comp, Nat.succ_eq_add_one, zero_add] at this
    rwa [Nat.sub_add_cancel hN] at this
  have hpos : 0 < Real.sqrt (2 * N) * ((N : ℝ) / Real.exp 1) ^ N :=
    mul_pos (Real.sqrt_pos.mpr (by positivity)) (pow_pos (div_pos hN0 (Real.exp_pos 1)) N)
  rw [Stirling.stirlingSeq, div_le_iff₀ hpos] at h1
  have hs : Real.sqrt (2 * N) = Real.sqrt 2 * Real.sqrt N := Real.sqrt_mul (by norm_num) _
  have he : ((N : ℝ) / Real.exp 1) ^ N = (N : ℝ) ^ N * Real.exp (-N) := by
    rw [div_pow, ← Real.exp_nat_mul, mul_one, Real.exp_neg, div_eq_mul_inv]
  rw [hs, he] at h1
  have h2 : Real.sqrt 2 ≠ 0 := by positivity
  calc _ ≤ _ := h1
    _ = _ := by field_simp

/-- On `{U ≥ -1 + η}` at distance at least `d` from `[0,1]`,
`|1/ω_N(x)| ≤ exp(N(1 - η) + 1/d - log d)`. -/
theorem inv_nodal_bound {x : ℂ} {η d : ℝ} (hd : 0 < d) (hx : ∀ t ∈ Icc (0 : ℝ) 1, d ≤ ‖x - t‖)
    (hU : -1 + η ≤ Ulog x) {N : ℕ} (hN : 1 ≤ N) :
    ‖(nodalN N x)⁻¹‖ ≤ Real.exp (N * (1 - η) + 1 / d - Real.log d) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hpos : ∀ k ∈ range (N + 1), 0 < ‖x - (k : ℂ) / N‖ := by
    intro k hk
    have hk' : (k : ℝ) ≤ N := by exact_mod_cast Nat.lt_succ_iff.mp (mem_range.mp hk)
    have := hx ((k : ℝ) / N) ⟨by positivity, by rw [div_le_one hN0]; exact hk'⟩
    push_cast at this
    linarith
  have hnorm : ‖nodalN N x‖ = Real.exp (∑ k ∈ range (N + 1), Real.log ‖x - (k : ℂ) / N‖) := by
    rw [nodalN, norm_prod, Real.exp_sum]
    exact prod_congr rfl fun k hk => (Real.exp_log (hpos k hk)).symm
  have hR := riemann_lower hd hx hN
  rw [norm_inv, hnorm, ← Real.exp_neg, Real.exp_le_exp]
  nlinarith

theorem hEdge_norm_le (hh : 0 < h) (F : ℂ → ℂ) (q : ℤ × ℤ) {B : ℝ}
    (hF : ∀ x : ℝ, x ∈ [[c.re + q.1 * h, c.re + (q.1 + 1) * h]] → ‖F (x + (c.im + q.2 * h) * I)‖ ≤ B) :
    ‖hEdge c h F q‖ ≤ B * h := by
  unfold hEdge
  refine (norm_integral_le_of_norm_le_const fun x hx => hF x (uIoc_subset_uIcc hx)).trans (le_of_eq ?_)
  rw [show c.re + (q.1 + 1) * h - (c.re + q.1 * h) = h by ring, abs_of_pos hh]

theorem vEdge_norm_le (hh : 0 < h) (F : ℂ → ℂ) (q : ℤ × ℤ) {B : ℝ}
    (hF : ∀ y : ℝ, y ∈ [[c.im + q.2 * h, c.im + (q.2 + 1) * h]] → ‖F ((c.re + q.1 * h : ℝ) + y * I)‖ ≤ B) :
    ‖vEdge c h F q‖ ≤ B * h := by
  unfold vEdge
  refine (norm_integral_le_of_norm_le_const fun y hy => hF y (uIoc_subset_uIcc hy)).trans (le_of_eq ?_)
  rw [show c.im + (q.2 + 1) * h - (c.im + q.2 * h) = h by ring, abs_of_pos hh]

/-- A point of the horizontal edge `H(q)` lies in the squares `q` and `q - (0,1)`. -/
theorem hEdge_pt_mem (hh : 0 < h) (q : ℤ × ℤ) {x : ℝ} (hx : x ∈ [[c.re + q.1 * h, c.re + (q.1 + 1) * h]]) :
    ((x : ℂ) + (c.im + q.2 * h) * I) ∈ sqSet c h q ∧
      ((x : ℂ) + (c.im + q.2 * h) * I) ∈ sqSet c h (q.1, q.2 - 1) := by
  rw [Set.uIcc_of_le (by nlinarith)] at hx
  have hre : ((x : ℂ) + (c.im + q.2 * h) * I).re = x := by simp
  have him : ((x : ℂ) + (c.im + q.2 * h) * I).im = c.im + q.2 * h := by simp
  rw [mem_sqSet_iff hh, mem_sqSet_iff hh, hre, him]
  simp only [Int.cast_sub, Int.cast_one]
  refine ⟨⟨⟨hx.1, ?_⟩, ?_, ?_⟩, ⟨hx.1, ?_⟩, ?_, ?_⟩ <;> nlinarith [hx.1, hx.2]

/-- A point of the vertical edge `V(q)` lies in the squares `q` and `q - (1,0)`. -/
theorem vEdge_pt_mem (hh : 0 < h) (q : ℤ × ℤ) {y : ℝ} (hy : y ∈ [[c.im + q.2 * h, c.im + (q.2 + 1) * h]]) :
    (((c.re + q.1 * h : ℝ) : ℂ) + y * I) ∈ sqSet c h q ∧
      (((c.re + q.1 * h : ℝ) : ℂ) + y * I) ∈ sqSet c h (q.1 - 1, q.2) := by
  rw [Set.uIcc_of_le (by nlinarith)] at hy
  have hre : (((c.re + q.1 * h : ℝ) : ℂ) + y * I).re = c.re + q.1 * h := by simp
  have him : (((c.re + q.1 * h : ℝ) : ℂ) + y * I).im = y := by simp
  rw [mem_sqSet_iff hh, mem_sqSet_iff hh, hre, him]
  simp only [Int.cast_sub, Int.cast_one]
  refine ⟨⟨⟨?_, ?_⟩, hy.1, ?_⟩, ⟨?_, ?_⟩, hy.1, ?_⟩ <;> nlinarith [hy.1, hy.2]

theorem sum_le_card_mul_of_subset {T : Finset (ℤ × ℤ)} {g : ℤ × ℤ → ℝ} {b : ℝ} {n : ℕ} (hb : 0 ≤ b)
    (hT : T.card ≤ n) (hg : ∀ q ∈ T, g q ≤ b) : ∑ q ∈ T, g q ≤ n * b := by
  refine (sum_le_card_nsmul T g b hg).trans ?_
  rw [nsmul_eq_mul]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hT) hb

/-- **Lemma 9.5 (Nörlund–Rice bound).** If `f` is holomorphic on an open set `D` containing
`Ω = {U ≤ -1}`, then `Σ_{n=0}^N (-1)^n C(N,n) f(n/N) = O(√N e^{-ηN})` for some `η > 0`. -/
theorem norlund_rice (f : ℂ → ℂ) (D : Set ℂ) (hD : IsOpen D) (hf : DifferentiableOn ℂ f D)
    (hΩ : {x : ℂ | Ulog x ≤ -1} ⊆ D) :
    ∃ η > 0, ∃ C : ℝ, ∀ N : ℕ, 1 ≤ N → ‖altBinom N f‖ ≤ C * Real.sqrt N * Real.exp (-(η * N)) := by
  classical
  obtain ⟨δ, hδ, η, hη, hη1, hηD⟩ := exists_margin hD hΩ
  -- the grid: mesh `h = 1/M` with `2h < δ`, origin `c = √2 + √2 i`
  obtain ⟨M, hM⟩ := exists_nat_gt (2 / δ)
  have hM0 : (0 : ℝ) < M := lt_trans (by positivity) hM
  have hM1 : (1 : ℝ) ≤ M := by
    have : M ≠ 0 := by rintro rfl; simp at hM0
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr this
  set h : ℝ := (M : ℝ)⁻¹ with hhdef
  have hh : 0 < h := inv_pos.mpr hM0
  have hh1 : h ≤ 1 := inv_le_one_of_one_le₀ hM1
  have hhM : h * M = 1 := inv_mul_cancel₀ hM0.ne'
  have hhδ : 2 * h < δ := by
    rw [div_lt_iff₀ hδ] at hM
    have : 2 * h * M < δ * M := by rw [mul_assoc, hhM]; linarith
    exact lt_of_mul_lt_mul_right this hM0.le
  obtain ⟨c, hcre, hcim⟩ : ∃ c : ℂ, c.re = Real.sqrt 2 ∧ c.im = Real.sqrt 2 := ⟨⟨_, _⟩, rfl, rfl⟩
  have hs0 := Real.sqrt_nonneg 2
  have hs2 : Real.sqrt 2 ≤ 2 := by nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  -- the nodes lie off the grid, in `{U ≤ -1}`
  have hnode : ∀ N k : ℕ, (k : ℂ) / N = (((k : ℝ) / N : ℝ) : ℂ) := fun N k => by push_cast; rfl
  have hoff : ∀ N k : ℕ, 1 ≤ N → OffGrid c h ((k : ℂ) / N) := by
    intro N k hN
    rw [hnode]
    refine ⟨fun i hi => ?_, fun j hj => ?_⟩
    · simp only [ofReal_re, hcre] at hi
      rw [div_eq_iff hh.ne'] at hi
      apply irrational_sqrt_two.ne_rat ((k : ℚ) / N - (i : ℚ) / M)
      push_cast
      rw [div_eq_mul_inv (i : ℝ)]
      linarith
    · simp only [ofReal_im, hcim] at hj
      rw [div_eq_iff hh.ne'] at hj
      apply irrational_sqrt_two.ne_rat (-(j : ℚ) / M)
      push_cast
      rw [neg_div, div_eq_mul_inv (j : ℝ)]
      linarith
  have hnodeU : ∀ N k : ℕ, 1 ≤ N → k ≤ N → Ulog ((k : ℂ) / N) ≤ -1 := by
    intro N k hN hk
    rw [hnode]
    exact Ulog_le_of_mem (by positivity) (by rw [div_le_one (by exact_mod_cast hN)]; exact_mod_cast hk)
  -- the squares meeting `{U ≤ -1 + η}`
  set R : ℤ := 5 * M with hR
  set S : Finset (ℤ × ℤ) := (Finset.Icc (-R) R ×ˢ Finset.Icc (-R) R).filter
    (fun p => ∃ y ∈ sqSet c h p, Ulog y ≤ -1 + η) with hSdef
  have hSmem : ∀ p, p ∈ S ↔ ∃ y ∈ sqSet c h p, Ulog y ≤ -1 + η := by
    intro p
    rw [hSdef, Finset.mem_filter]
    refine ⟨fun hp => hp.2, fun hp => ⟨?_, hp⟩⟩
    obtain ⟨y, hy, hU⟩ := hp
    have hy2 : ‖y‖ ≤ 2 := by
      have h1 := norm_le_of_Ulog_le hU
      have h2 : Real.exp (-1 + η) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
      linarith
    rw [mem_sqSet_iff hh, hcre, hcim] at hy
    have hre := abs_le.mp ((abs_re_le_norm y).trans hy2)
    have him := abs_le.mp ((abs_im_le_norm y).trans hy2)
    have e1 : (p.1 : ℝ) = p.1 * h * M := by rw [mul_assoc, hhM, mul_one]
    have e2 : (p.2 : ℝ) = p.2 * h * M := by rw [mul_assoc, hhM, mul_one]
    have b1 : (p.1 : ℝ) * h * M ≤ 5 * M := mul_le_mul_of_nonneg_right (by linarith) hM0.le
    have b2 : -5 * (M : ℝ) ≤ p.1 * h * M := by
      have := mul_le_mul_of_nonneg_right (show -5 ≤ (p.1 : ℝ) * h by linarith) hM0.le
      linarith
    have b3 : (p.2 : ℝ) * h * M ≤ 5 * M := mul_le_mul_of_nonneg_right (by linarith) hM0.le
    have b4 : -5 * (M : ℝ) ≤ p.2 * h * M := by
      have := mul_le_mul_of_nonneg_right (show -5 ≤ (p.2 : ℝ) * h by linarith) hM0.le
      linarith
    rw [Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc]
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · have : (-(5 * M : ℤ) : ℝ) ≤ p.1 := by push_cast; linarith
      exact_mod_cast this
    · have : (p.1 : ℝ) ≤ ((5 * M : ℤ) : ℝ) := by push_cast; linarith
      exact_mod_cast this
    · have : (-(5 * M : ℤ) : ℝ) ≤ p.2 := by push_cast; linarith
      exact_mod_cast this
    · have : (p.2 : ℝ) ≤ ((5 * M : ℤ) : ℝ) := by push_cast; linarith
      exact_mod_cast this
  have hSD : ∀ p ∈ S, sqSet c h p ⊆ D := by
    intro p hp z hz
    obtain ⟨y, hy, hU⟩ := (hSmem p).mp hp
    exact hηD y hU z (lt_of_le_of_lt (sq_dist_le hh hy hz) hhδ)
  have hin : ∀ N : ℕ, 1 ≤ N → ∀ k ∈ range (N + 1), sqIdx c h ((k : ℂ) / N) ∈ S := by
    intro N hN k hk
    have hk' := Nat.lt_succ_iff.mp (mem_range.mp hk)
    rw [hSmem]
    refine ⟨(k : ℂ) / N, ?_, by linarith [hnodeU N k hN hk']⟩
    obtain ⟨h1, h2, h3, h4⟩ := inside_sqIdx hh (hoff N k hN)
    exact ⟨Set.mem_uIcc_of_le h1.le h2.le, Set.mem_uIcc_of_le h3.le h4.le⟩
  -- the compact set `E` carrying the boundary edges
  set E : Set ℂ := (⋃ p ∈ (S : Set (ℤ × ℤ)), sqSet c h p) ∩ {y | -1 + η ≤ Ulog y} with hEdef
  have hEc : IsCompact E :=
    (S.finite_toSet.isCompact_biUnion fun p _ => isCompact_uIcc.reProdIm isCompact_uIcc).inter_right
      (isClosed_le continuous_const continuous_Ulog)
  have hED : E ⊆ D := fun y hy => by
    obtain ⟨p, hp, hyp⟩ := mem_iUnion₂.mp hy.1
    exact hSD p hp hyp
  have hEmem : ∀ x p₁ p₂, p₁ ∈ S → p₂ ∉ S → x ∈ sqSet c h p₁ → x ∈ sqSet c h p₂ → x ∈ E := by
    intro x p₁ p₂ h1 h2 hx1 hx2
    refine ⟨mem_iUnion₂.mpr ⟨p₁, Finset.mem_coe.mpr h1, hx1⟩, ?_⟩
    by_contra hlt
    simp only [mem_ofPred_eq, not_le] at hlt
    exact h2 ((hSmem p₂).mpr ⟨x, hx2, hlt.le⟩)
  obtain ⟨d, hd, hdE⟩ : ∃ d > 0, ∀ y ∈ E, ∀ t ∈ Icc (0 : ℝ) 1, d ≤ ‖y - t‖ := by
    set I01 : Set ℂ := (fun t : ℝ => (t : ℂ)) '' Icc 0 1
    have hI : IsClosed I01 := (isCompact_Icc.image continuous_ofReal).isClosed
    have hIne : I01.Nonempty := (Set.nonempty_Icc.mpr zero_le_one).image _
    rcases E.eq_empty_or_nonempty with he | hne
    · exact ⟨1, one_pos, fun y hy => by rw [he] at hy; exact absurd hy (Set.notMem_empty y)⟩
    · obtain ⟨y₀, hy₀, hmin⟩ := hEc.exists_isMinOn hne (continuous_infDist_pt I01).continuousOn
      have hy₀I : y₀ ∉ I01 := by
        rintro ⟨t, ht, rfl⟩
        have := hy₀.2
        simp only [mem_ofPred_eq] at this
        linarith [Ulog_le_of_mem ht.1 ht.2]
      refine ⟨infDist y₀ I01, (hI.notMem_iff_infDist_pos hIne).mp hy₀I, fun y hy t ht => ?_⟩
      rw [← dist_eq_norm]
      exact (hmin hy).trans (infDist_le_dist_of_mem (Set.mem_image_of_mem _ ht))
  obtain ⟨B₀, hB₀⟩ := hEc.exists_bound_of_continuousOn (hf.continuousOn.mono hED)
  set B := max B₀ 0
  have hB : 0 ≤ B := le_max_right _ _
  -- the constant
  refine ⟨η, hη, 4 * S.card * B * h * Real.exp (1 / d - Real.log d) * Real.exp 1 / (2 * Real.pi),
    fun N hN => ?_⟩
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  set Λ := Real.exp (N * (1 - η) + 1 / d - Real.log d) with hΛdef
  set F : ℂ → ℂ := fun x => f x * (nodalN N x)⁻¹ with hFdef
  have hFE : ∀ x ∈ E, ‖F x‖ ≤ B * Λ := by
    intro x hx
    rw [hFdef, norm_mul]
    exact mul_le_mul ((hB₀ x hx).trans (le_max_left _ _)) (inv_nodal_bound hd (hdE x hx) hx.2 hN)
      (norm_nonneg _) hB
  have hbd : 0 ≤ B * Λ * h := by positivity
  -- the boundary edges
  have hsum := gridSum_bound c h F S
  have s1 : ∑ q ∈ S \ shiftSet S (0, 1), ‖hEdge c h F q‖ ≤ S.card * (B * Λ * h) := by
    refine sum_le_card_mul_of_subset hbd (Finset.card_le_card Finset.sdiff_subset) fun q hq => ?_
    obtain ⟨hqS, hq'⟩ := Finset.mem_sdiff.mp hq
    refine hEdge_norm_le hh F q fun x hx => hFE _ ?_
    obtain ⟨m1, m2⟩ := hEdge_pt_mem hh q hx
    refine hEmem _ q (q.1, q.2 - 1) hqS (fun hS' => hq' ?_) m1 m2
    exact Finset.mem_image.mpr ⟨_, hS', by ext <;> simp⟩
  have s2 : ∑ q ∈ shiftSet S (0, 1) \ S, ‖hEdge c h F q‖ ≤ S.card * (B * Λ * h) := by
    refine sum_le_card_mul_of_subset hbd ((Finset.card_le_card Finset.sdiff_subset).trans Finset.card_image_le) fun q hq => ?_
    obtain ⟨hqS, hq'⟩ := Finset.mem_sdiff.mp hq
    obtain ⟨p, hp, hpq⟩ := Finset.mem_image.mp hqS
    refine hEdge_norm_le hh F q fun x hx => hFE _ ?_
    obtain ⟨m1, m2⟩ := hEdge_pt_mem hh q hx
    refine hEmem _ (q.1, q.2 - 1) q ?_ hq' m2 m1
    rw [← hpq]; simpa using hp
  have s3 : ∑ q ∈ shiftSet S (1, 0) \ S, ‖vEdge c h F q‖ ≤ S.card * (B * Λ * h) := by
    refine sum_le_card_mul_of_subset hbd ((Finset.card_le_card Finset.sdiff_subset).trans Finset.card_image_le) fun q hq => ?_
    obtain ⟨hqS, hq'⟩ := Finset.mem_sdiff.mp hq
    obtain ⟨p, hp, hpq⟩ := Finset.mem_image.mp hqS
    refine vEdge_norm_le hh F q fun y hy => hFE _ ?_
    obtain ⟨m1, m2⟩ := vEdge_pt_mem hh q hy
    refine hEmem _ (q.1 - 1, q.2) q ?_ hq' m2 m1
    rw [← hpq]; simpa using hp
  have s4 : ∑ q ∈ S \ shiftSet S (1, 0), ‖vEdge c h F q‖ ≤ S.card * (B * Λ * h) := by
    refine sum_le_card_mul_of_subset hbd (Finset.card_le_card Finset.sdiff_subset) fun q hq => ?_
    obtain ⟨hqS, hq'⟩ := Finset.mem_sdiff.mp hq
    refine vEdge_norm_le hh F q fun y hy => hFE _ ?_
    obtain ⟨m1, m2⟩ := vEdge_pt_mem hh q hy
    refine hEmem _ q (q.1 - 1, q.2) hqS (fun hS' => hq' ?_) m1 m2
    exact Finset.mem_image.mpr ⟨_, hS', by ext <;> simp⟩
  have key : ‖∑ p ∈ S, sqInt c h F p‖ ≤ 4 * S.card * (B * Λ * h) := by linarith
  -- the residue identity
  have hnorm : ‖∑ p ∈ S, sqInt c h F p‖ = 2 * Real.pi * ((N : ℝ) ^ N / N.factorial) * ‖altBinom N f‖ := by
    rw [hFdef, residue_identity hh f D hD hf S hSD hN (fun k _ => hoff N k hN) (hin N hN), sum_nodeW f hN]
    simp [abs_of_pos Real.pi_pos]
    ring
  have hNN : (0 : ℝ) < (N : ℝ) ^ N := pow_pos hN0 N
  have hfac : (0 : ℝ) < N.factorial := by exact_mod_cast Nat.factorial_pos N
  have hpos : 0 < 2 * Real.pi * ((N : ℝ) ^ N / N.factorial) := by positivity
  have h1 : ‖altBinom N f‖ ≤ 4 * S.card * (B * Λ * h) / (2 * Real.pi * ((N : ℝ) ^ N / N.factorial)) := by
    rw [le_div_iff₀ hpos]; linarith
  have hΛ : Λ * Real.exp (-N) = Real.exp (1 / d - Real.log d) * Real.exp (-(η * N)) := by
    rw [hΛdef, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have hst := factorial_le_stirling hN
  calc ‖altBinom N f‖ ≤ 4 * S.card * (B * Λ * h) / (2 * Real.pi * ((N : ℝ) ^ N / N.factorial)) := h1
    _ = 4 * S.card * B * h * Λ * N.factorial / (2 * Real.pi * (N : ℝ) ^ N) := by
      rw [mul_div_assoc', div_div_eq_mul_div]; ring
    _ ≤ 4 * S.card * B * h * Λ * (Real.exp 1 * Real.sqrt N * ((N : ℝ) ^ N * Real.exp (-N))) /
        (2 * Real.pi * (N : ℝ) ^ N) := by gcongr
    _ = 4 * S.card * B * h * (Λ * Real.exp (-N)) * Real.exp 1 * Real.sqrt N / (2 * Real.pi) := by
      rw [show 4 * S.card * B * h * Λ * (Real.exp 1 * Real.sqrt N * ((N : ℝ) ^ N * Real.exp (-N))) =
        (4 * S.card * B * h * (Λ * Real.exp (-N)) * Real.exp 1 * Real.sqrt N) * (N : ℝ) ^ N by ring,
        mul_div_mul_right _ _ hNN.ne']
    _ = _ := by rw [hΛ]; ring

end Szkraw
