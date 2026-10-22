import Szkraw.KrawOne
import Szkraw.LowerGeneric
import Szkraw.RaiseTopMass
import Szkraw.ProductSmooth
import Szkraw.Stability
import Szkraw.Bandwidth
import Szkraw.AffineInvariance
import Szkraw.UniformRules

/-!
# Proposition 9.8: interior points near the symmetric endpoint

`lowK N r ε` is `K_{N,r}` with its top mass lowered by `ε`, in the fixed coordinate `x`: by
`TopMass.lean` its coefficients are `a_n A_n / A_{n+1}`, `c_n A_{n+1} / A_n`, `b_n = 1 - a_n - c_n`
with `A_n = 1 - ε Σ_{j<n} C(N,j) r^{-j}`. Along `r = 1 - Λ ε` every triangle coefficient becomes
positive for large `Λ` and small `ε > 0`.
-/

namespace Szkraw

open Finset Filter Topology

variable {N : ℕ}

/-- `A_n = 1 - ε Σ_{j<n} C(N,j) r^{-j}`. -/
noncomputable def lowA (N : ℕ) (r ε : ℝ) (n : ℕ) : ℝ := 1 - ε * ∑ j ∈ range n, (N.choose j : ℝ) / r ^ j

/-- `K_{N,r}` with the top mass lowered by `ε`, in the fixed coordinate `x`. -/
noncomputable def lowK (N : ℕ) (r ε : ℝ) : Coefficients N where
  a n := ((N : ℝ) - n) / N * lowA N r ε n / lowA N r ε (n + 1)
  b n := 1 - ((N : ℝ) - n) / N * lowA N r ε n / lowA N r ε (n + 1) - r * n / N * lowA N r ε (n + 1) / lowA N r ε n
  c n := r * n / N * lowA N r ε (n + 1) / lowA N r ε n

theorem lowA_zero (r : ℝ) (n : ℕ) : lowA N r 0 n = 1 := by simp [lowA]

/-- At `ε = 0` the family is `K_{N,r}`. -/
theorem lowK_zero (hN : 1 ≤ N) (r : ℝ) :
    ∀ m, m ≤ N + 1 → productMatrix (lowK N r 0) m = productMatrix (krawCoefficients N r) m := by
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  apply product_congr
  · intro i _; simp only [lowK, lowA_zero, div_one, mul_one, krawCoefficients]
  · intro i _; simp only [lowK, lowA_zero, div_one, mul_one, krawCoefficients]; field_simp; ring
  · intro i _; simp only [lowK, lowA_zero, div_one, mul_one, krawCoefficients]

/-- For `0 < r ≤ 1` the family is the lowered system of `TopMass.lean`. -/
theorem lowK_eq_epsRaw (hN : 1 ≤ N) {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) (ε : ℝ) :
    ∀ m, m ≤ N + 1 → productMatrix (epsRaw (kv N r) (kx N r) (kw N r) (-ε)) m = productMatrix (lowK N r ε) m := by
  have hA : ∀ n, n ≤ N + 1 → Aeps (kv N r) (kx N r) (kw N r) (-ε) n = lowA N r ε n := by
    intro n hn
    rw [Aeps, lowA, Ssum]
    have : ∑ k ∈ range n, piw (kv N r) (kx N r) (kw N r) k = ∑ j ∈ range n, (N.choose j : ℝ) / r ^ j :=
      sum_congr rfl fun j hj => k_piw hN hr hr1 j (by rw [mem_range] at hj; omega)
    rw [this]; ring
  apply product_congr
  · intro i hi
    simp only [epsRaw, lowK, hA i (by omega), hA (i + 1) (by omega), kv_a i hi]
  · intro i hi
    simp only [epsRaw, lowK, hA i (by omega), hA (i + 1) (by omega), kv_a i hi, kv_c]
  · intro i hi
    simp only [epsRaw, lowK, hA i (by omega), hA (i + 1) (by omega), kv_c]

/-- The family is smooth in `(r, ε)` near `(1, 0)`. -/
theorem lowK_contDiffAt (m : ℕ) (hm : m ≤ N) (n k : Fin (N + 1)) :
    ContDiffAt ℝ 1 (fun p : ℝ × ℝ => productMatrix (lowK N p.1 p.2) m n k) (1, 0) := by
  have hA : ∀ i, ContDiffAt ℝ 1 (fun p : ℝ × ℝ => lowA N p.1 p.2 i) (1, 0) := by
    intro i
    simp only [lowA]
    refine contDiffAt_const.sub (contDiffAt_snd.mul (ContDiffAt.sum fun j _ => ?_))
    exact contDiffAt_const.div (contDiffAt_fst.pow j) (by simp)
  have hA0 : ∀ i, lowA N (1, (0 : ℝ)).1 (1, (0 : ℝ)).2 i ≠ 0 := fun i => by simp [lowA]
  have hcoef : ∀ i, ContDiffAt ℝ 1 (fun p : ℝ × ℝ => (lowK N p.1 p.2).a i) (1, 0) ∧
      ContDiffAt ℝ 1 (fun p : ℝ × ℝ => (lowK N p.1 p.2).b i) (1, 0) ∧
      ContDiffAt ℝ 1 (fun p : ℝ × ℝ => (lowK N p.1 p.2).c i) (1, 0) := by
    intro i
    have ha : ContDiffAt ℝ 1 (fun p : ℝ × ℝ => (lowK N p.1 p.2).a i) (1, 0) :=
      ((contDiffAt_const.mul (hA i)).div (hA (i + 1)) (hA0 _))
    have hc : ContDiffAt ℝ 1 (fun p : ℝ × ℝ => (lowK N p.1 p.2).c i) (1, 0) :=
      ((((contDiffAt_fst.mul contDiffAt_const).div_const _).mul (hA (i + 1))).div (hA i) (hA0 _))
    refine ⟨ha, ?_, hc⟩
    exact (contDiffAt_const.sub ha).sub hc
  have hpos : ∀ i, i < m → (lowK N (1, (0 : ℝ)).1 (1, (0 : ℝ)).2).a i ≠ 0 := by
    intro i hi'
    have hi : i < N := by omega
    simp only [lowK, lowA_zero, div_one, mul_one]
    have : (i : ℝ) < N := by exact_mod_cast hi
    exact (div_pos (by linarith) (by linarith)).ne'
  exact productMatrix_contDiffAt (fun p : ℝ × ℝ => lowK N p.1 p.2) (1, 0) (fun i => (hcoef i).1)
    (fun i => (hcoef i).2.1) (fun i => (hcoef i).2.2) m hpos n k

/-! ### Derivatives of the family at `(1, 0)` -/

/-- `G(r, ε) = g(m,n;k)` of `lowK N r ε`. -/
noncomputable def lowG (N m : ℕ) (n k : Fin (N + 1)) (p : ℝ × ℝ) : ℝ := productMatrix (lowK N p.1 p.2) m n k

theorem lowG_diff (m : ℕ) (hm : m ≤ N) (n k : Fin (N + 1)) : DifferentiableAt ℝ (lowG N m n k) (1, 0) :=
  (lowK_contDiffAt m hm n k).differentiableAt one_ne_zero

/-- The partial derivative in `r` at `(1, 0)`. -/
theorem lowG_hasDerivAt_r (m : ℕ) (hm : m ≤ N) (n k : Fin (N + 1)) :
    HasDerivAt (fun r => lowG N m n k (r, 0)) (fderiv ℝ (lowG N m n k) (1, 0) (1, 0)) 1 :=
  by
    have hl : HasDerivAt (fun r : ℝ => (r, (0 : ℝ))) ((1 : ℝ), (0 : ℝ)) 1 :=
      (hasDerivAt_id (1 : ℝ)).prodMk (hasDerivAt_const (1 : ℝ) (0 : ℝ))
    exact (lowG_diff m hm n k).hasFDerivAt.comp_hasDerivAt (1 : ℝ) hl

/-- The partial derivative in `ε` at `(1, 0)`. -/
theorem lowG_hasDerivAt_e (m : ℕ) (hm : m ≤ N) (n k : Fin (N + 1)) :
    HasDerivAt (fun ε => lowG N m n k (1, ε)) (fderiv ℝ (lowG N m n k) (1, 0) (0, 1)) 0 :=
  by
    have hl : HasDerivAt (fun ε : ℝ => ((1 : ℝ), ε)) ((0 : ℝ), (1 : ℝ)) 0 :=
      (hasDerivAt_const (0 : ℝ) (1 : ℝ)).prodMk (hasDerivAt_id (0 : ℝ))
    exact (lowG_diff m hm n k).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hl

/-- The derivative along `r = 1 - Λ ε`. -/
theorem lowG_hasDerivAt_path (m : ℕ) (hm : m ≤ N) (n k : Fin (N + 1)) (Λ : ℝ) :
    HasDerivAt (fun ε => lowG N m n k (1 - Λ * ε, ε))
      (-Λ * fderiv ℝ (lowG N m n k) (1, 0) (1, 0) + fderiv ℝ (lowG N m n k) (1, 0) (0, 1)) 0 := by
  have h1 : HasDerivAt (fun ε : ℝ => 1 - Λ * ε) (-Λ) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).const_mul Λ).const_sub 1
  have hpath : HasDerivAt (fun ε : ℝ => (1 - Λ * ε, ε)) (-Λ, (1 : ℝ)) 0 := h1.prodMk (hasDerivAt_id (0 : ℝ))
  have hG : HasFDerivAt (lowG N m n k) (fderiv ℝ (lowG N m n k) (1, 0)) ((fun ε : ℝ => (1 - Λ * ε, ε)) 0) := by
    simpa using (lowG_diff m hm n k).hasFDerivAt
  have h := HasFDerivAt.comp_hasDerivAt (l := lowG N m n k) (f := fun ε : ℝ => (1 - Λ * ε, ε)) (0 : ℝ) hG hpath
  refine h.congr_deriv ?_
  have : ((-Λ, (1 : ℝ)) : ℝ × ℝ) = (-Λ) • ((1 : ℝ), (0 : ℝ)) + ((0 : ℝ), (1 : ℝ)) := by
    ext <;> simp
  rw [this, map_add, map_smul, smul_eq_mul]

theorem kraw_nonneg {r : ℝ} (hN : 1 ≤ N) (hr : 0 < r) (hr1 : r ≤ 1) (m : ℕ) (hm : m ≤ N) (n k : Fin (N + 1)) :
    0 ≤ productMatrix (krawCoefficients N r) m n k := by
  rw [kraw_g_formula hN (by linarith) m hm n k (ivl N 0 k (by omega)) (card_ivl _)]
  refine mul_nonneg (kraw_const_pos m n k hm (by omega) (by omega)).le ?_
  refine sum_nonneg fun S _ => sum_nonneg fun T _ => sum_nonneg fun J _ => ?_
  split_ifs
  · have : 0 ≤ 1 - r := by linarith
    positivity
  · rfl

/-- On a zero triple of `K_{N,1}` the `r`-derivative is `≤ 0`, and `< 0` when `m + n + k` is odd. -/
theorem lowG_dr (hN : 1 ≤ N) (m : ℕ) (hm : m ≤ N) (n k : Fin (N + 1)) (h1 : m ≤ n.val + k.val)
    (h2 : n.val ≤ m + k.val) (h3 : k.val ≤ m + n.val)
    (hz : productMatrix (krawCoefficients N 1) m n k = 0) :
    fderiv ℝ (lowG N m n k) (1, 0) (1, 0) ≤ 0 ∧
      ((m + n.val + k.val) % 2 = 1 → m + n.val + k.val ≤ 2 * N + 1 → fderiv ℝ (lowG N m n k) (1, 0) (1, 0) < 0) := by
  have hr := lowG_hasDerivAt_r m hm n k
  have heq : (fun r => lowG N m n k (r, 0)) = fun r => productMatrix (krawCoefficients N r) m n k := by
    funext r; simp only [lowG]; rw [lowK_zero hN r m (by omega)]
  rw [heq] at hr
  constructor
  · by_contra hpos
    push Not at hpos
    -- `g(r) < 0` just left of `1`
    have hneg := neg_right_of_deriv (f := fun s => productMatrix (krawCoefficients N (1 - s)) m n k)
      (d := -fderiv ℝ (lowG N m n k) (1, 0) (1, 0)) ?_ (by simp [hz]) (by linarith)
    · obtain ⟨ε₀, hε₀, hlt⟩ := hneg
      set s := min ε₀ (1 / 2) / 2
      have hs : 0 < s := by positivity
      have hs1 : s < ε₀ := by have := min_le_left ε₀ (1 / 2); simp only [s]; linarith
      have hs2 : s < 1 := by have := min_le_right ε₀ (1 / 2); simp only [s]; linarith
      have := hlt s hs hs1
      have := kraw_nonneg hN (by linarith : 0 < 1 - s) (by linarith) m hm n k
      linarith
    · have hr' : HasDerivAt (fun r => productMatrix (krawCoefficients N r) m n k)
          (fderiv ℝ (lowG N m n k) (1, 0) (1, 0)) (1 - 0) := by rw [sub_zero]; exact hr
      have h := HasDerivAt.comp (h₂ := fun r => productMatrix (krawCoefficients N r) m n k)
        (h := fun s : ℝ => 1 - s) (0 : ℝ) hr' ((hasDerivAt_id' (0 : ℝ)).const_sub 1)
      exact h.congr_deriv (by ring)
  · intro hodd hle
    obtain ⟨D, hD, hDer⟩ := kraw_deriv_neg hN m hm n k h1 h2 h3 hodd hle
    rw [hr.unique hDer]; exact hD

theorem kv_one_product (m : ℕ) (hm : m ≤ N + 1) :
    productMatrix (kv N 1) m = productMatrix (krawCoefficients N 1) m :=
  (product_congr (krawCoefficients N 1) (kv N 1) (fun i hi => (kraw_geometric_prefix N 1 one_pos i hi).1)
    (fun i hi => (kraw_geometric_prefix N 1 one_pos i hi).2.1)
    (fun i hi => (kraw_geometric_prefix N 1 one_pos i hi).2.2) m hm).symm

/-- On a triangle triple with `m + n + k > 2N`, lowering the top mass of `K_{N,1}` makes
`g(m,n;k)` grow: the `ε`-derivative of the family is positive. -/
theorem lowG_de (hN : 1 ≤ N) (m : ℕ) (hm : m ≤ N) (n k : Fin (N + 1)) (hbig : 2 * N < m + n.val + k.val) :
    0 < fderiv ℝ (lowG N m n k) (1, 0) (0, 1) := by
  have hDe := lowG_hasDerivAt_e m hm n k
  have heq : (fun ε => lowG N m n k (1, ε)) =
      fun ε => productMatrix (epsRaw (kv N 1) (kx N 1) (kw N 1) (-ε)) m n k := by
    funext ε; simp only [lowG]; rw [lowK_eq_epsRaw hN one_pos le_rfl ε m (by omega)]
  rw [heq] at hDe
  have hv := kv_admissible (N := N) hN one_pos le_rfl
  have hz : productMatrix (kv N 1) m n k = 0 := by
    rw [kv_one_product m (by omega)]; exact kraw1_zero hN m hm n k (Or.inr hbig)
  have hg := gen_g_deriv (kv N 1) hv (k_act hN one_pos le_rfl) (k_orth hN one_pos le_rfl)
    (k_nrm_pos hN one_pos le_rfl) kx_zero m hm n k hz hDe
  -- all tails vanish
  have htail : ∀ a b c : Fin (N + 1), 2 * N < a.val + b.val + c.val → tailG (kv N 1) a b c = 0 := by
    intro a b c habc
    refine sum_eq_zero fun l _ => ?_
    split_ifs with hl
    · rw [kv_one_product b.val (by omega)]
      exact kraw1_zero hN b.val (by omega) c l (Or.inr (by omega))
    · rfl
  rw [htail _ _ _ (by simp; omega), htail _ _ _ (by simp; omega), htail _ _ _ (by simp; omega)] at hg
  have hn := k_nrm_pos hN one_pos (le_refl (1 : ℝ)) k (by omega)
  nlinarith

/-- The constant `Λ_N`: a bound for `∂_ε G / (-∂_r G)` over the triangle. -/
noncomputable def lamN (N : ℕ) : ℝ :=
  ∑ z : Fin (N + 1) × Fin (N + 1) × Fin (N + 1),
    |fderiv ℝ (lowG N z.1 z.2.1 z.2.2) (1, 0) (0, 1)| / |fderiv ℝ (lowG N z.1 z.2.1 z.2.2) (1, 0) (1, 0)|

theorem lamN_nonneg : 0 ≤ lamN N := sum_nonneg fun _ _ => by positivity

/-- For `Λ > Λ_N`, every vanishing triangle coefficient of `K_{N,1}` has positive derivative along
`r = 1 - Λ ε`. -/
theorem path_deriv_pos (hN : 1 ≤ N) {Λ : ℝ} (hΛ : lamN N < Λ) (m : Fin (N + 1)) (n k : Fin (N + 1))
    (hT : Triangle m.val n.val k.val) (hz : productMatrix (krawCoefficients N 1) m n k = 0) :
    0 < -Λ * fderiv ℝ (lowG N m n k) (1, 0) (1, 0) + fderiv ℝ (lowG N m n k) (1, 0) (0, 1) := by
  obtain ⟨h1, h2, h3⟩ := hT
  set Dr := fderiv ℝ (lowG N m n k) (1, 0) (1, 0)
  set De := fderiv ℝ (lowG N m n k) (1, 0) (0, 1)
  have hΛ0 : 0 < Λ := lt_of_le_of_lt lamN_nonneg hΛ
  obtain ⟨hDr, hDr'⟩ := lowG_dr hN m (by omega) n k h1 h2 h3 hz
  by_cases hbig : 2 * N < m.val + n.val + k.val
  · have hDe := lowG_de hN m (by omega) n k hbig
    nlinarith
  · -- small zero triples are odd, with `Dr < 0`
    have hodd : (m.val + n.val + k.val) % 2 = 1 := by
      by_contra hev
      have := kraw1_pos hN m (by omega) n k h1 h2 h3 (by omega) (by omega)
      linarith
    have hDrn := hDr' hodd (by omega)
    have hle : |De| / |Dr| ≤ lamN N := by
      have := single_le_sum (f := fun z : Fin (N + 1) × Fin (N + 1) × Fin (N + 1) =>
        |fderiv ℝ (lowG N z.1 z.2.1 z.2.2) (1, 0) (0, 1)| / |fderiv ℝ (lowG N z.1 z.2.1 z.2.2) (1, 0) (1, 0)|)
        (fun _ _ => by positivity) (mem_univ (m, n, k))
      exact this
    have habs : |Dr| = -Dr := abs_of_neg hDrn
    rw [habs] at hle
    have h4 : |De| ≤ lamN N * (-Dr) := by
      rwa [div_le_iff₀ (by linarith)] at hle
    have h5 : -De ≤ |De| := neg_le_abs De
    nlinarith

/-- **Proposition 9.8** (Interior points near the symmetric endpoint): for `Λ > Λ_N` and all
sufficiently small `ε > 0`, the measure of `K_{N,1-Λε}` with its top mass lowered by `ε` (in the
fixed coordinate `x`, `epsRaw … (-ε)`) has `g(m,n;k) > 0` on the whole triangle. -/
theorem interior_points (hN : 2 ≤ N) {Λ : ℝ} (hΛ : lamN N < Λ) :
    ∃ ε₀ > 0, ∀ ε, 0 < ε → ε < ε₀ →
      0 < 1 - Λ * ε ∧ 1 - Λ * ε < 1 ∧ ε < kw N (1 - Λ * ε) 0 ∧
        ∀ m, m ≤ N → ∀ n k : Fin (N + 1), Triangle m n.val k.val →
          0 < productMatrix (epsRaw (kv N (1 - Λ * ε)) (kx N (1 - Λ * ε)) (kw N (1 - Λ * ε)) (-ε)) m n k := by
  have hN1 : 1 ≤ N := by omega
  have hΛ0 : 0 < Λ := lt_of_le_of_lt lamN_nonneg hΛ
  -- eventual positivity of every triangle coefficient along the path
  have hz : ∀ z : Fin (N + 1) × Fin (N + 1) × Fin (N + 1), ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      Triangle z.1.val z.2.1.val z.2.2.val → 0 < lowG N z.1 z.2.1 z.2.2 (1 - Λ * ε, ε) := by
    rintro ⟨m, n, k⟩
    by_cases hT : Triangle m.val n.val k.val
    · have hpath := lowG_hasDerivAt_path m (by omega) n k Λ
      have h0 : lowG N m n k (1 - Λ * 0, 0) = productMatrix (krawCoefficients N 1) m n k := by
        simp only [lowG, mul_zero, sub_zero]; rw [lowK_zero hN1 1 m (by omega)]
      have hnn := kraw_nonneg hN1 one_pos le_rfl m (by omega) n k
      rcases lt_or_eq_of_le hnn with hpos | hzero
      · have hc := continuousAt_const.eventually_lt hpath.continuousAt (by rw [h0]; exact hpos)
        exact (hc.filter_mono nhdsWithin_le_nhds).mono fun ε hε _ => hε
      · have hd := path_deriv_pos hN1 hΛ m n k hT hzero.symm
        obtain ⟨ε₁, hε₁, hlt⟩ := neg_right_of_deriv (f := fun ε => -lowG N m n k (1 - Λ * ε, ε)) hpath.neg
          (by rw [h0, ← hzero, neg_zero]) (by linarith)
        rw [Filter.Eventually, mem_nhdsGT_iff_exists_Ioo_subset]
        exact ⟨ε₁, hε₁, fun ε hε _ => by have := hlt ε hε.1 hε.2; linarith⟩
    · exact Filter.Eventually.of_forall fun ε h => absurd h hT
  have hall := Filter.eventually_all.mpr hz
  -- the side conditions near `0`
  have hr : ∀ᶠ ε in 𝓝 (0 : ℝ), 0 < 1 - Λ * ε := by
    have hc : Continuous fun ε : ℝ => 1 - Λ * ε := by fun_prop
    exact continuousAt_const.eventually_lt hc.continuousAt (by simp)
  have hw : ∀ᶠ ε in 𝓝 (0 : ℝ), ε < ((1 - Λ * ε) / (1 + (1 - Λ * ε))) ^ N := by
    have hc : ContinuousAt (fun ε : ℝ => ((1 - Λ * ε) / (1 + (1 - Λ * ε))) ^ N) 0 := by
      have : ContinuousAt (fun ε : ℝ => (1 - Λ * ε) / (1 + (1 - Λ * ε))) 0 :=
        ContinuousAt.div (by fun_prop) (by fun_prop) (by norm_num)
      exact this.pow N
    exact continuousAt_id.eventually_lt hc (by simp only [id, mul_zero, sub_zero]; positivity)
  have hcomb := hall.and ((hr.and hw).filter_mono nhdsWithin_le_nhds)
  rw [Filter.Eventually, mem_nhdsGT_iff_exists_Ioo_subset] at hcomb
  obtain ⟨ε₀, hε₀, hsub⟩ := hcomb
  refine ⟨ε₀, hε₀, fun ε hε hεε => ?_⟩
  obtain ⟨hpos, hrε, hwε⟩ := hsub ⟨hε, hεε⟩
  have hr0 : 0 < 1 - Λ * ε := hrε
  have hr1 : 1 - Λ * ε < 1 := by nlinarith
  refine ⟨hr0, hr1, by rw [k_w0 hr0]; exact hwε, fun m hm n k hT => ?_⟩
  rw [lowK_eq_epsRaw hN1 hr0 hr1.le ε m (by omega)]
  exact hpos (⟨m, by omega⟩, n, k) hT

theorem interior_lowA (Λ : ℝ) (n : ℕ) : ∀ᶠ ε in 𝓝 (0 : ℝ), 0 < lowA N (1 - Λ * ε) ε n := by
  have hc : ContinuousAt (fun ε : ℝ => lowA N (1 - Λ * ε) ε n) 0 := by
    simp only [lowA]
    have hs : ContinuousAt (fun ε : ℝ => ∑ j ∈ range n, (N.choose j : ℝ) / (1 - Λ * ε) ^ j) 0 :=
      tendsto_finsetSum (range n) fun j _ =>
        (continuousAt_const.div ((by fun_prop : ContinuousAt (fun ε : ℝ => 1 - Λ * ε) 0).pow j) (by simp))
    exact continuousAt_const.sub (continuousAt_id.mul hs)
  exact continuousAt_const.eventually_lt hc (by simp [lowA])

/-- **Proposition 9.8**, the lowered measure: for `Λ > Λ_N` and small `ε > 0`, with `r = 1 - Λ ε`,
the masses `w_t - ε [t = 0]` of `K_{N,r}` stay positive, the polynomials of `epsRaw … (-ε)` are
orthogonal for them and equal `1` at `x_0 = 1`, and every triangle coefficient is positive. -/
theorem interior_measure (hN : 2 ≤ N) {Λ : ℝ} (hΛ : lamN N < Λ) :
    ∃ ε₀ > 0, ∀ ε, 0 < ε → ε < ε₀ →
      (∀ t, 0 < kw N (1 - Λ * ε) t - if t = 0 then ε else 0) ∧
      (∀ n, n ≤ N → (recurrencePolynomial (epsRaw (kv N (1 - Λ * ε)) (kx N (1 - Λ * ε)) (kw N (1 - Λ * ε)) (-ε))
        n).eval 1 = 1) ∧
      (∀ m n, m ≤ N → n ≤ N → m ≠ n →
        ∑ t, (kw N (1 - Λ * ε) t - if t = 0 then ε else 0) *
          (recurrencePolynomial (epsRaw (kv N (1 - Λ * ε)) (kx N (1 - Λ * ε)) (kw N (1 - Λ * ε)) (-ε)) m).eval
            (kx N (1 - Λ * ε) t) *
          (recurrencePolynomial (epsRaw (kv N (1 - Λ * ε)) (kx N (1 - Λ * ε)) (kw N (1 - Λ * ε)) (-ε)) n).eval
            (kx N (1 - Λ * ε) t) = 0) ∧
      ∀ m, m ≤ N → ∀ n k : Fin (N + 1), Triangle m n.val k.val →
        0 < productMatrix (epsRaw (kv N (1 - Λ * ε)) (kx N (1 - Λ * ε)) (kw N (1 - Λ * ε)) (-ε)) m n k := by
  have hN1 : 1 ≤ N := by omega
  obtain ⟨ε₀, hε₀, hmain⟩ := interior_points hN hΛ
  have hA := (Filter.eventually_all_finset (range (N + 2))).mpr fun n _ => interior_lowA (N := N) Λ n
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp hA
  refine ⟨min ε₀ δ, lt_min hε₀ hδ, fun ε hε hεε => ?_⟩
  obtain ⟨hr0, hr1, hw0, hpos⟩ := hmain ε hε (lt_of_lt_of_le hεε (min_le_left _ _))
  have hAε := hball (show dist ε 0 < δ by
    rw [Real.dist_eq, sub_zero, abs_of_pos hε]; exact lt_of_lt_of_le hεε (min_le_right _ _))
  have hA' : ∀ n, n ≤ N + 1 → Aeps (kv N (1 - Λ * ε)) (kx N (1 - Λ * ε)) (kw N (1 - Λ * ε)) (-ε) n ≠ 0 := by
    intro n hn
    have hpi : Aeps (kv N (1 - Λ * ε)) (kx N (1 - Λ * ε)) (kw N (1 - Λ * ε)) (-ε) n = lowA N (1 - Λ * ε) ε n := by
      rw [Aeps, lowA, Ssum]
      have : ∑ k ∈ range n, piw (kv N (1 - Λ * ε)) (kx N (1 - Λ * ε)) (kw N (1 - Λ * ε)) k =
          ∑ j ∈ range n, (N.choose j : ℝ) / (1 - Λ * ε) ^ j :=
        sum_congr rfl fun j hj => k_piw hN1 hr0 hr1.le j (by rw [mem_range] at hj; omega)
      rw [this]; ring
    rw [hpi]; exact (hAε n (mem_range.mpr (by omega))).ne'
  obtain ⟨hnorm, horth⟩ := gen_lower_measure (kv N (1 - Λ * ε)) (kv_admissible hN1 hr0 hr1.le)
    (k_act hN1 hr0 hr1.le) (k_orth hN1 hr0 hr1.le) (k_nrm_pos hN1 hr0 hr1.le) kx_zero hA'
  refine ⟨fun t => ?_, hnorm, horth, hpos⟩
  split_ifs with h
  · rw [h]; linarith
  · rw [sub_zero]; exact k_w_pos hr0 hr1.le t

theorem productMatrix_one_of_admissible (z : Coefficients N) (hz : Admissible z) :
    productMatrix z 1 = recurrenceMatrix z := by
  simp [productMatrix, matrixPair, hz.2.1, hz.2.2.1, hz.2.2.2.1]

/-- **Proposition 9.8**, consequence: after the affine normalization of Section 2 the lowered system
satisfies (2.1), and every array satisfying (2.1) within some `η > 0` of it has property (P). -/
theorem interior_open (hN : 2 ≤ N) {Λ : ℝ} (hΛ : lamN N < Λ) :
    ∃ ε₀ > 0, ∀ ε, 0 < ε → ε < ε₀ →
      Admissible (epsNorm (kv N (1 - Λ * ε)) (kx N (1 - Λ * ε)) (kw N (1 - Λ * ε)) (-ε)) ∧
      ∃ η > 0, ∀ w : Coefficients N, Admissible w →
        (∀ i, i ≤ N → |w.a i - (epsNorm (kv N (1 - Λ * ε)) (kx N (1 - Λ * ε)) (kw N (1 - Λ * ε)) (-ε)).a i| ≤ η ∧
          |w.b i - (epsNorm (kv N (1 - Λ * ε)) (kx N (1 - Λ * ε)) (kw N (1 - Λ * ε)) (-ε)).b i| ≤ η ∧
          |w.c i - (epsNorm (kv N (1 - Λ * ε)) (kx N (1 - Λ * ε)) (kw N (1 - Λ * ε)) (-ε)).c i| ≤ η) →
        MatrixPositivity w := by
  classical
  have hN1 : 1 ≤ N := by omega
  obtain ⟨ε₀, hε₀, hmain⟩ := interior_points hN hΛ
  have hA := (Filter.eventually_all_finset (range (N + 2))).mpr fun n _ => interior_lowA (N := N) Λ n
  obtain ⟨δ₁, hδ₁, hball⟩ := Metric.eventually_nhds_iff.mp hA
  refine ⟨min (min ε₀ δ₁) (1 / 2), by positivity, fun ε hε hεε => ?_⟩
  have hεε₀ : ε < ε₀ := lt_of_lt_of_le hεε (le_trans (min_le_left _ _) (min_le_left _ _))
  have hεδ : ε < δ₁ := lt_of_lt_of_le hεε (le_trans (min_le_left _ _) (min_le_right _ _))
  have hε1 : ε < 1 / 2 := lt_of_lt_of_le hεε (min_le_right _ _)
  obtain ⟨hr0, hr1, -, hpos⟩ := hmain ε hε hεε₀
  set r := 1 - Λ * ε
  set A := Aeps (kv N r) (kx N r) (kw N r) (-ε)
  have hAε := hball (show dist ε 0 < δ₁ by rw [Real.dist_eq, sub_zero, abs_of_pos hε]; exact hεδ)
  have hApos : ∀ n, n ≤ N + 1 → 0 < A n := by
    intro n hn
    have hpi : A n = lowA N r ε n := by
      simp only [A]
      rw [Aeps, lowA, Ssum]
      have : ∑ k ∈ range n, piw (kv N r) (kx N r) (kw N r) k = ∑ j ∈ range n, (N.choose j : ℝ) / r ^ j :=
        sum_congr rfl fun j hj => k_piw hN1 hr0 hr1.le j (by rw [mem_range] at hj; omega)
      rw [this]; ring
    rw [hpi]; exact hAε n (mem_range.mpr (by omega))
  have hv := kv_admissible hN1 hr0 hr1.le
  obtain ⟨_, ha0, hb0, hc0, haN, hsum, hapos, hcpos⟩ := hv
  set V := epsNorm (kv N r) (kx N r) (kw N r) (-ε)
  -- the normalized array is admissible
  have hA0 : A 0 = 1 := by simp [A, Aeps, Ssum]
  have hA1 : A 1 = 1 - ε := by simp [A, Aeps, Ssum, k_piw_zero hN1 hr0 hr1.le]; ring
  have hadm : Admissible V := by
    have h1ε : (1 - ε) ≠ 0 := by linarith
    refine ⟨hN1, ?_, ?_, ?_, ?_, fun i hi => ?_, fun i hi => ?_, fun i hi1 hi2 => ?_⟩
    · simp only [V, epsNorm, epsRaw]; rw [show Aeps (kv N r) (kx N r) (kw N r) (-ε) 0 = A 0 from rfl,
        show Aeps (kv N r) (kx N r) (kw N r) (-ε) (0 + 1) = A 1 from rfl, hA0, hA1, ha0]; field_simp; ring
    · simp only [V, epsNorm, epsRaw]; rw [show Aeps (kv N r) (kx N r) (kw N r) (-ε) 0 = A 0 from rfl,
        show Aeps (kv N r) (kx N r) (kw N r) (-ε) (0 + 1) = A 1 from rfl, hA0, hA1, ha0, hc0]; field_simp; ring
    · simp only [V, epsNorm, epsRaw, hc0]; simp
    · simp only [V, epsNorm, epsRaw, haN]; simp
    · simp only [V, epsNorm, epsRaw]; ring
    · simp only [V, epsNorm, epsRaw]
      have := hapos i hi; have := hApos i (by omega); have := hApos (i + 1) (by omega)
      have : 0 < 1 + -ε := by linarith
      change 0 < (1 + -ε) * (_ * A i / A (i + 1))
      positivity
    · simp only [V, epsNorm, epsRaw]
      have := hcpos i hi1 hi2; have := hApos i (by omega); have := hApos (i + 1) (by omega)
      have : 0 < 1 + -ε := by linarith
      change 0 < (1 + -ε) * (_ * A (i + 1) / A i)
      positivity
  -- its product coefficients are those of the lowered system
  have hprod : ∀ m, productMatrix V m = productMatrix (epsRaw (kv N r) (kx N r) (kw N r) (-ε)) m :=
    affine_product _ V (s := 1 + -ε) (β := -(-ε)) (by linarith) (fun i => rfl) (fun i => rfl) (fun i => rfl)
  have hVpos : ∀ m, m ≤ N → ∀ n k : Fin (N + 1), Triangle m n.val k.val → 0 < productMatrix V m n k := by
    intro m hm n k hT; rw [hprod]; exact hpos m hm n k hT
  have hVP : MatrixPositivity V := by
    intro m hm n k
    by_cases hT : Triangle m n.val k.val
    · exact (hVpos m hm n k hT).le
    · rw [product_triangle_zero V hadm m hm n k hT]
  refine ⟨hadm, ?_⟩
  -- constants for the stability lemma
  set Tri := univ.filter (fun z : Fin (N + 1) × Fin (N + 1) × Fin (N + 1) => Triangle z.1.val z.2.1.val z.2.2.val)
  have hTne : Tri.Nonempty := by
    refine ⟨((0 : Fin (N + 1)), (0 : Fin (N + 1)), (0 : Fin (N + 1))), mem_filter.mpr ⟨mem_univ _, ?_⟩⟩
    show Triangle (0 : Fin (N + 1)).val (0 : Fin (N + 1)).val (0 : Fin (N + 1)).val
    simp [Triangle]
  set δ := Tri.inf' hTne fun z => productMatrix V z.1.val z.2.1 z.2.2
  have hδ : 0 < δ := by
    rw [Finset.lt_inf'_iff]
    intro z hz
    simp only [Tri, mem_filter, mem_univ, true_and] at hz
    exact hVpos z.1.val (by omega) z.2.1 z.2.2 hz
  have hδle : ∀ m, m ≤ N → ∀ n k : Fin (N + 1), Triangle m n.val k.val → δ ≤ productMatrix V m n k := by
    intro m hm n k hT
    have := Finset.inf'_le (fun z : Fin (N + 1) × Fin (N + 1) × Fin (N + 1) => productMatrix V z.1.val z.2.1 z.2.2)
      (show ((⟨m, by omega⟩ : Fin (N + 1)), n, k) ∈ Tri by simp [Tri, hT])
    exact this
  have hrne : (range N).Nonempty := ⟨0, mem_range.mpr (by omega)⟩
  set α := min 1 ((range N).inf' hrne fun i => V.a i)
  have hα : 0 < α := by
    refine lt_min one_pos ?_
    rw [Finset.lt_inf'_iff]; intro i hi; exact hadm.2.2.2.2.2.2.1 i (mem_range.mp hi)
  have hαle : ∀ i, i < N → α ≤ V.a i := fun i hi =>
    le_trans (min_le_right _ _) (Finset.inf'_le _ (mem_range.mpr hi))
  have hbne : (Icc 1 N).Nonempty := ⟨1, mem_Icc.mpr ⟨le_rfl, hN1⟩⟩
  set β := (Icc 1 N).inf' hbne fun i => V.b i
  have hβ : 0 < β := by
    rw [Finset.lt_inf'_iff]
    intro i hi
    rw [mem_Icc] at hi
    have h := hVpos 1 hN1 ⟨i, by omega⟩ ⟨i, by omega⟩ (by simp [Triangle]; omega)
    rw [productMatrix_one_of_admissible V hadm] at h
    simpa [recurrenceMatrix] using h
  have hβle : ∀ i, 1 ≤ i → i ≤ N → β ≤ V.b i := fun i h1 h2 => Finset.inf'_le _ (mem_Icc.mpr ⟨h1, h2⟩)
  set η := min (α / 2) (min (δ / 2 / (8 / α) ^ N) β)
  have hη : 0 < η := by positivity
  refine ⟨η, hη, fun w hw hclose => ?_⟩
  have hwb : ∀ i, i ≤ N → 0 ≤ w.b i := by
    intro i hi
    rcases Nat.eq_zero_or_pos i with h0 | hpos'
    · rw [h0, hw.2.2.1]
    · have h1 := (hclose i hi).2.1
      rw [abs_le] at h1
      have h2 := hβle i hpos' hi
      have h3 : η ≤ β := le_trans (min_le_right _ _) (min_le_right _ _)
      linarith
  have hηα : η ≤ α / 2 := min_le_left _ _
  have hηδ : η * (8 / α) ^ N ≤ δ / 2 := by
    have h1 : η ≤ δ / 2 / (8 / α) ^ N := le_trans (min_le_right _ _) (min_le_left _ _)
    have h2 : 0 < (8 / α) ^ N := by positivity
    rwa [le_div_iff₀ h2] at h1
  obtain ⟨-, hmarg⟩ := stability N V w α δ η (fun m n k => Triangle m n k) hadm hVP hα (min_le_left _ _)
    hαle hδ hδle hw hwb hclose hηα hηδ
  intro m hm n k
  by_cases hT : Triangle m n.val k.val
  · have := hmarg m hm n k hT; linarith
  · rw [product_triangle_zero w hw m hm n k hT]

end Szkraw
