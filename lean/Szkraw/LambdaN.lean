import Szkraw.JetColumn
import Szkraw.Interior
import Szkraw.AffineInvariance

/-!
# P3, after Proposition 9.8: the exact values of `Λ_N`, and the top-mass direction

`lowK N r ε` (`Interior.lean`) is `K_{N,r}` with its top mass lowered by `ε`, in the fixed coordinate. For a triangle
triple `z = (m,n,k)` the rates are `A_z = ∂_ε g(m,n;k)` and `B_z = -∂_r g(m,n;k)` at `(r, ε) = (1, 0)`, and
`Λ_N = max({0} ∪ {-A_z/B_z : z ∈ Z_N, A_z < 0})` over the triples `Z_N` whose coefficient vanishes at `K_{N,1}`
(`interior_points` uses the cruder bound `lamN`).

* `lambda_values`: `Λ_N = 4, 10, 18, 28, 52, 90, 165` for `N = 4, …, 10` (every `-A_z/B_z ≤ Λ_N`, with equality
  attained), from exact integer jets of the product table (`JetColumn.lean`) checked in the kernel.
* `topmass_rates`: at `K_{N,1}`, `ċ_n = -(n/N) C(N,n)`, `ḃ_n = (2n/N - 1) C(N,n)`.
* `normalized_direction`: after the affine change `y = (1-ε)x + ε`, which keeps every product coefficient and
  restores `a_0 = 1`, `b_0 = 0`, the direction is `δa_n = (N-n)/N (C(N,n) - 1)`, `δb_n = 1 + (2n/N - 1) C(N,n)`,
  `δc_n = -(n/N)(1 + C(N,n))`.
* `direction_not_uniform`: neither this direction nor its negative (raising the top mass) is a uniform rule.
-/

namespace Szkraw

open Finset Filter Topology JetCol

/-! ### Coefficients of the two paths and their derivatives -/

theorem lowA_one_hasDerivAt (N n : ℕ) :
    HasDerivAt (fun ε => lowA N 1 ε n) (-(∑ j ∈ range n, (N.choose j : ℝ))) 0 := by
  have := ((hasDerivAt_id (0 : ℝ)).mul_const (∑ j ∈ range n, (N.choose j : ℝ) / (1 : ℝ) ^ j)).const_sub 1
  simp only [one_pow, div_one, id, one_mul] at this
  unfold lowA
  simpa [one_pow, div_one] using this

theorem lowA_one_zero (N n : ℕ) : lowA N 1 0 n = 1 := by simp [lowA]

theorem ratio_hasDerivAt (N n : ℕ) :
    HasDerivAt (fun ε => lowA N 1 ε n / lowA N 1 ε (n + 1)) (N.choose n : ℝ) 0 := by
  have h := (lowA_one_hasDerivAt N n).div (lowA_one_hasDerivAt N (n + 1)) (by rw [lowA_one_zero]; norm_num)
  rw [lowA_one_zero, lowA_one_zero, Finset.sum_range_succ] at h
  refine h.congr_deriv ?_
  ring

theorem ratio_hasDerivAt' (N n : ℕ) :
    HasDerivAt (fun ε => lowA N 1 ε (n + 1) / lowA N 1 ε n) (-(N.choose n : ℝ)) 0 := by
  have h := (lowA_one_hasDerivAt N (n + 1)).div (lowA_one_hasDerivAt N n) (by rw [lowA_one_zero]; norm_num)
  rw [lowA_one_zero, lowA_one_zero, Finset.sum_range_succ] at h
  refine h.congr_deriv ?_
  ring

theorem lowK_e_a (N n : ℕ) : HasDerivAt (fun ε => (lowK N 1 ε).a n) (((N : ℝ) - n) / N * N.choose n) 0 := by
  have := (ratio_hasDerivAt N n).const_mul (((N : ℝ) - n) / N)
  simp only [lowK]
  refine (this.congr_of_eventuallyEq (Filter.Eventually.of_forall fun ε => by ring)).congr_deriv rfl

theorem lowK_e_c (N n : ℕ) : HasDerivAt (fun ε => (lowK N 1 ε).c n) (-((n : ℝ) / N * N.choose n)) 0 := by
  have := (ratio_hasDerivAt' N n).const_mul ((1 : ℝ) * n / N)
  simp only [lowK]
  refine (this.congr_of_eventuallyEq (Filter.Eventually.of_forall fun ε => by ring)).congr_deriv (by ring)

theorem lowK_e_b (N n : ℕ) (hN : 1 ≤ N) :
    HasDerivAt (fun ε => (lowK N 1 ε).b n) ((2 * (n : ℝ) / N - 1) * N.choose n) 0 := by
  have h := ((hasDerivAt_const (0 : ℝ) (1 : ℝ)).sub (lowK_e_a N n)).sub (lowK_e_c N n)
  have e : (fun ε => (lowK N 1 ε).b n) = fun ε => 1 - (lowK N 1 ε).a n - (lowK N 1 ε).c n := by
    funext ε; simp only [lowK]; try ring
  rw [e]
  refine h.congr_deriv ?_
  have : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  field_simp; ring

/-! ### Integer data of the two paths (scaled by `N`) -/

def rangeL (N : ℕ) (f : ℕ → ℤ) : List ℤ := (List.range (N + 1)).map f

/-- `ε ↦ lowK N 1 ε` at `0`: `α_n = N - n`, `β = 0`, `γ_n = n`, `α'_n = (N-n) C(N,n)`, `β'_n = (2n-N) C(N,n)`,
`γ'_n = -n C(N,n)`. -/
def datE (N : ℕ) : Dat :=
  ⟨rangeL N fun n => (N : ℤ) - n, rangeL N fun _ => 0, rangeL N fun n => n,
    rangeL N fun n => ((N : ℤ) - n) * N.choose n, rangeL N fun n => (2 * (n : ℤ) - N) * N.choose n,
    rangeL N fun n => -((n : ℤ) * N.choose n)⟩

/-- `ε ↦ lowK N (1-ε) 0` (decreasing `r`): the same values, `α' = 0`, `β'_n = n`, `γ'_n = -n`. -/
def datR (N : ℕ) : Dat :=
  ⟨rangeL N fun n => (N : ℤ) - n, rangeL N fun _ => 0, rangeL N fun n => n,
    rangeL N fun _ => 0, rangeL N fun n => n, rangeL N fun n => -(n : ℤ)⟩

theorem eG_rangeL (N : ℕ) (f : ℕ → ℤ) (i : ℕ) (hi : i ≤ N) : eG (rangeL N f) i = f i := by
  rw [rangeL, eG_map_range, if_pos hi]

theorem lowK_one_zero (N n : ℕ) (hN : 1 ≤ N) :
    (lowK N 1 0).a n = ((N : ℝ) - n) / N ∧ (lowK N 1 0).b n = 0 ∧ (lowK N 1 0).c n = (n : ℝ) / N := by
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  simp only [lowK, lowA_one_zero]
  refine ⟨by ring, by field_simp; ring, by ring⟩

theorem lowK_r_zero (N n : ℕ) (r : ℝ) :
    (lowK N r 0).a n = ((N : ℝ) - n) / N ∧ (lowK N r 0).c n = r * n / N := by
  simp [lowK, lowA]

/-- Values and rates along the ε-path. -/
theorem jetE (N : ℕ) (hN : 1 ≤ N) (k : ℕ) (hk : k < N + 1) :
    ∀ m, m ≤ N → ∀ n : Fin (N + 1),
      productMatrix (lowK N 1 0) m n ⟨k, hk⟩ = (eG (jcol (datE N) N k m).V n : ℝ) / (jcol (datE N) N k m).T ∧
      HasDerivAt (fun ε => productMatrix (lowK N 1 ε) m n ⟨k, hk⟩)
        ((eG (jcol (datE N) N k m).W n : ℝ) / ((jcol (datE N) N k m).T : ℝ) ^ 2) 0 := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  intro m hm n
  have h := jet_column (datE N) (fun ε => lowK N 1 ε) N hN'
    (fun i hi => by rw [(lowK_one_zero N i hN).1, datE, eG_rangeL _ _ _ hi]; push_cast; ring)
    (fun i hi => by rw [(lowK_one_zero N i hN).2.1, datE, eG_rangeL _ _ _ hi]; simp)
    (fun i hi => by rw [(lowK_one_zero N i hN).2.2, datE, eG_rangeL _ _ _ hi]; push_cast; rfl)
    (fun i hi => by rw [datE, eG_rangeL _ _ _ hi]; push_cast
                    exact (lowK_e_a N i).congr_deriv (by field_simp))
    (fun i hi => by rw [datE, eG_rangeL _ _ _ hi]; push_cast
                    exact (lowK_e_b N i hN).congr_deriv (by field_simp))
    (fun i hi => by rw [datE, eG_rangeL _ _ _ hi]; push_cast
                    exact (lowK_e_c N i).congr_deriv (by field_simp))
    (fun i hi => by rw [datE, eG_rangeL _ _ _ hi.le]; omega)
    (by rw [datE, eG_rangeL _ _ _ (Nat.zero_le _)]; simp)
    (by rw [datE, eG_rangeL _ _ _ (Nat.zero_le _)]; simp) k m hm n hk
  exact ⟨h.1, h.2.1⟩

/-- Rates along the r-path `ε ↦ lowK N (1-ε) 0`. -/
theorem jetR (N : ℕ) (hN : 1 ≤ N) (k : ℕ) (hk : k < N + 1) :
    ∀ m, m ≤ N → ∀ n : Fin (N + 1),
      HasDerivAt (fun ε => productMatrix (lowK N (1 - ε) 0) m n ⟨k, hk⟩)
        ((eG (jcol (datR N) N k m).W n : ℝ) / ((jcol (datR N) N k m).T : ℝ) ^ 2) 0 := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hN0 : (N : ℝ) ≠ 0 := hN'.ne'
  intro m hm n
  have hb : ∀ i (ε : ℝ), (lowK N (1 - ε) 0).b i = ε * i / N := fun i ε => by
    simp only [lowK, lowA, zero_mul, sub_zero, div_one, mul_one]; field_simp; ring
  have h := jet_column (datR N) (fun ε => lowK N (1 - ε) 0) N hN'
    (fun i hi => by rw [(lowK_r_zero N i _).1, datR, eG_rangeL _ _ _ hi]; push_cast; ring)
    (fun i hi => by rw [hb, datR, eG_rangeL _ _ _ hi]; simp)
    (fun i hi => by rw [(lowK_r_zero N i _).2, datR, eG_rangeL _ _ _ hi]; push_cast; ring)
    (fun i hi => by
      rw [datR, eG_rangeL _ _ _ hi]
      simp only [(lowK_r_zero N i _).1, Int.cast_zero, zero_div]
      exact hasDerivAt_const _ _)
    (fun i hi => by
      rw [datR, eG_rangeL _ _ _ hi]
      simp only [hb]
      have := (hasDerivAt_id (0 : ℝ)).mul_const ((i : ℝ) / N)
      refine (this.congr_of_eventuallyEq (Filter.Eventually.of_forall fun ε => by simp; ring)).congr_deriv ?_
      push_cast; ring)
    (fun i hi => by
      rw [datR, eG_rangeL _ _ _ hi]
      simp only [(lowK_r_zero N i _).2]
      have := ((hasDerivAt_id (0 : ℝ)).const_sub 1).mul_const ((i : ℝ) / N)
      refine (this.congr_of_eventuallyEq (Filter.Eventually.of_forall fun ε => by simp; ring)).congr_deriv ?_
      push_cast; ring)
    (fun i hi => by rw [datR, eG_rangeL _ _ _ hi.le]; omega)
    (by rw [datR, eG_rangeL _ _ _ (Nat.zero_le _)]; simp)
    (by rw [datR, eG_rangeL _ _ _ (Nat.zero_le _)]; simp) k m hm n hk
  exact h.2.1

theorem jcol_T_same (N k : ℕ) : ∀ m, (jcol (datR N) N k m).T = (jcol (datE N) N k m).T
  | 0 => rfl
  | m + 1 => by
    show (jcol (datR N) N k m).T * eG (datR N).al m = (jcol (datE N) N k m).T * eG (datE N).al m
    rw [jcol_T_same N k m]; rfl

/-- `A_z`, `B_z` and the zero test in terms of the integer jets. -/
theorem rates_eq (N : ℕ) (hN : 1 ≤ N) (m n k : Fin (N + 1)) :
    fderiv ℝ (lowG N m n k) (1, 0) (0, 1) =
      (eG (jcol (datE N) N k m).W n : ℝ) / ((jcol (datE N) N k m).T : ℝ) ^ 2 ∧
    -fderiv ℝ (lowG N m n k) (1, 0) (1, 0) =
      (eG (jcol (datR N) N k m).W n : ℝ) / ((jcol (datE N) N k m).T : ℝ) ^ 2 ∧
    (productMatrix (krawCoefficients N 1) m n k = 0 ↔ eG (jcol (datE N) N k m).V n = 0) ∧
    0 < (jcol (datE N) N k m).T := by
  have hT := (T_pos (datE N) k (fun i hi => by rw [datE, eG_rangeL _ _ _ hi.le]; omega) m (by omega)).1
  have hk : k.val < N + 1 := k.isLt
  have hE := jetE N hN k hk m (by omega) n
  have hR := jetR N hN k hk m (by omega) n
  refine ⟨?_, ?_, ?_, hT⟩
  · exact (lowG_hasDerivAt_e m (by omega) n k).unique hE.2
  · have hr := lowG_hasDerivAt_r m (by omega) n k
    have hpath : HasDerivAt (fun ε : ℝ => 1 - ε) (-1) 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).const_sub 1
    have hr' : HasDerivAt (fun r => lowG N m n k (r, 0)) (fderiv ℝ (lowG N m n k) (1, 0) (1, 0)) (1 - 0) := by
      simpa using hr
    have hc := hr'.comp (0 : ℝ) hpath
    have hR' := hR
    rw [jcol_T_same] at hR'
    have := hc.unique hR'
    linarith
  · have hz := lowK_zero (N := N) hN 1 m (by omega)
    rw [show productMatrix (krawCoefficients N 1) m n k = productMatrix (lowK N 1 0) m n k by rw [hz],
      hE.1, div_eq_zero_iff]
    have : ((jcol (datE N) N k m).T : ℝ) ≠ 0 := by exact_mod_cast hT.ne'
    simp [this]

/-! ### The kernel check -/

def lamOk (N : ℕ) (Λ : ℤ) (m n k : ℕ) : Bool :=
  let Ve := eG (jcol (datE N) N k m).V n
  let We := eG (jcol (datE N) N k m).W n
  let Wr := eG (jcol (datR N) N k m).W n
  !(decide (m ≤ n + k) && decide (n ≤ m + k) && decide (k ≤ m + n) && decide (Ve = 0) && decide (We < 0)) ||
    (decide (0 < Wr) && decide (-We ≤ Λ * Wr))

def lamCheck (N : ℕ) (Λ : ℤ) : Bool :=
  (List.range (N + 1)).all fun m => (List.range (N + 1)).all fun n => (List.range (N + 1)).all fun k => lamOk N Λ m n k

def lamWit (N : ℕ) (Λ : ℤ) (m n k : ℕ) : Bool :=
  decide (m ≤ n + k) && decide (n ≤ m + k) && decide (k ≤ m + n) &&
    decide (eG (jcol (datE N) N k m).V n = 0) && decide (eG (jcol (datE N) N k m).W n < 0) &&
    decide (-eG (jcol (datE N) N k m).W n = Λ * eG (jcol (datR N) N k m).W n)

/-- `Λ_N` from the kernel checks. -/
theorem lambda_of_check (N : ℕ) (hN : 1 ≤ N) (Λ : ℤ) (hΛ0 : 0 < Λ) (hc : lamCheck N Λ = true) (m₀ n₀ k₀ : Fin (N + 1))
    (hw : lamWit N Λ m₀ n₀ k₀ = true) :
    let A := fun z : Fin (N + 1) × Fin (N + 1) × Fin (N + 1) => fderiv ℝ (lowG N z.1 z.2.1 z.2.2) (1, 0) (0, 1)
    let B := fun z : Fin (N + 1) × Fin (N + 1) × Fin (N + 1) => -fderiv ℝ (lowG N z.1 z.2.1 z.2.2) (1, 0) (1, 0)
    (∀ z : Fin (N + 1) × Fin (N + 1) × Fin (N + 1), Triangle z.1 z.2.1 z.2.2 →
      productMatrix (krawCoefficients N 1) z.1 z.2.1 z.2.2 = 0 → A z < 0 → 0 < B z ∧ -A z / B z ≤ Λ) ∧
    (∃ z : Fin (N + 1) × Fin (N + 1) × Fin (N + 1), Triangle z.1 z.2.1 z.2.2 ∧
      productMatrix (krawCoefficients N 1) z.1 z.2.1 z.2.2 = 0 ∧ A z < 0 ∧ -A z / B z = Λ) := by
  intro A B
  refine ⟨fun ⟨m, n, k⟩ hT hz hA => ?_, ⟨(m₀, n₀, k₀), ?_⟩⟩
  · obtain ⟨eA, eB, ez, hTpos⟩ := rates_eq N hN m n k
    simp only [A, B] at hA ⊢
    rw [eA] at hA ⊢; rw [eB]
    have hT2 : (0 : ℝ) < ((jcol (datE N) N k m).T : ℝ) ^ 2 := by positivity
    have hWe : eG (jcol (datE N) N k m).W n < 0 := by
      have := (div_neg_iff.1 hA); rcases this with ⟨-, h⟩ | ⟨h, -⟩
      · linarith
      · exact_mod_cast h
    have hok := hc
    simp only [lamCheck, List.all_eq_true, List.mem_range] at hok
    have h1 := hok m (by omega) n (by omega) k (by omega)
    simp only [lamOk, Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_true, decide_eq_true_eq,
      Bool.and_eq_false_iff, decide_eq_false_iff_not] at h1
    obtain ⟨hT1, hT2', hT3⟩ := hT
    rcases h1 with h1 | ⟨hWr, hle⟩
    · exfalso
      rcases h1 with ((((h | h) | h) | h) | h)
      · exact h hT1
      · exact h hT2'
      · exact h hT3
      · exact h (ez.1 hz)
      · exact h hWe
    · have hWr' : (0 : ℝ) < eG (jcol (datR N) N k m).W n := by exact_mod_cast hWr
      refine ⟨div_pos hWr' hT2, ?_⟩
      rw [neg_div, div_div_div_cancel_right₀ hT2.ne', neg_div', div_le_iff₀ hWr']
      have : (-(eG (jcol (datE N) N k m).W n : ℝ)) ≤ Λ * eG (jcol (datR N) N k m).W n := by exact_mod_cast hle
      linarith
  · obtain ⟨eA, eB, ez, hTpos⟩ := rates_eq N hN m₀ n₀ k₀
    simp only [lamWit, Bool.and_eq_true, decide_eq_true_eq] at hw
    obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := hw
    have hT2 : (0 : ℝ) < ((jcol (datE N) N k₀ m₀).T : ℝ) ^ 2 := by positivity
    have hWr : (0 : ℝ) < eG (jcol (datR N) N k₀ m₀).W n₀ := by
      have h5' : (eG (jcol (datE N) N k₀ m₀).W n₀ : ℝ) < 0 := by exact_mod_cast h5
      have h6' : (-(eG (jcol (datE N) N k₀ m₀).W n₀ : ℝ)) = Λ * eG (jcol (datR N) N k₀ m₀).W n₀ := by
        exact_mod_cast h6
      have hΛ : (0 : ℝ) < Λ := by exact_mod_cast hΛ0
      by_contra hneg
      push_neg at hneg
      nlinarith [mul_nonpos_of_nonneg_of_nonpos hΛ.le hneg]
    refine ⟨⟨h1, h2, h3⟩, ez.2 h4, ?_, ?_⟩
    · show fderiv ℝ (lowG N m₀ n₀ k₀) (1, 0) (0, 1) < 0
      rw [eA]; exact div_neg_of_neg_of_pos (by exact_mod_cast h5) hT2
    · show -fderiv ℝ (lowG N m₀ n₀ k₀) (1, 0) (0, 1) / -fderiv ℝ (lowG N m₀ n₀ k₀) (1, 0) (1, 0) = Λ
      rw [eA, eB, neg_div, div_div_div_cancel_right₀ hT2.ne', neg_div', div_eq_iff hWr.ne']
      have : (-(eG (jcol (datE N) N k₀ m₀).W n₀ : ℝ)) = Λ * eG (jcol (datR N) N k₀ m₀).W n₀ := by exact_mod_cast h6
      linarith

/-- **P3, after Proposition 9.8**: exact rational computation of the maximum gives `Λ_N = 4, 10, 18, 28, 52, 90, 165`
for `N = 4, …, 10`: every `-A_z/B_z` with `z ∈ Z_N` and `A_z < 0` is at most `Λ_N` (and `B_z > 0`), and the value is
attained. -/
theorem lambda_values :
    ∀ NΛ ∈ [((4 : ℕ), (4 : ℤ)), (5, 10), (6, 18), (7, 28), (8, 52), (9, 90), (10, 165)],
      let N := NΛ.1
      let A := fun z : Fin (N + 1) × Fin (N + 1) × Fin (N + 1) => fderiv ℝ (lowG N z.1 z.2.1 z.2.2) (1, 0) (0, 1)
      let B := fun z : Fin (N + 1) × Fin (N + 1) × Fin (N + 1) => -fderiv ℝ (lowG N z.1 z.2.1 z.2.2) (1, 0) (1, 0)
      (∀ z : Fin (N + 1) × Fin (N + 1) × Fin (N + 1), Triangle z.1 z.2.1 z.2.2 →
        productMatrix (krawCoefficients N 1) z.1 z.2.1 z.2.2 = 0 → A z < 0 → 0 < B z ∧ -A z / B z ≤ NΛ.2) ∧
      (∃ z : Fin (N + 1) × Fin (N + 1) × Fin (N + 1), Triangle z.1 z.2.1 z.2.2 ∧
        productMatrix (krawCoefficients N 1) z.1 z.2.1 z.2.2 = 0 ∧ A z < 0 ∧ -A z / B z = NΛ.2) := by
  intro NΛ h
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lambda_of_check 4 (by norm_num) 4 (by norm_num) (by decide +kernel) 1 1 1 (by decide +kernel)
  · exact lambda_of_check 5 (by norm_num) 10 (by norm_num) (by decide +kernel) 1 1 1 (by decide +kernel)
  · exact lambda_of_check 6 (by norm_num) 18 (by norm_num) (by decide +kernel) 1 1 1 (by decide +kernel)
  · exact lambda_of_check 7 (by norm_num) 28 (by norm_num) (by decide +kernel) 1 1 1 (by decide +kernel)
  · exact lambda_of_check 8 (by norm_num) 52 (by norm_num) (by decide +kernel) 1 2 2 (by decide +kernel)
  · exact lambda_of_check 9 (by norm_num) 90 (by norm_num) (by decide +kernel) 2 2 3 (by decide +kernel)
  · exact lambda_of_check 10 (by norm_num) 165 (by norm_num) (by decide +kernel) 2 2 3 (by decide +kernel)

/-! ### The top-mass direction -/

/-- **P3, Section 9**: at `K_{N,1}`, in the fixed spectral coordinate, lowering the top mass changes the coefficients
at the rates `ċ_n = -(n/N) C(N,n)` and `ḃ_n = (2n/N - 1) C(N,n)`. -/
theorem topmass_rates (N n : ℕ) (hN : 1 ≤ N) :
    HasDerivAt (fun ε => (lowK N 1 ε).c n) (-((n : ℝ) / N * N.choose n)) 0 ∧
    HasDerivAt (fun ε => (lowK N 1 ε).b n) ((2 * (n : ℝ) / N - 1) * N.choose n) 0 :=
  ⟨lowK_e_c N n, lowK_e_b N n hN⟩

/-- The lowered system after the affine change `y = (1-ε)x + ε`. -/
noncomputable def normK (N : ℕ) (ε : ℝ) : Coefficients N where
  a i := (1 - ε) * (lowK N 1 ε).a i
  b i := (1 - ε) * (lowK N 1 ε).b i + ε
  c i := (1 - ε) * (lowK N 1 ε).c i

/-- **P3, Section 9**: the affine change keeps every product coefficient and restores `a_0 = 1`, `b_0 = 0` and the
row sums; at `ε = 0` it is `K_{N,1}`; the direction is `δa_n = (N-n)/N (C(N,n) - 1)`, `δb_n = 1 + (2n/N - 1) C(N,n)`,
`δc_n = -(n/N)(1 + C(N,n))`. -/
theorem normalized_direction (N : ℕ) (hN : 1 ≤ N) :
    (∀ ε : ℝ, ε ≠ 1 → ∀ m, productMatrix (normK N ε) m = productMatrix (lowK N 1 ε) m) ∧
    (∀ ε : ℝ, ε ≠ 1 → (normK N ε).a 0 = 1 ∧ (normK N ε).b 0 = 0) ∧
    (∀ ε : ℝ, ∀ i, (normK N ε).a i + (normK N ε).b i + (normK N ε).c i = 1) ∧
    (∀ i, i ≤ N → (normK N 0).a i = (krawCoefficients N 1).a i ∧ (normK N 0).b i = (krawCoefficients N 1).b i ∧
      (normK N 0).c i = (krawCoefficients N 1).c i) ∧
    (∀ n, n ≤ N →
      HasDerivAt (fun ε => (normK N ε).a n) (((N : ℝ) - n) / N * (N.choose n - 1)) 0 ∧
      HasDerivAt (fun ε => (normK N ε).b n) (1 + (2 * (n : ℝ) / N - 1) * N.choose n) 0 ∧
      HasDerivAt (fun ε => (normK N ε).c n) (-((n : ℝ) / N * (1 + N.choose n))) 0) := by
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have h1e : HasDerivAt (fun ε : ℝ => 1 - ε) (-1) 0 := by simpa using (hasDerivAt_id (0 : ℝ)).const_sub 1
  refine ⟨fun ε hε m => affine_product (lowK N 1 ε) (normK N ε) (s := 1 - ε) (β := ε) (sub_ne_zero.2 (Ne.symm hε))
      (fun i => rfl) (fun i => rfl) (fun i => rfl) m, fun ε hε => ?_, fun ε i => ?_, fun i hi => ?_,
    fun n hn => ⟨?_, ?_, ?_⟩⟩
  · have h1 : (1 : ℝ) - ε ≠ 0 := sub_ne_zero.2 (Ne.symm hε)
    have hA1 : lowA N 1 ε 1 = 1 - ε := by simp [lowA]
    have hA0 : lowA N 1 ε 0 = 1 := by simp [lowA]
    constructor <;> simp only [normK, lowK, hA0, hA1, Nat.cast_zero, zero_add] <;> field_simp <;> ring
  · simp only [normK, lowK]; ring
  · obtain ⟨e1, e2, e3⟩ := lowK_one_zero N i hN
    simp only [normK, e1, e2, e3, krawCoefficients, sub_zero, one_mul, add_zero]
    refine ⟨?_, ?_, ?_⟩ <;> first | trivial | ring
  · have := h1e.mul (lowK_e_a N n)
    simp only [normK]
    refine this.congr_deriv ?_
    rw [(lowK_one_zero N n hN).1]; ring
  · have := (h1e.mul (lowK_e_b N n hN)).add (hasDerivAt_id (0 : ℝ))
    simp only [normK]
    refine this.congr_deriv ?_
    rw [(lowK_one_zero N n hN).2.1]; ring
  · have := h1e.mul (lowK_e_c N n)
    simp only [normK]
    refine this.congr_deriv ?_
    rw [(lowK_one_zero N n hN).2.2]; ring

/-- **P3, Section 9**: neither the affine-normalized top-mass direction nor its negative (raising the top mass) is a
uniform rule `δb_n = β(n/N)`, `δc_n = γ(n/N)`: its dependence on `N` is binomial (`N = 2, n = 1` and `N = 4, n = 2`). -/
theorem direction_not_uniform (σ : ℝ) (hσ : σ = 1 ∨ σ = -1) :
    ¬ ∃ β γ : ℝ → ℝ, ∀ N : ℕ, 1 ≤ N →
      (∀ n, 1 ≤ n → n < N → σ * (1 + (2 * (n : ℝ) / N - 1) * N.choose n) = β (n / N)) ∧
      (∀ n, 1 ≤ n → n ≤ N → σ * -((n : ℝ) / N * (1 + N.choose n)) = γ (n / N)) := by
  rintro ⟨β, γ, h⟩
  have h2 := (h 2 (by norm_num)).2 1 le_rfl (by norm_num)
  have h4 := (h 4 (by norm_num)).2 2 (by norm_num) (by norm_num)
  norm_num [Nat.choose] at h2 h4
  rw [← h4] at h2
  rcases hσ with rfl | rfl <;> norm_num at h2

end Szkraw
