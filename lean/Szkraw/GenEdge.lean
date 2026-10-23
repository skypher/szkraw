import Szkraw.VRAffineEnds

/-!
# Edge linearization of quadratic forms in a log-concave sequence

This replaces the weight sums of Lemma 8.15 in the proof of the key inequality of Theorem 8.16. For an
`LCNZ` sequence `u` and nonnegative, `u₀`-free coefficient sequences `x`, `y`, keeping only the products
`u_i u_j` with `i ≤ 2` or `j ≤ 2` and using `u_i u_j ≥ u₁ u_{i+j-1}` (`i, j ≥ 1`) gives
`(Σ x_i u_i)(Σ y_j u_j) ≥ u₁ Σ_n (edgeCoef x y n) u_n`. Negative terms `u₀ Σ h_n u_n` are bounded by
`u₁ Σ h_{n+1} u_n`, from `u₀ u_{n+1} ≤ u₁ u_n`. Every form of the key is then `≥ u₁ Σ_n e_n u_n`.
-/

set_option linter.unusedSectionVars false

namespace Szkraw

open Finset

/-- The linear form `Σ_{n < R} c_n u_n`. -/
noncomputable def lf (R : ℕ) (c u : ℕ → ℝ) : ℝ := ∑ n ∈ range R, c n * u n

/-- Coefficients of the edge bound of a product. -/
noncomputable def edgeCoef (x y : ℕ → ℝ) (n : ℕ) : ℝ :=
  x 1 * y n + x 2 * (if 1 ≤ n then y (n - 1) else 0) + y 1 * (if 3 ≤ n then x n else 0) +
    y 2 * (if 4 ≤ n then x (n - 1) else 0)

variable {u : ℕ → ℝ}

theorem LCNZ.zero_shift (hu : LCNZ u) (n : ℕ) : u 0 * u (n + 1) ≤ u 1 * u n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [mul_comm]
  · have := hu.balanced 1 1 n le_rfl hn
    simpa using this

theorem lf_nonneg (hu : LCNZ u) {R : ℕ} {c : ℕ → ℝ} (hc : ∀ n, n < R → 0 ≤ c n) : 0 ≤ lf R c u :=
  sum_nonneg fun n hn => mul_nonneg (hc n (mem_range.1 hn)) (hu.1 n)

theorem lf_add (R : ℕ) (c d : ℕ → ℝ) : lf R (fun n => c n + d n) u = lf R c u + lf R d u := by
  unfold lf; rw [← sum_add_distrib]; exact sum_congr rfl fun n _ => by ring

theorem lf_smul (R : ℕ) (k : ℝ) (c : ℕ → ℝ) : lf R (fun n => k * c n) u = k * lf R c u := by
  unfold lf; rw [mul_sum]; exact sum_congr rfl fun n _ => by ring

theorem lf_sub (R : ℕ) (c d : ℕ → ℝ) : lf R (fun n => c n - d n) u = lf R c u - lf R d u := by
  unfold lf; rw [← sum_sub_distrib]; exact sum_congr rfl fun n _ => by ring

/-- Extending the range by indices where the coefficients vanish. -/
theorem lf_extend {R S : ℕ} (hRS : R ≤ S) {c : ℕ → ℝ} (hc : ∀ n, R ≤ n → c n = 0) :
    lf R c u = lf S c u := by
  unfold lf
  apply sum_subset (by intro n hn; simp only [mem_range] at hn ⊢; omega)
  intro n hn hn'; simp only [mem_range, not_lt] at hn hn'; rw [hc n hn', zero_mul]

theorem lf_congr {R : ℕ} {c d : ℕ → ℝ} (h : ∀ n, n < R → c n = d n) : lf R c u = lf R d u :=
  sum_congr rfl fun n hn => by rw [h n (mem_range.1 hn)]

/-- `u₀ Σ_{n ≤ R} h_n u_n ≤ u₁ Σ_{m < R} h_{m+1} u_m` for nonnegative `h` with `h₀ = 0`. -/
theorem LCNZ.u0_lf (hu : LCNZ u) (R : ℕ) (h : ℕ → ℝ) (hh : ∀ n, 0 ≤ h n) (h0 : h 0 = 0) :
    u 0 * lf (R + 1) h u ≤ u 1 * lf R (fun m => h (m + 1)) u := by
  unfold lf
  rw [sum_range_succ', h0, zero_mul, add_zero, mul_sum, mul_sum]
  refine sum_le_sum fun m _ => ?_
  have := hu.zero_shift m
  calc u 0 * (h (m + 1) * u (m + 1)) = h (m + 1) * (u 0 * u (m + 1)) := by ring
    _ ≤ h (m + 1) * (u 1 * u m) := mul_le_mul_of_nonneg_left this (hh _)
    _ = u 1 * (h (m + 1) * u m) := by ring

/-- Shifted linear form: `Σ_{j < R} y_j u_{j+1} = Σ_{n < R+1} [1 ≤ n] y_{n-1} u_n`. -/
theorem lf_shift (R : ℕ) (y : ℕ → ℝ) :
    ∑ j ∈ range R, y j * u (j + 1) = lf (R + 1) (fun n => if 1 ≤ n then y (n - 1) else 0) u := by
  unfold lf
  rw [sum_range_succ']
  simp only [show ¬ (1 ≤ 0) by omega, if_false, zero_mul, add_zero]
  exact sum_congr rfl fun j _ => by rw [if_pos (by omega), Nat.add_sub_cancel]

/-- **Edge bound** for a product of two nonnegative `u₀`-free linear forms supported below `R`. -/
theorem LCNZ.edge_prod (hu : LCNZ u) {R : ℕ} (hR : 3 ≤ R) {x y : ℕ → ℝ} (hx : ∀ i, 0 ≤ x i)
    (hy : ∀ j, 0 ≤ y j) (hx0 : x 0 = 0) (hy0 : y 0 = 0) (hxR : ∀ n, R ≤ n → x n = 0)
    (hyR : ∀ n, R ≤ n → y n = 0) :
    u 1 * lf (R + 1) (edgeCoef x y) u ≤ lf R x u * lf R y u := by
  -- the four pieces of the edge bound
  set Sy := ∑ j ∈ range R, y j * u j with hSy
  set Sy' := ∑ j ∈ range R, y j * u (j + 1) with hSy'
  set Tx := ∑ i ∈ range R, (if 3 ≤ i then x i else 0) * u i with hTx
  set Tx' := ∑ i ∈ range R, (if 3 ≤ i then x i else 0) * u (i + 1) with hTx'
  have hlhs : lf (R + 1) (edgeCoef x y) u = x 1 * Sy + x 2 * Sy' + y 1 * Tx + y 2 * Tx' := by
    have e1 : lf (R + 1) y u = Sy := by
      rw [← lf_extend (show R ≤ R + 1 by omega) (fun n hn => hyR n hn)]; rfl
    have e2 : lf (R + 1) (fun n => if 1 ≤ n then y (n - 1) else 0) u = Sy' := (lf_shift R y).symm
    have e3 : lf (R + 1) (fun n => if 3 ≤ n then x n else 0) u = Tx := by
      rw [← lf_extend (show R ≤ R + 1 by omega)]
      · rfl
      · intro n hn; rw [hxR n hn]; simp
    have e4 : lf (R + 1) (fun n => if 4 ≤ n then x (n - 1) else 0) u = Tx' := by
      rw [hTx', lf_shift R (fun i => if 3 ≤ i then x i else 0)]
      refine lf_congr fun n _ => ?_
      by_cases h4 : 4 ≤ n
      · rw [if_pos h4, if_pos (by omega), if_pos (by omega)]
      · rw [if_neg h4]
        by_cases h1 : 1 ≤ n
        · rw [if_pos h1, if_neg (by omega)]
        · rw [if_neg h1]
    unfold edgeCoef
    rw [show (fun n => x 1 * y n + x 2 * (if 1 ≤ n then y (n - 1) else 0) +
        y 1 * (if 3 ≤ n then x n else 0) + y 2 * (if 4 ≤ n then x (n - 1) else 0)) =
        (fun n => (fun n => (fun n => x 1 * y n + x 2 * (if 1 ≤ n then y (n - 1) else 0)) n +
          y 1 * (if 3 ≤ n then x n else 0)) n + y 2 * (if 4 ≤ n then x (n - 1) else 0)) from rfl,
      lf_add, lf_add, lf_add, lf_smul, lf_smul, lf_smul, lf_smul, e1, e2, e3, e4]
  rw [hlhs]
  -- the product as a sum over `i` of `x_i u_i Sy`
  have hprod : lf R x u * lf R y u = ∑ i ∈ range R, x i * u i * Sy := by
    unfold lf; rw [sum_mul]
  rw [hprod]
  have h1R : 1 ∈ range R := mem_range.2 (by omega)
  have h2R : 2 ∈ range R := mem_range.2 (by omega)
  -- pointwise bounds
  have hSy0 : 0 ≤ Sy := sum_nonneg fun j _ => mul_nonneg (hy j) (hu.1 j)
  have hSy12 : y 1 * u 1 + y 2 * u 2 ≤ Sy := by
    have hsub : ({1, 2} : Finset ℕ) ⊆ range R := by
      intro n hn; simp only [mem_insert, mem_singleton] at hn; rcases hn with rfl | rfl <;> assumption
    have := sum_le_sum_of_subset_of_nonneg hsub (fun j _ _ => mul_nonneg (hy j) (hu.1 j))
    simpa [hSy] using this
  have hSy' : u 1 * Sy' ≤ u 2 * Sy := by
    rw [hSy', hSy, mul_sum, mul_sum]
    refine sum_le_sum fun j _ => ?_
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · rw [hy0]; simp
    · have hp := hu.pair (i := 2) (j := j) (by norm_num) hj
      rw [show 2 + j - 1 = j + 1 by omega] at hp
      calc u 1 * (y j * u (j + 1)) = y j * (u 1 * u (j + 1)) := by ring
        _ ≤ y j * (u 2 * u j) := mul_le_mul_of_nonneg_left hp (hy j)
        _ = u 2 * (y j * u j) := by ring
  -- reorganize the left side as a sum over `i`
  have hT2 : ∑ i ∈ range R, (if 3 ≤ i then x i else 0) * (u 1 * (y 1 * u i + y 2 * u (i + 1))) =
      u 1 * (y 1 * Tx + y 2 * Tx') := by
    simp only [hTx, hTx', mul_sum, ← sum_add_distrib]
    exact sum_congr rfl fun i _ => by ring
  have hT : u 1 * (x 1 * Sy + x 2 * Sy' + y 1 * Tx + y 2 * Tx') =
      u 1 * x 1 * Sy + x 2 * (u 1 * Sy') +
        ∑ i ∈ range R, (if 3 ≤ i then x i else 0) * (u 1 * (y 1 * u i + y 2 * u (i + 1))) := by
    rw [hT2]; ring
  rw [hT]
  -- split the right side into `i = 1`, `i = 2` and `i ≥ 3`
  have hsplit : ∑ i ∈ range R, x i * u i * Sy =
      x 1 * u 1 * Sy + x 2 * u 2 * Sy + ∑ i ∈ range R, (if 3 ≤ i then x i * u i * Sy else 0) := by
    have hpt : ∀ i ∈ range R, x i * u i * Sy =
        (if i = 1 then x 1 * u 1 * Sy else 0) + (if i = 2 then x 2 * u 2 * Sy else 0) +
          (if 3 ≤ i then x i * u i * Sy else 0) := by
      intro i _
      rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ 3 ≤ i by omega) with rfl | rfl | rfl | h3
      · simp [hx0]
      · simp
      · simp
      · rw [if_neg (by omega), if_neg (by omega), if_pos h3]; ring
    rw [sum_congr rfl hpt, sum_add_distrib, sum_add_distrib, sum_ite_eq' (range R) 1,
      sum_ite_eq' (range R) 2, if_pos h1R, if_pos h2R]
  rw [hsplit]
  have hrest : ∑ i ∈ range R, (if 3 ≤ i then x i else 0) * (u 1 * (y 1 * u i + y 2 * u (i + 1))) ≤
      ∑ i ∈ range R, (if 3 ≤ i then x i * u i * Sy else 0) := by
    refine sum_le_sum fun i _ => ?_
    by_cases h3 : 3 ≤ i
    · rw [if_pos h3, if_pos h3]
      have hp := hu.pair (i := i) (j := 2) (by omega) (by norm_num)
      rw [show i + 2 - 1 = i + 1 by omega] at hp
      have hui : 0 ≤ u i := hu.1 i
      have h1 : u 1 * (y 1 * u i + y 2 * u (i + 1)) ≤ u i * (y 1 * u 1 + y 2 * u 2) := by
        nlinarith [mul_le_mul_of_nonneg_left hp (hy 2)]
      calc x i * (u 1 * (y 1 * u i + y 2 * u (i + 1))) ≤ x i * (u i * (y 1 * u 1 + y 2 * u 2)) :=
            mul_le_mul_of_nonneg_left h1 (hx i)
        _ ≤ x i * (u i * Sy) := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hSy12 hui) (hx i)
        _ = x i * u i * Sy := by ring
    · rw [if_neg h3, if_neg h3, zero_mul]
  have h2 : x 2 * (u 1 * Sy') ≤ x 2 * u 2 * Sy := by
    rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hSy' (hx 2)
  linarith

theorem edgeCoef_zero (x y : ℕ → ℝ) : edgeCoef x y 0 = x 1 * y 0 := by simp [edgeCoef]
theorem edgeCoef_one (x y : ℕ → ℝ) : edgeCoef x y 1 = x 1 * y 1 + x 2 * y 0 := by simp [edgeCoef]
theorem edgeCoef_two (x y : ℕ → ℝ) : edgeCoef x y 2 = x 1 * y 2 + x 2 * y 1 := by simp [edgeCoef]
theorem edgeCoef_three (x y : ℕ → ℝ) : edgeCoef x y 3 = x 1 * y 3 + x 2 * y 2 + y 1 * x 3 := by
  simp [edgeCoef]
theorem edgeCoef_ge4 (x y : ℕ → ℝ) {n : ℕ} (hn : 4 ≤ n) :
    edgeCoef x y n = x 1 * y n + x 2 * y (n - 1) + y 1 * x n + y 2 * x (n - 1) := by
  unfold edgeCoef; rw [if_pos (by omega), if_pos (by omega), if_pos hn]

/-- `C(a, k+1) (k+1) = C(a,k) (a - k)` over `ℝ`. -/
theorem choose_succ_real (a k : ℕ) (hk : k ≤ a) :
    ((a.choose (k + 1) : ℕ) : ℝ) * ((k : ℝ) + 1) = (a.choose k : ℝ) * ((a : ℝ) - k) := by
  have h := Nat.choose_succ_right_eq a k
  have h' : ((a.choose (k + 1) * (k + 1) : ℕ) : ℝ) = ((a.choose k * (a - k) : ℕ) : ℝ) := by rw [h]
  push_cast [Nat.cast_sub hk] at h'; linarith

/-- `a C(a-1, k) = C(a, k+1) (k+1)` over `ℝ`. -/
theorem choose_pred_real (a k : ℕ) (ha : 1 ≤ a) :
    ((a - 1).choose k : ℝ) * (a : ℝ) = (a.choose (k + 1) : ℝ) * ((k : ℝ) + 1) := by
  have h := Nat.add_one_mul_choose_eq (a - 1) k
  rw [show a - 1 + 1 = a by omega] at h
  have h' : ((a * (a - 1).choose k : ℕ) : ℝ) = ((a.choose (k + 1) * (k + 1) : ℕ) : ℝ) := by rw [h]
  push_cast at h'; linarith

/-- The edge coefficients are nonnegative when `x` and `y` are. -/
theorem edgeCoef_nonneg {x y : ℕ → ℝ} (hx : ∀ i, 0 ≤ x i) (hy : ∀ j, 0 ≤ y j) (n : ℕ) :
    0 ≤ edgeCoef x y n := by
  unfold edgeCoef
  have h1 : 0 ≤ (if 1 ≤ n then y (n - 1) else 0) := by split_ifs <;> simp [hy]
  have h3 : 0 ≤ (if 3 ≤ n then x n else 0) := by split_ifs <;> simp [hx]
  have h4 : 0 ≤ (if 4 ≤ n then x (n - 1) else 0) := by split_ifs <;> simp [hx]
  exact add_nonneg (add_nonneg (add_nonneg (mul_nonneg (hx 1) (hy n)) (mul_nonneg (hx 2) h1))
    (mul_nonneg (hy 1) h3)) (mul_nonneg (hy 2) h4)

end Szkraw
