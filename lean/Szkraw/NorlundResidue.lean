import Szkraw.GridCauchy
import Mathlib.LinearAlgebra.Lagrange

/-!
# The residue identity of the Nörlund–Rice bound

For the nodes `k/N` (`0 ≤ k ≤ N`) and `ω_N(z) = Π_k (z - k/N)`, partial fractions give
`1/ω_N(z) = Σ_k w_k/(z - k/N)` with `w_k = N^N (-1)^{N-k} C(N,k)/N!`. Hence, for a finite union of
grid squares containing the nodes (off the grid lines) inside the domain of a holomorphic `f`,
`Σ_{p ∈ S} ∮_{∂p} f/ω_N = 2πi (-1)^N (N^N/N!) Σ_n (-1)^n C(N,n) f(n/N)` (Lemma 9.5).
-/

namespace Szkraw

open Complex MeasureTheory intervalIntegral Set Finset Polynomial
open scoped Interval

/-- The nodal polynomial `ω_N(z) = Π_{j=0}^N (z - j/N)`. -/
noncomputable def nodalN (N : ℕ) (z : ℂ) : ℂ := ∏ j ∈ range (N + 1), (z - (j : ℂ) / N)

/-- The weights `w_k = Π_{j ≠ k} (k/N - j/N)⁻¹`. -/
noncomputable def nodeW (N k : ℕ) : ℂ := ∏ j ∈ (range (N + 1)).erase k, ((k : ℂ) / N - (j : ℂ) / N)⁻¹

/-- The alternating binomial sum `Σ_{n=0}^N (-1)^n C(N,n) f(n/N)`. -/
noncomputable def altBinom (N : ℕ) (f : ℂ → ℂ) : ℂ :=
  ∑ n ∈ range (N + 1), (-1 : ℂ) ^ n * (N.choose n : ℂ) * f ((n : ℂ) / N)

theorem nodes_injOn {N : ℕ} (hN : 1 ≤ N) : Set.InjOn (fun j : ℕ => (j : ℂ) / N) ((Finset.range (N + 1) : Finset ℕ) : Set ℕ) := by
  intro i _ j _ hij
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  simp only at hij
  rw [div_left_inj' hN0] at hij
  exact_mod_cast hij

/-- **Partial fractions** for `1/ω_N`. -/
theorem partial_fractions {N : ℕ} (hN : 1 ≤ N) {z : ℂ} (hz : ∀ k ∈ range (N + 1), z ≠ (k : ℂ) / N) :
    (nodalN N z)⁻¹ = ∑ k ∈ range (N + 1), nodeW N k * (z - (k : ℂ) / N)⁻¹ := by
  set v : ℕ → ℂ := fun j => (j : ℂ) / N
  have h1 := congrArg (Polynomial.eval z) (Lagrange.sum_basis (nodes_injOn hN) ⟨0, mem_range.mpr (Nat.succ_pos N)⟩)
  rw [Polynomial.eval_finsetSum, Polynomial.eval_one] at h1
  rw [sum_congr rfl fun i hi => Lagrange.eval_basis_not_at_node (v := v) hi (hz i hi), ← mul_sum,
    Lagrange.eval_nodal] at h1
  exact inv_eq_of_mul_eq_one_right h1

/-- `Π_{j ≠ k} (k - j) = (-1)^{N-k} k! (N-k)!`. -/
theorem prod_node_diff {N k : ℕ} (hk : k ≤ N) :
    ∏ j ∈ (range (N + 1)).erase k, ((k : ℂ) - j) = (-1) ^ (N - k) * k.factorial * (N - k).factorial := by
  induction N, hk using Nat.le_induction with
  | base =>
    rw [range_add_one, erase_insert notMem_range_self, Nat.sub_self, pow_zero, Nat.factorial_zero,
      Nat.cast_one, one_mul, mul_one]
    clear! N
    induction k with
    | zero => simp
    | succ k ih =>
      rw [prod_range_succ', Nat.factorial_succ]
      push_cast
      simp only [add_sub_add_right_eq_sub] at *
      rw [ih]; ring
  | succ N hkN ih =>
    rw [range_add_one, erase_insert_of_ne (by omega), prod_insert (by simp), ih,
      show N + 1 - k = (N - k) + 1 by omega, Nat.factorial_succ, pow_succ]
    push_cast [Nat.cast_sub hkN]
    ring

/-- `w_k = N^N (-1)^{N-k} C(N,k) / N!`. -/
theorem nodeW_eq {N k : ℕ} (hN : 1 ≤ N) (hk : k ≤ N) :
    nodeW N k = (N : ℂ) ^ N * (-1) ^ (N - k) * (N.choose k : ℂ) / N.factorial := by
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  have e : ∀ j ∈ (range (N + 1)).erase k, ((k : ℂ) / N - (j : ℂ) / N)⁻¹ = (N : ℂ) * ((k : ℂ) - j)⁻¹ := by
    intro j _; rw [← sub_div, inv_div, div_eq_mul_inv]
  rw [nodeW, prod_congr rfl e, prod_mul_distrib, prod_const, card_erase_of_mem (by simp; omega), card_range,
    Nat.add_sub_cancel, prod_inv_distrib, prod_node_diff hk]
  have hc : (N.choose k : ℂ) * k.factorial * (N - k).factorial = N.factorial := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hk
  have hf1 : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  have hf2 : ((N - k).factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  have hs : ((-1 : ℂ) ^ (N - k))⁻¹ = (-1) ^ (N - k) := by
    rw [← inv_pow, inv_neg, inv_one]
  have hcne : (N.choose k : ℂ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hk).ne'
  rw [← hc, mul_inv, mul_inv, hs]
  field_simp

/-- The residue sum is a multiple of the alternating binomial sum. -/
theorem sum_nodeW (f : ℂ → ℂ) {N : ℕ} (hN : 1 ≤ N) :
    ∑ k ∈ range (N + 1), nodeW N k * f ((k : ℂ) / N) =
      (-1) ^ N * ((N : ℂ) ^ N / N.factorial) * altBinom N f := by
  rw [altBinom, mul_sum]
  refine sum_congr rfl fun k hk => ?_
  have hk' : k ≤ N := Nat.lt_succ_iff.mp (mem_range.mp hk)
  rw [nodeW_eq hN hk']
  have hp : (-1 : ℂ) ^ (N - k) = (-1) ^ N * (-1) ^ k := by
    rw [← pow_add, show N + k = (N - k) + 2 * k by omega, pow_add, pow_mul, neg_one_sq, one_pow, mul_one]
  rw [hp]
  ring

/-! ### Linearity of rectangle integrals on the boundary -/

/-- The boundary of the rectangle with corners `z`, `w`. -/
def rectBd (z w : ℂ) : Set ℂ :=
  {x | x ∈ [[z.re, w.re]] ×ℂ [[z.im, w.im]] ∧ (x.re = z.re ∨ x.re = w.re ∨ x.im = z.im ∨ x.im = w.im)}

theorem bd_bot (z w : ℂ) {x : ℝ} (hx : x ∈ [[z.re, w.re]]) : (x : ℂ) + z.im * I ∈ rectBd z w :=
  ⟨⟨by simpa using hx, by simp⟩, by simp⟩

theorem bd_top (z w : ℂ) {x : ℝ} (hx : x ∈ [[z.re, w.re]]) : (x : ℂ) + w.im * I ∈ rectBd z w :=
  ⟨⟨by simpa using hx, by simp⟩, by simp⟩

theorem bd_right (z w : ℂ) {y : ℝ} (hy : y ∈ [[z.im, w.im]]) : (w.re : ℂ) + y * I ∈ rectBd z w :=
  ⟨⟨by simp, by simpa using hy⟩, by simp⟩

theorem bd_left (z w : ℂ) {y : ℝ} (hy : y ∈ [[z.im, w.im]]) : (z.re : ℂ) + y * I ∈ rectBd z w :=
  ⟨⟨by simp, by simpa using hy⟩, by simp⟩

theorem rectInt_congr_bd (f g : ℂ → ℂ) (z w : ℂ) (hfg : ∀ x ∈ rectBd z w, f x = g x) :
    rectInt f z w = rectInt g z w :=
  rectInt_congr f g z w (fun _ hx => hfg _ (bd_bot z w hx)) (fun _ hx => hfg _ (bd_top z w hx))
    (fun _ hy => hfg _ (bd_right z w hy)) (fun _ hy => hfg _ (bd_left z w hy))

theorem edge_integrable_bd (g : ℂ → ℂ) (z w : ℂ) (hg : ContinuousOn g (rectBd z w)) :
    IntervalIntegrable (fun x : ℝ => g (x + z.im * I)) volume z.re w.re ∧
      IntervalIntegrable (fun x : ℝ => g (x + w.im * I)) volume z.re w.re ∧
      IntervalIntegrable (fun y : ℝ => g (re w + y * I)) volume z.im w.im ∧
      IntervalIntegrable (fun y : ℝ => g (re z + y * I)) volume z.im w.im :=
  ⟨(hg.comp (by fun_prop) fun _ hx => bd_bot z w hx).intervalIntegrable,
    (hg.comp (by fun_prop) fun _ hx => bd_top z w hx).intervalIntegrable,
    (hg.comp (by fun_prop) fun _ hy => bd_right z w hy).intervalIntegrable,
    (hg.comp (by fun_prop) fun _ hy => bd_left z w hy).intervalIntegrable⟩

theorem rectInt_const_mul (g : ℂ → ℂ) (a z w : ℂ) : rectInt (fun x => a * g x) z w = a * rectInt g z w := by
  simp only [rectInt, smul_eq_mul, intervalIntegral.integral_const_mul]
  ring

theorem rectInt_sum {ι : Type*} (s : Finset ι) (g : ι → ℂ → ℂ) (z w : ℂ)
    (hg : ∀ i ∈ s, ContinuousOn (g i) (rectBd z w)) :
    rectInt (fun x => ∑ i ∈ s, g i x) z w = ∑ i ∈ s, rectInt (g i) z w := by
  simp only [rectInt, smul_eq_mul]
  rw [intervalIntegral.integral_finsetSum fun i hi => (edge_integrable_bd _ z w (hg i hi)).1,
    intervalIntegral.integral_finsetSum fun i hi => (edge_integrable_bd _ z w (hg i hi)).2.1,
    intervalIntegral.integral_finsetSum fun i hi => (edge_integrable_bd _ z w (hg i hi)).2.2.1,
    intervalIntegral.integral_finsetSum fun i hi => (edge_integrable_bd _ z w (hg i hi)).2.2.2]
  simp only [mul_sum, ← sum_sub_distrib, ← sum_add_distrib]

/-! ### The residue identity on a grid -/

variable {c : ℂ} {h : ℝ}

theorem offGrid_re_ne (hh : 0 < h) {a : ℂ} (ha : OffGrid c h a) (i : ℤ) : a.re ≠ c.re + i * h := by
  intro e; apply ha.1 i; rw [e]; field_simp; ring

theorem offGrid_im_ne (hh : 0 < h) {a : ℂ} (ha : OffGrid c h a) (j : ℤ) : a.im ≠ c.im + j * h := by
  intro e; apply ha.2 j; rw [e]; field_simp; ring

/-- An off-grid point is not on the boundary of any grid square. -/
theorem offGrid_not_bd (hh : 0 < h) {a : ℂ} (ha : OffGrid c h a) (p : ℤ × ℤ) :
    a ∉ rectBd (sqLo c h p) (sqLo c h (p.1 + 1, p.2 + 1)) := by
  rintro ⟨-, h1 | h1 | h1 | h1⟩
  · exact offGrid_re_ne hh ha p.1 (by rw [h1, sqLo_re])
  · exact offGrid_re_ne hh ha (p.1 + 1) (by rw [h1, sqLo_re])
  · exact offGrid_im_ne hh ha p.2 (by rw [h1, sqLo_im])
  · exact offGrid_im_ne hh ha (p.2 + 1) (by rw [h1, sqLo_im])

theorem rectBd_subset_sqSet (p : ℤ × ℤ) : rectBd (sqLo c h p) (sqLo c h (p.1 + 1, p.2 + 1)) ⊆ sqSet c h p :=
  fun _ hx => hx.1

/-- **Residue identity**: if the squares of `S` lie in the domain of `f` and contain the nodes `k/N`,
which lie off the grid, then `Σ_{p ∈ S} ∮_{∂p} f/ω_N = 2πi Σ_k w_k f(k/N)`. -/
theorem residue_identity (hh : 0 < h) (f : ℂ → ℂ) (D : Set ℂ) (hD : IsOpen D) (hf : DifferentiableOn ℂ f D)
    (S : Finset (ℤ × ℤ)) (hS : ∀ p ∈ S, sqSet c h p ⊆ D) {N : ℕ} (hN : 1 ≤ N)
    (hoff : ∀ k ∈ range (N + 1), OffGrid c h ((k : ℂ) / N))
    (hin : ∀ k ∈ range (N + 1), sqIdx c h ((k : ℂ) / N) ∈ S) :
    ∑ p ∈ S, sqInt c h (fun x => f x * (nodalN N x)⁻¹) p =
      2 * Real.pi * I * ∑ k ∈ range (N + 1), nodeW N k * f ((k : ℂ) / N) := by
  have hpt : ∀ p ∈ S, sqInt c h (fun x => f x * (nodalN N x)⁻¹) p =
      ∑ k ∈ range (N + 1), nodeW N k * sqInt c h (fun x => f x * (x - (k : ℂ) / N)⁻¹) p := by
    intro p hp
    have hne : ∀ x ∈ rectBd (sqLo c h p) (sqLo c h (p.1 + 1, p.2 + 1)), ∀ k ∈ range (N + 1), x ≠ (k : ℂ) / N :=
      fun x hx k hk e => offGrid_not_bd hh (hoff k hk) p (e ▸ hx)
    rw [sqInt, rectInt_congr_bd _ (fun x => ∑ k ∈ range (N + 1), nodeW N k * (f x * (x - (k : ℂ) / N)⁻¹)) _ _
      fun x hx => by rw [partial_fractions hN (hne x hx), mul_sum]; exact sum_congr rfl fun k _ => by ring]
    rw [rectInt_sum]
    · exact sum_congr rfl fun k _ => rectInt_const_mul _ _ _ _
    · intro k hk
      refine continuousOn_const.mul (ContinuousOn.mul ?_ ?_)
      · exact hf.continuousOn.mono ((rectBd_subset_sqSet p).trans (hS p hp))
      · exact (continuousOn_id.sub continuousOn_const).inv₀ fun x hx => sub_ne_zero.mpr (hne x hx k hk)
  rw [sum_congr rfl hpt, sum_comm, mul_sum]
  refine sum_congr rfl fun k hk => ?_
  rw [← mul_sum, gridSum_cauchy hh f D hD hf S hS (hoff k hk), if_pos (hin k hk)]
  ring

end Szkraw
