import Szkraw.ColumnCheck

/-!
# P3, Section 9 and open problems: constant-ratio counterexamples to shape conditions on the profile

Each example is a constant-ratio array `a = 1 - d`, `b = (1 - r) d`, `c = r d` whose profile `d` has prescribed
increments: one kink (`m` unit increments, then `1 + δ`), log-concave increments (`k` steps of ratio `1 + 1/(2N)`,
then flat), or log-convex increments. The statement says that the array exists and is admissible and that every
admissible array with this profile and ratio has `g(N,N;N) < 0`; the sign is decided by an exact column of the
product table, evaluated in the kernel (`ColCheck.ratio_example`).
-/

namespace Szkraw

open Finset ColCheck

/-- The normalized profile with increments `e`: `d_i = (Σ_{j<i} e_j) / (Σ_{j<N} e_j)`. -/
noncomputable def incProfile (e : ℕ → ℝ) (N i : ℕ) : ℝ := (∑ j ∈ range i, e j) / ∑ j ∈ range N, e j

/-- One-kink increments: `1` for the first `m` steps, then `1 + δ`. -/
noncomputable def kinkInc (m : ℕ) (δ : ℝ) (j : ℕ) : ℝ := if j < m then 1 else 1 + δ

/-- Log-concave increments: `k` steps of ratio `q`, then flat (`e_j = q^min(j,k)`). -/
noncomputable def stepInc (q : ℝ) (k j : ℕ) : ℝ := q ^ min j k

namespace ColCheck

/-- `Σ_{j<i} inc_j` as a list sum (evaluated by the kernel). -/
def psum (inc : ℕ → ℤ) (i : ℕ) : ℤ := ((List.range i).map inc).sum

theorem psum_eq (inc : ℕ → ℤ) (i : ℕ) : (psum inc i : ℝ) = ∑ j ∈ range i, (inc j : ℝ) := by
  induction i with
  | zero => simp [psum]
  | succ i ih =>
    have h : psum inc (i + 1) = psum inc i + inc i := by
      simp [psum, List.range_succ, List.map_append, List.sum_append]
    rw [h, Int.cast_add, ih, Finset.sum_range_succ]

/-- A constant-ratio counterexample whose profile has the increments `e_j = inc_j / w`. -/
theorem incProfile_example (inc : ℕ → ℤ) (w : ℤ) (e : ℕ → ℝ) (p q : ℤ) (r : ℝ) (N : ℕ) (hw : 0 < w)
    (he : ∀ j < N, e j = (inc j : ℝ) / w) (hr : r = (p : ℝ) / q) (hN : 1 ≤ N) (hq : 0 < q)
    (hlt : ∀ i < N, psum inc i < psum inc N) (hDpos : ∀ i < N, 0 < psum inc (i + 1))
    (hp : ∀ i < N, 0 < p) (hbm : ∀ i < N, (q - p) * psum inc i ≤ (q - p) * psum inc (i + 1))
    (m n k : ℕ) (hm : m ≤ N) (hn : n < N + 1) (hk : k < N + 1)
    (hneg : eG (ccol (rA (psum inc) q N) (rB (psum inc) (fun _ => p) q N) (rC (psum inc) (fun _ => p) N)
      N k m).2 n < 0) :
    (∃ v : Coefficients N, Admissible v ∧ (∀ i, i ≤ N → profile v i = incProfile e N i) ∧
      ∀ i, i ≤ N → v.c i = r * profile v i) ∧
    ∀ v : Coefficients N, Admissible v → (∀ i, i ≤ N → profile v i = incProfile e N i) →
      (∀ i, i ≤ N → v.c i = r * profile v i) → productMatrix v m ⟨n, hn⟩ ⟨k, hk⟩ < 0 := by
  have hw' : (w : ℝ) ≠ 0 := by exact_mod_cast hw.ne'
  have hs : ∀ i, i ≤ N → ∑ j ∈ range i, e j = (∑ j ∈ range i, (inc j : ℝ)) / w := fun i hi => by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun j hj => he j (by simp at hj; omega)
  have hd : ∀ i, i ≤ N → incProfile e N i = (psum inc i : ℝ) / psum inc N := fun i hi => by
    simp only [incProfile, hs i hi, hs N le_rfl, psum_eq]
    rw [div_div_div_cancel_right₀ hw']
  have h := ratio_example (psum inc) (fun _ => p) q N (incProfile e N) (fun _ => r) hN hq rfl hlt hDpos
    hp hd (fun i _ => hr) hbm m n k hm hn hk hneg
  exact ⟨h.1, fun v hv h1 h2 => (h.2 v hv h1 h2).2⟩

end ColCheck

/-! ### One-kink profiles (P3, Section 9 table and open problems) -/

/-- Shape of the one-kink statements: constant ratio `r`, profile with increments `kinkInc m δ`. -/
def KinkFails (r δ : ℝ) (N m : ℕ) : Prop :=
  (∃ v : Coefficients N, Admissible v ∧ (∀ i, i ≤ N → profile v i = incProfile (kinkInc m δ) N i) ∧
    ∀ i, i ≤ N → v.c i = r * profile v i) ∧
  ∀ v : Coefficients N, Admissible v → (∀ i, i ≤ N → profile v i = incProfile (kinkInc m δ) N i) →
    (∀ i, i ≤ N → v.c i = r * profile v i) → productMatrix v N (Fin.last N) (Fin.last N) < 0

/-- Integer increments `w` (first `m` steps) and `w + u` for `δ = u/w`. -/
def kinkZ (m : ℕ) (u w : ℤ) (j : ℕ) : ℤ := if j < m then w else w + u

theorem kinkInc_eq (m : ℕ) (u w : ℤ) (hw : (w : ℝ) ≠ 0) (j : ℕ) :
    kinkInc m ((u : ℝ) / w) j = (kinkZ m u w j : ℝ) / w := by
  unfold kinkInc kinkZ
  split_ifs <;> push_cast <;> field_simp

/-- `r = 1/2`, `N = 14`: seven unit increments, then `6/5` (P3, open problems). -/
theorem kink14_fails : KinkFails (1 / 2) (1 / 5) 14 7 := by
  have h := incProfile_example (kinkZ 7 1 5) 5 (kinkInc 7 ((1 : ℤ) / (5 : ℤ) : ℝ)) 1 2 (1 / 2) 14 (by norm_num)
    (fun j _ => kinkInc_eq 7 1 5 (by norm_num) j) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) 14 14 14 le_rfl (by norm_num) (by norm_num)
    (by decide +kernel)
  norm_num at h
  exact h

/-- `r = 2/5`, `N = 20`: twelve unit increments, then `21/20` (P3, Section 9 table and open problems). -/
theorem kink20_2_5_fails : KinkFails (2 / 5) (1 / 20) 20 12 := by
  have h := incProfile_example (kinkZ 12 1 20) 20 (kinkInc 12 (((1 : ℤ) : ℝ) / ((20 : ℤ) : ℝ))) 2 5 (2 / 5) 20
    (by norm_num) (fun j _ => kinkInc_eq 12 1 20 (by norm_num) j) (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) 20 20 20 le_rfl
    (by norm_num) (by norm_num) (by decide +kernel)
  norm_num at h
  exact h

/-- `r = 1/3`, `N = 40`, `m = 28`, `δ = 1/5` (P3, Section 9 table). -/
theorem kink40_1_3_fails : KinkFails (1 / 3) (1 / 5) 40 28 := by
  have h := incProfile_example (kinkZ 28 1 5) 5 (kinkInc 28 (((1 : ℤ) : ℝ) / ((5 : ℤ) : ℝ))) 1 3 (1 / 3) 40
    (by norm_num) (fun j _ => kinkInc_eq 28 1 5 (by norm_num) j) (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) 40 40 40 le_rfl
    (by norm_num) (by norm_num) (by decide +kernel)
  norm_num at h
  exact h

/-- `r = 3/10`, `N = 40`, `m = 28`, `δ = 1/10` (P3, Section 9 table). -/
theorem kink40_3_10_fails : KinkFails (3 / 10) (1 / 10) 40 28 := by
  have h := incProfile_example (kinkZ 28 1 10) 10 (kinkInc 28 (((1 : ℤ) : ℝ) / ((10 : ℤ) : ℝ))) 3 10 (3 / 10) 40
    (by norm_num) (fun j _ => kinkInc_eq 28 1 10 (by norm_num) j) (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) 40 40 40 le_rfl
    (by norm_num) (by norm_num) (by decide +kernel)
  norm_num at h
  exact h

/-- `r = 1/4`, `N = 60`, `m = 45`, `δ = 1/10` (P3, Section 9 table). -/
theorem kink60_1_4_fails : KinkFails (1 / 4) (1 / 10) 60 45 := by
  have h := incProfile_example (kinkZ 45 1 10) 10 (kinkInc 45 (((1 : ℤ) : ℝ) / ((10 : ℤ) : ℝ))) 1 4 (1 / 4) 60
    (by norm_num) (fun j _ => kinkInc_eq 45 1 10 (by norm_num) j) (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) 60 60 60 le_rfl
    (by norm_num) (by norm_num) (by decide +kernel)
  norm_num at h
  exact h

/-- `r = 2/7`, `N = 80`, `m = 60`, `δ = 1/5` (P3, Section 9 table). -/
theorem kink80_2_7_fails : KinkFails (2 / 7) (1 / 5) 80 60 := by
  have h := incProfile_example (kinkZ 60 1 5) 5 (kinkInc 60 (((1 : ℤ) : ℝ) / ((5 : ℤ) : ℝ))) 2 7 (2 / 7) 80
    (by norm_num) (fun j _ => kinkInc_eq 60 1 5 (by norm_num) j) (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) 80 80 80 le_rfl
    (by norm_num) (by norm_num) (by decide +kernel)
  norm_num at h
  exact h

/-- `r = 1/5`, `N = 100`, `m = 80`, `δ = 1/10` (P3, Section 9 table). -/
theorem kink100_1_5_fails : KinkFails (1 / 5) (1 / 10) 100 80 := by
  have h := incProfile_example (kinkZ 80 1 10) 10 (kinkInc 80 (((1 : ℤ) : ℝ) / ((10 : ℤ) : ℝ))) 1 5 (1 / 5) 100
    (by norm_num) (fun j _ => kinkInc_eq 80 1 10 (by norm_num) j) (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) 100 100 100 le_rfl
    (by norm_num) (by norm_num) (by decide +kernel)
  norm_num at h
  exact h

/-! ### Log-concave and log-convex increments -/

/-- Shape of the statements with increments `e`: constant ratio `r`, profile `incProfile e N`. -/
def IncFails (r : ℝ) (e : ℕ → ℝ) (N : ℕ) : Prop :=
  (∃ v : Coefficients N, Admissible v ∧ (∀ i, i ≤ N → profile v i = incProfile e N i) ∧
    ∀ i, i ≤ N → v.c i = r * profile v i) ∧
  ∀ v : Coefficients N, Admissible v → (∀ i, i ≤ N → profile v i = incProfile e N i) →
    (∀ i, i ≤ N → v.c i = r * profile v i) → productMatrix v N (Fin.last N) (Fin.last N) < 0

theorem stepInc_pos (q : ℝ) (hq : 0 < q) (k j : ℕ) : 0 < stepInc q k j := pow_pos hq _

/-- The increments `stepInc q k` with `q ≥ 1` are log-concave: step ratios at least `1` and nonincreasing. -/
theorem stepInc_logconcave (q : ℝ) (hq : 1 ≤ q) (k : ℕ) :
    (∀ j, 1 ≤ stepInc q k (j + 1) / stepInc q k j) ∧
    ∀ j, stepInc q k (j + 2) / stepInc q k (j + 1) ≤ stepInc q k (j + 1) / stepInc q k j := by
  have hq0 : 0 < q := by linarith
  have hr : ∀ j, stepInc q k (j + 1) / stepInc q k j = if j < k then q else 1 := fun j => by
    unfold stepInc
    split_ifs with h
    · rw [min_eq_left (by omega), min_eq_left (by omega), pow_succ]; field_simp
    · rw [min_eq_right (by omega), min_eq_right (by omega), div_self (pow_ne_zero _ hq0.ne')]
  refine ⟨fun j => ?_, fun j => ?_⟩
  · rw [hr]; split_ifs <;> linarith
  · rw [hr, hr]; split_ifs <;> first | linarith | omega

/-- Integer form of `stepInc (x/y) k j = x^a y^(k-a) / y^k`, `a = min j k`. -/
def stepZ (x y : ℤ) (k j : ℕ) : ℤ := x ^ min j k * y ^ (k - min j k)

theorem stepInc_eq (x y : ℤ) (hy : (y : ℝ) ≠ 0) (k j : ℕ) :
    stepInc ((x : ℝ) / y) k j = (stepZ x y k j : ℝ) / ((y ^ k : ℤ) : ℝ) := by
  unfold stepInc stepZ
  have ha : min j k ≤ k := min_le_right _ _
  push_cast
  rw [div_pow, div_eq_div_iff (pow_ne_zero _ hy) (pow_ne_zero _ hy), mul_assoc, ← pow_add,
    Nat.sub_add_cancel ha]

/-- `k` steps of ratio `1 + 1/(2N)`, then flat increments: `r = 2/5`, `N = 32`, `k = 22` (P3, Section 9). -/
theorem logconcave32_fails : IncFails (2 / 5) (stepInc (1 + 1 / (2 * 32)) 22) 32 := by
  have h := incProfile_example (stepZ 65 64 22) (64 ^ 22) (stepInc ((65 : ℤ) / (64 : ℤ) : ℝ) 22) 2 5 (2 / 5) 32
    (by norm_num) (fun j _ => stepInc_eq 65 64 (by norm_num) 22 j) (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) 32 32 32 le_rfl
    (by norm_num) (by norm_num) (by decide +kernel)
  norm_num at h
  rw [show (1 + 1 / (2 * 32) : ℝ) = 65 / 64 by norm_num]
  exact h

/-- `r = 1/2`, `N = 80`, `k = 40` steps of ratio `1 + 1/(2N)`, then flat increments (P3, Section 9). -/
theorem logconcave80_fails : IncFails (1 / 2) (stepInc (1 + 1 / (2 * 80)) 40) 80 := by
  have h := incProfile_example (stepZ 161 160 40) (160 ^ 40) (stepInc ((161 : ℤ) / (160 : ℤ) : ℝ) 40) 1 2
    (1 / 2) 80 (by norm_num) (fun j _ => stepInc_eq 161 160 (by norm_num) 40 j) (by norm_num) (by norm_num)
    (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) 80 80 80 le_rfl
    (by norm_num) (by norm_num) (by decide +kernel)
  norm_num at h
  rw [show (1 + 1 / (2 * 80) : ℝ) = 161 / 160 by norm_num]
  exact h

/-- `r = 1/3`, `N = 90`, `k = 62` steps of ratio `1 + 1/(2N)`, then flat increments (P3, Section 9). -/
theorem logconcave90_fails : IncFails (1 / 3) (stepInc (1 + 1 / (2 * 90)) 62) 90 := by
  have h := incProfile_example (stepZ 181 180 62) (180 ^ 62) (stepInc ((181 : ℤ) / (180 : ℤ) : ℝ) 62) 1 3
    (1 / 3) 90 (by norm_num) (fun j _ => stepInc_eq 181 180 (by norm_num) 62 j) (by norm_num) (by norm_num)
    (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) 90 90 90 le_rfl
    (by norm_num) (by norm_num) (by decide +kernel)
  norm_num at h
  rw [show (1 + 1 / (2 * 90) : ℝ) = 181 / 180 by norm_num]
  exact h

/-- Log-convex increments: fourteen unit increments, then `(21/20)^t`, `t = 1, …, 4`, i.e. `e_j = (21/20)^(j-13)`
for `j < 18` (truncated subtraction). -/
noncomputable def cvxInc (j : ℕ) : ℝ := (21 / 20 : ℝ) ^ (j - 13)

/-- The increments `cvxInc` are log-convex: step ratios at least `1` and nondecreasing. -/
theorem cvxInc_logconvex :
    (∀ j, 1 ≤ cvxInc (j + 1) / cvxInc j) ∧ ∀ j, cvxInc (j + 1) / cvxInc j ≤ cvxInc (j + 2) / cvxInc (j + 1) := by
  have hr : ∀ j, cvxInc (j + 1) / cvxInc j = if 13 ≤ j then 21 / 20 else 1 := fun j => by
    unfold cvxInc
    split_ifs with h
    · rw [show j + 1 - 13 = (j - 13) + 1 by omega, pow_succ]; field_simp
    · rw [show j + 1 - 13 = 0 by omega, show j - 13 = 0 by omega]; simp
  refine ⟨fun j => ?_, fun j => ?_⟩
  · rw [hr]; split_ifs <;> norm_num
  · rw [hr, hr]; split_ifs <;> first | omega | norm_num

/-- `r = 1/2`, `N = 18`, log-convex increments `cvxInc` (P3, open problems). -/
theorem logconvex18_fails : IncFails (1 / 2) cvxInc 18 := by
  have h := incProfile_example (fun j => 21 ^ (j - 13) * 20 ^ (4 - (j - 13))) (20 ^ 4) cvxInc 1 2 (1 / 2) 18
    (by norm_num) (fun j hj => by
      unfold cvxInc
      have : j - 13 ≤ 4 := by omega
      push_cast
      rw [div_pow, div_eq_div_iff (by positivity) (by positivity), mul_assoc, ← pow_add,
        Nat.sub_add_cancel this]
      norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) 18 18 18 le_rfl (by norm_num) (by norm_num) (by decide +kernel)
  norm_num at h
  exact h

end Szkraw
