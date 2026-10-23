import Szkraw.LCAssembly
import Szkraw.LogConcaveStatement

/-!
# P1, "Log-concavity is not necessary either": the positive case

For `D(i) = (1 - μ) i + μ [i]_q` with `μ = 1/10`, `q = 11/10`, the constant-ratio arrays with profile
`d_i = D(i)/D(N)` have property (P) for every `r ∈ (0, 1]` and `N ∈ {6, 8, 10, 12}`, although
`ν₁ ν₃ = 10 ν₂²` violates log-concavity of the Newton coefficients.

Proof. With `E_i = 10^N D(i) ∈ ℤ` and `S_m = ∏_{j<m} (E_N - E_j)`, the number `S_m g(m,n;k)` is a
homogeneous polynomial of degree `m` in `(r, 1 - r)` whose coefficients (Bernstein coefficients up to
binomial factors) are integers given by an exact recurrence (`htab`). The kernel checks that they are all
nonnegative (`checkAll`, by `decide +kernel`); `product_eq_of_rec` identifies the array with `productMatrix`.
-/

namespace Szkraw
namespace LCVPos

open Finset

/-! ### Homogeneous polynomials in `(r, s)` as coefficient lists -/

/-- `evH r s [p₀, …, p_d] = Σ pₑ rᵉ s^(d-e)`. -/
noncomputable def evH (r s : ℝ) : List ℤ → ℝ
  | [] => 0
  | x :: p => (x : ℝ) * s ^ p.length + r * evH r s p

def padd (p q : List ℤ) : List ℤ := List.zipWith (· + ·) p q
def pscale (c : ℤ) (p : List ℤ) : List ℤ := p.map (c * ·)
/-- Multiplication by `r`. -/
def mulR (p : List ℤ) : List ℤ := 0 :: p
/-- Multiplication by `s`. -/
def mulS (p : List ℤ) : List ℤ := p ++ [0]
/-- Multiplication by `r + s`. -/
def mulT (p : List ℤ) : List ℤ := padd (mulR p) (mulS p)

section ev

variable (r s : ℝ)

theorem evH_mulR (p : List ℤ) : evH r s (mulR p) = r * evH r s p := by
  simp [mulR, evH]

theorem evH_mulS (p : List ℤ) : evH r s (mulS p) = s * evH r s p := by
  induction p with
  | nil => simp [mulS, evH]
  | cons x p ih =>
    simp only [mulS] at ih
    simp only [mulS, List.cons_append, evH, List.length_append, List.length_cons, List.length_nil, ih]
    ring

theorem length_padd (p q : List ℤ) : (padd p q).length = min p.length q.length :=
  List.length_zipWith ..

theorem evH_padd : ∀ p q : List ℤ, p.length = q.length → evH r s (padd p q) = evH r s p + evH r s q
  | [], [], _ => by simp [padd, evH]
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | x :: p, y :: q, h => by
    have h' : p.length = q.length := by simpa using h
    have e : padd (x :: p) (y :: q) = (x + y) :: padd p q := rfl
    rw [e, evH, evH, evH, evH_padd p q h', length_padd, h', min_self]
    push_cast; ring

theorem evH_pscale (c : ℤ) : ∀ p : List ℤ, evH r s (pscale c p) = c * evH r s p
  | [] => by simp [pscale, evH]
  | x :: p => by
    have e : pscale c (x :: p) = (c * x) :: pscale c p := rfl
    rw [e, evH, evH, evH_pscale c p, show (pscale c p).length = p.length from List.length_map ..]
    push_cast; ring

theorem evH_mulT (p : List ℤ) : evH r s (mulT p) = (r + s) * evH r s p := by
  rw [mulT, evH_padd _ _ _ _ (by simp [mulR, mulS]), evH_mulR, evH_mulS]; ring

theorem evH_nonneg (hr : 0 ≤ r) (hs : 0 ≤ s) : ∀ p : List ℤ, (∀ x ∈ p, 0 ≤ x) → 0 ≤ evH r s p
  | [], _ => by simp [evH]
  | x :: p, h => by
    rw [evH]
    have hx : (0 : ℝ) ≤ x := by exact_mod_cast h x (by simp)
    exact add_nonneg (mul_nonneg hx (pow_nonneg hs _))
      (mul_nonneg hr (evH_nonneg hr hs p fun y hy => h y (by simp [hy])))

end ev

/-! ### The integer tables -/

abbrev Tab := List (List (List ℤ))

/-- Entry `(n, k)` of a table, with the zero polynomial of length `d` outside it. -/
def tget (T : Tab) (d n k : ℕ) : List ℤ := (T.getD n []).getD k (List.replicate d 0)

def build (N : ℕ) (f : ℕ → ℕ → List ℤ) : Tab :=
  (List.range (N + 1)).map fun n => (List.range (N + 1)).map fun k => f n k

theorem tget_build (N d n k : ℕ) (f : ℕ → ℕ → List ℤ) :
    tget (build N f) d n k = if n ≤ N ∧ k ≤ N then f n k else List.replicate d 0 := by
  unfold tget build
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range]
  by_cases hn : n ≤ N <;> by_cases hk : k ≤ N <;>
    simp [hn, hk, show n < N + 1 ↔ n ≤ N by omega, show k < N + 1 ↔ k ≤ N by omega]

/-- `E_i`, read from the list `E`. -/
def eE (E : List ℤ) (i : ℕ) : ℤ := E.getD i 0

/-- One step of the scaled recurrence: from `H_{m-1}` (`P`) and `H_m` (`C`) to `H_{m+1}`. -/
def hstep (E : List ℤ) (N m : ℕ) (P C : Tab) : Tab :=
  build N fun n k =>
    padd (padd (padd
      (pscale (eE E N - eE E n) (mulT (tget C (m + 1) (n + 1) k)))
      (pscale (eE E n - eE E m) (mulS (tget C (m + 1) n k))))
      (pscale (eE E n) (mulR (tget C (m + 1) (n - 1) k))))
      (pscale (-(eE E m * (eE E N - eE E (m - 1)))) (mulR (mulT (tget P m n k))))

/-- `(H_{m-1}, H_m)`. -/
def htab (E : List ℤ) (N : ℕ) : ℕ → Tab × Tab
  | 0 => ([], build N fun n k => if n = k then [1] else [0])
  | m + 1 => ((htab E N m).2, hstep E N m (htab E N m).1 (htab E N m).2)

/-- All coefficients of all `H_m(n, k)`, `m, n, k ≤ N`, are nonnegative. -/
def checkAll (E : List ℤ) (N : ℕ) : Bool :=
  (List.range (N + 1)).all fun m => (List.range (N + 1)).all fun n => (List.range (N + 1)).all fun k =>
    (tget (htab E N m).2 (m + 1) n k).all fun x => decide (0 ≤ x)

theorem htab_len (E : List ℤ) (N : ℕ) : ∀ m n k,
    (tget (htab E N m).2 (m + 1) n k).length = m + 1 ∧ (tget (htab E N m).1 m n k).length = m
  | 0, n, k => by
    constructor
    · simp only [htab, tget_build]; split_ifs <;> simp
    · simp [htab, tget]
  | m + 1, n, k => by
    have h1 := fun n k => (htab_len E N m n k).1
    have h2 := fun n k => (htab_len E N m n k).2
    constructor
    · simp only [htab, hstep, tget_build]
      split_ifs
      · simp [length_padd, mulT, mulR, mulS, pscale, h1, h2]
      · simp
    · exact h1 n k

/-! ### The real coefficients -/

section real

variable (E : List ℤ) (N : ℕ)

/-- `S_m = ∏_{j<m} (E_N - E_j)`. -/
noncomputable def S : ℕ → ℝ
  | 0 => 1
  | m + 1 => S m * ((eE E N : ℝ) - eE E m)

/-- The candidate for `g(m,n;k)`: `H_m(n,k)(r, 1 - r) / S_m`. -/
noncomputable def G (r : ℝ) (m n k : ℕ) : ℝ := evH r (1 - r) (tget (htab E N m).2 (m + 1) n k) / S E N m

variable {E N}

theorem S_pos (hlt : ∀ i < N, eE E i < eE E N) : ∀ m, m ≤ N → 0 < S E N m
  | 0, _ => by simp [S]
  | m + 1, h => by
    have := S_pos hlt m (by omega)
    have hm : (eE E m : ℝ) < eE E N := by exact_mod_cast hlt m (by omega)
    simp only [S]
    exact mul_pos this (by linarith)

theorem G_rec (hlt : ∀ i < N, eE E i < eE E N) (hE0 : eE E 0 = 0) (v : Coefficients N) (r : ℝ)
    (ha : ∀ i, i ≤ N → v.a i = 1 - (eE E i : ℝ) / eE E N)
    (hb : ∀ i, i ≤ N → v.b i = (1 - r) * ((eE E i : ℝ) / eE E N))
    (hc : ∀ i, i ≤ N → v.c i = r * ((eE E i : ℝ) / eE E N))
    (m n k : ℕ) (hm : m + 1 ≤ N) (hn : n ≤ N) (hk : k ≤ N) :
    v.a m * G E N r (m + 1) n k =
      (if n + 1 ≤ N then v.a n * G E N r m (n + 1) k else 0) + v.b n * G E N r m n k +
      (if 1 ≤ n then v.c n * G E N r m (n - 1) k else 0) - v.b m * G E N r m n k -
      (if 1 ≤ m then v.c m * G E N r (m - 1) n k else 0) := by
  have hEN : (0 : ℝ) < eE E N := by
    have := hlt 0 (by omega); rw [hE0] at this; exact_mod_cast this
  have hEm : (eE E m : ℝ) < eE E N := by exact_mod_cast hlt m (by omega)
  have hSm := S_pos hlt m (by omega)
  have h1 := fun n k => (htab_len E N m n k).1
  have h2 := fun n k => (htab_len E N m n k).2
  set X1 := evH r (1 - r) (tget (htab E N m).2 (m + 1) (n + 1) k)
  set X2 := evH r (1 - r) (tget (htab E N m).2 (m + 1) n k)
  set X3 := evH r (1 - r) (tget (htab E N m).2 (m + 1) (n - 1) k)
  set Y := evH r (1 - r) (tget (htab E N m).1 m n k)
  have hL : evH r (1 - r) (tget (htab E N (m + 1)).2 (m + 1 + 1) n k) =
      ((eE E N : ℝ) - eE E n) * X1 + ((eE E n : ℝ) - eE E m) * (1 - r) * X2 + (eE E n : ℝ) * r * X3 -
        (eE E m : ℝ) * ((eE E N : ℝ) - eE E (m - 1)) * r * Y := by
    simp only [htab, hstep, tget_build, if_pos (And.intro hn hk)]
    rw [evH_padd _ _ _ _ (by simp [length_padd, mulT, mulR, mulS, pscale, h1, h2]),
      evH_padd _ _ _ _ (by simp [length_padd, mulT, mulR, mulS, pscale, h1, h2]),
      evH_padd _ _ _ _ (by simp [length_padd, mulT, mulR, mulS, pscale, h1])]
    simp only [evH_pscale, evH_mulT, evH_mulS, evH_mulR]
    push_cast
    ring
  have hG1 : G E N r (m + 1) n k =
      (((eE E N : ℝ) - eE E n) * X1 + ((eE E n : ℝ) - eE E m) * (1 - r) * X2 + (eE E n : ℝ) * r * X3 -
        (eE E m : ℝ) * ((eE E N : ℝ) - eE E (m - 1)) * r * Y) / (S E N m * ((eE E N : ℝ) - eE E m)) := by
    rw [G, hL]; rfl
  rw [hG1, ha m (by omega), hb m (by omega), hb n hn]
  have hX2 : G E N r m n k = X2 / S E N m := rfl
  rw [hX2]
  have hEm' : (eE E N : ℝ) - eE E m ≠ 0 := by linarith
  -- the three boundary cases
  have hA : (if n + 1 ≤ N then v.a n * G E N r m (n + 1) k else 0) =
      (1 - (eE E n : ℝ) / eE E N) * (X1 / S E N m) := by
    split_ifs with h
    · rw [ha n hn]; rfl
    · have : n = N := by omega
      subst this; simp [div_self (ne_of_gt hEN)]
  have hC : (if 1 ≤ n then v.c n * G E N r m (n - 1) k else 0) =
      r * ((eE E n : ℝ) / eE E N) * (X3 / S E N m) := by
    split_ifs with h
    · rw [hc n hn]; rfl
    · have : n = 0 := by omega
      subst this; simp [hE0]
  have hD : (if 1 ≤ m then v.c m * G E N r (m - 1) n k else 0) =
      r * ((eE E m : ℝ) / eE E N) * ((eE E N : ℝ) - eE E (m - 1)) * (Y / S E N m) := by
    split_ifs with h
    · obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      rw [hc (m' + 1) (by omega)]
      have hm' : (eE E m' : ℝ) < eE E N := by exact_mod_cast hlt m' (by omega)
      have hSm' := S_pos hlt m' (by omega)
      have hY : Y = evH r (1 - r) (tget (htab E N m').2 (m' + 1) n k) := rfl
      have hS : S E N (m' + 1) = S E N m' * ((eE E N : ℝ) - eE E m') := rfl
      have hm'' : (eE E N : ℝ) - eE E m' ≠ 0 := by linarith
      simp only [Nat.add_sub_cancel, G, hY, hS]
      field_simp
    · have : m = 0 := by omega
      subst this; simp [hE0]
  rw [hA, hC, hD]
  field_simp
  ring

/-- Soundness: if the kernel check passes, every array with these coefficients has (P) for `0 ≤ r ≤ 1`. -/
theorem matrixPositivity_of_check (hN : 1 ≤ N) (hlt : ∀ i < N, eE E i < eE E N) (hE0 : eE E 0 = 0)
    (hcheck : checkAll E N = true) (v : Coefficients N) (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (ha : ∀ i, i ≤ N → v.a i = 1 - (eE E i : ℝ) / eE E N)
    (hb : ∀ i, i ≤ N → v.b i = (1 - r) * ((eE E i : ℝ) / eE E N))
    (hc : ∀ i, i ≤ N → v.c i = r * ((eE E i : ℝ) / eE E N)) : MatrixPositivity v := by
  have hEN : (0 : ℝ) < eE E N := by
    have := hlt 0 (by omega); rw [hE0] at this; exact_mod_cast this
  have hva : ∀ i, i < N → v.a i ≠ 0 := by
    intro i hi
    have hi' : (eE E i : ℝ) < eE E N := by exact_mod_cast hlt i hi
    rw [ha i hi.le]
    have : (eE E i : ℝ) / eE E N < 1 := (div_lt_one hEN).2 hi'
    linarith
  have h0 : ∀ n k : ℕ, n ≤ N → k ≤ N → G E N r 0 n k = if n = k then 1 else 0 := by
    intro n k hn hk
    simp only [G, S, htab, tget_build, if_pos (And.intro hn hk)]
    split_ifs <;> simp [evH]
  intro m hm i j
  rw [product_eq_of_rec v (G E N r) hva h0
    (fun m n k hm hn hk => G_rec hlt hE0 v r ha hb hc m n k hm hn hk) m hm i j]
  apply div_nonneg _ (S_pos hlt m hm).le
  apply evH_nonneg _ _ hr0 (by linarith)
  simp only [checkAll, List.all_eq_true, List.mem_range, decide_eq_true_eq] at hcheck
  exact hcheck m (by omega) i (by omega) j (by omega)

end real

/-! ### The four arrays -/

/-- `E_i = 10^N D(i)` for `N = 6`. -/
def E6 : List ℤ := [0, 1000000, 2010000, 3031000, 4064100, 5110510, 6171561]
def E8 : List ℤ := [0, 100000000, 201000000, 303100000, 406410000, 511051000, 617156100, 724871710, 834358881]
def E10 : List ℤ := [0, 10000000000, 20100000000, 30310000000, 40641000000, 51105100000, 61715610000,
  72487171000, 83435888100, 94579476910, 105937424601]
def E12 : List ℤ := [0, 1000000000000, 2010000000000, 3031000000000, 4064100000000, 5110510000000,
  6171561000000, 7248717100000, 8343588810000, 9457947691000, 10593742460100, 11753116706110,
  12938428376721]

theorem check6 : checkAll E6 6 = true := by decide +kernel
theorem check8 : checkAll E8 8 = true := by decide +kernel
theorem check10 : checkAll E10 10 = true := by decide +kernel
theorem check12 : checkAll E12 12 = true := by decide +kernel

/-- The list `E` for `N ∈ {6, 8, 10, 12}`. -/
def lcvE : ℕ → List ℤ
  | 6 => E6
  | 8 => E8
  | 10 => E10
  | 12 => E12
  | _ => []

theorem lcvE_check (N : ℕ) (hN : N = 6 ∨ N = 8 ∨ N = 10 ∨ N = 12) :
    checkAll (lcvE N) N = true ∧ (∀ i < N, eE (lcvE N) i < eE (lcvE N) N) ∧ eE (lcvE N) 0 = 0 ∧
      ∀ i < N, 0 < eE (lcvE N) (i + 1) := by
  rcases hN with rfl | rfl | rfl | rfl
  · exact ⟨check6, by decide +kernel, by decide +kernel, by decide +kernel⟩
  · exact ⟨check8, by decide +kernel, by decide +kernel, by decide +kernel⟩
  · exact ⟨check10, by decide +kernel, by decide +kernel, by decide +kernel⟩
  · exact ⟨check12, by decide +kernel, by decide +kernel, by decide +kernel⟩

/-- `D(i) = (1 - μ) i + μ [i]_q` with `μ = 1/10`, `q = 11/10`. -/
noncomputable def lcvD (i : ℕ) : ℝ := (1 - 1 / 10) * i + 1 / 10 * ∑ j ∈ range i, (11 / 10 : ℝ) ^ j

theorem lcvE_ratio (N : ℕ) (hN : N = 6 ∨ N = 8 ∨ N = 10 ∨ N = 12) (i : ℕ) (hi : i ≤ N) :
    (eE (lcvE N) i : ℝ) / eE (lcvE N) N = lcvD i / lcvD N := by
  rcases hN with rfl | rfl | rfl | rfl <;> interval_cases i <;>
    norm_num [lcvD, lcvE, eE, E6, E8, E10, E12, sum_range_succ]

end LCVPos

open LCVPos in
/-- **P1, "Log-concavity is not necessary either", the positive case.** Let `D(i) = (1-μ) i + μ [i]_q` with
`μ = 1/10`, `q = 11/10` (`lcvD`), `N ∈ {6, 8, 10, 12}` and `0 < r ≤ 1`. The constant-ratio array with ratio `r`
and profile `d_i = D(i)/D(N)` exists and is admissible; every such array has Newton coefficients with
`ν₁ ν₃ = (1/μ) ν₂² = 10 ν₂²`, so they are not log-concave, and it has property (P): every `g(m,n;k)` is
nonnegative. -/
theorem lc_violation_holds (N : ℕ) (hN : N = 6 ∨ N = 8 ∨ N = 10 ∨ N = 12) (r : ℝ) (hr0 : 0 < r)
    (hr1 : r ≤ 1) :
    (∃ v : Coefficients N, Admissible v ∧ (∀ i, i ≤ N → v.c i = r * profile v i) ∧
      ∀ i, i ≤ N → profile v i = lcvD i / lcvD N) ∧
    ∀ v : Coefficients N, Admissible v → (∀ i, i ≤ N → v.c i = r * profile v i) →
      (∀ i, i ≤ N → profile v i = lcvD i / lcvD N) →
      newtonCoeff (profile v) 1 * newtonCoeff (profile v) 3 = 10 * newtonCoeff (profile v) 2 ^ 2 ∧
      ¬ LogConcaveNoInternalZeros N (newtonCoeff (profile v)) ∧ MatrixPositivity v := by
  obtain ⟨hcheck, hlt, hE0, hpos⟩ := lcvE_check N hN
  have hN1 : 1 ≤ N := by omega
  have hN3 : 3 ≤ N := by omega
  have hEN : (0 : ℝ) < eE (lcvE N) N := by
    obtain ⟨n, hn⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
    rw [hn] at hpos ⊢; exact_mod_cast hpos n (by omega)
  have hrat := lcvE_ratio N hN
  have hDN : lcvD N ≠ 0 := by
    intro h
    have := hrat N le_rfl
    rw [h, div_zero, div_self (ne_of_gt hEN)] at this
    exact one_ne_zero this
  refine ⟨⟨⟨fun i => 1 - lcvD i / lcvD N, fun i => (1 - r) * (lcvD i / lcvD N),
    fun i => r * (lcvD i / lcvD N)⟩, ?_, fun i _ => ?_, fun i _ => ?_⟩, fun v hv hc hp => ?_⟩
  · refine ⟨hN1, by simp [lcvD], by simp [lcvD], by simp [lcvD], by simp [div_self hDN],
      fun i _ => by ring, fun i hi => ?_, fun i hi hiN => ?_⟩
    · show 0 < 1 - lcvD i / lcvD N
      rw [← hrat i hi.le]
      have : (eE (lcvE N) i : ℝ) < eE (lcvE N) N := by exact_mod_cast hlt i hi
      have := (div_lt_one hEN).2 this
      linarith
    · show 0 < r * (lcvD i / lcvD N)
      rw [← hrat i hiN]
      have : (0 : ℝ) < eE (lcvE N) i := by
        obtain ⟨n, rfl⟩ : ∃ n, i = n + 1 := ⟨i - 1, by omega⟩
        exact_mod_cast hpos n (by omega)
      positivity
  · simp only [profile]; ring
  · simp only [profile]; ring
  · -- the coefficients on `0 ≤ i ≤ N`
    have hd : ∀ i, i ≤ N → profile v i = (eE (lcvE N) i : ℝ) / eE (lcvE N) N := fun i hi => by
      rw [hp i hi, hrat i hi]
    have hcv : ∀ i, i ≤ N → v.c i = r * ((eE (lcvE N) i : ℝ) / eE (lcvE N) N) := fun i hi => by
      rw [hc i hi, hd i hi]
    have hbv : ∀ i, i ≤ N → v.b i = (1 - r) * ((eE (lcvE N) i : ℝ) / eE (lcvE N) N) := fun i hi => by
      have h1 : profile v i = v.b i + v.c i := rfl
      rw [hd i hi, hcv i hi] at h1
      linarith
    have hav : ∀ i, i ≤ N → v.a i = 1 - (eE (lcvE N) i : ℝ) / eE (lcvE N) N := fun i hi => by
      have h1 := hv.2.2.2.2.2.1 i hi
      rw [hbv i hi, hcv i hi] at h1
      linarith
    -- Newton coefficients
    have hnu : newtonCoeff (profile v) 1 = 1 / lcvD N ∧ newtonCoeff (profile v) 2 = (1 / 100) / lcvD N ∧
        newtonCoeff (profile v) 3 = (1 / 1000) / lcvD N := by
      simp only [newtonCoeff, Finset.sum_range_succ, Finset.sum_range_zero]
      rw [hp 0 (by omega), hp 1 (by omega), hp 2 (by omega), hp 3 (by omega)]
      simp only [lcvD, Finset.sum_range_succ, Finset.sum_range_zero]
      refine ⟨?_, ?_, ?_⟩ <;> norm_num [Nat.choose] <;> field_simp <;> ring
    obtain ⟨h1, h2, h3⟩ := hnu
    refine ⟨by rw [h1, h2, h3]; field_simp; ring, fun hlc => ?_,
      matrixPositivity_of_check hN1 hlt hE0 hcheck v r hr0.le hr1 hav hbv hcv⟩
    have := hlc.2.2.1 2 le_rfl (by omega)
    rw [show 2 - 1 = 1 from rfl, h1, h2, h3] at this
    have key : 1 / lcvD N * (1 / 1000 / lcvD N) - (1 / 100 / lcvD N) ^ 2 = 9 / 10000 / lcvD N ^ 2 := by
      field_simp; ring
    have : (0 : ℝ) < 9 / 10000 / lcvD N ^ 2 := by positivity
    linarith

end Szkraw
