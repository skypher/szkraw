import Szkraw.ColumnCheck
import Szkraw.UniformRules

/-!
# P3, Section 9: failures of property (P) along directions at `K_{N,r}`, `r < 1`

`krawDir N δb δc r ε` is `K_{N,r} + ε v` with `δb_n` for `1 ≤ n < N`, `δc_n` for `1 ≤ n ≤ N` (and `b_N = 1 - c_N`).
For the rule `β = 1`, `γ = 0` (P3, Section 9, computations away from `r = 1`) and for the terminal direction
`δc_N = 1`, `δb_N = -1` (P3, Section 9, fixed `r`), the arrays below are admissible with `b ≥ 0` and have a
negative product coefficient; the sign is decided by an exact column of the product table in the kernel.
-/

namespace Szkraw

open ColCheck

namespace ColCheck

/-- Numerators of `a` for `krawDir N δb δc (p/q) (u/E)` over `Q = q N E`. -/
def kA (N : ℕ) (δb δc : ℕ → ℤ) (p q u E : ℤ) : List ℤ := (List.range (N + 1)).map fun n =>
  if n = 0 then q * N * E else if n = N then 0 else
    q * N * E - ((q - p) * n * E + q * N * u * δb n) - (p * n * E + q * N * u * δc n)
/-- Numerators of `b`. -/
def kB (N : ℕ) (δb δc : ℕ → ℤ) (p q u E : ℤ) : List ℤ := (List.range (N + 1)).map fun n =>
  if n = 0 then 0 else if n = N then q * N * E - (p * n * E + q * N * u * δc n) else
    (q - p) * n * E + q * N * u * δb n
/-- Numerators of `c`. -/
def kC (N : ℕ) (δc : ℕ → ℤ) (p q u E : ℤ) : List ℤ := (List.range (N + 1)).map fun n =>
  if n = 0 then 0 else p * n * E + q * N * u * δc n

variable {N : ℕ} {δb δc : ℕ → ℤ} {δb' δc' : ℕ → ℝ} {p q u E : ℤ}

theorem krawDir_coeffs (hN : 1 ≤ N) (hq : 0 < q) (hE : 0 < E) (hb' : ∀ n, δb' n = δb n)
    (hc' : ∀ n, δc' n = δc n) (i : ℕ) (hi : i ≤ N) :
    let v := krawDir N δb' δc' ((p : ℝ) / q) ((u : ℝ) / E)
    let Q : ℝ := q * N * E
    v.a i = eG (kA N δb δc p q u E) i / Q ∧ v.b i = eG (kB N δb δc p q u E) i / Q ∧
      v.c i = eG (kC N δc p q u E) i / Q := by
  intro v Q
  have hq' : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have hE' : (E : ℝ) ≠ 0 := by exact_mod_cast hE.ne'
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have hQ : (q : ℝ) * N * E ≠ 0 := mul_ne_zero (mul_ne_zero hq' hN') hE'
  simp only [v, Q, krawDir, stochArray, kA, kB, kC, eG_map_range _ _ _ hi, hb', hc']
  refine ⟨?_, ?_, ?_⟩ <;> rw [eq_div_iff hQ] <;> split_ifs with h0 h1 <;> (try subst h0) <;>
    (try subst h1) <;> push_cast <;> field_simp <;> ring

/-- Integer checks give admissibility, `b ≥ 0`, and a negative coefficient. -/
theorem krawDir_example (hN : 1 ≤ N) (hq : 0 < q) (hE : 0 < E) (hb' : ∀ n, δb' n = δb n)
    (hc' : ∀ n, δc' n = δc n) (hApos : ∀ i < N, 0 < eG (kA N δb δc p q u E) i)
    (hCpos : ∀ i < N, 0 < eG (kC N δc p q u E) (i + 1)) (hBnn : ∀ i < N + 1, 0 ≤ eG (kB N δb δc p q u E) i)
    (m n k : ℕ) (hm : m ≤ N) (hn : n < N + 1) (hk : k < N + 1)
    (hneg : eG (ccol (kA N δb δc p q u E) (kB N δb δc p q u E) (kC N δc p q u E) N k m).2 n < 0) :
    let v := krawDir N δb' δc' ((p : ℝ) / q) ((u : ℝ) / E)
    Admissible v ∧ (∀ i, i ≤ N → 0 ≤ v.b i) ∧ productMatrix v m ⟨n, hn⟩ ⟨k, hk⟩ < 0 := by
  intro v
  have hQ : (0 : ℝ) < q * N * E := by
    have : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have : (0 : ℝ) < q := by exact_mod_cast hq
    have : (0 : ℝ) < E := by exact_mod_cast hE
    positivity
  have hco : ∀ i, i ≤ N → v.a i = eG (kA N δb δc p q u E) i / ((q : ℝ) * N * E) ∧
      v.b i = eG (kB N δb δc p q u E) i / ((q : ℝ) * N * E) ∧
      v.c i = eG (kC N δc p q u E) i / ((q : ℝ) * N * E) :=
    fun i hi => krawDir_coeffs (p := p) (u := u) hN hq hE hb' hc' i hi
  refine ⟨⟨hN, ?_, ?_, ?_, ?_, fun i hi => ?_, fun i hi => ?_, fun i hi hiN => ?_⟩, fun i hi => ?_, ?_⟩
  · simp [v, krawDir, stochArray]
  · simp [v, krawDir, stochArray]
  · simp [v, krawDir, stochArray]
  · simp [v, krawDir, stochArray]; omega
  · simp only [v, krawDir, stochArray]; split_ifs with h0 h1 <;> (try subst h1) <;> ring
  · rw [(hco i hi.le).1]
    have : (0 : ℝ) < eG (kA N δb δc p q u E) i := by exact_mod_cast hApos i hi
    positivity
  · rw [(hco i hiN).2.2]
    obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    have : (0 : ℝ) < eG (kC N δc p q u E) (j + 1) := by exact_mod_cast hCpos j (by omega)
    positivity
  · rw [(hco i hi).2.1]
    have : (0 : ℝ) ≤ eG (kB N δb δc p q u E) i := by exact_mod_cast hBnn i (by omega)
    positivity
  · exact productMatrix_neg (by simp [kA]) (by simp [kB]) (by simp [kC]) hApos
      (by simp [kC, eG_map_range _ _ _ (Nat.zero_le N)]) _ hQ v (fun i hi => (hco i hi).1)
      (fun i hi => (hco i hi).2.1) (fun i hi => (hco i hi).2.2) m hm ⟨n, hn⟩ ⟨k, hk⟩ hneg

end ColCheck

/-! ### The rule `β = 1`, `γ = 0` at `r < 1` -/

/-- **P3, Section 9**: for the rule `β = 1`, `γ = 0`, property (P) fails at `r = 4/5` with perturbation size
`1/100` for every `N = 6, …, 14`; the perturbed arrays are admissible with `b ≥ 0`. -/
theorem rule_fails_4_5 (N : ℕ) (h6 : 6 ≤ N) (h14 : N ≤ 14) :
    let v := krawDir N (fun _ => 1) (fun _ => 0) (4 / 5) (1 / 100)
    Admissible v ∧ (∀ i, i ≤ N → 0 ≤ v.b i) ∧ ¬ MatrixPositivity v := by
  have key : ∀ m n k : ℕ, ∀ (hm : m ≤ N) (hn : n < N + 1) (hk : k < N + 1),
      eG (ccol (kA N (fun _ => 1) (fun _ => 0) 4 5 1 100) (kB N (fun _ => 1) (fun _ => 0) 4 5 1 100)
        (kC N (fun _ => 0) 4 5 1 100) N k m).2 n < 0 →
      let v := krawDir N (fun _ => 1) (fun _ => 0) (4 / 5) (1 / 100)
      Admissible v ∧ (∀ i, i ≤ N → 0 ≤ v.b i) ∧ ¬ MatrixPositivity v := by
    intro m n k hm hn hk hneg
    have h := krawDir_example (N := N) (δb := fun _ => 1) (δc := fun _ => 0) (δb' := fun _ => 1)
      (δc' := fun _ => 0) (p := 4) (q := 5) (u := 1) (E := 100) (by omega) (by norm_num) (by norm_num)
      (fun _ => by norm_num) (fun _ => by norm_num) ?_ ?_ ?_ m n k hm hn hk hneg
    · norm_num at h
      exact ⟨h.1, h.2.1, fun hP => absurd (hP m hm ⟨n, hn⟩ ⟨k, hk⟩) (not_le.2 h.2.2)⟩
    all_goals interval_cases N <;> decide +kernel
  interval_cases N
  · exact key 6 6 6 le_rfl (by norm_num) (by norm_num) (by decide +kernel)
  · exact key 7 7 7 le_rfl (by norm_num) (by norm_num) (by decide +kernel)
  · exact key 7 8 8 (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
  · exact key 7 9 9 (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
  · exact key 7 10 10 (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
  · exact key 11 11 11 le_rfl (by norm_num) (by norm_num) (by decide +kernel)
  · exact key 12 12 12 le_rfl (by norm_num) (by norm_num) (by decide +kernel)
  · exact key 7 13 13 (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
  · exact key 7 14 14 (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)

/-- **P3, Section 9**: for the rule `β = 1`, `γ = 0`, property (P) fails at `r = 19/20` with perturbation size
`1/1000` for every `N = 4, …, 14`; the perturbed arrays are admissible with `b ≥ 0`. -/
theorem rule_fails_19_20 (N : ℕ) (h4 : 4 ≤ N) (h14 : N ≤ 14) :
    let v := krawDir N (fun _ => 1) (fun _ => 0) (19 / 20) (1 / 1000)
    Admissible v ∧ (∀ i, i ≤ N → 0 ≤ v.b i) ∧ ¬ MatrixPositivity v := by
  have key : ∀ m n k : ℕ, ∀ (hm : m ≤ N) (hn : n < N + 1) (hk : k < N + 1),
      eG (ccol (kA N (fun _ => 1) (fun _ => 0) 19 20 1 1000) (kB N (fun _ => 1) (fun _ => 0) 19 20 1 1000)
        (kC N (fun _ => 0) 19 20 1 1000) N k m).2 n < 0 →
      let v := krawDir N (fun _ => 1) (fun _ => 0) (19 / 20) (1 / 1000)
      Admissible v ∧ (∀ i, i ≤ N → 0 ≤ v.b i) ∧ ¬ MatrixPositivity v := by
    intro m n k hm hn hk hneg
    have h := krawDir_example (N := N) (δb := fun _ => 1) (δc := fun _ => 0) (δb' := fun _ => 1)
      (δc' := fun _ => 0) (p := 19) (q := 20) (u := 1) (E := 1000) (by omega) (by norm_num) (by norm_num)
      (fun _ => by norm_num) (fun _ => by norm_num) ?_ ?_ ?_ m n k hm hn hk hneg
    · norm_num at h
      exact ⟨h.1, h.2.1, fun hP => absurd (hP m hm ⟨n, hn⟩ ⟨k, hk⟩) (not_le.2 h.2.2)⟩
    all_goals interval_cases N <;> decide +kernel
  interval_cases N
  · exact key 3 4 4 (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
  · exact key 3 5 5 (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
  · exact key 6 6 6 le_rfl (by norm_num) (by norm_num) (by decide +kernel)
  · exact key 7 7 7 le_rfl (by norm_num) (by norm_num) (by decide +kernel)
  · exact key 3 8 8 (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
  · exact key 3 9 9 (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
  · exact key 10 10 10 le_rfl (by norm_num) (by norm_num) (by decide +kernel)
  · exact key 11 11 11 le_rfl (by norm_num) (by norm_num) (by decide +kernel)
  · exact key 3 12 12 (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
  · exact key 3 13 13 (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
  · exact key 14 14 14 le_rfl (by norm_num) (by norm_num) (by decide +kernel)

/-! ### The terminal direction at fixed `r < 1` -/

/-- `K_{N,r}` with `c_N → c_N + e`, `b_N → b_N - e`. -/
noncomputable def termArray (N : ℕ) (r e : ℝ) : Coefficients N :=
  krawDir N (fun _ => 0) (fun n => if n = N then 1 else 0) r e

set_option maxHeartbeats 4000000 in
/-- **P3, Section 9**: along the terminal direction, property (P) fails at size `10⁻¹⁵` for `r = 4/5`, `N = 40`
(`e = 10⁻¹⁵`), at size `6.3 · 10⁻⁶` for `r = 1/2`, `N = 120`, at size `3.2 · 10⁻³` for `r = 2/5`, `N = 100`, and at
size `1.6 · 10⁻²` for `r = 1/3`, `N = 120` (`e < 0` in the last three); the arrays are admissible with `b ≥ 0`
and `g(N,N;N) < 0`. -/
theorem terminal_fails :
    (Admissible (termArray 40 (4 / 5) (1 / 10 ^ 15)) ∧ (∀ i, i ≤ 40 → 0 ≤ (termArray 40 (4 / 5) (1 / 10 ^ 15)).b i) ∧
      productMatrix (termArray 40 (4 / 5) (1 / 10 ^ 15)) 40 (Fin.last 40) (Fin.last 40) < 0) ∧
    (Admissible (termArray 120 (1 / 2) (-63 / 10 ^ 7)) ∧
      (∀ i, i ≤ 120 → 0 ≤ (termArray 120 (1 / 2) (-63 / 10 ^ 7)).b i) ∧
      productMatrix (termArray 120 (1 / 2) (-63 / 10 ^ 7)) 120 (Fin.last 120) (Fin.last 120) < 0) ∧
    (Admissible (termArray 100 (2 / 5) (-32 / 10 ^ 4)) ∧
      (∀ i, i ≤ 100 → 0 ≤ (termArray 100 (2 / 5) (-32 / 10 ^ 4)).b i) ∧
      productMatrix (termArray 100 (2 / 5) (-32 / 10 ^ 4)) 100 (Fin.last 100) (Fin.last 100) < 0) ∧
    (Admissible (termArray 120 (1 / 3) (-16 / 10 ^ 3)) ∧
      (∀ i, i ≤ 120 → 0 ≤ (termArray 120 (1 / 3) (-16 / 10 ^ 3)).b i) ∧
      productMatrix (termArray 120 (1 / 3) (-16 / 10 ^ 3)) 120 (Fin.last 120) (Fin.last 120) < 0) := by
  have T : ∀ (N : ℕ) (p q u E : ℤ) (r e : ℝ), r = (p : ℝ) / q → e = (u : ℝ) / E → 1 ≤ N → 0 < q → 0 < E →
      (∀ i < N, 0 < eG (kA N (fun _ => 0) (fun n => if n = N then 1 else 0) p q u E) i) →
      (∀ i < N, 0 < eG (kC N (fun n => if n = N then 1 else 0) p q u E) (i + 1)) →
      (∀ i < N + 1, 0 ≤ eG (kB N (fun _ => 0) (fun n => if n = N then 1 else 0) p q u E) i) →
      eG (ccol (kA N (fun _ => 0) (fun n => if n = N then 1 else 0) p q u E)
        (kB N (fun _ => 0) (fun n => if n = N then 1 else 0) p q u E)
        (kC N (fun n => if n = N then 1 else 0) p q u E) N N N).2 N < 0 →
      Admissible (termArray N r e) ∧ (∀ i, i ≤ N → 0 ≤ (termArray N r e).b i) ∧
        productMatrix (termArray N r e) N (Fin.last N) (Fin.last N) < 0 := by
    intro N p q u E r e hr he hN hq hE hA hC hB hneg
    subst hr he
    exact krawDir_example (δb := fun _ => 0) (δc := fun n => if n = N then 1 else 0)
      (δb' := fun _ => 0) (δc' := fun n => if n = N then 1 else 0) hN hq hE
      (fun _ => by simp) (fun n => by split_ifs <;> simp) hA hC hB N N N le_rfl (by omega) (by omega) hneg
  exact ⟨T 40 4 5 1 (10 ^ 15) _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel),
    T 120 1 2 (-63) (10 ^ 7) _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel),
    T 100 2 5 (-32) (10 ^ 4) _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel),
    T 120 1 3 (-16) (10 ^ 3) _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)⟩

end Szkraw
