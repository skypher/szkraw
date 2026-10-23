# Lean statement fidelity, round 32: remarks of P3 formalized after round 30, and the final not-formalized paragraphs of P1–P3

Repository: github.com/skypher/szkraw, commit 3f6ee84. Axiom audit: lean/axioms.log (380 lines, only propext, Classical.choice, Quot.sound).

As in earlier rounds, **do not check proofs**. Check whether each Lean statement says what the cited passage says (hypotheses equivalent or weaker, conclusions equivalent or stronger), and report MATCH / MISMATCH per item with reasons and exact replacement text for any fix. Conventions as in rounds 1–25 (`Coefficients`, `Admissible`, `MatrixPositivity`, `productMatrix v m n k = g(m,n;k)`, `profile`, `newtonCoeff d k = Δ^k d(0)`, `krawCoefficients N r` = K_{N,r}, `geometricCoefficients N p q` with p = 1/r, `szwarcCoefficients N p` = (eq:szwarc-q)/(eq:qarray) of length 2N+1, `revCoeff` = reversed array, `krawDir`/`stochArray` as in round 23). Paper passages: read them at the commit in papers/p1.tex, p2.tex, p3.tex; each declaration's docstring names its passage, and the paper's Lean table (section "Code and formalization") lists it. Where a Lean statement transcribes a condition from another paper (Szwarc's Theorem 3.3 from his survey; Miclo's condition as P3 states it), say whether the transcription matches what the paper says.

## P3 (papers/p3.tex)

```lean
/-- `[0,∞)`, `(-∞,0]`, `{0}`, `ℝ`. -/
def SignSet.mem : SignSet → ℝ → Prop
  | .nonneg, x => 0 ≤ x
  | .nonpos, x => x ≤ 0
  | .zero, x => x = 0
  | .all, _ => True

theorem SignSet.mem_zero (S : SignSet) : S.mem 0 := …

/-- `[0,∞)`, `(-∞,0]`, `{0}`, `ℝ`. -/
def SignSet.mem : SignSet → ℝ → Prop
  | .nonneg, x => 0 ≤ x
  | .nonpos, x => x ≤ 0
  | .zero, x => x = 0
  | .all, _ => True

/-- The class of the sign-pattern discussion of P3. -/
def SignClass {N : ℕ} (S₁ S₂ : SignSet) (ρmax : ℝ) (v : Coefficients N) : Prop :=
  Admissible v ∧ (∀ n, n < N → v.a (n + 1) ≤ v.a n) ∧ (∀ n, n < N → v.b n ≤ v.b (n + 1)) ∧
  (∀ n, n < N → v.c n ≤ v.c (n + 1)) ∧
  (∀ n, n + 2 ≤ N → S₁.mem (profile v (n + 2) - 2 * profile v (n + 1) + profile v n)) ∧
  (∀ n, 1 ≤ n → n + 1 ≤ N → S₂.mem (v.c (n + 1) / profile v (n + 1) - v.c n / profile v n)) ∧
  (∀ n, 1 ≤ n → n ≤ N → v.c n / profile v n ≤ ρmax)

/-- Every class contains `K_{N,r}` for `0 < r ≤ 1`, `r ≤ ρ_max`. -/
theorem kraw_mem_signClass (N : ℕ) (hN : 1 ≤ N) (S₁ S₂ : SignSet) (ρmax r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1)
    (hρ : r ≤ ρmax) : SignClass S₁ S₂ ρmax (krawCoefficients N r) := …

/-- The class `S₁ = S₂ = {0}` consists of the arrays `K_{N,r}`, `0 < r ≤ min(1, ρ_max)`, and has property (P). -/
theorem signClass_zero_zero {N : ℕ} (hN : 1 ≤ N) (ρmax : ℝ) (v : Coefficients N)
    (hv : SignClass .zero .zero ρmax v) :
    (∃ r, 0 < r ∧ r ≤ 1 ∧ r ≤ ρmax ∧ ∀ i, i ≤ N → v.a i = (krawCoefficients N r).a i ∧
      v.b i = (krawCoefficients N r).b i ∧ v.c i = (krawCoefficients N r).c i) ∧ MatrixPositivity v := …

/-- **P3, open problems, sign conditions on the shape.** For `ρ_max ≥ 83/400`, among the classes
`SignClass S₁ S₂ ρ_max`, exactly `S₁ = S₂ = {0}` guarantees property (P) for all `N`; every other class contains an
array with `g(N,N;N) < 0`, and every class contains `K_{N,r}` for `0 < r ≤ min(1, ρ_max)`. -/
theorem sign_pattern (S₁ S₂ : SignSet) (ρmax : ℝ) (hρ : 83 / 400 ≤ ρmax) :
    ((∀ N, 1 ≤ N → ∀ v : Coefficients N, SignClass S₁ S₂ ρmax v → MatrixPositivity v) ↔
      (S₁ = .zero ∧ S₂ = .zero)) ∧
    ((S₁, S₂) ≠ (.zero, .zero) → ∃ N, ∃ v : Coefficients N, SignClass S₁ S₂ ρmax v ∧
      productMatrix v N (Fin.last N) (Fin.last N) < 0) := …

theorem g111 (v : Coefficients N) (hN : 1 ≤ N) :
    productMatrix v 1 ⟨1, by omega⟩ ⟨1, by omega⟩ = (v.b 1 - v.b 0) / v.a 0 := …

theorem g222 (v : Coefficients N) (hN : 2 ≤ N) (ha0 : v.a 0 ≠ 0) (ha1 : v.a 1 ≠ 0) :
    productMatrix v 2 ⟨2, by omega⟩ ⟨2, by omega⟩ =
      ((if 3 ≤ N then v.a 2 * v.c 3 else 0) + (v.b 2 - v.b 1) * (v.b 2 - v.b 0) + v.c 2 * v.a 1 -
        v.a 0 * v.c 1) / (v.a 0 * v.a 1) := …

/-- The constant-ratio array with `N = 2`, `r = 1` and `d_1 = x`. -/
noncomputable def heavyEx (x : ℝ) : Coefficients 2 where
  a i := if i = 0 then 1 else if i = 1 then 1 - x else 0
  b _ := 0
  c i := if i = 0 then 0 else if i = 1 then x else 1

/-- **Sharpness of `d_{N-1} ≤ 1/2`**: for `N = 2`, `r = 1`, `g(2,2;2) = (1 - 2 d_1)/(1 - d_1)`, negative when
`1/2 < d_1 < 1`. -/
theorem heavy_top_sharp (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1) :
    Admissible (heavyEx x) ∧ (∀ i, i ≤ 2 → (heavyEx x).c i = 1 * profile (heavyEx x) i) ∧
    productMatrix (heavyEx x) 2 2 2 = (1 - 2 * x) / (1 - x) ∧ (1 / 2 < x → productMatrix (heavyEx x) 2 2 2 < 0) := …

/-- **Scope of Corollary 8.4**: it contains the arrays (eq:parameters) with `q ≥ 2` (`d_{N-1} ≤ 1/2`) but not the
Krawtchouk arrays with `N ≥ 3` (`d_{N-1} = (N-1)/N > 1/2`); the profile need not be convex. -/
theorem heavy_top_scope :
    (∀ N : ℕ, 1 ≤ N → ∀ p q : ℝ, 1 ≤ p → 2 ≤ q → profile (geometricCoefficients N p q) (N - 1) ≤ 1 / 2) ∧
    (∀ N : ℕ, 3 ≤ N → ∀ r : ℝ, 0 < r → 1 / 2 < profile (krawCoefficients N r) (N - 1)) ∧
    (∃ v : Coefficients 3, Admissible v ∧ HeavyTop v ∧
      profile v 2 - profile v 1 < profile v 1 - profile v 0 ∧ MatrixPositivity v) := …

/-- Convex sequences with `d_0 = 0` are superadditive: `d_i + d_j ≤ d_{i+j}`. -/
theorem convex_superadditive (d : ℕ → ℝ) (hd0 : d 0 = 0)
    (hconv : ∀ n, d (n + 1) - d n ≤ d (n + 2) - d (n + 1)) (i j : ℕ) : d i + d j ≤ d (i + j) := …

/-- `K_{2,1}` with `c_1 = 1/2 + ε`, `a_1 = 1/2 - ε`, `b ≡ 0`, `c_2 = 1`. -/
noncomputable def k21Pert (ε : ℝ) : Coefficients 2 where
  a i := if i = 0 then 1 else if i = 1 then 1 / 2 - ε else 0
  b _ := 0
  c i := if i = 0 then 0 else if i = 1 then 1 / 2 + ε else 1

/-- **P3, after Corollary 7.7**: for `0 < ε < 1/2`, every coefficient that is positive at `K_{2,1}` stays positive,
but `g(2,2;2) = -2ε/(1/2 - ε) < 0`. -/
theorem k21_perturbation (ε : ℝ) (hε0 : 0 < ε) (hε : ε < 1 / 2) :
    (∀ m, m ≤ 2 → ∀ n k : Fin 3, 0 < productMatrix (krawCoefficients 2 1) m n k →
      0 < productMatrix (k21Pert ε) m n k) ∧
    productMatrix (k21Pert ε) 2 2 2 = -2 * ε / (1 / 2 - ε) ∧ productMatrix (k21Pert ε) 2 2 2 < 0 := …

/-- If `b_{N-1} < b_N`, the reversed array has `g'(1,1;1) = (b_{N-1} - b_N)/c_N < 0`; so condition (b) of the
deep reduction fails for `N ≥ 3`. In particular for `K_{N,r}`, `0 < r < 1`. -/
theorem reversal_obstruction_kraw (N : ℕ) (hN : 3 ≤ N) (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) :
    productMatrix (revCoeff (krawCoefficients N r)) 1 ⟨1, by omega⟩ ⟨1, by omega⟩ =
      ((krawCoefficients N r).b (N - 1) - (krawCoefficients N r).b N) / (krawCoefficients N r).c N ∧
    productMatrix (revCoeff (krawCoefficients N r)) 1 ⟨1, by omega⟩ ⟨1, by omega⟩ < 0 ∧
    ¬ (∀ i j, (h : i + j < N) → ∀ t : Fin (N + 1),
      0 ≤ productMatrix (revCoeff (krawCoefficients N r)) i ⟨j, by omega⟩ t) := …

/-- Szwarc's array (eq:qarray) reversed: `g'(2,2;2) = (2p₀ - 1)/(N p₀) < 0` for `0 < p₀ < 1/2`, which violates
condition (b) of the deep reduction for the array of length `2N + 1` when `N ≥ 3`. -/
theorem reversal_obstruction_szwarc (N : ℕ) (hN : 3 ≤ N) (p : ℝ) (hp0 : 0 < p) (hp : p < 1 / 2) :
    productMatrix (revCoeff (szwarcCoefficients N p)) 2 ⟨2, by omega⟩ ⟨2, by omega⟩ = (2 * p - 1) / (N * p) ∧
    (2 * p - 1) / (N * p) < 0 ∧
    ¬ (∀ i j, (h : i + j < 2 * N) → ∀ t : Fin (2 * N + 1),
      0 ≤ productMatrix (revCoeff (szwarcCoefficients N p)) i ⟨j, by omega⟩ t) := …

/-- Miclo's palindromic criterion requires `2^n P(n, n+1)` to be nonincreasing on `[0, N/2]`; for the symmetric
Krawtchouk chain `P(n, n+1) = a_n = (N - n)/N`, this fails for `N > 2` (already at `n = 0`). -/
theorem miclo_condition_fails (N : ℕ) (hN : 2 < N) :
    ∃ n : ℕ, ((n : ℝ) + 1 ≤ N / 2) ∧
      (2 : ℝ) ^ n * (krawCoefficients N 1).a n < 2 ^ (n + 1) * (krawCoefficients N 1).a (n + 1) := …

/-- Functions of `e` that are polynomials. -/
def IsPolyFun (f : ℝ → ℝ) : Prop := ∃ P : Polynomial ℝ, ∀ e, f e = P.eval e

theorem IsPolyFun.const (c : ℝ) : IsPolyFun fun _ => c := ⟨Polynomial.C c, fun _ => by simp⟩
theorem IsPolyFun.id : IsPolyFun fun e => e := ⟨Polynomial.X, fun _ => by simp⟩
theorem IsPolyFun.add {f g : ℝ → ℝ} (hf : IsPolyFun f) (hg : IsPolyFun g) : IsPolyFun fun e => f e + g e := …

/-- **P3, Section 9**: along the terminal direction `c_N ↦ c_N + e`, `b_N ↦ b_N - e` at `K_{N,r}`, every product
coefficient `g(m,n;k)`, `m ≤ N`, in particular `g(N,N;N)`, is a polynomial in `e`. -/
theorem terminal_polynomial (N : ℕ) (hN : 1 ≤ N) (r : ℝ) :
    ∀ m, m ≤ N → ∀ n k : Fin (N + 1), IsPolyFun fun e => productMatrix (termArray N r e) m n k := …

theorem known_directions_satisfy :
    (Leven (fun x => x) (fun x => -x) = 0 ∧ Lodd (fun x => x) (fun x => -x) = 0) ∧
    (∀ γ : ℝ → ℝ, (∀ x, γ (1 - x) = -γ x) → γ 0 = 0 → γ 1 = 0 →
      Leven (fun _ => 0) γ = 0 ∧ Lodd (fun _ => 0) γ = 0) ∧
    (Leven (fun _ => 0) (fun x => x * (x - 1)) = 0 ∧ Lodd (fun _ => 0) (fun x => x * (x - 1)) = 0) ∧
    (∀ β γ : ℝ, Leven (fun _ => β) (fun _ => γ) = 2 * β + 3 * γ ∧ Lodd (fun _ => β) (fun _ => γ) = -γ) ∧
    (∀ β γ : ℝ, Leven (fun _ => β) (fun _ => γ) = 0 → Lodd (fun _ => β) (fun _ => γ) = 0 → β = 0 ∧ γ = 0) := …

/-- The polynomial with coefficient vector `c`. -/
noncomputable def polyOf {d : ℕ} (c : Fin (d + 1) → ℝ) : ℝ[X] := ∑ i, Polynomial.C (c i) * X ^ (i : ℕ)

/-- **P3, after Theorem 9.4**: for every `d`, no set of arrays with property (P) admits all rules of a nonempty open
set of polynomial rules of degree at most `d` (coefficient vectors of `β` and `γ`). -/
theorem no_open_set_of_rules (d : ℕ) (S : (N : ℕ) → Set (Coefficients N))
    (hS : ∀ N, ∀ v ∈ S N, MatrixPositivity v) (U : Set ((Fin (d + 1) → ℝ) × (Fin (d + 1) → ℝ)))
    (hU : IsOpen U) (hne : U.Nonempty) :
    ¬ ∀ c ∈ U, AdmitsRule S (polyOf c.1).eval (polyOf c.2).eval := …

/-- Increments `e_i = d_i - d_{i-1}` (`1 ≤ i ≤ N`) are positive, with step ratios `e_{i+1}/e_i ≥ 1` and
nonincreasing. -/
def LogConcaveIncrements (N : ℕ) (d : ℕ → ℝ) : Prop :=
  (∀ i, 1 ≤ i → i ≤ N → 0 < d i - d (i - 1)) ∧
  (∀ i, 1 ≤ i → i + 1 ≤ N → d i - d (i - 1) ≤ d (i + 1) - d i) ∧
  (∀ i, 1 ≤ i → i + 2 ≤ N → (d (i + 2) - d (i + 1)) * (d i - d (i - 1)) ≤ (d (i + 1) - d i) ^ 2)

/-- **P3, Section 9**: the class contains the Krawtchouk profile `i/N`, the geometric profiles `[i]_q/[N]_q`
(`q > 1`) and the normalized quadratic profiles `d_κ(i/N)`, `d_κ(x) = (x + κx²)/(1 + κ)`, `κ ≥ 0`; it excludes the
one-kink profiles (`m ≥ 2` unit increments, then `1 + δ`, `δ > 0`, `m < N`). -/
theorem logconcave_increment_class (N : ℕ) (hN : 1 ≤ N) :
    LogConcaveIncrements N (fun i => (i : ℝ) / N) ∧
    (∀ q : ℝ, 1 < q → LogConcaveIncrements N (fun i => qInteger q i / qInteger q N)) ∧
    (∀ κ : ℝ, 0 ≤ κ → LogConcaveIncrements N (fun i => ((i : ℝ) / N + κ * ((i : ℝ) / N) ^ 2) / (1 + κ))) ∧
    (∀ m : ℕ, 2 ≤ m → m < N → ∀ δ : ℝ, 0 < δ → ¬ LogConcaveIncrements N (incProfile (kinkInc m δ) N)) := …
```
Context: `HeavyTop` (AllProducts.lean) is the hypothesis of Corollary 8.4; `Stmt_deep_reduction` condition (b) is `∀ i j, i + j < N → ∀ t, 0 ≤ productMatrix (revCoeff v) i j t`; `termArray N r e = krawDir N 0 [n = N] r e` (round 23); `Leven`, `Lodd`, `AdmitsRule`, `forced_equalities` (UniformRules.lean, rounds 6–8).

## Not-formalized paragraphs

Each paper's section "Code and formalization" now ends with a paragraph naming what is not formalized and why (P1, P2, P3 at 3f6ee84). Rounds 29–30 audited earlier versions. Check (1) that every sentence is accurate against the paper, the Lean tables and papers/FORMALIZATION.md, in particular that nothing formalized at 3f6ee84 is still listed as unformalized; (2) completeness: any numbered result, mathematical remark or exact computational claim that is neither covered by a table row (or FORMALIZATION.md scope notes) nor named in the paragraph. Ignore internal proof steps, results attributed to the literature, open questions, and the AI-use disclosure.

Answer per item, then an overall verdict (PASS / PASS WITH MINOR FIXES / FAIL), with exact replacement text for any fix.
