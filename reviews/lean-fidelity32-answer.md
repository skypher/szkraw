## Statement audit at `3f6ee84`

| Item | Verdict | Reason |
|---|---|---|
| `SignSet.mem` — both occurrences | **MATCH** | Exactly the four specified subsets of ℝ. The repeated occurrence in the question is not a second repository declaration. |
| `SignSet.mem_zero` | **MATCH** | Zero belongs to all four sets. |
| `SignClass` | **MATCH** | Correct monotonicity directions, second-difference and ratio-difference ranges, and ratio cap. Admissibility plus monotonicity of `b` ensures the relevant profile denominators are positive. |
| `kraw_mem_signClass` | **MATCH** | Correct parameter range, including equality at both upper bounds. |
| `signClass_zero_zero` | **MATCH** | Identifies the array on precisely `0,…,N` and supplies property (P). Together with the preceding membership theorem, this gives the claimed characterization. |
| `sign_pattern` | **MATCH** | Correct universal-in-`N` classification and threshold `83/400`; every other class has a negative terminal coefficient. The companion membership theorem supplies the additional Krawtchouk assertion in its docstring. |
| `g111` | **MATCH** | Correct coefficient formula; omitting admissibility makes the statement more general. |
| `g222` | **MATCH** | Correct formula, including omission of the `a₂c₃` contribution at `N=2`. The nonzero denominators are automatic in the intended admissible setting. |
| `heavyEx` | **MATCH** | Exactly the stated two-step constant-ratio array on the relevant indices. |
| `heavy_top_sharp` | **MATCH** | Correct admissibility range, ratio, exact value and strict negativity range. |
| `heavy_top_scope` | **MATCH** | Supplies the geometric half-bound, the Krawtchouk obstruction and an admissible nonconvex positive example. The unrestricted positive `r` in the Krawtchouk bound is harmless strengthening. |
| `convex_superadditive` | **MISMATCH — domain scope** | Requires convexity on **all of ℕ**, whereas the cited application assumes convexity only through `N`. Fix A below. |
| `k21Pert` | **MATCH** | Exactly the specified perturbation on indices `0,1,2`. |
| `k21_perturbation` | **MATCH** | Quantifies over every reference-positive product coefficient and gives both the exact negative value and its sign. |
| `reversal_obstruction_kraw` | **MATCH** | Correct formula, parameter range and failure of condition (b): the offending pair has `1+1<N`. The general-array formula in the surrounding remark is supplied by `g111` applied to `revCoeff v`, not by this specialization alone. |
| `reversal_obstruction_szwarc` | **MATCH** | Correct denominator, sign and array length. Here condition (b) uses `2+2<2*N`, explaining `N≥3`. |
| `miclo_condition_fails` | **MATCH** | Correct negation of the monotonicity condition **as P3 states it**; both adjacent indices lie in the specified interval. |
| `IsPolyFun`; `.const`; `.id`; `.add` | **MATCH** | Standard polynomial-function predicate and the stated closure properties. |
| `terminal_polynomial` | **MATCH** | Stronger than the particular terminal-coefficient assertion: it covers every product entry with `m≤N`. No positivity restriction on `r` is needed for this algebraic assertion. |
| `known_directions_satisfy` | **MISMATCH — domain scope in the second conjunct only** | Requires antisymmetry on all of ℝ, whereas the paper’s rules are functions on `[0,1]`. The other four conjuncts match. Fix B below. |
| `polyOf` | **MATCH** | Represents every polynomial of degree at most `d`, including lower-degree polynomials through zero coefficients. |
| `no_open_set_of_rules` | **MATCH** | Correct quantifier order and coefficient-space topology, including `d=0`. It excludes simultaneous admission of every rule in any nonempty open set. |
| `LogConcaveIncrements` | **MATCH** | With positive increments, its last inequality is exactly nonincrease of successive increment ratios; the middle condition makes those ratios at least one. |
| `logconcave_increment_class` | **MATCH** | Correct three included families and excluded kink range. The restriction `m≥2` is essential to the stated log-concavity obstruction. |

The sign-pattern declarations and the two remark modules contain these statements at the specified commit. [1][2][3]

### Fix A — finite convexity

The paper’s assertion concerns `i+j≤N`; values beyond `N` are irrelevant. The current declaration nevertheless constrains them. A convex extension would bridge this gap, but that extension is not part of the displayed statement. Under the requested hypothesis-direction test, use a finite-domain statement. [4][2]

Replace the declaration’s statement with:

```lean
theorem convex_superadditive (N : ℕ) (d : ℕ → ℝ) (hd0 : d 0 = 0)
    (hconv : ∀ n, n + 2 ≤ N →
      d (n + 1) - d n ≤ d (n + 2) - d (n + 1))
    (i j : ℕ) (hij : i + j ≤ N) :
    d i + d j ≤ d (i + j) := …
```

### Fix B — interval antisymmetry

P3 defines rules on `[0,1]`. An arbitrary extension outside that interval need not remain antisymmetric. Restricting the hypothesis to the interval removes the extra assumption; the endpoint conditions already suffice for the two displayed equalities. [4][5][3]

Replace the second conjunct of `known_directions_satisfy` with:

```lean
    (∀ γ : ℝ → ℝ,
      (∀ x, 0 ≤ x → x ≤ 1 → γ (1 - x) = -γ x) →
      γ 0 = 0 → γ 1 = 0 →
      Leven (fun _ => 0) γ = 0 ∧ Lodd (fun _ => 0) γ = 0) ∧
```

## Transcribed literature conditions

**Szwarc’s Theorem 3.3 — MATCH.** The survey’s indexed theorem text specifies `β≡0`, separate monotonicity of the even/odd subsequences of `α` and of `α+γ`, and `α_n≤γ_n`. These are the conditions checked by `szwarc_thm33_check`, with downward coefficient `c=α` and upward coefficient `a=γ`. The even-row normalization divides both coefficients by the same positive constant `N`, preserving all these comparisons. Thus the odd test is `p≤1/2`, the even test is `n≤N−n`, and the terminal obstruction is correctly represented. This checks coefficient conditions, not applicability of the infinite-system theorem. The survey PDF itself timed out; the external comparison uses its indexed theorem text. [6][7][8]

**Miclo’s condition as stated in P3 — MATCH.** At `n=0`, the two quantities are `1` and `2(N−1)/N`; the latter is larger precisely when `N>2`. The theorem also requires the second index to remain within `[0,N/2]`. It does not purport to formalize Miclo’s complete criterion or the separate small-size coverage assertions. [4]

## Final “Not formalized” paragraphs

### P1 — MATCH: accuracy and completeness

The paragraph correctly distinguishes unformalized literature identifications and numerical searches from the formalized coefficient comparisons. In particular, its transcription disclaimer does **not** incorrectly classify `szwarc_thm33_check` as unformalized. The table and scope notes account for the exact examples and Bernstein-coefficient assertion. No additional eligible omission found. **No replacement required.** [8][9]

### P2 — MATCH: accuracy and completeness

The remaining exclusions are correctly distinguished: the probabilistic interpretation, the unsuccessful `u=9/5` certificate search, sampled experiments, and the exact negative entry of the resummed operator at `N=6`. The last claim is correctly described as an obstruction to extending that resummation, not a counterexample to the affine theorem. The newly mapped remarks are not still excluded. No additional eligible omission found. **No replacement required.** [10]

### P3 — MISMATCH: one stale explanation

The exclusion list is otherwise consistent with the table and scope notes, including the Miclo exception, `N=500`, numerical-only examples and contour/saddle-point material. The two statement-domain gaps above should be corrected in the mapped declarations rather than added as permanent exclusions. [4][9]

The parenthetical claiming that explicit Krawtchouk spectral data are reached only through an existence statement is inaccurate. `BinomialMeasure.lean` already gives explicit nodes and weights, orthogonality, positive norms and the product identity. This does **not** mean that the listed exact maxima or normalized top-mass formulas have themselves been formalized. [11]

**Exact replacement:** replace the parenthetical beginning `they need explicit spectral data` with:

```tex
(the mapped top-mass results give a sufficient bound and general
fixed-coordinate derivatives, not these computed maxima or the displayed
affine-normalized formulas; explicit binomial spectral data are formalized
separately in \path{Szkraw.BinomialMeasure})
```

The distinction between a sufficient bound and the reported maxima, and between fixed-coordinate derivatives and normalized formulas, agrees with the documented scope. No further eligible coverage omission found. [9][12]

## Overall verdict: **PASS WITH MINOR FIXES**

Two local domain-scope corrections—`convex_superadditive` and the palindromic conjunct of `known_directions_satisfy`—and one replacement of P3’s stale spectral-data explanation.

Sources:
[1] https://raw.githubusercontent.com/skypher/szkraw/3f6ee84/lean/Szkraw/SignPattern.lean
[2] https://raw.githubusercontent.com/skypher/szkraw/3f6ee84/lean/Szkraw/RemarksP3.lean
[3] https://raw.githubusercontent.com/skypher/szkraw/3f6ee84/lean/Szkraw/RemarksP3b.lean
[4] https://raw.githubusercontent.com/skypher/szkraw/3f6ee84/papers/p3.tex
[5] https://raw.githubusercontent.com/skypher/szkraw/3f6ee84/lean/Szkraw/UniformRules.lean
[6] Orthogonal polynomials and Banach algebras — https://www.math.uni.wroc.pl/pdf/inzell
[7] https://raw.githubusercontent.com/skypher/szkraw/3f6ee84/lean/Szkraw/RemarksP1.lean
[8] https://raw.githubusercontent.com/skypher/szkraw/3f6ee84/papers/p1.tex
[9] https://raw.githubusercontent.com/skypher/szkraw/3f6ee84/papers/FORMALIZATION.md
[10] https://raw.githubusercontent.com/skypher/szkraw/3f6ee84/papers/p2.tex
[11] https://raw.githubusercontent.com/skypher/szkraw/3f6ee84/lean/Szkraw/BinomialMeasure.lean
[12] https://raw.githubusercontent.com/skypher/szkraw/3f6ee84/lean/Szkraw/LowerTopMass.lean

