## Lean statements

**All supplied theorem statements: MATCH.** The issues below concern documentation locators, not the mathematical statements.

### P2 — ratio counterexamples

The existence conjuncts prevent vacuity, and the profile and ratio equations determine the finite array under the accepted convention. All five declarations match their respective examples. [1]

| Statement | Verdict | Reason |
|---|---|---|
| `cubicBinom48_fails` | **MATCH** | Correct linear profile, binomial cubic ratio, \(\kappa=1/80\), nondecreasing \(b\), and negative entry \(g(48,48;48)\). The prescribed ratio also gives \(t=\tau=0\) and \(\sigma>0\), hence \(r\sigma>t\tau\). |
| `cubicPow64_fails` | **MATCH** | Correct profile, ratio, monotonicity, and entry \(g(64,64;63)\). The expansion uses \(i^3=i+6\binom i2+6\binom i3\), so the stated \(t,\tau,\sigma\) and strict inequality match. |
| `steepRatio40_fails` | **MATCH** | The exponent uses **integer subtraction**, correctly representing \(10^{i-40}\), not truncated natural subtraction. Global nonnegativity of the Newton coefficients is stronger than the required finite-range assertion. |
| `topRatio40_fails` | **MATCH** | Correct terminal-only increase, nondecreasing \(b\), Newton nonnegativity through order \(40\), and entry \(g(40,40;38)\). |
| `topRatio120_fails` | **MATCH** | Correct \(r=2/5\), terminal-only increase, nondecreasing \(b\), and entry \(g(120,120;119)\). On \(0,\ldots,120\), the prescribed ratio is convex and kinked. |

The finite restriction on Newton nonnegativity in the last two statements is appropriate: their chosen extensions beyond \(N\) are not claims about the paper’s finite arrays.

### P3 — profile counterexamples

**`incProfile`, `kinkInc`, `stepInc`, `KinkFails`, `IncFails`, and `cvxInc`: MATCH as encodings.** `incProfile` normalizes the stated increment patterns to \(d_N=1\); the failure predicates include existence and the required negative corner coefficient. [2]

| Statement or group | Verdict | Reason |
|---|---|---|
| All seven `kink*_fails` declarations | **MATCH** | Correct \(r,N,m,\delta\). The positive, nondecreasing increment patterns give convex profiles. The six Section 9 cases with \(N\le100\) and the additional \(N=14\) open-problems case are covered; \(N=20\) correctly serves both passages. |
| `stepInc_logconcave` | **MATCH** | States precisely that consecutive increment ratios are at least \(1\) and nonincreasing. Its assertion for every index is stronger than the finite requirement. |
| `logconcave32_fails`, `logconcave80_fails`, `logconcave90_fails` | **MATCH** | Correct three \((r,N,k)\) triples and \(q=1+1/(2N)\). With \(e_j=q^{\min(j,k)}\), there are exactly \(k\) ratio-\(q\) transitions before the increments become flat. |
| `cvxInc_logconvex`, `logconvex18_fails` | **MATCH** | Truncated subtraction gives fourteen unit increments at \(j=0,\ldots,13\), followed by powers \(1,\ldots,4\). The shape assertion and \(g(18,18;18)<0\) match. |

### P3 — rule and terminal perturbations

**`rule_fails_4_5`, `rule_fails_19_20`: MATCH.** The intervals are exactly \(6\le N\le14\) and \(4\le N\le14\), with the stated perturbation sizes. `stochArray` applies the perturbation in the independent coordinates: the constant \(\delta b\) changes the interior \(b_i\), not the constrained terminal \(b_N\). Admissibility, \(b\ge0\), and failure of (P) are all stated. [3]

**`termArray`, `terminal_fails`: MATCH.** The array changes only \(c_N\mapsto c_N+e\) and \(b_N\mapsto b_N-e\). The four signed values are
\[
10^{-15},\qquad -6.3\cdot10^{-6},\qquad
-3.2\cdot10^{-3},\qquad -1.6\cdot10^{-2}.
\]
Thus their absolute sizes match the prose. Each case includes admissibility, \(b\ge0\), and the specified negative corner coefficient. This does not assert failure for every smaller perturbation, or formalize the separate polynomiality or first-order observations. [3][4]

### P1 — convex combinations

**`combo`, `comboLam`, `combo_shape`: MATCH.** The parametrization \(p\ge1\), \(r=p^{-1}\), corresponds to \(0<r\le1\). The constant-ratio condition and normalized increment formula match, including the factor \(q^{N-1}\) in \(t\). Positivity is correctly stated for \(\nu_1,\ldots,\nu_N\), not \(\nu_0=0\), and the strict inequality has exactly the required \(N\ge3\) qualification. The explicit coefficients also supply \(b\ge0\); this need not be inferred from `Admissible` alone. [5]

**All seven `combo_fails_*` declarations: MATCH.** Every listed \((r,N,q,t)\) agrees. Each statement includes an interior convex weight, the equation recovering the specified \(t\), positivity of both endpoints, admissibility of the combination, and \(g(N,N;N)<0\). The exclusion of a convex sufficient-criterion set containing both endpoints follows immediately from these facts; no separate theorem quantifying over such sets is displayed. [5][6]

## Proposed changes

### 1. P1 Lean-table row — **MATCH**

The row accurately identifies the general combination statement and all seven failures. It does not claim formalization of the remaining searches or the entire surrounding paragraph.

### 2(a). P2 Lean-table row — **MATCH**

The five declarations correspond exactly to \(N=48,64,40,40,120\). The two \(N=40\) cases remain distinct through their theorem names and specified negative entries.

### 2(b). P2 cross-reference — **MISMATCH: minor locator wording**

Removing the P3 citation is correct. However, **“the last example of this section”** is not a precise locator: the section subsequently gives the \(N=6\) example with a negative entry of \(M\). Identify the intended top-raised ratio explicitly instead. [7]

Replace the proposed clause with:

```latex
and a convex kinked ratio on the linear profile fails at $N=120$
(the example below with $r=2/5$ and $\rho_N=r+(1-r)/N$).
```

### 3. P3 Lean-table rows — **MATCH**, all four rows

The terminal row covers the four finite witnesses; the rule row covers the two stated finite ranges; the Section 9 profile row correctly excludes \(N=500\) and the floating-point examples; and the open-problems row covers both convex-profile examples and the log-convex-increment example. Repeating `kink20_2_5_fails` in the two relevant rows is accurate. [2][3]

### 4(a). `FORMALIZATION.md` ratio and combination coverage — **MATCH**

“Section~10” correctly uses the full-manuscript numbering: its ratio-counterexample material appears in P2 Section 6. The five new ratio examples, their stated properties, and the seven combination failures are correctly described. The sampled tests and negative \(M\)-entry remain explicitly excluded. [8][7]

### 4(b). `FORMALIZATION.md` P3 computational coverage — **MISMATCH: minor section attribution**

The listed coverage and exclusions match. The opening, however, places the open-problems examples under “Section~9.” Those examples belong to **Section 10**, both in P3 and in the full manuscript. The notes expressly use full-manuscript numbering. [8][9]

Replace only the opening through its colon with:

```latex
The following exact computations in P3 Section~9 and its open-problems
section (Sections~9 and~10 of \path{paper.tex}) are formalized, except
as stated below:
```

The remainder of proposed 4(b), including its exclusions and the supplied description of kernel-evaluated integer columns, can remain unchanged.

## Overall verdict: **PASS WITH MINOR FIXES**

No Lean-statement changes are needed. Apply the two documentation-locator replacements in **2(b)** and **4(b)**.

Sources:
[1] https://raw.githubusercontent.com/skypher/szkraw/81eddf3/lean/Szkraw/RatioCounterexamples.lean
[2] https://raw.githubusercontent.com/skypher/szkraw/81eddf3/lean/Szkraw/ProfileCounterexamples.lean
[3] https://raw.githubusercontent.com/skypher/szkraw/81eddf3/lean/Szkraw/RuleCounterexamples.lean
[4] https://raw.githubusercontent.com/skypher/szkraw/81eddf3/paper.tex
[5] https://raw.githubusercontent.com/skypher/szkraw/81eddf3/lean/Szkraw/ComboCounterexamples.lean
[6] https://raw.githubusercontent.com/skypher/szkraw/81eddf3/papers/p1.tex
[7] https://raw.githubusercontent.com/skypher/szkraw/81eddf3/papers/p2.tex
[8] https://raw.githubusercontent.com/skypher/szkraw/81eddf3/papers/FORMALIZATION.md
[9] https://raw.githubusercontent.com/skypher/szkraw/81eddf3/papers/p3.tex

