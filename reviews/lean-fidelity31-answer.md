## P1

| Item | Verdict | Reason |
|---|---|---|
| `binomial_mean` | **MATCH** | A more general algebraic identity than the footnote needs. Substituting `x = 1-p`, `y = p` gives its mean formula. Allowing `N = 0` causes no discrepancy. |
| `szwarc_footnote` | **MATCH** | Gives normalization, the mean, and the stated expectation of `K₁`. The absence of `0 < p` weakens the hypotheses appropriately: these are algebraic identities, not a claim that the weights are positive for every permitted `p`. [1] |
| `newton_examples` | **MATCH** | Gives the required coefficients, with weaker hypotheses for the quadratic calculation. The `q = 1` case is covered by the linear-profile clause. Formulas beyond `N` concern the displayed infinite extensions; restriction to the paper’s finite coefficient range gives the intended statements. They do not identify those extensions with the paper’s zero padding. [1] |
| `convex_counterexamples_newton_signs` | **MATCH** | The three profiles and sizes correspond to the cited counterexamples, and each conjunction supplies explicit positive and negative Newton coefficients. [2] |
| `szwarc_thm33_check` | **MATCH** | Correct parity ranges, coefficient orientation, odd-index threshold, even-index equivalence, and terminal obstruction. The bound `m ≤ N` makes the natural subtraction `N-m` harmless. Although Lean uses the normalized array, dividing both even coefficients by the same positive `N` preserves every condition being checked. [1] |

**Szwarc transcription:** **MATCH.** The survey’s recurrence has upward coefficient `γ` and downward coefficient `α`; its Theorem 3.3 lists precisely the four parity-monotonicity conditions and `α_n ≤ γ_n`, with `β ≡ 0`. Direct PDF retrieval timed out; this comparison uses the indexed author-version text of the recurrence and theorem. [3]

## P2

The two **MISMATCH** entries below concern the scope or completeness of the advertised remark, not a claim that the displayed identities are false.

| Item | Verdict | Reason |
|---|---|---|
| `quadArray` | **MATCH** | Exactly the quadratic binomial-basis parametrization, with `a = 1-b-c`. Admissibility is appropriately imposed separately. |
| `quadratic_hypotheses_needed` | **MATCH** | Each conjunct retains admissibility and the other two hypotheses, violates the omitted hypothesis, and supplies an in-range negative product coefficient. Explicit witnesses at `N = 3` suffice for the paper’s assertion. [4] |
| `strict_ratio_example` | **MATCH** | Covers every positive common scaling, hence the normalization used in the passage. Adjacent strict inequalities for all `i ≥ 1` give strict increase on the finite range. |
| `openEx1_b_newton` | **MATCH** | Two opposite-sign coefficients establish the claimed mixed signs. The chosen extension past index `3` does not affect these coefficients. |
| `linear_ratio_concave_b` | **MISMATCH — exclusion wording only** | The identities match, but the claimed exclusion from the finite Corollary 3.2 needs **`N ≥ 2`**. For `N = 1`, the negative second coefficient belongs only to the extension, outside the finite Newton range. See Fix 1. [5] |
| `exponential_ratio` | **MATCH** | Includes the Newton formula, `LCNZ` including `ε = 0`, the general criterion’s hypothesis, and positivity. The finite-array assumptions supply the relevant admissibility and diagonal monotonicity restrictions. [4] |
| `cubic_example_ratio_newton` | **MATCH** | Lists all coefficients through `N = 4`, all applicable log-concavity inequalities, and an explicit internal zero between positive entries. It does not mistakenly assert `LCNZ`. |
| `general_contains` | **MATCH — citation correction needed** | The three implications express the intended containments. Omitting admissibility from these hypothesis implications makes the statement stronger. The numerical references in the docstring are stale; see Fix 3. [6] |
| `quad_lowdeg_incomparable` | **MATCH — citation correction needed** | The two admissible witnesses establish both failures of inclusion. Different sizes are sufficient. The docstring’s numerical references need Fix 3. [7] |
| `weight_sums_geometric` | **MATCH** | Correct upper-triangular indexing, no erroneous off-diagonal factor of two, and the complete weight range `0,…,2M`. No sign assumptions are needed for this identity. |
| `log_rho_not_concave` | **MISMATCH — full docstring coverage** | The type states only the first three Newton coefficients and the second derivative. It does **not** state the advertised zero tail or `LCNZ`. It does match the table’s deliberately narrower derivative claim. See Fix 2. [5] |
| `kapTTau` | **MATCH** | Correct polarized `tτ` coefficient: both cross terms, the shifted sequence, and the specialization `(ℓ,n)=(0,3)` are present. |
| `kapRSig` | **MATCH** | Correct polarized `rσ` coefficient, with the same specialization and normalization. No missing polarization factor. |
| `geoSeq` | **MATCH** | Correct zero initial coefficient and geometric positive-index sequence. The duplicated declaration is in the supplied block; the committed file contains one definition. [7] |
| `geometric_kappa_values` | **MATCH** | The two expressions are the cited coefficients. Quantifying over all real `q` strengthens the intended positive-`q` calculation. |
| `geometric_kappa` | **MATCH** | States the positive-infinity limit and, for every `u > 2`, a positive-`q` failure of the combined coefficient test. It does **not** claim failure of property (P), or that `2` is a positivity cutoff. Positive normalization of the profile does not change the ratio or the sign of the quadratic-form combination. [4] |

## Exact fixes

### Fix 1: qualify the finite-array exclusion by `N ≥ 2`

For example, at `N = 1`, taking `r = κ = 1/4` gives `b₁ = c₁ = 1/2`. The finite Newton sequences satisfy the weighted corollary with `w₁ = 1`, despite the extension having a negative second difference.

Keep the theorem statement unchanged. Replace its docstring with:

```lean
/-- For `N ≥ 1`, the quadratic extension of the diagonal associated with
`ρ_i = r + κ i/N` and `d_i = i/N` has constant second difference
`-2κ/N² < 0`. For `N ≥ 2`, this is an in-range negative Newton
coefficient, excluding the array from Corollary 3.2. -/
```

In `papers/p2.tex`, replace the sentence beginning “They also exclude” after Corollary `cor:lc-vary` with:

```tex
For $N\geq2$, a strictly increasing linear ratio on a linear profile
violates the corollary's assumptions because $\Delta^2b(0)<0$;
Proposition~\ref{prop:lc-quad} covers it when $b$ is nondecreasing.
```

### Fix 2: include the full Newton-sequence assertion

To retain the existing full docstring, replace the statement of `log_rho_not_concave` with:

```lean
theorem log_rho_not_concave :
    let ρ : ℕ → ℝ :=
      fun i => 1 + (i : ℝ) / 2 + (i : ℝ) ^ 2 / 2
    (∀ k : ℕ,
      newtonCoeff ρ k = if k ≤ 2 then (1 : ℝ) else 0) ∧
    LCNZ (newtonCoeff ρ) ∧
    deriv (deriv fun x : ℝ =>
      Real.log (1 + x / 2 + x ^ 2 / 2)) 0 = 3 / 4 := …
```

This covers the complete advertised example, rather than only its first three coefficients and derivative. The existing Lean-table row needs no change.

### Fix 3: correct the numerical references

At this commit, the convex-quadratic ratio result is **Theorem 4.2**, and the low-degree ratio corollary is **Corollary 5.2**. The accepted predicate meanings are unchanged. [8]

Before `general_contains`, use:

```lean
/-- Theorem 5.5 contains Theorem 4.1, Corollary 5.2 and the case
`t² ≥ rτ` of Theorem 4.2: their hypotheses imply those of
Theorem 5.5. -/
```

Before `quad_lowdeg_incomparable`, use:

```lean
/-- Theorem 4.2 and Corollary 5.2 are not comparable. -/
```

Apply the same exact substitutions in the corresponding module-description comments of `RemarksP2.lean` and `RemarksP2b.lean`:

```text
Theorem 5.3  → Theorem 4.2
Corollary 4.4 → Corollary 5.2
```

The second identical `geoSeq` block should simply be deleted from the supplied listing; no corresponding repository edit is needed.

## Added Lean-table rows

The added rows have the following correspondence verdicts. The Koelink row correctly limits its claim to the transcribed recurrence comparison, rather than the whole construction or polynomial interpretation. [9]

| Paper | Added row | Verdict |
|---|---|---|
| P1 | Introductory footnote → `szwarc_footnote` | **MATCH** |
| P1 | Newton examples → `newton_examples`, `convex_counterexamples_newton_signs` | **MATCH** |
| P1 | Koelink recurrence → `koelink_recurrence_71` | **MATCH** |
| P1 | Szwarc hypotheses → `szwarc_thm33_check` | **MATCH** |
| P2 | Remarks after the weighted corollary → the three listed remarks | **MATCH as a mapping**; the underlying exclusion sentence needs Fix 1. |
| P2 | Necessity of the three quadratic hypotheses | **MATCH** |
| P2 | Section 5 examples, containments, and incomparability | **MATCH**; the table itself does not contain the stale numerical references. |
| P2 | Weight sums on geometric sequences | **MATCH** |
| P2 | Positive second derivative of `log ρ` | **MATCH**; this row promises less than the current docstring. |
| P2 | Geometric coefficients and `u > 2` | **MATCH**; the obstruction is to the coefficientwise test. |

**Requested Miclo transcription check:** `miclo_condition_fails` is **MATCH to P3’s formulation**. Its existential conclusion gives an adjacent strict increase of `2^n P(n,n+1)`, with both indices in the specified half-interval. That is precisely a violation of the stated nonincreasing condition; it does not purport to formalize Miclo’s entire criterion. [10]

## Overall verdict: **PASS WITH MINOR FIXES**

The corrections are the `N = 1` exclusion caveat, the missing advertised Newton-tail/`LCNZ` conclusions, and stale numerical locators. The remaining statements and the new table mappings match.

Sources:
[1] https://raw.githubusercontent.com/skypher/szkraw/3f6ee84/papers/p1.tex
[2] https://raw.githubusercontent.com/skypher/szkraw/3f6ee84/papers/p3.tex
[3] Orthogonal polynomials and Banach algebras — https://www.math.uni.wroc.pl/~szwarc/pdf/inzell.pdf
[4] https://raw.githubusercontent.com/skypher/szkraw/3f6ee84/papers/p2.tex
[5] https://raw.githubusercontent.com/skypher/szkraw/3f6ee84/lean/Szkraw/RemarksP2.lean
[6] https://raw.githubusercontent.com/skypher/szkraw/3f6ee84/lean/Szkraw/GenMain.lean
[7] https://raw.githubusercontent.com/skypher/szkraw/3f6ee84/lean/Szkraw/RemarksP2b.lean
[8] https://raw.githubusercontent.com/skypher/szkraw/3f6ee84/papers/preamble.tex
[9] Papers: Lean tables list the newly formalized remarks of P1-P3; not-f… · skypher/szkraw@3f6ee84 · GitHub — https://github.com/skypher/szkraw/commit/3f6ee84
[10] https://raw.githubusercontent.com/skypher/szkraw/3f6ee84/lean/Szkraw/RemarksP3.lean

