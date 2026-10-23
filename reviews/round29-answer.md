## P1

**Accuracy:** The existing sentence is accurate. The searches report grid minima, not certified values of \(V_N\). The exact examples, their Bernstein certificates, and the seven convex-combination failures are covered by the table and scope notes; they should **not** be added to the exclusions. No additional numbered result is unmapped. [1][2]

**Completeness:** The paragraph misses the following auxiliary assertions. These are the paper’s own calculations or identifications, not merely attributed literature results.

| Location in `papers/p1.tex` | Unmarked material |
|---|---|
| Introduction, parameter-convention footnote | The binomial-mean calculation and the resulting nonzero integral of the displayed \(K_1\). |
| Introduction and Section 4 | The assessment that the cited criteria do not cover all finite Krawtchouk products; the explicit check of which hypotheses of Szwarc’s Theorem 3.3 hold or fail. |
| Immediately after Theorem 3.1 | The special-case Newton-coefficient observations for Krawtchouk, geometric and convex-quadratic profiles, and the assertion that the cited convex counterexamples have Newton coefficients of both signs. The positivity conclusions and convex-combination calculation are covered; these ancillary shape observations are not separately recorded. |
| After Corollary 3.7 | Identification with Koelink’s normalized recurrence and dual \(q\)-Krawtchouk interpretation. |

The relevant passages are the introduction, the two paragraphs after Theorem 3.1, and the transition from Corollary 3.7 to Section 4. [1]

**Replacement:**

```latex
Not formalized, or not stated separately in Lean: the
parameter-convention calculation in the introductory footnote,
the comparisons with the applicability of the cited criteria,
the special-case Newton-coefficient observations immediately
after Theorem~\ref{thm:lc} other than the convex-combination
calculation covered above, the identification with Koelink's
normalized recurrence after Corollary~\ref{cor:additional}, and
the check of Szwarc's hypotheses in Section~\ref{sec:szwarc}.
These are auxiliary calculations and comparisons, distinct from
the positivity statements in the table.
The float and high-precision searches concerning $V_N$ in
``How sharp is log-concavity?'' are not formalized: they give
numerical evidence over sampled parameters, not certified
thresholds. The questions in Section~\ref{sec:open} remain open.
```

## P2

**Accuracy:** The existing sentence correctly distinguishes sampled evidence from the exact negative-\(M\) diagnostic. The latter uses rational arithmetic internally, even though its final output converts the minimum to a float. More precisely, it tests an attempted extension of the affine proof method to cubic ratios; it is not a counterexample to Theorem 4.1. [3][4]

**Numbered results:** No additional omission. In particular, Lemma 5.4 is covered by the paper’s `abel_weight` row, and the \(7/4\) extension is covered by `cubic_ratio74_matrix`. [4]

**Completeness:**

| Location in `papers/p2.tex` | Unmarked material |
|---|---|
| After Corollary 3.2 | **Strict** increase in the quadratic weighted example; the mixed-sign Newton coefficients of \(b=(0,1,1,1)/91\); and the exclusion of increasing affine ratios on linear profiles because their diagonals are concave. The mapped corollary states nondecreasing ratios, not this strict example. |
| Section 5, around Corollary 5.2 and Theorem 5.5 | The exponential-ratio specializations and the comparisons of the scopes of the criteria, particularly the noncomparability of Theorem 4.2 and Corollary 5.2. |
| After Proposition 5.3 | The random-set interpretation, including the displayed union-cardinality probability and its identification with Walkup’s formulation. This is an additional interpretation, not the attributed closure theorem itself. |
| After Lemma 5.4 | Identification of the weight sums with the coefficients obtained by evaluating \(Q\) on a geometric sequence. |
| Parenthesis in the proof of Theorem 5.5 | The continuous-variable counterexample \(\rho(x)=1+x/2+x^2/2\), with \((\log\rho)''(0)>0\). This is an illustrative counterexample, not a step needed for the proof. |
| After Theorem 5.6 | The explicit geometric-profile coefficient formulas, their ratio tending to \(2\), and the resulting obstruction for \(u>2\). Also the reported failure of `bdetour_u.py` at \(u=9/5\). Neither is covered by proving the \(7/4\) extension. |

The distinction between strict and weak monotonicity is visible in `varyratio_weights`; `openEx1_fails` records the counterexample but does not state the additional mixed-sign assertion about its diagonal. [4][5][6] The Section 5 interpretations and comparisons occur outside the numbered statements. [4] The \(u>2\) obstruction and \(9/5\) certificate failure are separate claims about the proof method. [4][7]

**Replacement:**

```latex
Not formalized, or not stated separately in Lean: the strict-ratio
example and the exclusion observations after
Corollary~\ref{cor:lc-vary}; the exponential-ratio examples and
the comparisons between the scopes of the criteria in Section~5;
the random-set interpretation and identification with Walkup's
formulation after Proposition~\ref{prop:np}; the geometric-sequence
interpretation of the weight sums after
Lemma~\ref{lem:abel-weights}; and the continuous-variable
log-concavity counterexample in the proof of
Theorem~\ref{thm:lc-general}.
The geometric-profile coefficient formulas and the resulting
obstruction for $u>2$ after Theorem~\ref{thm:lc-cubic}, and the
reported failure of \path{runs/cubic/bdetour_u.py} at $u=9/5$,
are also not formalized; these concern the limits of particular
certificates, not failures of property (P).
In Section~\ref{sec:open}, the sampled tests of cubic ratios and
of the resummed operator are numerical evidence over finitely
many arrays. The negative entry of $M$ for $N=6$ is checked in
exact arithmetic by \path{runs/varratio/cubic_diag.py}, but not
in Lean; it obstructs extending the resummation used in
Theorem~\ref{thm:lc-affine} to those cubic data, rather than
contradicting that theorem.
```

## P3

### Accuracy of the existing sentences

The statement about **Proposition 6.3 is correct**: the external identification is not used to prove another result. The paper constructs and uses its algebra independently; the proposition subsequently identifies that construction with Koelink’s. [8]

The **Miclo sentence is correct but incomplete**: there is also a comparison at the end of Section 8, not just in Section 10. “The same holds” should not suggest that Miclo’s setting is the type-B Hecke algebra. [8]

The descriptions of **Proposition 3.4 and Corollary 7.7 match the scope notes**. For Proposition 3.4, say “nonnegative linear combinations” rather than “in the basis”: independence is precisely one of the assertions not separately stated. The coefficient box does justify the openness/dimension conclusion of Corollary 7.7, although that conclusion is not separately stated in Lean. [2]

The **\(N=500\) sentence matches the documented exception**, including the reported 50-minute kernel run. This is a report in the repository, not a runtime result independently reproduced in this review. [2]

The final sentence needs a distinction: the **contour representation is asserted as an exact identity**; the saddle-point conclusion is heuristic. Calling the entire penultimate item “numerical or heuristic” is overbroad. [8]

### Completeness

No additional numbered theorem, lemma, proposition or corollary is wholly unmapped. Proposition 9.8 is not an additional missing theorem: its statement requires the existence of a finite bound, which the Lean sum supplies. **The subsequent exact values of the paper’s maximum are a different matter.** [8][9]

Additional unmarked material:

| Location | Uncovered assertion or part |
|---|---|
| Introduction; Sections 6–7 | The introductory convention calculation; the \(O(N)\) comparison count; the applicability check for Szwarc’s infinite-system criterion; and the subdivided-cube adjacency/counting interpretation. |
| After Corollary 7.7 | The exact \(K_{2,1}\) perturbation formula and the assertion that previously positive coefficients stay positive. Negativity alone is obtainable from the mapped sharpness result; that does not record the whole remark. |
| After Corollary 8.4 | The nonconvex-profile observation, inclusion of \(q\ge2\), exclusion of Krawtchouk for \(N\ge3\), and sharpness via \(g(2,2;2)=(1-2d_1)/(1-d_1)\). |
| End of Section 8 | Both reversal obstructions: the increasing-diagonal formula for \(g'(1,1;1)\), and the reversed Szwarc formula for \(g'(2,2;2)\), including their size restrictions. Also the Miclo comparison there. |
| Beginning of Section 9 | Reduction of an arbitrary finite orthogonal system to the stated normalization. `finite_realization` starts from the normalized recurrence; it is not this converse normalization assertion. |
| After Theorem 9.4; before Lemma 9.5 | The listed deformation directions, including the geometric tangent; independence of the two functionals on constant rules; and the interpretation of \(\Omega\) as an equispaced-interpolation convergence region. The separately formalized geometry of \(\Omega\) is **not** a gap. |
| After Proposition 9.8 | \(\Lambda_N=4,10,18,28,52,90,165\) for \(N=4,\ldots,10\); the affine-normalized top-mass direction; and its non-uniform-rule assertion. The fixed-coordinate rates are covered by `lower_rates`. The analogous non-uniform-rule assertion for raising the top mass is also unmarked. |
| Computational discussion in Section 9 | The \(O(N^2)\) operation count; and the class-membership assertions that convex profiles with log-concave increments include the stated Krawtchouk, geometric and quadratic profiles but exclude the one-kink examples. Correctness of the column recurrence does not formalize its complexity. |
| Section 10, convex combinations | The additional **150-/300-digit** example and the unsuccessful \(r=1/5,\ N\le1000\) grid search. These are not the 80-/150-digit examples named in the current paragraph. |
| Final sign-pattern discussion | The classification of the \(S_1,S_2\) classes, their Krawtchouk containment/equality assertions, and the counterexample conclusion for \(\rho_{\max}\ge83/400\). The \(N=100\) witness’s negative sign is already covered by `kink100_1_5_fails`; the additional \(N=20,120,80\) witnesses and the classification are not. |

The first four groups are explicit prose claims beyond the mapped conclusions. [8] The normalization, deformation and interpolation assertions likewise exceed the documented statements. [8][10] For the numerical maximum, note especially that Lean’s `lamN` is a **sum of absolute derivative ratios**, not the paper’s computed maximum. [9][11] The remaining computational omissions are visible in the column implementation, the concluding experiments and `signpattern_probe.py`. [12][8][13]

**Replacement:**

```latex
Not formalized, or formalized only in part:
Proposition~\ref{prop:source} identifies the construction with
Koelink's type-B Hecke-algebra construction, which is not
formalized; no other result depends on this identification.
The introductory parameter-convention calculation, the
applicability comparisons with Szwarc's conditions, and the
comparisons with Miclo's conditions in Sections~\ref{sec:low}
and~\ref{sec:open} are also not formalized.
For Proposition~\ref{prop:subalgebra}, Lean states that every
$E_mE_n$ is a nonnegative linear combination of
$E_0,\ldots,E_N$; generation of $B$ by $E_1$ and linear
independence of the $E_k$ are not stated separately.
For Corollary~\ref{cor:symmetric-new}, the relatively open set
with $2N-1$ free coefficients is not stated separately; it
follows from the positive-radius coefficient box in
\path{Szkraw.symmetric_criterion}.
The subdivided-cube interpretation, the $O(N)$ hypothesis-checking
count, the exact perturbation remark after that corollary, the
scope and sharpness remarks after Corollary~\ref{cor:heavy},
and the two reversal obstructions at the end of
Section~\ref{sec:low} are not separately formalized.
In Section~\ref{sec:limits}, this also applies to the reduction
of arbitrary finite systems to the chosen normalization, the
listed deformation directions and independence calculation
after Theorem~\ref{thm:uniform}, the equispaced-interpolation
interpretation of $\Omega$, the exact computed values of
$\Lambda_N$, the affine-normalized top-mass direction and the
non-uniform-rule observations for top-mass changes, the
$O(N^2)$ operation count, and the stated inclusions and
exclusions for the class of convex profiles with log-concave
increments. These are auxiliary interpretations, calculations
and scope observations beyond the mapped Lean statements.
The one-kink example with $N=500$ is checked in exact arithmetic
by \path{smallr_probe.py}, but the documented Lean-kernel
evaluation did not finish within 50 minutes.
The polynomial dependence on a terminal perturbation and the
exact contour representation of its first-order change are
not formalized; the accompanying saddle-point discussion is
heuristic. The 80-/150-digit examples in
Section~\ref{sec:limits}, the 150-/300-digit example and the
unsuccessful sampled search in Section~\ref{sec:open} are
numerical evidence, not exact sign certificates.
Finally, the sign-pattern classification in
Section~\ref{sec:open} is not formalized:
\path{signpattern_probe.py} checks its witnesses in exact
arithmetic, but only the negative-sign claim for its $N=100$
witness is covered by the Lean results listed above; the
additional $N=20,120,80$ witnesses and the classification
argument are not.
```

## Overall verdict: **FAIL**

The principal numbered-result coverage is substantially documented, and most existing exclusion sentences are accurate. The failure is **completeness**: substantial unnumbered mathematical content remains unmarked, particularly P2’s certificate obstructions and P3’s exact maximum values, reversal obstructions and sign-pattern classification. P3 also needs the exact-contour/heuristic-saddle distinction.

This was a source-and-coverage review at `92848bf`; I did not rebuild Lean or rerun the diagnostic scripts.

Sources:
[1] https://raw.githubusercontent.com/skypher/szkraw/92848bf/papers/p1.tex
[2] https://raw.githubusercontent.com/skypher/szkraw/92848bf/papers/FORMALIZATION.md
[3] https://raw.githubusercontent.com/skypher/szkraw/92848bf/runs/varratio/cubic_diag.py
[4] https://raw.githubusercontent.com/skypher/szkraw/92848bf/papers/p2.tex
[5] https://raw.githubusercontent.com/skypher/szkraw/92848bf/lean/Szkraw/VRCorollaries.lean
[6] https://raw.githubusercontent.com/skypher/szkraw/92848bf/lean/Szkraw/OpenExamples.lean
[7] https://raw.githubusercontent.com/skypher/szkraw/92848bf/runs/cubic/bdetour_u.py
[8] https://raw.githubusercontent.com/skypher/szkraw/92848bf/papers/p3.tex
[9] https://raw.githubusercontent.com/skypher/szkraw/92848bf/lean/Szkraw/Interior.lean
[10] https://raw.githubusercontent.com/skypher/szkraw/92848bf/lean/Szkraw/OmegaShape.lean
[11] https://raw.githubusercontent.com/skypher/szkraw/92848bf/lean/Szkraw/LowerTopMass.lean
[12] https://raw.githubusercontent.com/skypher/szkraw/92848bf/lean/Szkraw/ColumnCheck.lean
[13] https://raw.githubusercontent.com/skypher/szkraw/92848bf/signpattern_probe.py

