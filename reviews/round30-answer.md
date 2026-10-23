## P1 — PASS

**Accuracy:** No incorrect exclusion found. In particular, the convex-combination calculation, exact counterexamples and Bernstein certificates remain covered by the table and scope notes; the paragraph correctly excludes only the additional observations and comparisons. [1][2]

**Completeness:** No additional numbered result, mathematical remark or exact computational claim requiring disclosure was found under the requested exclusions. **No replacement needed.** [1][2]

## P2 — PASS WITH MINOR FIXES

**Accuracy:** The existing sentences are accurate. The distinction between failure of a particular certificate and failure of property (P) is preserved. Lemma 5.4 and the \(7/4\) extension are mapped and should not be added to the exclusions. [3]

**Completeness:** One exact-computation claim remains unmarked: immediately after Proposition 3.3, `runs/varratio/quadratic.py` is said to produce counterexamples with \(N\leq3\) when **each of the three hypotheses is dropped individually**. The mapped `Szkraw.quadratic_matrix` proves sufficiency, not these counterexamples or the non-redundancy assertion. Neither the current paragraph nor the scope notes identify this claim as unformalized. [3][4][2]

**Exact fix:** Insert the following after the paragraph’s first sentence:

```latex
The exact computations reported after
Proposition~\ref{prop:lc-quad}, using
\path{runs/varratio/quadratic.py} to give counterexamples with
$N\leq3$ when any one of its three hypotheses is dropped while
the other two are retained, are not formalized.
```

No additional numbered-result omission was found. [3]

## P3 — PASS WITH MINOR FIXES TO EXPLICIT SCOPE DOCUMENTATION

**Accuracy:** No sentence incorrectly excludes either newly completed result. Proposition 3.4 and the last sentence of Corollary 7.7 are now fully mapped. The Koelink qualification also correctly distinguishes agreement with hand-transcribed formulas from verification of their fidelity to the source or formalization of the external construction. [5][6][2]

**Completeness:** No additional numbered result is unmapped. Two groups of prose applications would benefit from explicit scope mapping:

- **After Corollary 7.7:** transfer of the perturbation/stability criteria through the quadratic decomposition, and the converse observation about the even component.
- **After Corollary 8.8:** application of the palindromic criterion to both components, including the \(p_0=1/2\) specialization. [7]

These are **combinations of mapped results**, not new missing foundational formalizations: `decomp_positivity` and `decomp_converse` supply the transfer statements. They therefore should **not** simply be added to the list of unformalized results. The remaining issue is making their coverage explicit. [8]

**Exact fix:** Leave the P3 exclusion paragraph unchanged. Insert the following into `FORMALIZATION.md`, immediately after the existing scope note for full-manuscript Theorem 7.8:

```markdown
The quadratic-decomposition applications after P3 Corollary 7.7
combine `Szkraw.decomp_positivity` with the mapped perturbation
or stability result, retaining the stated support or
remaining-coefficient proviso for stability. The even-component
observation combines `Szkraw.decomp_converse` with the symmetric
criterion. The application after P3 Corollary 8.8 combines
`Szkraw.decomp_positivity` with `Szkraw.palin_mono`; its
$p_0=1/2$ specialization uses the component identifications
documented for P1 Corollary 4.2 and the symmetric-Krawtchouk
case `Szkraw.palin_mono_kraw`.
```

The component identifications, their small-\(N\) scope and the symmetric-Krawtchouk case are already present in the documented development. [2][9]

## Overall verdict — PASS WITH MINOR FIXES

The definite missing **not-formalized disclosure** is P2’s three hypothesis-dropping counterexamples. P3 needs only an explicit mapping of the combined applications—not another substantive exclusion. No regression concerning Proposition 3.4, Corollary 7.7 or the Koelink transcription checks was found.

*This was a source-and-scope audit, not a fresh Lean build or rerun of the computational searches.*

Sources:
[1] https://raw.githubusercontent.com/skypher/szkraw/abff2bc/papers/p1.tex
[2] https://raw.githubusercontent.com/skypher/szkraw/abff2bc/papers/FORMALIZATION.md
[3] https://raw.githubusercontent.com/skypher/szkraw/abff2bc/papers/p2.tex
[4] https://raw.githubusercontent.com/skypher/szkraw/abff2bc/lean/Szkraw/VRCorollaries.lean
[5] https://raw.githubusercontent.com/skypher/szkraw/abff2bc/lean/Szkraw/CompletionP3.lean
[6] https://raw.githubusercontent.com/skypher/szkraw/abff2bc/lean/Szkraw/Koelink.lean
[7] https://raw.githubusercontent.com/skypher/szkraw/abff2bc/papers/p3.tex
[8] https://raw.githubusercontent.com/skypher/szkraw/abff2bc/lean/Szkraw/QuadDecomp.lean
[9] https://raw.githubusercontent.com/skypher/szkraw/abff2bc/lean/Szkraw/Reversal.lean

