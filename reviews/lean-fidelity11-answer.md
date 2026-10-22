| Paper claim | Lean declaration | MATCH / MATCH, SCOPE NOTED / MISMATCH | Reason |
|---|---|---|---|
| §8 Newton coefficients, padding, and log-concavity without internal zeros | `newtonCoeff`, `padNewton`, `LogConcaveNoInternalZeros` | **MATCH** | The Newton formula and padding agree exactly. For admissible \(N\ge1\), nonnegativity, positivity at \(1\), and propagation of zeros are equivalent to positive support \(\{1,\ldots,K\}\). The log-concavity index range agrees. |
| Theorem 8.6 | `MixedIneq`, `VaryRatioHyp`, `Stmt_varyratio`, `varyratio_matrix` | **MATCH** | Both mixed inequalities have the correct factors, shifts, and index ranges. Here `iterShift … (ℓ + 1) 0` equals \(c_{\ell+1}\), since \(\ell<N\). Nonnegativity of \(\beta_k\) on \(1\le k\le N\) covers all coefficients after padding. The conclusion is nonnegative linearization. |
| Corollary 8.7 | `WeightHyp`, `Stmt_varyratio_weights`, `varyratio_weights` | **MATCH, SCOPE NOTED** | Restricting weight hypotheses to \(1,\ldots,N\) loses nothing because the Newton sequences are padded. Adjacent ratio inequalities express monotonicity throughout \(1,\ldots,N\). The support condition uses “nonzero,” equivalent here to “positive.” The conclusion \(b_i=w_0c_i\) implies the claimed constant ratio. |
| Proposition 8.8 | `QuadHyp`, `Stmt_quadratic`, `quadratic_matrix` | **MATCH** | The quadratic formulas are hypotheses on every \(0\le n\le N\). Both scalar inequalities agree, and adjacent inequalities express \(b_0\le\cdots\le b_N\). There is no extra requirement \(\beta_2\ge0\). The existential parameters do not restrict the paper’s class of arrays. |
| Code table and theorem-statement scope descriptions | The three named public theorems above | **MATCH, SCOPE NOTED** | Names and stated scope agree. Claims describing auxiliary proofs are outside this statement-only review. |

**Boundary and scope notes.** For Proposition 8.8, when \(N\ge2\), the quadratic identities force the parameters to equal the corresponding Newton coefficients. When \(N=1\), the second-order parameters are undetermined by the identities, but choosing both zero gives exactly the paper’s padded convention; there is no coverage gap.

In Corollary 8.7’s constant-weight case, \(w_0=w_1\ge0\), so the Lean conclusion yields
\[
\frac{c_i}{b_i+c_i}=\frac1{1+w_0}\qquad(1\le i\le N).
\]
Thus the constant-ratio conclusion is not missing. The further identification with the arrays of `thm:lc` cannot be independently audited because that theorem’s statement was not supplied.

**Exact fixes:** None required for the supplied mathematical statements.

**Overall verdict: PASS.**
