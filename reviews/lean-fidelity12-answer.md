| Paper claim | Lean declaration | Status | Reason |
|---|---|---|---|
| Section 8 Newton condition | `LogConcaveNoInternalZeros N (newtonCoeff (profile vv))` | MATCH | Positivity at 1, nonnegativity, and propagation of zeros give precisely support \(\{1,\ldots,K\}\). The log-concavity indices agree. Values above \(N\) are not inspected; no zero-tail hypothesis is needed here. |
| Theorem 8.9 hypotheses | `Admissible vv` and `AffineRatioHyp vv` | MATCH | Admissibility gives \(d_0=0,d_N=1,a_i=1-d_i\); the ratio relation gives the stated \(b_i,c_i\). Nonnegative Newton coefficients with \(\nu_1>0\) give strict profile increase. Since \(N\ge1\), the cross-multiplied bound is equivalent to the paper’s bound. Existentially packaging \(r,\kappa\) loses no cases. |
| Theorem 8.9 conclusion | `affine_matrix : Stmt_affine` | MATCH | `MatrixPositivity` is the stipulated nonnegative-linearization conclusion. No paper cases are omitted. |
| Linear-profile specialization and bound | `Stmt_affine` specialized to \(d_i=i/N\) | MATCH, SCOPE NOTED | This profile satisfies the Newton condition. Here \(b_i-b_{i-1}=(1-r)/N-\kappa(2i-1)/N^2\), so nondecreasing \(b\) is exactly the stated bound. Identification with Proposition `lc-quad` cannot be checked because that proposition was not supplied. |
| New table row | `Szkraw.affine_matrix` | MATCH | Identifies the supplied theorem implementing `Stmt_affine`. |
| Scope sentence’s hypothesis list | `Stmt_affine` / `AffineRatioHyp` | MISMATCH | The prose omits the required log-concavity-without-internal-zeros condition on the profile’s Newton coefficients. “As in Theorem 8.1” should not substitute for explicitly stating this hypothesis. |

**Exact fix:** Replace the scope sentence’s first clause with:
```latex
Theorem~\ref{thm:lc-affine} is stated for arrays satisfying
\eqref{eq:basic} whose profile $d_i=b_i+c_i$ has Newton coefficients
log-concave without internal zeros, with
$c_i=(r+\kappa i/N)(b_i+c_i)$ for $i\leq N$, $0<r\leq1$,
$\kappa\geq0$ and $(2N-1)\kappa\leq N(1-r)$, using the same
array-based encoding as in Theorem~\ref{thm:lc};
```

No Lean statement or table-row change is needed. The proof-method assertions—helper lemmas, constant \(4\), selected products, and resummation—are outside this statement-only review and are not certified by the supplied declarations. The finite indexing mentioned for the resummation identity does not itself restrict the theorem’s `MatrixPositivity` conclusion.

**Overall verdict: PASS WITH MINOR FIXES.** The Lean theorem covers the paper theorem; the scope prose needs the missing Newton hypothesis.
