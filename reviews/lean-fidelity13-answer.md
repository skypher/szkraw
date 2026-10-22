| Paper claim | Lean declaration | Assessment | Reason |
|---|---|---|---|
| Section 8: log-concavity without internal zeros | `LogConcaveNoInternalZeros` | MATCH | Positive first coefficient, nonnegativity, zero propagation, and the interior log-concavity inequalities encode exactly the stated finite-sequence condition. Zero-padding beyond \(N\) is not an additional profile hypothesis. |
| Theorem 8.9: nonnegative linearization assuming \(b\) nondecreasing | `AffineRatioHyp`, `Stmt_affine`, `affine_matrix` | MATCH | Uses precisely the strengthened monotonicity hypothesis, not the old bound. Admissibility supplies \(d_0=0,d_N=1,a_i=1-d_i\); the Newton conditions recover strict increase. Conversely, the paper’s constructed arrays satisfy admissibility. |
| Theorem 8.9: equivalence with the endpoint inequality | `affine_bmono_iff` | MATCH | Exact monotonicity condition and exact inequality. Omitting \(r\le1\) weakens the hypotheses, which is permitted. Admissibility ensures \(N\ge1\) and \(1-d_{N-1}>0\). |
| Remarks following Theorem 8.9 | No separate declarations supplied | MATCH, SCOPE NOTED | The general criterion is formalized, but separate statements for the linear-profile bound, convex-profile range inclusion, strict inclusion for nonlinear profiles, and numerical example are not supplied. |
| Proposition 8.10: nonnegative linearization | `QuadProfileHyp`, `Stmt_quadprofile`, `quadprofile_matrix` | MATCH | All parameter signs, profile and ratio formulas, and monotonicity hypotheses agree. Normalization \(d_N=1\) and \(a_i=1-d_i\) follow from admissibility; the paper’s construction conversely satisfies admissibility. No extra restriction excludes \(\nu_2=0\), \(t=0\), or \(\tau=0\). |
| Endpoint criterion following Proposition 8.10 | None supplied | MATCH, SCOPE NOTED | This equivalence is not formalized, exactly as the scope sentence discloses. |
| Code-table rows | `affine_matrix`, `quadprofile_matrix` | MATCH | Correct references for the positivity conclusions. The additional affine equivalence is correctly identified separately in the scope prose. |
| Array-based hypothesis descriptions in the scope prose | `AffineRatioHyp`, `QuadProfileHyp`, their enclosing statements | MATCH | Parameter restrictions, index ranges, profile/ratio relations, admissibility, and adjacent monotonicity agree. |
| Scope’s inequality \(\varphi_2(\ell)\varphi_2(\ell+1)\ge c_{\ell+1}\varphi_4(\ell)\) | `phi2_phi2` | MATCH | Its type states precisely this inequality, using \(c=\rho d\) and iterated forward differences, under the proposition’s parameter signs. |

**Exact fixes:** None required for statement fidelity or the table’s mathematical scope. If the trailing repeated `theorem quadprofile_matrix : Stmt_quadprofile` is literal source rather than an excerpted signature, delete that duplicate and retain the earlier declaration.

Proof bodies and assertions about which intermediate results or resummation choices the proofs use are not assessed. The other cited auxiliary signatures are not supplied, so their detailed scope is not independently certified here.

**Overall verdict: PASS.**
