| Paper claim | Lean declaration | Assessment | Reason |
|---|---|---|---|
| Positive lowered masses; orthogonality in fixed \(x\); normalization at \(x_0=1\) | `interior_measure` | MATCH | States positivity of every `kw … t − ε[t=0]`, pairwise orthogonality through degree \(N\) at `kx`, and evaluation \(1\) at \(1\). Uses `epsRaw … (-ε)`, with the correct lowering sign. |
| Strict positivity of every triangle coefficient for \(N\ge2\), \(\Lambda>\Lambda_N\), and all sufficiently small positive \(\varepsilon\) | `interior_points`, `interior_measure` | MATCH | Quantifiers agree. `Triangle` together with the index bounds is exactly \(\lvert m-n\rvert\le k\le\min(m+n,N)\). `interior_points` additionally states \(0<r<1\) and \(\varepsilon<kw(N,r,0)\). |
| Normalized array satisfies (2.1), with a relatively open neighborhood having (P) | `interior_open` | MATCH | `epsNorm … (-ε)` gives \(y=(1-\varepsilon)x+\varepsilon\). The center is admissible, and every admissible array in the positive-radius coefficient box has `MatrixPositivity`. The closed box stated with `≤ η` contains the required relatively open box with `< η`. |
| Existence of a finite threshold \(\Lambda_N\) | `lamN`, `lowG`, `lowK` | MATCH, SCOPE NOTED | Uses the specified first-order rates at \((1,0)\). A finite sum rather than the paper’s maximum is sufficient for the existential claim. Lean division by zero contributes zero; ordinary ratio bounds concern nonzero \(r\)-rates. No numerical identification is claimed. |
| Explicit \(H\)-formula for \(K_{N,r}\) | `kraw_g_formula` | MATCH | The normalized fixed-\(U\) count is the same combinatorial formula, with \(j=\lvert S\cap T\rvert\), \(s=\lvert J\rvert\), and \(k=m+n-2j+s\). Its hypotheses cover the paper’s parameter range. |
| On triangles, endpoint zeros occur exactly for odd total degree or total degree \(>2N\) | `kraw1_zero`, `kraw1_pos` | MATCH | Together they give both directions of the stated zero pattern. The zero theorem does not require a triangle hypothesis, which strengthens it. |
| Supporting negative \(r\)-derivative statement | `kraw_deriv_neg` | MATCH, SCOPE NOTED | Covers odd triangle triples **only when \(m+n+k\le2N+1\)**. It makes no assertion for odd totals \(\ge2N+3\). This is not a gap in the supplied proposition, but the helper’s unrestricted docstring overstates its scope. |
| Proposition 9.8 scope sentence | Code-and-formalization section | MATCH, SCOPE NOTED | Correctly describes the finite threshold, measure identification, and coefficient-box neighborhood. The box inequalities are explicit; the radius \(\eta\) is existential, not explicitly calculated. |

**Exact fixes — documentation only:**

1. In the `kraw_deriv_neg` docstring, replace “For `m + n + k` odd on the triangle” with “For `m + n + k` odd on the triangle and `m + n + k ≤ 2 * N + 1`”.
2. In the scope sentence, replace “an explicit coefficient box” with “a coefficient box of some positive radius”. For precision, describe the sum as bounding “the absolute first-order-rate ratios with nonzero \(r\)-rate”.

**Overall verdict: PASS WITH MINOR FIXES.** No theorem-statement changes are needed, and no part of Proposition 9.8’s asserted scope is missing.
