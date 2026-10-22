| Paper claim | Lean declaration | Status | Reason |
|---|---|---|---|
| Quadratic algebra with squarefree-monomial basis | `QuadRel`, `B`, `hB`, `cube_model` | MATCH, SCOPE NOTED | The abstract formulation covers the paper’s algebra; the Boolean cube gives the stated model when \(r\ne-1\). **The displayed theorem does not actually include `hB`; see fix below.** |
| \(y_lf_l=f_l\), \(f_l^2=f_l\) | `edge_idempotents` | MATCH | Exact identities. Allowing every \(r\ne-1\) broadens the paper’s parameter range. |
| \(f_ly_S\), \(l\notin S\), is a basis of \(f_lA\) | `edgeFamily`, `edge_idempotents` | MATCH | Linear independence plus equality of the real span with the restricted principal ideal expresses precisely this basis assertion. |
| Nonnegative \(u\) gives nonnegative edge-basis coordinates | `BasisNonneg`, `edge_idempotents` | MATCH | With \(B S=y_S\), the nonnegativity notion agrees. Existence of nonnegative coordinates, together with independence, gives the paper’s unique coordinates. |
| Definitions of \(Y,U_k\) and array (7.2) | `Yop`, `Uvec`, `szwarcCoefficients` | MATCH | Correct summation sets, binomial normalizations, parity indexing, and coefficients; \(b_k=0\). |
| Three-term identity for \(0\le k\le2N\) | `three_term_action` | MATCH, SCOPE NOTED | `hN` matches the positive-\(N\) setting. `p₀ < 1` is weaker than \(0<p_0<1\); omitting a basis hypothesis further generalizes the result. Ambient equality gives the same identity on \(V\). |
| \(U_{-1}=U_{2N+1}=0\) conventions | `Uvec_top`, `three_term_action` | MATCH | Upper endpoint is stated separately. At \(k=0\), truncated subtraction is harmless because \(c_0=0\); \(a_{2N}=0\) also matches. |
| Updated formalization scope sentences | Both lemma entries | MATCH, SCOPE NOTED | Model and span descriptions are accurate. No separate algebra-isomorphism theorem, bundled \(V\), or \(A\)-linearity theorem is displayed; none is needed to express these lemma conclusions. Make the parameter scope explicit as below. |

### Exact fixes

**1. Include `hB` in the displayed `edge_idempotents` declaration.** Add the explicit binder
```lean
(hB : ∀ S, B S = ySet y S)
```
or wrap that declaration with `include hB in`. Merely declaring `hB` as a section variable does not include it in a theorem whose header never references it. [1]

This omission is an unintended **strengthening**, not undercoverage under the stipulated acceptance rule. An existing surrounding `include hB` would make this only an excerpt correction.

**2. Clarify the Lemma 7.3 scope sentence:**

> Lemma 7.3 is stated for \(N\ge1\), \(p_0<1\), and \(r=p_0/(1-p_0)\), in every commutative real algebra satisfying the quadratic relations, without a basis hypothesis. Its recurrence is an equality in \(A\times A^N\), restricting to \(V\); `Szkraw.Uvec_top` separately states \(U_{2N+1}=0\).

**Overall verdict: PASS WITH MINOR FIXES.** No mathematical conclusion of either lemma is missing.

Sources:
[1] Namespaces and Sections — https://lean-lang.org/doc/reference/latest/Namespaces-and-Sections/

