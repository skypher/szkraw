| Paper claim | Lean declaration | Assessment | Reason |
|---|---|---|---|
| Theorem 7.1: realization, symmetry, nonnegative products, coefficient sums one | `szwarc_full : Stmt_szwarc_full` | MATCH | Same \(N,p_0\) hypotheses. `FiniteRealization` supplies exactly \(2N+1\) distinct positive-weight support points, orthogonality, support product identities, and sums one. `MatrixPositivity` supplies nonnegativity. Symmetry of **every** realization strengthens the existential paper conclusion. |
| Theorem 7.1: measure symmetry | `realization_symmetric` | MATCH, SCOPE NOTED | Under `Admissible v` and \(b\equiv0\), pairing each support point with its negative at equal weight expresses symmetry exactly. The declaration covers arbitrary admissible arrays, not just Szwarc arrays. |
| Corollary 7.9: even downward profile | `ps_d_formula` | MATCH, SCOPE NOTED | States \(d_n=[n]_q/[N]_q\) throughout \(0\le n\le N\). Included hypotheses are `hv hb hp`; omission of \(p_0\le1/2\) weakens the hypotheses. Admissibility excludes \(N=0\). |
| Corollary 7.9: normalized even parameters \((N,q,r)\) | `ps_even_params` | MATCH, SCOPE NOTED | Lean uses \(p=(1-p_0)/p_0=1/r\). All three coefficients agree on precisely the paper’s index range. No \(N\ge2\) or \(p_0\le1/2\) restriction is imposed, so the statement is stronger. |
| Corollary 7.9: normalized odd parameters \((N-1,q,r/q)\) | `ps_odd_params` | MATCH, SCOPE NOTED | Lean uses \(p=q(1-p_0)/p_0=q/r=1/(r/q)\). The \(N\ge2\) restriction and index range match; omission of \(p_0\le1/2\) weakens the hypotheses. |
| Theorem 7.1: formalization scope sentence | `szwarc_full`, `realization_symmetric`, previously reviewed `szwarc_sharp` | MATCH, SCOPE NOTED | Coverage matches. Explicitly retain **admissibility** in the universal-symmetry wording. The claimed proof route is outside this statement-only review. |
| Corollary 7.9: formalization scope sentence | `ps_even_params`, `ps_odd_params`, previously reviewed parity-split declarations | MATCH | Correctly describes parameter identification for \(N\ge2\), under the corollary’s hypotheses, and separately notes positivity at \(N=1\). Finite-range coefficient equality is sufficient; equality of arbitrary out-of-range values is not required. |

**Exact fix — scope wording only:** replace
```latex
every finite realization of an array with $b\equiv0$
```
with
```latex
every finite realization of an array satisfying \eqref{eq:basic} with $b\equiv0$
```

No Lean statement changes are needed. Sharpness remains covered by the previously reviewed `szwarc_sharp`.

**Overall verdict: PASS WITH MINOR FIXES.**
