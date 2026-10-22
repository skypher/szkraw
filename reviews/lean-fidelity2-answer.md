## 1. Statement comparison

| Paper result | Lean declaration | Status | Reason |
|---|---|---|---|
| Theorem 2.1 | `geometric_criterion : Stmt_geometric` | **MATCH** | `Admissible` supplies (2.1), including \(N\ge1\). Since \(c_i>0\), `b i = β * c i` is equivalent to \(b_i/c_i=\beta\). Increment conditions and ranges agree. `FiniteRealization` and `MatrixPositivity` provide all conclusions, including normalization and sums one. |
| Theorem 5.3 | `perturbation_criterion : Stmt_perturbation` | **MATCH** | Radius, coordinatewise closeness, nonnegative diagonal, and triangle margin agree exactly. Finite realization includes sums one. Exact zeros outside the triangle are an additional, stronger conclusion. |
| Lemma 7.4 | `szwarc_margin : Stmt_szwarc_margin` | **MISMATCH** | **Textual defect as supplied:** the paper does not define \(r\). Lean fixes \(r=p_0/(1-p_0)\), rather than treating it as an independent parameter. With that definition inserted, the margin, parity condition, and complementary zeros match. |
| Lemma 7.5 | `stability : Stmt_stability` | **MATCH** | All assumptions match, including reference positivity, the bound on \(a_i\) only for \(i<M\), perturbed diagonal nonnegativity, and both smallness inequalities. Both the global error bound and the margin on \(\Sigma\) are present. |
| Theorem 7.6 | `symmetric_criterion : Stmt_symmetric` | **MATCH** | Endpoints, \(b=0\), \(a=1-c\), radius, margin, and zero pattern agree. `1 ≤ k` and `k + 1 ≤ 2*N` mean exactly \(1\le k\le2N-1\). Admissibility is **concluded**, not imposed as an extra hypothesis. Realization supplies sums one. |
| Corollary 7.7 | `symmetric_new`, with `symmetric_criterion` for the neighborhood assertion | **MATCH, SCOPE NOTED** | The specified perturbation and both exclusions match. Exclusion using only \(c\), or \(b,c\), suffices to exclude equality of arrays. The geometric parameter range \(p'\ge1,\ q'\ge1\) covers exactly \(0<r\le1,\ q\ge1\). The final neighborhood assertion follows from `symmetric_criterion`, not from `symmetric_new` alone. |

There are **no material index-range or normalization discrepancies**. The `Fin` indices enforce the finite upper bounds; consequently `Triangle` expresses the paper’s triangle condition including \(k\le\min(m+n,N)\), or its \(2N\) counterpart.

## 2. Exact fixes

**Lemma 7.4:** replace its opening sentence with:
```latex
Let $N\geq1$, $0<p_0<1/2$, $r=p_0/(1-p_0)$,
and $s=\min(r,1-r)$.
```
The explicit \(N\ge1\) merely restates the inherited convention; defining \(r\) is the essential correction.

**Scope paragraph:** replace
```latex
its last sentence is Theorem~\ref{thm:symmetric}.
```
with
```latex
its last sentence follows from the explicit positive-radius
coefficient box formalized in \path{Szkraw.symmetric_criterion}.
There is no separate Lean statement of topological openness or dimension.
```

No supplied Lean type needs modification.

## 3. Scope-text check

The descriptions of the geometric and perturbation criteria are accurate. The new margin, stability, and symmetric-criterion entries correctly identify the corresponding mathematical statements.

For Corollary 7.7, the positive-radius box allows all \(2N-1\) interior coefficients to vary independently. Its interior supplies the asserted relatively open neighborhood. Thus the mathematical neighborhood claim is covered by the stronger explicit criterion, although openness and dimension are not separately stated in Lean. The replacement above makes that distinction precise.

The existing exclusions for measure symmetry, parameter identification, and the log-concavity remark remain consistent with the supplied scope. The AI disclosure needs no further substantive change once the scope clarification is made. Script behavior, proof routes, compilation, and axiom-audit claims are not verifiable from theorem types alone.

## 4. Overall verdict

**PASS WITH MINOR FIXES** — insert the missing definition of \(r\) in Lemma 7.4 and clarify the attribution of Corollary 7.7’s neighborhood assertion.
