**Statement — MATCH.** The two conjuncts assert the real derivative **with respect to \(\varepsilon\), at \(\varepsilon=0\)**, with \(r=4/5\) fixed: \(512/1875\) for \(N=4\), and \(-71936/5859375\) for \(N=8\). Under the accepted `productMatrix` convention, the indices select \(g(N,N;N)\). The declaration at `e479a4e` matches the supplied statement. [1]

The supplied definitions encode the intended direction exactly: constant \(\beta=1\) gives \(\delta b_n=1\) on \(1\le n<N\), and \(\gamma=0\) gives \(\delta c_n=0\). `stochArray` ignores the supplied `b` values at the endpoints, so `(fun _ => 1)` introduces no unwanted endpoint perturbation. There is no additional \(1/N\) factor for this constant rule.

The opposite signs at \(N=4\) and \(N=8\), which are congruent modulo four, also substantiate the passage’s nonpersistence claim. The theorem need not separately express that qualitative consequence.

**Change 1 — MATCH.** The proposed table row accurately describes the theorem’s scope and uses its correct fully qualified name, `Szkraw.PolyCol.rule_deriv_4_5`. [1]

**Change 2 — MATCH.** As an edit to the **pending round-23 sentence**, it correctly moves the two derivative computations from the exceptions into the formalized coverage and supplies the corresponding declaration. The one-kink \(N=500\) example remains excluded. The theorem supports precisely the added derivative coverage. [1]

**Overall verdict — PASS.** No replacement text is needed. Applying the combined documentation changes remains conditional on round 23 also passing.

Sources:
[1] szkraw/lean/Szkraw/PolyColumn.lean at e479a4ea0c6eed86cf8f70d2489c6dcc3ad4493b · skypher/szkraw · GitHub — https://github.com/skypher/szkraw/blob/e479a4e/lean/Szkraw/PolyColumn.lean

