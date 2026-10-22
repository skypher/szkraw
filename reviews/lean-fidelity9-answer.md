| Paper claim | Lean declaration | Assessment | Reason |
|---|---|---|---|
| For every \(d\ge0\), any nonempty open set of degree-\(\le d\) rules contains a rule not admitted by \(S\). | `no_open_rule_set` | **MATCH** | Includes \(d=0\); uses coefficient-vector pairs with the product topology and exactly `AdmitsRule`. The existential conclusion is the requested non-admission. |
| Under Proposition 9.9(2), \(\gamma(0)+\beta(1)+\gamma(1)=0\). | `boundary_layers_palindromic`, first conjunct | **MATCH, SCOPE NOTED** | Same hypotheses and exact necessary equality. Does not assert a converse, sufficiency, or an equivalence expressing the full “reduction.” |
| Boundary-layer palindromy for \(k\ge1\), \(N\ge k+K+1\). | `boundary_layers_palindromic`, remaining conjunct | **MATCH** | Exactly the expanded boundary-layer identities, with \(\delta a=-\delta b-\delta c\). The bound ensures interior indices and \(N-(N-k)=k\). Neither the full bulk-plus-boundary directions nor the separate terminal adjustment are asserted to be palindromic. |
| No positive \(N\)-independent coefficient-ball radius for fixed \(r\in(0,1)\). | `radius_no_uniform` | **MATCH, SCOPE NOTED** | `stableRadii` uses admissibility, \(b\ge0\), and coefficientwise bounds on all three coefficients. Eventual exclusion of every positive radius is stronger than failure of containment around **all** \(K_{N,r}\), and excludes containment by any \(P\)-only set. No coverage of \(r\notin(0,1)\). |
| New scope sentence. | All three named declarations | **MATCH, SCOPE NOTED** | Correctly identifies the three consequence groups and only the necessary bulk equality. Make the qualifications below explicit. The assertion about every numbered result is carried over from prior rounds, not independently reassessed here. |

### Exact documentation fixes

**Polynomial clauses, both locations:** replace “an open subset/set” with “a nonempty open subset/set.” In the scope sentence, explicitly prepend “for every \(d\in\mathbb N\)” to this consequence.

**Palindromic clauses:** write “for \(k\ge1\) and \(N\ge k+K+1\), where \(K\) bounds the supports of \(p,q,p',q'\).” Apply this qualification to the post-Proposition prose and its scope-summary clause.

**Radius clauses, both locations:** specify “for every fixed \(r\in(0,1)\)” and “a positive radius independent of \(N\).” Retain “in the sense of \(\rho_N(r)\)” in the scope sentence.

**Overall verdict: PASS WITH MINOR FIXES — documentation only.** No Lean-statement changes are needed for the stipulated claims.
