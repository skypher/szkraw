| Paper claim | Lean declaration | Assessment | Reason |
|---|---|---|---|
| Lemma 9.5 | `norlund_rice` | **MATCH** | Correct potential, region, analyticity hypothesis, and alternating sum. Constants are independent of \(N\). Requiring the bound for every \(N\ge1\) is equivalent to the asymptotic claim after enlarging \(C\). |
| Corollary 9.6: forced equalities | `analytic_forced_equalities` | **MATCH** | Correct restriction-based analyticity, admission quantifiers, property (P), and both equalities. Separate extension domains cause no restriction: their intersection is a common domain. |
| Corollary 9.6: small derivative | `analytic_rule_small` | **MATCH** | Establishes derivative existence and the exact \(\lvert s_N\rvert C\sqrt N e^{-\eta N}\) bound, with uniform constants, for every \(N\ge2\). |
| Corollary 9.6: nonvanishing example | `expRule_analytic`, `expRule_L`, `expRule_deriv` | **MATCH** | Correct rule with \(\gamma=0\), analyticity, both equalities, and the stated derivative and nonvanishing for every \(N\ge2\). |
| General derivative, context | `analytic_rule_deriv` | **MATCH** | Correct parity branches and endpoint corrections: \(D_N(\beta+2\gamma)-L_{\mathrm{even}}\) and \(D_N\beta-L_{\mathrm{odd}}\). No analyticity assumption is needed here. |
| Proposition 9.9 (2) | `families_boundary_layers` | **MATCH** | A common fixed \(K\) is equivalent to four finite supports. Separate eventual thresholds can be combined. Coordinate ranges and endpoint conventions agree. The family hypothesis and every asserted equality, including all \(k\ge1\), are present. |
| New table rows and numbered-result coverage | Listed declarations | **MATCH, SCOPE NOTED** | No coverage gap for the three results reviewed here. `families_weak_sign` is not supplied; earlier results and named proof helpers are not independently certified in this round. |
| Zero-layer derivation sentence | Specialization of `families_boundary_layers` | **MISMATCH** | Zero layers recover **only the first statement** of Corollary 9.6—not its derivative estimate or nonvanishing example. |
| Grid-cycle scope sentence | Reference to `residue_identity` | **MATCH, SCOPE NOTED** | The construction is outside this proof-free review. Independently, irrational origin coordinates alone do not guarantee node avoidance for an unrestricted grid mesh; the wording needs qualification. |

### Exact fixes

1. Replace:
   > Corollary~`\ref{cor:analytic-rules}` is derived from it with zero boundary layers.

   with:
   > The first statement of Corollary~`\ref{cor:analytic-rules}` is obtained by specializing Proposition~`\ref{prop:families}`~(2) to zero boundary layers.

2. In the grid sentence, replace:
   > whose origin has irrational coordinates, so that no node \(k/N\) lies on a grid line

   with:
   > whose grid lines contain no node \(k/N\)

   Alternatively, specify an axis-parallel grid with positive rational mesh and irrational origin coordinates, provided that describes the construction.

**No Lean statement changes are required.** The absence of an explicit `Admissible` hypothesis is not a defect under the acceptance rule: it does not strengthen the Lean hypotheses.

**Overall verdict: PASS WITH MINOR FIXES — documentation only.**
