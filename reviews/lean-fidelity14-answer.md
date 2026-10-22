| Paper claim | Lean declaration | Assessment | Reason |
|---|---|---|---|
| Proposition 8.10 | `quadprofile_matrix` | MATCH | The accepted array encoding supplies normalization and the stated profile, ratio, parameter and monotonicity conditions. |
| Monotonicity equivalence after Proposition 8.10 | `quadprofile_bmono_iff` | MATCH | Exactly the stated bound. Lean omits `r > 0`, weakening the hypotheses as permitted. |
| Theorem 8.11 | `quadratic_ratio_matrix` | MATCH | Full theorem under the accepted array/Newton-coefficient encoding; no additional substantive restriction. Existential ratio parameters cause no loss. |
| Monotonicity equivalence after Theorem 8.11 | `quadratic_bmono_iff` | MATCH | Exactly the stated bound; again, `r > 0` is not required. In both equivalences, admissibility ensures the denominator is positive, including at `N = 1`. |
| Quadratic Leibniz rule in every order | `leibniz_quad` | MATCH | `PhiQ` has the correct three terms, shifts and coefficients, including orders zero and one. |
| Equation `quad-B` | `quadB_seq` | MATCH | With `v k = f_k(ℓ)`, the shifted sequence is `v k + v (k+1)` and the factor multiplying `PhiQ … (n+2)` is \(c_{\ell+1}\). Constants agree. The local sequence hypotheses hold for the paper’s profiles. |
| Equation `quad-cert` | `cert_nonneg` | MATCH | `certE` expands precisely \(K_nAB-L_npC\); the parameter restrictions agree. |
| Equation `quad-key` | `QuadSetting.key` | MATCH, SCOPE NOTED | In its `QuadSetting` context, this is the exact rearrangement of the paper inequality, for `ℓ + a ≤ N` and `a ≥ 3`. The latter restriction is not explicit in the paper’s scope sentence. |
| Reduced key-inequality auxiliary | `quad_key_red` | MATCH, SCOPE NOTED | Accurately identified as a conditional reduced inequality, not a standalone statement of `quad-key`. No corresponding expanded reduced formula was supplied for comparison. |
| Resummation with the third family | `ResumWeights2`, `resum_nonneg2`, `gkernel_resum2` | MATCH | The stated abstract resummation scope agrees. Constants are **4** for \(B,C',H,V\), **3** for \(W\), with key correction \(2V_1+W_1\). |
| Table rows and equivalence scope sentences | Both main theorems and both `*_bmono_iff` declarations | MATCH | Names and coverage agree. “Same arrays without monotonicity” understates the equivalences’ generality because `r > 0` is also omitted. |
| Blanket exclusion of prose remarks from machine verification | Both `*_bmono_iff` declarations | MISMATCH | These two prose equivalences are explicitly covered by listed Lean declarations. Other assertions in those paragraphs are not thereby formalized. |

### Exact fixes

1. Add to **each equivalence scope sentence and corresponding docstring**:  
   **“The Lean statement also omits the assumption \(r>0\).”**

2. Qualify the key-inequality citation:  
   **“the key inequality \(\eqref{eq:quad-key}\) on \(\Omega\) for \(a\geq3\) (`Szkraw.QuadSetting.key`), together with its reduced auxiliary inequality (`Szkraw.quad_key_red`)”.**

3. In the final disclosure, replace **“Other results and the prose remarks”** with:  
   **“Results and prose remarks not covered by those listed Lean theorems”.**

Adding `quadprofile_bmono_iff` to the proposition’s table row is optional: the scope paragraph already lists it.

**Overall verdict: PASS WITH MINOR FIXES.** No changes to the main theorem or equivalence statements are needed. Proof-route claims, compilation and axiom usage were not assessed.
