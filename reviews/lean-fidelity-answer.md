## 1. Statement comparison

**No semantic mismatch is demonstrated in the supplied Section 7 theorem types.** Theorem 8.1 matches under the Newton convention specified below. Two requested rows cannot be assessed because their theorem statements were not supplied.

All declaration names below have prefix `Szkraw.`.

| Paper result | Lean declaration(s) | Verdict | Reason |
|---|---|---|---|
| Theorem 2.1: geometric criterion | `geometric_criterion` | **Not assessable** | `Admissible`, `Geometric`, `FiniteRealization` and `MatrixPositivity` encode the intended hypotheses and conclusion faithfully, but the declaration’s type is absent. |
| Perturbation theorem | `perturbation_criterion` | **Not assessable** | Neither the paper theorem nor the Lean type is supplied. The radius, margin and triangle-zero claims cannot be compared. |
| Theorem 7.1: Szwarc system | `szwarc_system`, `szwarc_sharp` | **MATCH, SCOPE NOTED** | Correct parameter ranges, \(2N+1\) distinct support points, product identities, nonnegativity, coefficient sums and strict negative coefficient. Measure symmetry is absent but explicitly disclosed. |
| Theorem 7.8: decomposition | `decomp_positivity`, `decomp_converse`, `even_block`, `odd_block`, `evenComp_admissible`, `oddComp_admissible` | **MATCH** | Normalizations, component ranges, transfer and converse match. `product_normalize` reconciles raw versus normalized components. `Gk_parity` and `piW_entry` cover parity and norm reciprocity. Several Lean conclusions allow \(N=1\), which is stronger, not a restriction. |
| Corollary 7.9: parity split | `parity_split`, `parity_split_sharp` | **MATCH, SCOPE NOTED** | Positivity and sharpness match, including \(N=1\). Admissibility supplies \(0<p_0<1\). Explicit component-parameter identification is disclosed as unformalized. The scope sentence needs an \(N\ge2\) qualifier; see below. |
| Theorem 7.10: low products | `low_products` | **MATCH** | Exact monotonicity cutoffs and cross-inequality range. The conclusion covers all three possible pair sums, including the paper’s consequence about negative coefficients. |
| Corollary 7.11: convex profiles | `convex_low`, `geometric_convex` | **MATCH** | Strict increase follows from admissibility, the positive constant ratio and nondecreasing increments. All three pair-sum cases are covered. `geometric_convex` supplies the geometric subclass. |
| Theorem 7.12: all products | `all_products` | **MATCH** | Full monotonicity ranges match; the cross inequality stops at \(i=N-1\). Admissibility makes `gammaS … N = 0`. |
| Corollary 7.13: heavy top step | `heavy_top` | **MATCH** | Same ratio, strict profile increase and \(d_{N-1}\le1/2\). Profile endpoints and coefficient formulas follow from admissibility and the ratio equation. |
| Lemma 7.14: reversal | `reversal_identity` | **MATCH** | Includes the supplied section hypotheses `v`, `hv`. The matrix identity expresses the support identity, using the genuinely reversed recurrence—not an incorrectly standardized reversed array. |
| Theorem 7.15: deep reduction | `deep_formula`, `top_expansion`, `deep_reduction` | **MATCH** | The reduction formula holds for every \(x,y\le N\), stronger than the deep-only claim. Top expansion and all three positivity assumptions match. |
| Theorem 7.16: palindromic criterion | `palindromic` | **MATCH** | Same palindromicity and low-product hypotheses; positivity covers every triple. |
| Corollary 7.17: monotone palindromic systems | `palin_mono`, `palin_mono_kraw` | **MATCH** | The paper’s hypotheses imply admissibility: \(c_1>0\), monotonicity and palindromicity force positive interior \(a_i,c_i\). The Krawtchouk specialization matches. |
| Theorem 8.1: log-concave Newton criterion | `logconcave_criterion` | **MATCH, SCOPE NOTED** | Matches for **nonnegative binomial-basis Newton coefficients** \(\nu_k=\Delta^k d(0)\). The extra finite-realization conclusion is stronger. The coefficientwise/Bernstein remark is explicitly excluded. The paper excerpt should specify the Newton convention. |

### Boundary and normalization checks

There is **no mismatch** from dropping \(\sigma_0=1\): replacing \(\sigma\) by \(\sigma/\sigma_0\) preserves every `alphaS` and `gammaS`. Universal quantification over a supplied qualifying \(\sigma\) is equivalent to the paper’s existential-witness formulation. Values beyond \(N\) impose no additional requirement.

The decomposition’s natural-number subtraction and unrestricted coefficient functions cause no endpoint discrepancy: the affected terms vanish through \(c_0=0\), \(a_{2N}=0\), or `Gk`’s zero extension.

The reciprocity orientation is correct. With \(h_i=\int R_i^2\,d\mu=C/\pi_i\), `piW_entry`
\[
\pi_n g(m,n;k)=\pi_k g(m,k;n)
\]
is precisely \(g(m,n;k)h_k=g(m,k;n)h_n\).

## 2. Exact fixes and evidence gaps

**Parity-component scope sentence.** Replace the unqualified assertion about both normalized components by:

> For Corollary 7.9, when \(N\ge2\), Lean proves that both normalized components satisfy the hypotheses of Theorem 2.1. The theorem `parity_split` also covers \(N=1\), where the odd component consists only of the constant polynomial and is not an admissible positive-length system. The explicit parameter identification is not formalized.

This qualifier matters: for \(N=1\), the odd component has length zero, whereas `Admissible` requires positive length.

**Newton convention.** Unless already defined elsewhere in the paper, add:

> Here the Newton coefficients are \(\nu_k=\Delta^k d(0)\), so \(d_i=\sum_{k=0}^i\binom{i}{k}\nu_k\). “Log-concave without internal zeros” refers to the nonnegative sequence \((\nu_k)_{k=1}^N\).

Under that convention, Lean’s \(\nu_1>0\) follows from \(d_1>0\); the omitted log-concavity inequality at \(k=1\) is automatic because \(\nu_0=0\). A signed-sequence, inequality-only interpretation, or a different Newton-basis normalization, would **not** establish the same hypothesis match.

**Axiom disclosure.** Add to the code section:

> The axiom audit reports only `propext`, `Classical.choice` and `Quot.sound`.

The existing phrase “without added axioms” is consistent with the audit, but the AI disclosure’s “with the axioms stated there” currently points to no explicit list.

**Missing review evidence—not demonstrated development gaps.** A complete audit requires the types of `geometric_criterion` and `perturbation_criterion`, plus the paper’s perturbation statement. No statement correction can responsibly be prescribed for those unseen declarations.

## 3. Scope and AI-use disclosure

The disclosed exclusions—measure symmetry in 7.1, parameter identification in 7.9, and the two-parameter/Bernstein remark—accurately delimit the supplied formal statements. The descriptions of low-product versus all-product coverage are correct. The matrix formulation of reversal, deep reduction and norm reciprocity does not weaken the corresponding support statements.

The claims about the generic `finite_realization` theorem, component-geometric helper results, cone argument and Section 8 auxiliary lemmas are **not independently auditable from the displayed types alone**. Their absence from the excerpts does not establish absence from the development.

The AI-use disclosure’s formalization scope otherwise agrees with the code section. Its provenance and review-history assertions are outside this statement audit.

## 4. Overall verdict

**PASS WITH MINOR FIXES for the supplied declarations**, subject to the explicit Newton convention. No Lean-statement change is indicated for Section 7.

**A full-table PASS is not established:** the geometric theorem type and both perturbation statements were omitted.
