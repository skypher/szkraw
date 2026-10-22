# Mission for finite orthogonal polynomial linearization

Solve the recurrence-coefficient problem identified in Problem 2 of §5 of Ryszard Szwarc’s *Orthogonal Polynomials and Banach Algebras*: establish a general theorem giving structural assumptions on the three-term recurrence coefficients that imply nonnegative linearization for finite orthogonal polynomial systems, cover the full Krawtchouk parameter range with property (P), cover Szwarc’s symmetric system Q_n, and also cover a meaningful additional class of finite orthogonal systems.

Source: [Szwarc’s Inzell survey, §5, Problem 2](https://www.math.uni.wroc.pl/~szwarc/pdf/inzell.pdf), printed pp. 125–126. The problem reads: “Find any criteria for the property (P) for finite systems of orthogonal polynomials, like the Krawtchouk polynomials.” It then introduces the symmetric system

    y Q_{2n}   = (N − n) Q_{2n+1} + n Q_{2n−1},
    y Q_{2n−1} = (1 − p) Q_{2n}   + p Q_{2n−2},

notes K_n(y²) = Q_{2n}(y) and that Q_n has property (P) for p ≤ 1/2, and ends: “The problem is to find a general criterion that would handle this case.” The original version of this mission covered only the Krawtchouk sentence; criterion 6 below was added on 2026-10-19 to cover the Q_n sentence.

## Acceptance criteria

1. State explicit, checkable structural hypotheses on the recurrence coefficients. Checking them must not require computing the linearization coefficients or verifying an equivalent collection of product-positivity inequalities.
2. Deduce nonnegative linearization from those hypotheses for the entire stated class. Interpret products on the finite orthogonality support, including products whose degree sum exceeds the terminal degree.
3. Cover Krawtchouk systems for every size and the full parameter range with property (P), with normalization and parameter conventions stated explicitly.
4. Exhibit a meaningful additional class of finite orthogonal systems satisfying the same hypotheses. The hypotheses must not effectively characterize only Krawtchouk systems.
5. Supply a paper proof, check the terminating boundary and all parameter cases in the stated theorem, and independently review the proof and its applications before claiming a solution.
6. Cover Szwarc’s symmetric system Q_n for every N and every 0 < p ≤ 1/2 by the same kind of checkable recurrence hypotheses, with sharpness at p > 1/2.

## Discovery methods and exclusions

Explicit formulas, exact computations, and known Krawtchouk product expansions may be used to discover and test the proof mechanism. The final theorem must establish positivity for its whole class from the recurrence assumptions without requiring explicit computation of the linearization coefficients.

A product formula only for Krawtchouk, a reformulation of positivity as equally difficult matrix inequalities, or numerical checks alone do not satisfy the mission. A symmetric-only result is intermediate progress, not a replacement for coverage of the full positive Krawtchouk range.

## Status (2026-10-22)

Section numbers refer to paper.tex. No §7 result is independently reviewed, so criterion 5 is unmet for §7. Lean (2026-10-22): Theorem 7.10 (`Szkraw.low_products`, including the two-of-three consequence), Corollary 7.11 (`Szkraw.convex_low`, `Szkraw.geometric_convex`), Theorem 7.12 (`Szkraw.all_products`), Corollary 7.13 (`Szkraw.heavy_top`), Lemma 7.14 (`Szkraw.reversal_identity`), Theorem 7.15 (`Szkraw.deep_formula`, `top_expansion`, `deep_reduction`), Theorem 7.16 (`Szkraw.palindromic`) and Corollary 7.17 (`Szkraw.palin_mono`, `palin_mono_kraw`) are machine-verified, axiom audit clean. Not yet formalized: Theorems 7.1, 7.6, 7.8, Corollaries 7.7, 7.9, Lemmas 7.2–7.5.

- Criteria 1–4 are met by §§2–6 in their exact (geometric) and perturbative forms: Theorems 2.1 and 5.3, Corollaries 6.1 and 6.2, Lean-checked and AI-reviewed.
- Criterion 6 is met in equality form by Theorem 7.1 (graded algebra; all N, all p ≤ 1/2; sharp) and Corollary 7.9 (parity-split criterion: constant odd downward coefficients p ≤ 1/2 and geometric even increments; q = 1 is Q_n). Theorem 7.6 adds explicit symmetric neighbourhoods for p < 1/2.
- Toward inequality-type (Szwarc 3.2/3.3-style) hypotheses:
  - Theorem 7.10: Szwarc’s inequalities, with no condition on the terminal coefficients, give g(n,m;k) ≥ 0 whenever two of the three indices sum to at most N, for every finite system.
  - Theorems 7.15–7.16 and Corollary 7.17: a deep-triple reduction through the reversed system; palindromic systems satisfying Theorem 7.10’s inequalities have (P). This covers symmetric Krawtchouk (r = 1) by inequalities alone.
  - Theorem 7.8: any symmetric system has (P) when its two quadratic components do, so Q_n at p = 1/2 is covered by inequalities.
- Deep triples, status 2026-10-22: settled by inequalities on the profile for constant-ratio arrays (Theorem 8.1 of paper.tex: b_i/c_i constant and Newton coefficients of d_i = b_i + c_i nonnegative and log-concave without internal zeros imply nonnegative linearization for every N and every product; AI-reviewed, PASS, by the same system that proposed its key steps; machine-verified in Lean 2026-10-22 as `Szkraw.logconcave_criterion` (finite realization and nonnegative linearization), axiom audit clean; the remark after its proof, on two-parameter and Bernstein coefficients, is not formalized). This covers asymmetric Krawtchouk (r < 1) and, through Theorem 7.8, Q_n with p < 1/2. The fully open version, allowing a varying ratio b_i/c_i, remains open.
- Prior art: Miclo, *On the Markov commutator* (arXiv:1505.02540), Theorem 31, gives inequality conditions for palindromic, strongly convex birth–death chains; it excludes Krawtchouk and Q_n.
