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

## Status (2026-10-19)

Section numbers refer to paper.tex. Nothing in §7 is Lean-formalized or independently reviewed, so criterion 5 is unmet for §7.

- Criteria 1–4 are met by §§2–6 in their exact (geometric) and perturbative forms: Theorems 2.1 and 5.3, Corollaries 6.1 and 6.2, Lean-checked and AI-reviewed.
- Criterion 6 is met in equality form by Theorem 7.1 (graded algebra; all N, all p ≤ 1/2; sharp) and Corollary 7.9 (parity-split criterion: constant odd downward coefficients p ≤ 1/2 and geometric even increments; q = 1 is Q_n). Theorem 7.6 adds explicit symmetric neighbourhoods for p < 1/2.
- Toward inequality-type (Szwarc 3.2/3.3-style) hypotheses:
  - Theorem 7.10: Szwarc’s inequalities, with no condition on the terminal coefficients, give g(n,m;k) ≥ 0 whenever two of the three indices sum to at most N, for every finite system.
  - Theorems 7.13–7.14 and Corollary 7.15: a deep-triple reduction through the reversed system; palindromic systems satisfying Theorem 7.10’s inequalities have (P). This covers symmetric Krawtchouk (r = 1) by inequalities alone.
  - Theorem 7.8: any symmetric system has (P) when its two quadratic components do, so Q_n at p = 1/2 is covered by inequalities.
- Open: an inequality-type criterion for the deep triples (all pairwise index sums > N) of systems whose diagonal increases at the top, which includes asymmetric Krawtchouk (r < 1) and Q_n with p < 1/2. Recorded obstructions: the reversal route fails whenever b_{N−1} < b_N; product-weight (checkerboard) certificates reach at most 22 of 110 deep points for Krawtchouk at N = 8, and general lightcone certificates exist but must depend nonlinearly on the coefficients and are, on all tested arrays, equivalent to (P) itself (RESEARCH.md, deep_certificates.py); tilted reversal is vacuous and site-dependent tower generators destroy finiteness; convex and log-convex profiles have exact counterexamples at g(N,N;N). These systems are currently covered only by the equality-type criteria and perturbation neighbourhoods above.
- Prior art: Miclo, *On the Markov commutator* (arXiv:1505.02540), Theorem 31, gives inequality conditions for palindromic, strongly convex birth–death chains; it excludes Krawtchouk and Q_n.
