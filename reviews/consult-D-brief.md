# Research consult, round 2: proving lemma (D) for log-concave Newton profiles

Thank you for round 1 (your answer is at github.com/skypher/szkraw, reviews/consult-B-answer.md, commit 2b7de8a). I checked your claims independently in exact arithmetic: the (u,v) homogeneity, the identity g = Σ_j Γ_j r^j (1−r)^{s−2j} against a direct linearization code, and your control Γ_{444,2} = −809/172081. Below are my results since then and a focused question.

## Notation (as in your answer)

Profile 0 = d_0 < … < d_N = 1, a_i = 1 − d_i; x P_i = a_i P_{i+1} + u d_i P_i + v d_i P_{i−1}; H_{mn}^k(t) = H_{mn}^k(t, 1). Recurrence:
a_m H_{m+1,n} = t(d_n − d_m) H_{mn} + a_n H_{m,n+1} + D_{mn},  D_{mn}^k = d_n H_{m,n−1}^k − d_m H_{m−1,n}^k.
(LC): Newton coefficients σ_k = Δ^k d(0) nonnegative, log-concave, no internal zeros; equivalently σ_{k+1}/σ_k = ρ_k = x_k + … + x_{N−1} with x ≥ 0 (an orthant; the extreme rays are the truncated geometric profiles σ_k = ε^{k−1} for k ≤ K, 0 after).

## New results

1. **Evidence for (D) and (Γ)** (exact rational arithmetic, all triples):
   - 990 grid LC profiles at N = 3–5 (quotients in {0, 1/100, 1/10, 1/3, 1/2, 1, 2, 5, 20, 1000});
   - 205 boundary and random LC profiles at N = 6–14;
   - all extreme rays K = 2..N at ε = 10^{−12} and 10^{−4} for N = 4–16, which tests the first-order behaviour near Krawtchouk;
   - no failure anywhere. On convex non-LC controls, (D) fails only on deep triples.
2. **A recursion for D.** From the H recurrence at m − 1,
   a_{m−1} D_{m,n} = t d_n (d_{n−1} − d_{m−1}) H_{m−1,n−1} + (φ(n) − φ(m)) H_{m−1,n} + d_n D_{m−1,n−1},  with φ(n) = d_n a_{n−1},
   and D_{1,n}^k = (φ(n) − φ(1)) δ_{kn} + t d_n d_{n−1} δ_{k,n−1} + d_n d_{n−1} δ_{k,n−2}. Iterating down the diagonal, D is a nonnegative combination of t-terms t·H_{m−1−j,n−1−j} and of the terms (φ(n−j) − φ(m−j)) H_{m−1−j,n−j}. Consequences:
   - If φ is nondecreasing on 1..N, then (D), (Γ) and (P) hold for all r. This is an inequality criterion, close to "last increment ≥ 1/2", and it excludes Krawtchouk.
   - For Krawtchouk, φ(n) − φ(m) = (n − m)(N + 1 − n − m)/N² is negative exactly when n + m > N + 1. At N = 8 the negative φ-terms sit only on deep triples (20 of them; 6 for geometric ε = 1/5, none for ε = 3).
   - The naive strengthening D_{m,n} ≥ θ_{m,n} H_{m,n+1}, with θ_{m,n} = max(0, φ(m+1) − φ(n+1))/d_{n+1} chosen to absorb the next negative φ-term, is false at most of the triples where it is needed. The t-term is essential.
3. **(D) for Krawtchouk, all triples (proved).** In the commutative algebra y_i² = u y_i + v (i = 1..N), with E_k elementary symmetric and P_k = E_k/C(N,k),
   N C(N,m) C(N,n) (d_n P_m P_{n−1} − d_m P_{m−1} P_n) = (N−n+1) E_m E_{n−1} − (N−m+1) E_{m−1} E_n.
   Take sets |S| = m, |T| = n with overlap A, |A| = s, and squarefree part M, |M| = L = m + n − 2s − 1. Before reduction, the coefficient of y_A² y_M is (N − s − L)[C(L, m−s) − C(L, m−s−1)] ≥ 0 (a ballot inequality, m ≤ n), and reducing y_A² = Π(u y_i + v) keeps it nonnegative. (Verified against the D tables at N = 5, 6.)
4. Known from before: for constant ratio, an increasing profile with d_{N−1} ≤ 1/2 gives (P) on all triples by the cone identity, whose only negative terms are the left-edge constants 1 − d_i − d_j.

## Question

Prove (D) for all N under (LC), or find an LC profile where it fails. Specific sub-questions:

(a) Is there a strengthened induction hypothesis that closes under the D recursion above? For example, a lower bound for D_{m,n} in terms of H_{m,n+1} and t·H_{m,n} with profile-dependent constants, or a family of Turán-type expressions D^{(j)}_{m,n} = d_{n} ⋯ H_{m−j,n+j−1} − ⋯, whose recursions have nonnegative coefficients exactly under (LC). Log-concavity of σ should enter as a 2×2 minor condition. Where would σ_k² ≥ σ_{k−1}σ_{k+1} appear in a φ-type difference?

(b) Can the Krawtchouk ballot proof be transported to LC profiles? For instance: a non-commutative or weighted algebra whose elementary sums reproduce d_k for an LC profile, or a mixture or composition of Krawtchouk algebras of different sizes, or a path model in which LC weights act as transfer matrices with nonnegative 2×2 minors (Lindström–Gessel–Viennot). Note: the algebraic tower construction I tried realizes only geometric profiles.

(c) Failing a proof for all LC profiles, is there an LC subfamily strictly larger than geometric, for example truncated geometric (σ_k = x^{k−1} for k ≤ K, else 0) for all K, or two-level quotients, for which you can prove (D) or (Γ) for all N?

Please give complete arguments for whatever you can prove, and exact witnesses for any counterexample.
