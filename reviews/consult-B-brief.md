# Research consult: Bernstein positivity of linearization coefficients for log-concave Newton profiles

This is a research question, not a review. I want proof ideas, relevant literature, or a counterexample. The background is in the public repository github.com/skypher/szkraw (commit 0a65ce1: paper.tex, RESEARCH.md, lc_certificate.py), but everything needed is below.

## Setup

A finite system on indices 0..N has coefficients a_i, b_i, c_i with
a_0 = 1, b_0 = c_0 = 0, a_N = 0, a_i + b_i + c_i = 1, a_i > 0 (i < N), c_i > 0 (i > 0).
Polynomials: R_{-1} = 0, R_0 = 1, x R_i = a_i R_{i+1} + b_i R_i + c_i R_{i-1} (0 <= i < N). The orthogonality support is the spectrum of the (N+1)x(N+1) tridiagonal matrix J; R_i(1) = 1. Linearization coefficients are defined on the support:
R_m R_n = sum_k g(m,n;k) R_k, and they satisfy g(0,n;k) = [n = k] and, for 0 <= m < N,
a_m g(m+1,n;k) = (b_n - b_m) g(m,n;k) + c_n g(m,n-1;k) + a_n g(m,n+1;k) - c_m g(m-1,n;k)
(terms with an index outside 0..N are zero). Property (P) means all g(m,n;k) >= 0. A triple is *deep* if each two of its indices sum to more than N.

**Constant-ratio class.** Fix a profile 0 = d_0 < d_1 < ... < d_N = 1 and r in [0,1]; set b_i = (1-r) d_i, c_i = r d_i, a_i = 1 - d_i. Krawtchouk is d_n = n/N (for which g(N,N;N) = (1-r)^N). Geometric profiles d_n = (q^n - 1)/(q^N - 1) are dual q-Krawtchouk arrays; (P) is proved for them for all r (equality-type criterion).

**Newton coefficients.** sigma_k = Delta^k d(0), so d_n = sum_k C(n,k) sigma_k. Condition (LC): sigma_k >= 0, log-concave (sigma_k^2 >= sigma_{k-1} sigma_{k+1}), no internal zeros. Parametrization: sigma_1 = 1 (up to scale), sigma_{k+1} = sigma_k rho_k with rho_k = x_k + ... + x_{N-1}, x_i >= 0. Krawtchouk is rho = 0, geometric is rho constant (x_i = 0 for i < N-1). Log-convex sigma (rho nondecreasing) are mixtures of geometric profiles.

## What is known

1. *Proved for N <= 6 (exact, symbolic).* With r = R/(R+W), multiply each recurrence step by (R+W)(D_N - D_m), where D_n = sum_k C(n,k) sigma_k is the unnormalized profile. Then g(m,n;k) = P_{mnk}/Q_m with Q_m = prod_{m' < m} (R+W)(D_N - D_{m'}), and every numerator P_{mnk} is a polynomial with nonnegative integer coefficients in (R, W, x_1, ..., x_{N-1}) for N = 2,...,6. (N = 6: 106 numerators, 91 min.) With log-convex sigma (rho nondecreasing in place of nonincreasing) negative coefficients appear from N = 4, only on deep triples.
2. *Non-deep triples, all N.* For every convex profile (nondecreasing increments; implied by sigma >= 0) and every r, g(m,n;k) >= 0 whenever two indices sum to at most N. (Szwarc's maximum-principle argument, Theorems 3.2/3.4 of Szwarc's *Orthogonal polynomials and Banach algebras*, adapted to finite systems.)
3. *Polynomial in r.* For a fixed profile, g(m,n;k) is a polynomial in r of degree <= m. The N <= 6 certificate says more than (P): the numerators are homogeneous in (R, W), so g(m,n;k) has nonnegative Bernstein coefficients of degree m in r.
4. *Lemma (all N).* d/dr g(N,N;N) at r = 0 equals -1/a_{N-1}, so the first two Bernstein coefficients of the corner satisfy beta_1/beta_0 = 1 - 1/(N a_{N-1}). Proof: R_N(J) is the unique matrix commuting with J whose row 0 is e_N^T. At r = 0, J is upper bidiagonal and R_N(J_0) = 1 e_N^T. Differentiate TJ = JT, take row N and use row sums.
5. *Corner at N = 4, 5, generic profile* (a_n = 1 - d_n). N = 4: g(4,4;4) = sum_j C(4,j) beta_j r^j (1-r)^{4-j} / (a_1^2 a_2^2 a_3) with beta_0 = a_1^2 a_2^2 a_3, beta_1/beta_0 = 1 - 1/(4a_3), beta_3 = beta_4/2 = a_1 a_2 (2a_1a_2a_3 - a_1a_2 + d_3(a_2 - a_3))/2, and beta_2 = a_1a_2(Y + a_1a_2(4a_3 - 1))/6 with Y = 2a_1a_2a_3 - a_1a_2 + d_3(a_2 - a_3). N = 5: beta_3 = beta_4 = a_1^2 a_2^3 a_3^2 Z/5 with Z = 5a_1a_2a_3a_4 - 2a_1a_2a_3 + d_4(a_3 - a_4)(a_1 + a_2 - a_4), beta_5 = 0. In Newton variables, the top quantity (Y, resp. Z) is the only place where log-concavity enters at these N.

## Evidence for all N

Conjecture (B): for every N and every profile with (LC), every g(m,n;k) has nonnegative Bernstein coefficients of degree m in r. (B) implies (P) for the whole constant-ratio LC class.

- Exact rational full tables, all triples: N = 6, 8, 10 (geometric, truncated geometric sigma_k = x^{k-1} for k <= K with K = 2, 3, N/2, two-level quotients; x in {1/10, 1, 9}) and N = 16, 20, 24, 30 (the same plus random nonincreasing quotients). No negative Bernstein coefficient on any triple.
- Earlier, for (P) itself: 750 exact tables (N <= 12), 544 high-precision full tables (N = 16-30), 680 corners (N = 50-400), no failure.
- Controls. Segment profiles d = (1-l) n/N + l (10^n - 1)/(10^N - 1) are log-convex in Newton coefficients. At l = 1/20 they have 7, 18, 37 triples with negative Bernstein coefficients at N = 6, 8, 10, all deep, and at fixed small r they violate (P) at g(N,N;N) for large N (over a searched segment family, the first failing N is 19, 50, 114 for r = 1/2, 2/5, 1/3). Non-deep triples keep nonnegative Bernstein coefficients even for them. Their corner at N = 19 has negative middle Bernstein coefficients, so the small-N structure of item 5 does not persist for general convex profiles.
- A non-constant-ratio extension (log-concave Newton coefficients for both d and c, with b nondecreasing) is false: at N = 3, d = (0,25,55,91)/91 and c = (0,24,54,90)/91 give g(3,3;3) = -3/2002.

## Questions

1. Is there a proof mechanism for (B) for all N? Candidates I see:
   (a) a probabilistic model: g(m,n;k) = E[w(J)], with J ~ Binomial(m, r) counting "down" steps and weights w >= 0 depending only on the profile (Krawtchouk corner: w = delta_0);
   (b) a coefficientwise (in R, W) version of Szwarc's maximum principle for non-deep triples, plus a separate argument for deep triples (the paper has a reversal identity R_N R'_t = R_{N-t} on the support, where R' is the reversed system, and the deep reduction g(x,y;z) = sum_t g'(N-x,N-y;t) g(N,N-t;z));
   (c) total positivity or Polya-frequency arguments in which log-concavity of sigma is the natural PF_2 condition;
   (d) known positivity results for q-Krawtchouk, quantum Krawtchouk or affine q-Krawtchouk linearization (Rahman, Gasper, Koornwinder, Stanton) or hypergroup results for birth-death chains, which could cover the geometric case in Bernstein form and extend.
   Please say which you consider most promising and sketch the key step.
2. Is (B) known, or a known special case of something (for instance positivity of connection or linearization coefficients in two variables)?
3. Do you see a reason (B) should fail at larger N, or a family where it fails while (LC) holds? Please give exact witnesses if you can.
4. If a full proof is out of reach, what is the cleanest provable statement for deep triples, for example the corner g(N,N;N) alone?

Please be concrete. Partial results with proofs are more useful than general remarks.
