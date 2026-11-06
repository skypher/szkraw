# Do the P1/P2 criteria cover the other finite classical families?

Question (2026-11-06, after the SIGMA desk rejection of P1): does any criterion
of P1 or P2 give property (P) for Hahn-type families, which would answer
"several of its applications recover previously known positivity results"?

Answer: no.

Method. `families.py` builds each family from its (basic) hypergeometric
definition (Koekoek-Lesky-Swarttouw), fits the three-term recurrence on the
grid and verifies it exactly at every grid point, then normalizes at either
endpoint of the support (row sums one, R_i(1) = 1). `criteria.py` computes
property (P) exactly (all g(m,n;k) = [R_m(J)]_{n,k}) and tests the hypotheses
of P1 Theorem 3.1 and of P2 Theorems A (log-concave ratio), quadratic ratio,
Corollary cubic 7/4, varying ratio, quadratic arrays and low-degree profiles.
For the ratio criteria the free value rho(0) is searched. `sanity.py`
reproduces the Krawtchouk picture (P at the end where r <= 1, failure at the
other end, all criteria true there). Runs: `scan.py <family> 3,4,5,6` and
`scan_neg.py` (Hahn and dual Hahn with parameters below -N).

Findings (stochastic arrays only, N = 3..6):

- Hahn, dual Hahn, Racah, q-Hahn, dual q-Hahn, q-Krawtchouk, quantum and
  affine q-Krawtchouk: no array is covered by any P1/P2 criterion, except two
  dual q-Hahn arrays at N = 3 (small-N accident). The dual q-Krawtchouk arrays
  with property (P) are covered by P1 (known, P1 Corollary 3.3).
- Reason: the profile's Newton coefficients have mixed signs (mostly
  alternating, i.e. concave-type profiles) for almost all of these arrays; P1
  and P2 need them nonnegative and log-concave. The exceptions are dual Hahn
  arrays at the endpoint x = 0 with large gamma: profile quadratic and convex,
  but the ratio c_i/d_i = (N+delta+1-i)/(i+gamma+1-N) decreases, while P2
  allows only increasing ratios.
- Property (P) itself holds for many of these arrays: Hahn with alpha >> beta
  (at x = 0) and on the whole branch alpha, beta < -N; most dual Hahn, q-Hahn,
  dual q-Hahn, q-Krawtchouk, quantum and affine q-Krawtchouk configurations
  tried. Covering them needs a new criterion for profiles with mixed-sign
  Newton coefficients, not a corollary of P1/P2.
