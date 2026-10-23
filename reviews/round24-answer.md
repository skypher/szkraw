# PASS WITH MINOR FIXES

The required inequalities and certificates check. I found no counterexample or missing case invalidating Theorem 8.16.

I reviewed the pinned source and dependencies. Reruns used local transcriptions with path/import adaptations, **not an unmodified Git checkout**. [1]

## Corrections

1. **Setup: specify integer arguments.** Replace “for every \(x\ge0\)” by “for every integer \(x\ge0\),” and describe \((\rho(n))_{n\ge0}\) as a log-concave sequence. Continuous log-concavity is false: coefficients \((1,1,1,0,\ldots)\) give \(\rho(x)=1+x/2+x^2/2\), with \((\log\rho)''(0)=3/4>0\). Also replace “all of these are nonnegative” by an explicit list excluding \(\psi_n\).

2. **Step (vi): qualify the closed-form assertion.** Exclude \(L\) from the blanket formula involving \(\binom{2a-1}W\): \(N_{2a}(L)=a-2>0\), whereas both displayed binomials vanish there. Introduce the certificate rational formulas for \(W\ge4\), treating \(W=3\) separately; the latter includes the \(\Psi\) correction
   \[
   \binom{a-1}{2}(a-1)[W=3],
   \]
   correctly retained in the scripts.

3. **The \(Q_s\) certificate is stronger than the described bound.** Dropping the nonnegative \(G^{(s)}\)-terms and setting \(s=3\) produces a bracket ending in \(2a/3-2\); the script uses \(2a/3-1\). Thus its lower bound is **smaller by \(\binom a{W-1}\)**. This is harmless. Exact fix: state that this additional nonnegative quantity is subtracted before certification. Say the negative terms’ *magnitudes decrease* as \(s\) increases. [2]

4. **Distinguish diagnostics from universal proofs.** `key_weight_closed.py` checks finitely many \(a\); it does not establish the identities for arbitrary \(a\). Add the general coefficient derivation from the generating functions, supplied in the linked audit below. The symbolic polynomial certificates then establish the universal inequalities. [3]

5. **Make the scripts portable and fail on rejection.** Replace `/home/yang/...` paths with paths relative to `Path(__file__).resolve().parent`. Add `assert ok and allsmall and mism == 0` to the weight checker, `assert mism == 0` to the closed-form checker, and require `CERTIFIED` for each nonzero LP target. Currently printed failures need not produce a nonzero exit status. This does not invalidate the successful results observed. [2]

## Independent mathematical checks

**Lemma and setup — pass.** The Abel argument remains valid with boundary zeros. Truncation preserves log-concavity without internal zeros; integer shifts preserve it; both inequalities (8.7), the Leibniz expansion, and the application of Proposition 8.14 check. No division by a possibly zero \(P_k\) is needed.

**Detours and resummation — pass.** Independently collecting the three pairings gives
\[
\theta_{n,2}=\frac{n(n-1)}{(n+1)(n+2)},\qquad
\theta_{n,i}=\frac{(n+2-i)(n+1+i)}{(n+1)(n+2)}
\quad(3\le i\le n),
\]
with \(\theta_{n,n+1}=2/(n+2)\) and \(\theta_{n,n+2}=1\).
The \(V\) pointwise factor \(n/(n+2)\), quotient \(\ge6\), and every \(\widehat W\) quotient \(>2\) check. In particular, the potentially overlooked target \(i=m\) has quotient \(\ge10\). The \(H,C',B\) arguments carry over. With \(\mu_V=6,\mu_W=2,\gamma_V=2\), the surviving \(V_1\) coefficient is \(2/3-1/2=1/6\), as required.

**Key algebra and (i)–(ii) — pass.** All \(\beta,\beta',\chi,\chi',\delta,\zeta,\nu,l_k\), the three \(E\)'s, and \(M_{k,m}\) agree with direct expansion. All four inequalities (8.9) check. A particularly transparent version of reduction (i) is
\[
\mathrm{Key}
=\left(1-\frac{\Delta c}{F}\right)\mathrm{Lin}+\frac{\Phi}{F}\ge0.
\]
The central-sum criterion correctly handles the nonsymmetric \(M\): off-diagonal polynomial coefficients are \(M_{k,m}+M_{m,k}\), with no diagonal factor-of-two error.

**Affine reduction (iii) — pass.** Explicitly,
\[
\alpha=tB/F=tR_{\ell+a-1}\ge tu_0/u_1,
\]
and
\[
\beta_1-Y=(a-1)X,\qquad
\beta'_1-Y'=(a-1)(A-d_{\ell+2})\ge0.
\]
Both \(A^\psi_0\) weights are nonnegative. Only the local inequality proved in Theorem 8.9 is needed—not global admissibility of the scaled affine ratio. Taking \(P_0=0\), then letting \(P_0\) vary, establishes \(M_{1,1}\ge0\) and \(M_{0,1}\ge0\).

**Steps (iii′)–(v) — pass.** Both \(M_{0,s}\) identities and the \(S_{2,0}\) identity are exact. The two brackets in (iii′) are bounded below by
\[
\tfrac12c'_mBR,\qquad \tfrac12c'_mAR_2.
\]
Every subsequent inequality has the correct direction. In particular, replacing \(u_1B\) by \(u_0F\) requires exactly the asserted \(K''\ge0\) or \(K_a\ge0\); dividing by \(u_1\) is legitimate because the profile is strictly increasing.

**Weight sums — pass universally, not merely experimentally.** Every listed form satisfies Lemma 8.15’s coefficient-sign hypotheses. Independent derivation gives
\[
G^{(s)}
=\sum_{n=3}^{a}(n-2)\binom an\binom ns r^n,
\]
hence exactly the stated closed form, including the \(+[s=1]ar\) correction, \(r\nu_s=sG^{(s)}\), and \(Z_s=\binom asH_*-G^{(s)}\). The \(Q_s\) bound, its special \(W=3\) formula, and the comparison for \(L\) check.

For \(W\ge6\), all seven Vandermonde indices are distinct. After substitution, every denominator is a positive constant times a product of \(x+1,x+2,y+6\), optionally \(x+y+5\); none vanishes at the boundary. All seven numerator certificates pass. The small-weight shifted-polynomial checks prove the asserted ranges \(a\ge a_0\). The degree argument for \(W\ge a+2\) and the direct \(W\le2\) checks complete coverage.

## Exact reruns

| Window \(a\) | Certified central-sum targets | Certified \(l_k\) |
|---:|---:|---:|
| 3 | 9 | 4 |
| 4 | 14 | 5 |
| 5 | 20 | 6 |

The LP solver supplies only candidate support. Acceptance requires a nonnegative **rational** solution reproducing every coefficient exactly; floating-point error cannot create a false accepted certificate. [4]

The loops cover every required anti-diagonal and central tail. Skipped out-of-support tails duplicate already checked sums; zero targets need no certificate. All \(k=0,\ldots,a\) are covered. I reran \(a=3,4,5\), not the unnecessary advertised extension through \(10\). [5]

Also passed: all seven universal polynomial certificates, all 20 small-weight checks, both closed-form diagnostics with zero mismatches, independent symbolic key/decomposition checks through \(a=8\), and 3,248 independent weight comparisons.

**Boundary cases — pass.** Windows \(\ell+a=N\) use no \(d_{N+1}\); the finite move/resummation framework applies. When \(P_1=0\), log-concavity and \(P_0>0\) force \(P_k=0\) for \(k\ge1\), giving \(\mathrm{Key}=P_0(1-P_0)K\ge0\). Other zero \(P_k\), and windows \(a\le2\), cause no gap.

## Literature

**The Abel/central-sum technique is known.** Add Wang–Yeh, *Log-concavity and LC-positivity*, JCTA **114** (2007), 195–210: Lemma 2.1, the subsequent equal-weight quadratic argument, and Corollary 2.6 give the substance of Lemma 8.15 and its single-sign-change criterion. [6]

Earlier recurrence/discrete-hyperbolic methods include Szwarc (2003). I located **no matching prior statement of Theorem 8.16 or its specific key inequality and constants**; that is not a guarantee of novelty. [7]

[Detailed coefficient derivations, corrections, and rerun logs](sandbox:/mnt/data/review24-audit.txt)

Sources:
[1] https://raw.githubusercontent.com/skypher/szkraw/c145f1f/paper.tex — https://raw.githubusercontent.com/skypher/szkraw/c145f1f/paper.tex
[2] https://raw.githubusercontent.com/skypher/szkraw/c145f1f/runs/varratio/key_weight_cert.py
[3] https://raw.githubusercontent.com/skypher/szkraw/c145f1f/runs/varratio/key_weight_closed.py
[4] https://raw.githubusercontent.com/skypher/szkraw/c145f1f/runs/varratio/key_cert_exact.py
[5] https://raw.githubusercontent.com/skypher/szkraw/c145f1f/runs/varratio/key_phi_ustep.py
[6] Log-concavity and LC-positivity — https://arxiv.org/abs/math/0504164
[7] https://scispace.com/pdf/a-necessary-and-sufficient-condition-for-nonnegative-product-d6zy3q5vuz.pdf

