## Overall verdict: **PASS WITH MINOR FIXES**

**Proposition 8.12 and Corollary 8.13 have correct statements.** The required fixes concern the proof of the coefficient bound for unrestricted \(\tau\), explicit admissibility and limiting details, and the distinction between a heuristic saddle-point factor and a proved perturbation threshold.

| New item | Verdict | Reason |
|---|---|---|
| Proposition 8.12 | **PASS WITH MINOR FIXES** | Polynomial identity, finite-support kernel, corner formula, threshold, and recurrence formulas are correct. The final normalization estimate needs repair for arbitrary \(\tau>0\). |
| Corollary 8.13 | **PASS WITH MINOR FIXES** | Both upper bounds and the fixed-\(r\) conclusion are correct. Make strict slack, positivity of off-diagonal coefficients, and the limit \(\tau\downarrow\tau_N^*\) explicit. |
| Remark after Corollary 8.13 | **PASS WITH MINOR FIXES** | Exact contour representation and finite counterexample check out. Describe the proposed rate as a candidate oscillatory envelope for \(r>1/2\), not an unqualified decay rate. |
| Section 9, “Sharper stability radii” | **PASS** | Accurately states the new upper bound and remaining gap. |
| Section 9, “Monotonicity-type criteria…” | **PASS WITH MINOR FIXES** | “Gives exponentially small coefficient balls” misdescribes an upper bound; “locates the threshold” overstates the explicitly unproved remark. |
| Other changes to `paper.tex` | **PASS** | The repository history confirms exactly the supplied changes relative to `54c4dca`. |

### Independent mathematical checks

Put \(A_n=1+\varepsilon S_n\), with \(\varepsilon=\tau w_0\). Direct orthogonality gives, **exactly**,
\[
R_n^\tau=A_nR_n-\varepsilon\sum_{j<n}\pi_jR_j,
\qquad
\int(R_n^\tau)^2\,d\mu^\tau=\frac{A_nA_{n+1}}{\pi_n}.
\]
Thus the displayed recurrence formulas follow from leading coefficients and detailed balance, including the initial and terminal rows. There is no missing denominator in the formula for \(R_n^\tau\).

The reproducing-kernel argument is valid **as an identity of functions on the finite support**: polynomials of degree at most \(N\) span all functions there. Consequently,
\[
\sum_{j=0}^{N}\pi_jR_j(x)=\frac{\boldsymbol1_{x=x_0}}{w_0},
\qquad
R_N^\tau=(1+\tau)R_N-\tau\boldsymbol1_{x_0}.
\]
The stated second and third moments, their ratio, and the exact threshold follow. In particular \(h>w_0>I>0\), so there is no denominator-sign issue. As a boundary check, \(N=1\) reduces to
\[
g(1,1;1)=1-r(1+\tau),\qquad \tau_1^*=r^{-1}-1.
\]
Its negativity coincides with a negative normalized diagonal, so this does **not** contradict the two-point exception.

I ran **200 independent exact-rational raised-mass checks**, using discrete Gram–Schmidt rather than the author’s code: \(N=1,\ldots,10\), five rational biases, and \(\tau\in\{1/1000,1/2,2,100\}\). All identities passed, including the stronger normalized bound \(2\tau\max_nw_n\). [Check script](sandbox:/mnt/data/referee_round5/check.py) · [Exact-check output](sandbox:/mnt/data/referee_round5/check.txt)

### 1. Proposition 8.12: required proof repair

**Location:** final paragraph of the proof, beginning “Finally \(b_0^\tau=\cdots\).”

The existing estimate retains a factor \(1+\varepsilon\) but supplies no restriction on \(\varepsilon\); it therefore does not establish the claimed constant \(3\) for every \(\tau>0\). Nor is the affine correction itself always bounded by \(\varepsilon\): for \(N=1,r=1/2,\tau=4\), one has \(c_1^\tau=15/14\), and its affine correction is \(10/7>\varepsilon=4/3\). The **proposition’s bound nevertheless remains true**. This is a proof defect, not a counterexample to its statement. [1]

Replace those final sentences with:

:::writing{variant="document" id="71493" title="Proposition 8.12 — replacement normalization argument"}
Put \(A_n=1+\varepsilon S_n\) and \(t_n=\varepsilon\pi_n=\tau w_n\). Since \(b_0^\tau=\varepsilon/(1+\varepsilon)\), the affine coordinate is \(y=(1+\varepsilon)x-\varepsilon\), and the normalized coefficients are
\[
\widetilde a_n=(1+\varepsilon)a_n^\tau,\qquad
\widetilde b_n=(1+\varepsilon)b_n^\tau-\varepsilon,\qquad
\widetilde c_n=(1+\varepsilon)c_n^\tau.
\]
For \(n\geq1\), we have \(A_n\geq1+\varepsilon\), and
\[
\begin{aligned}
\widetilde a_n-a_n
 &=\varepsilon a_n-(1+\varepsilon)a_nt_n/A_{n+1},\\
\widetilde c_n-c_n
 &=\varepsilon c_n+(1+\varepsilon)c_nt_n/A_n,\\
\widetilde b_n-b_n
 &=-\varepsilon(a_n+c_n)
 +(1+\varepsilon)t_n(a_n/A_{n+1}-c_n/A_n).
\end{aligned}
\]
Because \(a_n,c_n\geq0\) and \(a_n+c_n\leq1\), each absolute change is at most
\(\varepsilon+t_n\leq2\tau\max_jw_j\). Row zero is restored exactly. This proves, in particular, the stated bound \(3\tau\max_jw_j\) for every \(\tau>0\).
:::

### 2. Corollary 8.13: required proof clarification

**Location:** entire proof.

The inequality \(\tau_N^*\leq(1-r^2)^N\) is correct under the stated hypothesis; indeed it is **strict**. That strictness resolves the apparent issue of choosing \(\tau\) above the threshold even when the second smallness condition holds with equality.

The remaining basic conditions should be justified by the **exact positive coefficient formulas**, not by the distance bound alone: when \(r<1/2\), a bound involving \((1-r)/N\) does not by itself protect coefficients of size \(r/N\). The stated corollary needs no additional hypothesis. [2]

Replace the proof body with:

:::writing{variant="document" id="28640" title="Corollary 8.13 — replacement proof"}
Put \(x=(1-r^2)^N\) and \(W=\max_nw_n\). For \(0<x\leq1/2\),
\[
(1+x)^2(1-x)-1=x(1-x-x^2)>0,
\]
so \(\tau_N^*<x\). Choose \(\tau\in(\tau_N^*,x)\). Proposition 8.12 gives a negative corner coefficient and full-array distance at most
\[
3\tau W<3x\leq(1-r)/N.
\]
Thus \(\widetilde b_n>0\) for \(n\geq1\), while \(\widetilde b_0=0\). The exact coefficient formulas and the positive affine scale give \(\widetilde a_n>0\) for \(n<N\), \(\widetilde c_n>0\) for \(n>0\), and all the basic boundary and row-sum equalities. Letting \(\tau\downarrow\tau_N^*\) proves
\[
\rho_N(r)\leq3\tau_N^*W\leq3x.
\]
For each fixed \(r\in(0,1)\), both smallness conditions hold for all sufficiently large \(N\), since \(N(1-r^2)^N\to0\).
:::

### 3. Remark and Section 9: scope corrections

I independently derived the terminal-row contour formula appearing in `fixedr_probe.py`. Exact Laurent integration agrees with independently differentiated recurrence calculations in **84 cases**, \(N=1,\ldots,14\). The eigenvalue assertion \(R_N(x_j)=(-r)^j\) is correct. [3]

The saddle moduli give
\[
Q(r)=\frac{1+r^3}{(1+r)^2}
=\frac{1-r+r^2}{1+r},
\qquad
Q(r)-(1-r)=\frac{r(2r-1)}{1+r}.
\]
Thus the algebraic comparison at \(r=1/2\) is exact. But nonzero endpoint phase values give the competing factor \(1-r\), and oscillatory cancellation prevents treating the saddle factor as an automatic lower bound on the derivative. The companion analysis itself considers the saddle-dominant regime \(r>1/2\). The manuscript’s “not proved here” disclaimer is appropriate; its terminology should preserve that scope. [4]

The finite numerical claim is independently confirmed **at exactly \(10^{-15}\)**: changing only
\[
c_{40}\mapsto \frac45+10^{-15},\qquad
b_{40}\mapsto \frac15-10^{-15}
\]
preserves admissibility and gives \(g(40,40;40)<0\) in exact rational arithmetic. Its ratio to \((1-r)^{40}\) is approximately \(-1.63715914\). [Contour derivation and audit](sandbox:/mnt/data/referee_round5/terminal_audit.md)

The second Section 9 update must distinguish an **upper bound on ball radii** from a construction of positive balls, and must not turn heuristic evidence into an established threshold. [2]

Use these replacements:

:::writing{variant="document" id="93517" title="Remark and Section 9 — replacement passages"}
**Remark after Corollary 8.13: replace the two sentences beginning “A saddle-point analysis” and “This would explain”.**

The formal saddle contributions have exponential factor \((1-r+r^2)/(1+r)\), which exceeds \(1-r\) exactly when \(r>\tfrac12\). For \(r>\tfrac12\) this suggests an oscillatory first-order envelope, not a proved threshold for finite perturbations. No asymptotic estimate or uniform control of the nonlinear remainder is proved here.

**Section 9, “Monotonicity-type criteria for finite systems”: replace the sentence beginning “First, Corollary”.**

First, Corollary 8.13 gives an exponential upper bound on the admissible coefficient-ball radius around \(K_{N,r}\) for every fixed \(r\in(0,1)\), witnessed by raising the top mass. Determine whether analogous upper bounds hold for terminal-row perturbations, and which uniform rules exhibit such thinness, when \(r\in(\tfrac12,1)\); the remark after that corollary gives only heuristic evidence for a transition at \(r=\tfrac12\).
:::

### 4. Change audit

**No additional changes to `paper.tex` were found beyond the supplied diff.** The intervening commit `b17dfca` changes only companion files; `9973c6f` contains precisely the new Section 8 material and the two Section 9 edits. The earlier transition from the previously reviewed version to `54c4dca` changes only the paper’s AI-use disclosure. [5][2][6]

This is a source-content audit, not a claim that the entire repository is unchanged: `README.txt`, `RESEARCH.md`, `fixedr_probe.py`, and `paper.pdf` also changed after `54c4dca`. **I did not independently recompute the supplied SHA-256.**

All replacement passages, with LaTeX labels retained, are collected in [replacements.tex](sandbox:/mnt/data/referee_round5/replacements.tex).

Sources:
[1] https://raw.githubusercontent.com/skypher/szkraw/9973c6f9d176869365eae9f9b1f922f2192f7e23/paper.tex
[2] https://github.com/skypher/szkraw/commit/9973c6f9d176869365eae9f9b1f922f2192f7e23.patch
[3] https://raw.githubusercontent.com/skypher/szkraw/9973c6f9d176869365eae9f9b1f922f2192f7e23/fixedr_probe.py
[4] https://raw.githubusercontent.com/skypher/szkraw/9973c6f9d176869365eae9f9b1f922f2192f7e23/RESEARCH.md
[5] https://github.com/skypher/szkraw/commit/b17dfca.patch
[6] https://github.com/skypher/szkraw/commit/54c4dca.patch

