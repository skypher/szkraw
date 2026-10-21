## Overall verdict: **PASS WITH MINOR FIXES**

The substantive mathematical repairs are successful. I find no remaining substantive defect in the numbered results of Sections 7 and 8. The remaining corrections concern quantifiers, overstatements in the computational discussion and Section 9, and a few normalization or documentation details.

**The author’s objection to the fixed-\(N\) argument is not correct as an objection to the argument actually proposed:** removing mass only at \(+1\) is different from removing equal masses at both endpoints. The restriction to \(N\leq10\) is nevertheless a valid, conservative repair.

### Disposition of the defects in the first report

| Original defect | Status | Reason |
|---|---|---|
| Lemma 7.4: wording about every monomial coefficient having the stated lower bound | **Fixed** | The bound is now attached to a nonzero term from a chosen reduction. |
| Corollary 7.9: undefined odd-component parametrization for \(N=1\) | **Fixed** | The singleton odd component is separated, and Theorem 7.1 supplies positivity. |
| Theorem 7.10: omitted transposition calculation and undefined \(\alpha_0\) | **Fixed** | The displayed \(H^*v\) formula and \(\alpha_0=0\) convention are correct. |
| Lemma 7.12: reversed initial normalization | **Fixed** | \(R'_1=(x-b_N)/c_N\) is stated; the recurrence and cyclicity argument remain valid. |
| After Corollary 7.9: unrestricted transfer of Lemma 7.5 | **Partly fixed** | The added condition on \(\Sigma\) correctly repairs the transfer. The example still needs \(0<\varepsilon<1/2\), rather than every \(\varepsilon>0\). |
| Lemma 8.2: physical-coordinate/eigenbasis notation collision | **Fixed** | \(\widehat X,\widehat E\) distinguish the eigenbasis coordinates correctly. |
| Definition 8.3: real-valued functions and admission quantifiers | **Fixed** | Both are explicit; the small-\(\varepsilon\) threshold may depend on \(N\). |
| After Theorem 8.4: palindromic example lacks endpoint conditions | **Fixed** | \(\gamma(0)=\gamma(1)=0\), together with oddness about \(1/2\), gives the required endpoint-compatible symmetry. |
| After Theorem 8.4: geometric tangent confused with an admitted straight ray | **Fixed** | It is now explicitly described as a tangent direction. |
| Lemma 8.5: incomplete contour construction and uniform estimate | **Fixed** | The chosen polygonal region lies inside the analytic domain, and positive separation from the nodes gives the uniform Riemann-sum bound. |
| Description of \(\Omega\) as having corners | **Fixed** | “Nonanalytic boundary points (with vertical tangents)” is correct. |
| Corollary 8.6: exact first-order vanishing asserted for analytic rules | **Fixed** | Only the necessary equalities extend; the exponentially small bound and entire-function counterexample are correct. |
| Proposition 8.7(1): ambiguous fixed-sign hypothesis | **Fixed** | Strict and weak eventual signs are distinguished correctly. |
| Proposition 8.7(2): invalid proof and failure to combine the constant terms | **Fixed** | The displayed \(P_e,P_o\) are correct. Their eventual strict signs contradict part (1) unless both vanish identically. |
| Corollary 8.9: free-coordinate norm and admissibility gap | **Fixed** | The terminal direction has full-array norm one, negative corner derivative, and the required admissibility bounds. The exclusion \(N=1\) is retained. |
| General “disproof of inequality criteria” exceeds the proved scope | **Partly fixed** | Section 8’s opening is corrected. The introduction should retain the analytic-domain qualification, and Section 9 still overstates the certificate experiments. |
| After Corollary 7.15: “inequalities alone” despite symmetry equalities | **Fixed** | The claim is now explicitly within the symmetric palindromic subclass. |
| Final Section 7 paragraph: increasing-top-diagonal obstruction lacks size qualification | **Fixed** | The condition \(N\geq3\) is correct. |
| Final Section 7 paragraph: diagonal argument incorrectly applied to Szwarc’s array | **Fixed** | The separate reversal calculation and \(N\geq3\) qualification are correct. |
| Blanket assertion that deep positivity occurs “only through cancellation” | **Fixed** | Deleted. |
| Miclo comparison lacks small-size exceptions | **Partly fixed** | Corrected in Section 7, but Section 9 again says the conditions exclude the families without qualification. |
| Universal fixed-\(N\) interior assertion supported only by finite computations | **Fixed** | Restricting the reported computation to \(N\leq10\) is legitimate. I independently verified such directions and both stated perturbation sizes. |
| Period-four sign assertion away from \(r=1\) | **Partly fixed** | The countervalues are correct, but they disprove period four—not periodicity of every possible period. |
| Claimed onset scaling approximately \(5/r^2\) | **Partly fixed** | Removed from Section 8’s mathematical claims, but Section 9 still infers that admissible bias “therefore shrinks with \(N\).” |
| High-precision agreement treated as an exact sign certificate | **Fixed** | The two examples are now properly labelled. The paragraph’s opening blanket description as “exact computations” should also be adjusted. |
| Smooth convexity asserted to imply log-concave increments | **Fixed** | That general implication has been removed. The quadratic examples need explicit endpoint normalization. |
| “Only smooth deformations survived” generalized beyond the searches | **Fixed** | The conclusion is restricted to tested families. The reproducibility statement still needs qualification. |
| Claim that finitely many local inequalities cannot enforce smoothness | **Fixed** | Deleted. |
| Affine change alone claimed to provide the full normalization | **Fixed** | Positive degree-wise normalization at the largest support point is now included. |

## Remaining and newly noticed corrections

### 1. After Corollary 7.9: restrict the perturbation parameter

The transfer through Lemma 7.5 is now correct. Its illustrative example is not correct for “every \(\varepsilon>0\)”: at \(\varepsilon=1/2\) the recurrence degenerates, and beyond that point it violates the basic assumptions.

**Replace the example sentence by:**

> Lemma 7.5 controls only \(\Sigma\): for example, starting from \(K_{2,1}\), keeping \(b\equiv0\) and \(c_2=1\), and setting \(c_1=\tfrac12+\varepsilon\), \(a_1=\tfrac12-\varepsilon\), with \(0<\varepsilon<\tfrac12\), gives
> \[
> g(2,2;2)=-\frac{2\varepsilon}{1/2-\varepsilon}<0,
> \]
> although the coefficients positive at the reference remain positive.

Thus the author’s decision to retain the Lemma 7.5 transfer **is justified**, subject to this parameter-range correction.

### 2. Section 8, “Computations away from \(r=1\),” first bullet: distinguish failure of period four from nonperiodicity

The two quoted values establish only that the signs do not always repeat after four indices. They do not prove nonperiodicity for every possible period. Similarly, the two tested biases do not establish a result for every fixed \(r\in(1/2,1)\).

**Replace that bullet by:**

> For the rule \(\beta=1,\gamma=0\), exact computation shows that property (P) fails at \(r=4/5\), with perturbation size \(1/100\), for every \(N=6,\ldots,14\), and at \(r=19/20\), with perturbation size \(1/1000\), for every \(N=4,\ldots,14\). The period-four sign pattern at \(r=1\) does not persist in general for \(r<1\): at \(r=4/5\), the first-order derivatives are \(512/1875\) for \(N=4\) and \(-71936/5859375\) for \(N=8\).

I independently obtained both fractions exactly.

### 3. Introduction and Section 9: preserve the analytic-domain restriction

The formal Corollary 8.6 is correctly restricted. The informal references should not broaden it to arbitrary real-analytic rules or functions analytic merely near \([0,1]\).

**In the final introduction paragraph, replace “uniformly sampled polynomial or analytic deformations” by:**

> uniformly sampled polynomial deformation rules, and analytic rules whose defining functions extend holomorphically to an open neighborhood of the region \(\Omega\) specified in Section 8

**In Section 9, “Monotonicity-type criteria,” replace the corresponding sentence by:**

> Section 8 explains part of this: admission at the symmetric endpoint imposes two first-order boundary equalities for the polynomial rules of Theorem 8.4 and the analytic rules of Corollary 8.6.

### 4. Section 9, “Monotonicity-type criteria”: restore Miclo’s small-size exceptions

The sentence “Those conditions exclude the Krawtchouk recurrence and the system…” repeats the original overstatement.

Miclo’s Theorem 31 uses reflection invariance and condition (H). For symmetric Krawtchouk, \(2^na_n\) satisfies the required condition at \(N=1,2\); the first increase occurs when \(N>2\). [1]

**Replace that sentence by:**

> These conditions do not cover the full Krawtchouk or Szwarc families. For symmetric Krawtchouk they fail when \(N>2\), but the cases \(N=1,2\) are covered. The Szwarc instance \(N=1,p_0=1/2\) is the same covered three-point system.

### 5. Section 9: remove the remaining unsupported size-scaling inference

The sentence beginning “The admissible bias for such profiles therefore shrinks with \(N\)” does not follow from the preceding examples. Different profiles at selected sizes do not establish monotonicity, a threshold, or an asymptotic law.

**Replace it by:**

> These examples show that the stated shape restrictions do not guarantee positivity at the specified biases and sizes. Each failure is witnessed by a negative terminal coefficient \(g(N,N;N)\).

### 6. Section 9, final certificate discussion: numerical feasibility is not an exact certificate or a general impossibility theorem

The repository’s certificate routine converts coefficients to floating point and returns the linear-programming solver’s status. It does not reconstruct exact feasible weights or exact infeasibility certificates. Moreover, some triples do admit a common weight at the two biases; failure for other triples does not exclude every family of linear-inequality criteria. [2][3]

**Replace the passage from “For each Krawtchouk array tested…” through the end of that paragraph by:**

> Floating-point linear-programming searches returned feasible backward-cone certificates for every deep triple in the tested Krawtchouk arrays. For some triples, the joint search for one coefficient-independent weight at \(r=1/5\) and \(r=1/2\) was reported infeasible. These numerical findings concern the specified certificate construction; no exact infeasibility certificates or general exclusion of linear-inequality criteria are supplied. Checkerboard-restricted searches did not certify all deep triples at the tested \(r<1\). The exact marching calculations also produced examples with negative boundary flux. On the tested random perturbed arrays, the solver’s certificate-feasibility results agreed with property (P).

This also avoids the imprecise assertion that the canonical weight satisfies \(H^*v=0\) everywhere in the deep region: its apex has the nonzero normalization needed to isolate the target coefficient.

### 7. Section 8 computational discussion: normalize the quadratic profiles and qualify reproducibility

The profile convention requires \(d(1)=1\). The literal expression \(x+\kappa x^2\) violates that convention unless \(\kappa=0\).

**At both occurrences, replace “quadratic profiles \(x+\kappa x^2\)” by:**

> normalized quadratic profiles
> \[
> d_\kappa(x)=\frac{x+\kappa x^2}{1+\kappa},\qquad \kappa\geq0
> \]

The two named scripts reproduce the explicit fixed-size failures and listed kink/log-concave examples, but they do not reproduce every unspecified concave-profile search or the full smooth-ratio search claimed in the paragraph. [4][5]

**Replace the computational paragraph’s opening by:**

> The explicit fixed-size, one-kink, and log-concave-increment examples below are reproduced by `rigidity_probe.py` and `smallr_probe.py`. Exact rational computations certify the stated finite examples; the separately labelled high-precision calculations provide numerical evidence. No asymptotic conclusion is asserted.

For the other search reports, supply the tested parameter sets and reproduction procedure, or delete them. A self-contained replacement for the final summary paragraph is:

> The exact examples above disprove the stated shape conditions at the listed parameters and sizes. The two larger high-precision examples provide additional numerical evidence. These findings establish neither minimal failure sizes nor general conclusions about smooth deformations.

### 8. Two small wording clarifications

**After Proposition 8.7**, “The boundary layers must be palindromic to first order” should distinguish the interior layers from the separately adjusted terminal coordinate.

Replace it by:

> For \(k\geq1\), the boundary-layer contributions satisfy the palindromic first-order relations \(\delta b_k=\delta b_{N-k}\) and \(\delta a_k=\delta c_{N-k}\). The separate terminal adjustment need not itself be palindromic.

**In Corollary 8.9’s proof**, “The array is admissible for Theorem 5.3 and lacks property (P)” can misleadingly suggest that it satisfies all hypotheses of that theorem, including its radius bound.

Replace it by:

> The array satisfies the basic conditions and \(\widetilde b_i\geq0\), lies at full-array distance \(\varepsilon=C(1-r)^N\) from \(K_{N,r}\), and lacks property (P). Hence \(\rho_N(r)\leq C(1-r)^N\).

## The disputed fixed-\(N\) argument

The author’s observation is correct **for the symmetric perturbation**
\[
\mu_t=\mu_0-t(\delta_{-1}+\delta_1).
\]
That perturbation preserves \(b\equiv0\), so all odd-parity coefficients remain zero. Adding the Krawtchouk direction does not give a strictly positive derivative at odd-perimeter zeros whose excess is at least three.

But the proposed fixed-\(N\) repair used the **one-endpoint perturbation**
\[
\mu_t=\mu_0-t\delta_1.
\]
This does not preserve symmetry.

Here is the missing distinction explicitly. Let \(P_j^t(1)=1\) be the endpoint-normalized orthogonal polynomials for this measure, with \(P_j^0=R_j\). Differentiating orthogonality gives
\[
\dot P_j=\sum_{h<j}\binom Nh(R_h-R_j).
\]
At a perimeter zero \(m+n+k>2N\), the binary subset model implies that every term in \(R_mR_n\) has degree at most \(2N-m-n<k\). Consequently,
\[
\int \dot P_kR_mR_n\,d\mu_0=1,
\]
and the analogous two terms also equal one. Therefore
\[
\left.\frac d{dt}\int P_m^tP_n^tP_k^t\,d\mu_t\right|_{t=0}
=-1+1+1+1=2,
\]
so
\[
\dot g(m,n;k)=2\binom Nk>0.
\]
In particular, **\(\dot g(N,N;N)=2\), including odd \(N\)**.

An affine normalization restoring \(R_1=x\) leaves the linearization coefficients unchanged. The resulting direction is not symmetric; explicitly,
\[
\delta b_n=1+\left(\frac{2n}{N}-1\right)\binom Nn,
\qquad
\delta c_n=-\frac nN\left(1+\binom Nn\right).
\]

The Krawtchouk direction has positive derivative at every remaining odd-parity zero inside the perimeter bound and nonnegative derivative at all reference zeros. A sufficiently large positive multiple therefore completes the strict direction, exactly as proposed in the first report.

Thus **the objection rejects a different, symmetric construction—not the one-endpoint argument**. The manuscript may still retain its finite-size-only statement; that statement is correct without adopting this proof.

## Independent checks

My independent exact recurrence implementation confirms the four requested Szwarc reversal evaluations, both quoted derivatives at \(r=4/5\), the corner gradient through \(N=20\), all listed rational counterexamples, and strict first-order directions for every \(1\leq N\leq10\), with property (P) at both stated perturbation sizes. Separate 80- and 150-digit calculations also agree on the two larger examples; they remain numerical evidence rather than exact certificates.

[Independent exact-check script](sandbox:/mnt/data/followup_referee_checks.py)

The linked Szwarc survey PDF remained inaccessible, so its historical transcription is not independently certified here. That limitation does not affect the recurrence calculations or proof checks above.

Sources:
[1] https://arxiv.org/pdf/1505.02540 — https://arxiv.org/pdf/1505.02540
[2] https://raw.githubusercontent.com/skypher/szkraw/4381af5ae43b4b94f62dd49dd8c98f9e4067142c/deep_certificates.py
[3] https://raw.githubusercontent.com/skypher/szkraw/4381af5ae43b4b94f62dd49dd8c98f9e4067142c/RESEARCH.md
[4] https://raw.githubusercontent.com/skypher/szkraw/4381af5ae43b4b94f62dd49dd8c98f9e4067142c/rigidity_probe.py
[5] https://raw.githubusercontent.com/skypher/szkraw/4381af5ae43b4b94f62dd49dd8c98f9e4067142c/smallr_probe.py

