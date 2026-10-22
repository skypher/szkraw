## Verdict: PASS WITH MINOR FIXES

The proposition’s argument is correct. The only correction is an \(N=1\) qualification in the following paragraph: the paper permits \(N\ge1\), but defines \(\kappa_k=\beta_k=0\) for \(k>N\). Thus its statement \(\kappa_2=2\kappa/N^2\) is literally correct only for \(N\ge2\). This does not affect the positivity conclusion. [1]

### 1. The recurrence is unconditional

Yes—subject to the standing normalization and endpoint assumptions. Its derivation uses Newton interpolation, Vandermonde’s identity, the three-term recurrence, and coefficient extraction. Neither log-concavity nor signs of the Newton coefficients enter.

Likewise, \(\omega_{\ell,a}=0\) for \(\ell+a>N\) follows from the kernel’s bidegree bound and symmetry, independently of positivity. There is no circular invocation of Theorem 8.6. [2][1]

### 2. Higher moves vanish, and the surviving weights are correct

The definition
\[
W_{p,q}(\ell,a)
=\sum_{n\ge p}\binom{n-p+q}{q}\binom an\varphi_n(\ell)
\]
(and its \(\psi\)-analogue) makes this immediate: for \(j\ge1\), \(A^\psi_j\) starts at \(n=2j+1\ge3\), while \(B_j,C_j,C^\psi_j\) start at \(n=2j+2\ge4\). Every summand vanishes. [2]

For \(N\ge2\),
\[
\psi_1(\ell)=\beta_1+\ell\beta_2,\qquad
\psi_2(\ell)=\beta_2,\qquad \varphi_2(\ell)=\kappa_2,
\]
so the three submitted \(j=0\) weights are correct.

**With the source indices substituted**, the recurrence is
\[
\begin{aligned}
c_{\ell+1}\omega_{\ell+1,a}
={}&a_{\ell+a}\omega_{\ell,a}\\
&+(b_{\ell+a+1}-b_\ell)\omega_{\ell,a+1}\\
&+\binom{a+2}{2}\kappa_2\,\omega_{\ell,a+2}\\
&+\binom{a+2}{2}(\kappa_2+\beta_2)\omega_{\ell-1,a+2}.
\end{aligned}
\]
In particular, the incoming A-weight is **\(b_{\ell+a+1}-b_\ell\)**, not \(b_{\ell+a}-b_\ell\). The submitted proof correctly states the weight as a function of its **source**.

### 3. The induction and boundary treatment are valid

For a target \((\ell+1,a)\in\Omega\), every contributing source has first coordinate \(\ell\) or \(\ell-1\). At sources inside \(\Omega\), all four weights are nonnegative under the stated assumptions, and \(c_{\ell+1}>0\).

**Sources outside \(\Omega\) contribute zero**, regardless of their weights, because their \(\omega\)-coefficients vanish independently of the induction. In the reduced recurrence, the B-source \((\ell,a+2)\) can be outside \(\Omega\); its term is then zero. Negative-index terms are omitted.

Starting from \(\omega_{0,a}=\mathbf1_{a=k}\), induction therefore proves \(\omega\ge0\). Expansion of \(S^aZ^\ell=(z+w)^a(zw)^\ell\), followed by the positive \(e_i\)-rescaling, proves \(g\ge0\). No additional boundary hypothesis is needed.

### 4. Linear-profile claims

Directly,
\[
c_n=\left(\frac rN+\frac{\kappa}{N^2}\right)n
       +\frac{2\kappa}{N^2}\binom n2,\qquad
b_n=\frac{(1-r)n}{N}-\frac{\kappa n^2}{N^2}.
\]
Thus, for \(N\ge2\), the asserted Newton coefficients are correct. Moreover,
\[
b_{n+1}-b_n
=\frac{1-r}{N}-\frac{\kappa(2n+1)}{N^2}.
\]
Since \(\kappa\ge0\), the smallest increment occurs at \(n=N-1\), giving exactly
\[
b\text{ nondecreasing}
\iff \kappa\le\frac{(1-r)N}{2N-1}.
\]
This bound also implies \(r+\kappa\le1\), so no separate stochastic-admissibility restriction is missing once monotonicity is imposed. [2]

**Replacement for the first sentence after the proof:**
```latex
With the linear profile $d_n=n/N$ and the ratio
$c_n/d_n=r+\kappa n/N$ ($1\leq n\leq N$, $r>0$,
$\kappa\geq0$), one has $\kappa_2=2\kappa/N^2$ and
$\kappa_2+\beta_2=0$ for $N\geq2$. For $N=1$, property (P)
follows directly from $R_1^2=c_1R_0+b_1R_1$ when $b_1\geq0$.
```
The remainder of the paragraph can stay unchanged.

### 5. Each assumption really cannot be dropped

Here are independently verified exact witnesses. In every row, \(a=1-b-c\), all standing assumptions hold, and the other two proposition hypotheses remain satisfied.

| Dropped hypothesis | \(N\) | \(b\) | \(c\) | Negative coefficient |
|---|---:|---|---|---|
| \(\kappa_2\ge0\) | 2 | \((0,0,\tfrac14)\) | \((0,\tfrac12,\tfrac34)\) | \(g(2,2;2)=-\tfrac18\) |
| \(\kappa_2+\beta_2\ge0\) | 2 | \((0,\tfrac13,\tfrac13)\) | \((0,\tfrac13,\tfrac23)\) | \(g(2,2;2)=-\tfrac13\) |
| \(b\) nondecreasing | 3 | \((0,\tfrac16,\tfrac16,0)\) | \((0,\tfrac16,\tfrac12,1)\) | \(g(3,3;3)=-\tfrac18\) |

Their \((\kappa_2,\kappa_2+\beta_2)\) pairs are respectively
\[
(-\tfrac14,0),\qquad(0,-\tfrac13),\qquad(\tfrac16,0).
\]
Thus “each hypothesis is needed” is correct in the stated sense of **non-omissibility**, not necessity for every individual positive array.

The author’s script makes its sign decisions using exact `Fraction` arithmetic; only the displayed witness magnitude is converted to floating point. [3][4]

### 6. Exact-arithmetic tests

For every \(N=2,\ldots,10\), I independently computed complete tables using \(g(m,n;k)=[R_m(J)]_{n,k}\), then compared them coefficientwise with reconstruction from the kernel recurrence.

**Results:** 1,368 admissible quadratic cases, covering 660,744 table entries: **zero negative coefficients and zero recurrence mismatches**. These include random parameters, \(\kappa_2=0\), \(\kappa_2+\beta_2=0\), equality in the final diagonal increment, \(b\equiv0\), near-boundary parameters, and explicit linear-ratio endpoint cases.

A further **180 general normalized arrays**, including nonquadratic arrays and signed diagonals, gave **zero mismatches with the unrestricted recurrence**.

[Download the reproducible exact-arithmetic audit and results](sandbox:/mnt/data/round18_exact_audit.zip).

Sources:
[1] https://raw.githubusercontent.com/skypher/szkraw/244a607e412a7624f9fc1eba7e886c8a7066e823/paper.tex
[2] szkraw/paper.tex at 244a607e412a7624f9fc1eba7e886c8a7066e823 · skypher/szkraw · GitHub — https://github.com/skypher/szkraw/blob/244a607e412a7624f9fc1eba7e886c8a7066e823/paper.tex
[3] https://raw.githubusercontent.com/skypher/szkraw/244a607e412a7624f9fc1eba7e886c8a7066e823/runs/varratio/quadratic.py
[4] https://raw.githubusercontent.com/skypher/szkraw/244a607e412a7624f9fc1eba7e886c8a7066e823/probe.py

