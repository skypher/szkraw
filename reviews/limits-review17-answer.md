## Verdict: PASS WITH MINOR FIXES

**Theorem 8.6 and Corollary 8.7 survive the audit.** I found no substantive failure in the normalization, kernel recurrence, detours, matching argument, or corollary implication. The one literal notation defect is the use of undefined \(w_0\) in the corollary proof. Endpoint conventions, the domain of the detour inequalities, and zero-case cancellations should also be made explicit.

References below are to **one-based source lines 750–804** at the specified commit. I inspected the pinned source; I could not independently recompute the supplied whole-file SHA-256 because a raw local download was unavailable. [1]

### 1. Normalization and generator — correct

For \(0\le i<N\),
\[
a_i\frac{e_i}{e_{i+1}}=c_{i+1},
\qquad
c_i\frac{e_i}{e_{i-1}}=a_{i-1}\quad(i\ge1).
\]
Thus the rescaled recurrence is correct, with the endpoint relations
\[
xE_0=c_1E_1,\qquad
xE_N=b_NE_N+a_{N-1}E_{N-1}.
\]
All \(e_i\) are strictly positive. The missing \(E_{-1}\) and \(E_{N+1}\) terms should explicitly be omitted, as they were in the earlier constant-ratio proof. [1]

The generator acts on a monomial as
\[
\mathcal L_z z^i=c_i z^{i-1}+b_i z^i+a_i z^{i+1}.
\]
Consequently \(c_0=0\) removes the lower-boundary term, and \(a_N=0\) removes the upper-boundary term. There is **no terminal truncation error**: \(xF=\mathcal L_zF\) holds as an identity of support-valued polynomials.

The conversion back to the original linearization,
\[
g(m,n;k)=L_{mn}^k\frac{e_k}{e_me_n},
\]
also has the correct orientation.

### 2. Divided-difference formula — correct, including both \(p=0\) terms

The displayed formula at lines 775–777 follows directly from applying the two Newton operators separately. In particular,
\[
\chi_{-2}=-Z^{-1},\qquad \chi_{-1}=0,\qquad \chi_0=1.
\]
Its complete \(p=0\) contribution is
\[
-c_\ell S^aZ^{\ell-1}
-(c_\ell+b_\ell)S^aZ^\ell.
\]

This is an important distinction: **\(\beta_0=0\) does not imply \(\psi_0(\ell)=0\)**. Generally \(\psi_0(\ell)=b_\ell\), and its contribution must not be dropped. The submitted formula retains it correctly. [1]

The \(j=0\) parts of all the \(-\chi_p\) terms sum, by Vandermonde, to
\[
-(c_{\ell+a}+b_{\ell+a})S^aZ^\ell.
\]
Together with the initial \(S^aZ^\ell\), this gives precisely \(a_{\ell+a}\), not \(a_\ell\).

### 3. Kernel recurrence — correct

The four families are correctly identified:

| Contribution | Family |
|---|---|
| \(\psi_p\chi_{p-1}\) | \(A^\psi_j=W^\psi_{2j+1,j}\) |
| \(\varphi_p\chi_{p-2}\), \(p\ge2\) | \(B_j=W_{2j+2,j}\) |
| Higher-\(Z\) terms of \(-\varphi_p\chi_p\) | \(C_j=W_{2j+2,j+1}\) |
| Higher-\(Z\) terms of \(-\psi_p\chi_p\) | \(C^\psi_j=W^\psi_{2j+2,j+1}\) |

Reindexing the higher-\(Z\) terms gives the displayed sign \((-1)^j\) in both \(C\)-families. The negative term
\(-c_\ell S^aZ^{\ell-1}\) gives the left-hand coefficient \(c_{\ell+1}\). All source shifts in the submitted recurrence are correct. [1]

The support argument also transfers unchanged. In the coefficient of \(z^{\ell+a}w^\ell\), contributions other than \(\omega_{\ell,a}\) come from smaller first indices; induction therefore forces \(\omega_{\ell,a}=0\) when \(\ell+a>N\).

There is no problematic use of polynomially extended negative straight weights: only \(a_{\ell+a}\) on \(\Omega\) is used. At its boundary the outward straight move has weight \(a_N=0\).

Regarding the constant term of \(b\): it does not enter the four non-straight families, because their Newton indices are positive. A hypothetical nonzero \(\beta_0\) would still affect the straight coefficient through \(a=1-b-c\). Thus “plays no role” is accurate for the **detours**, not literally for the entire generator.

### 4. Detour inequalities and matching — correct

The mixed-index ranges are exactly sufficient. For \(j\ge1\), the first detour uses
\[
\psi_1(\ell)\varphi_n(\ell+1),\quad n\ge2j\ge2,
\]
and
\[
\varphi_2(\ell)\psi_n(\ell+1),\quad n\ge2j-1\ge1.
\]
The \(C^\psi\)-detour uses the latter inequality only for \(n\ge2j\). No missing \(n=1\) instance of the first mixed inequality is needed. [1]

The lower bounds stated in the proof reproduce the coefficient comparison in Lemma 8.4 exactly. For the first detour, after division by \(c_{\ell+1}\), the target sequence is \(\psi_m(\ell)\), with coefficient
\[
\binom{m+1}{2}\binom{m-j-2}{j-1}\binom am.
\]
The other two comparisons have target sequences \(\varphi_m(\ell)\) and
\(\varphi_m(\ell)+\psi_m(\ell)\), respectively. The three coefficient ratios are therefore the same as before, with minima \(5,5,6\), all exceeding \(4\).

Using Lemma 8.3 for \(\varphi\) is legitimate even though \(c_N\) need not equal \(1\): its inequality is homogeneous of degree two. Equivalently, apply it to \(\kappa/c_N\) and multiply back.

For a source \((\ell,a)\), the displacements are
\[
A^\psi_j:(j+1,-2j-1),\quad
B_j:(j+1,-2j-2),\quad
C_j+C^\psi_j:(j+2,-2j-2).
\]
They are distinct **after merging the two \(C\)-families**. The matched intermediate nodes stay in \(\Omega\), and each matched path has exactly the additional denominator \(c_{\ell+1}\). There is no double-counting in the entrywise comparison \(\mathcal P^2\ge4\mathcal Q\).

The subsequent induction proving
\(\omega\ge\frac12\mathcal P\omega\ge0\) transfers without alteration.

**Clarification:** state the detours for \(0\le\ell\le N-1\), rather than implicitly importing Lemma 8.4’s unrestricted \(\ell\)-range.

### 5. Corollary proof — correct after defining \(w_0\)

The double-sum identity is correct. Its \(i=0\) instance, however, contains \(w_0\), which has not been defined. Set \(w_0=w_1\); because \(\kappa_0=0\), this changes nothing else. [1]

The precise pairing is:
\[
\{x\ge y+2,\ y\ge i\}
\longleftrightarrow
\{i+1\le x\le y\},
\qquad
(x,y)\mapsto(y+1,x-1).
\]
It is a bijection onto this subset, **not onto every term with \(x\le y\)**. The remaining terms have \(x=i\) and are nonnegative. Terms with \(x=y+1\) vanish.

The paired sum has the stated sign because
\[
u_{y+1}u_{x-1}\ge u_yu_x\qquad(x\ge y+2).
\]
This balanced-product inequality follows from log-concavity of the zero-extended binomial sequence. It remains valid when an endpoint binomial coefficient is zero.

Chaining is legitimate: \(G\) has interval support, and \(G_i=0\) implies \(H_i=0\). There is no division across a support gap.

For completeness, the compressed “Multiplying gives” step can be written explicitly. Put \(C=G_0+G_1\). Since \(G_1\ge\kappa_1>0\),
\[
H_1(G_n+G_{n+1})
\ge C\,\frac{H_1G_{n+1}}{G_1}
\ge CH_{n+1}.
\]
For the second inequality, when \(G_{n+2}>0\),
\[
G_2(H_n+H_{n+1})
\ge
G_2\frac{H_{n+2}(G_n+G_{n+1})}{G_{n+2}}
\ge CH_{n+2}.
\]
When \(G_{n+2}=0\), also \(H_{n+2}=0\), so the desired inequality is immediate. These are precisely the two mixed hypotheses.

The \(i=0\) identity becomes
\[
H_0G_1-H_1G_0
=b_\ell c_{\ell+1}-b_{\ell+1}c_\ell\ge0.
\]
For \(1\le\ell<N\), division by positive \(c_\ell c_{\ell+1}\) proves the ratio assertion. At \(\ell=0\), the identity is merely \(0=0\); no division by \(c_0\) is needed.

Finally, constant \(w\) gives
\[
b=wc,\qquad r=\frac1{1+w},\qquad \nu_k=(1+w)\kappa_k.
\]
Thus \(d=b+c\) has the required normalized log-concave Newton sequence. Conversely, Theorem 8.1 gives \(w=(1-r)/r\). The constant-weight subfamily is **exactly** Theorem 8.1.

### 6. Quadratic example and exclusions — correct

Write \(A=\kappa_1>0\), \(B=\kappa_2/2>0\). Then
\[
\frac{b_i}{c_i}
=\frac{w_1A+w_2B(i-1)}{A+B(i-1)},
\]
and
\[
\frac{b_i}{c_i}-\frac{b_{i+1}}{c_{i+1}}
=
\frac{(w_1-w_2)AB}
{(A+B(i-1))(A+Bi)}>0.
\]
Hence the claimed ratio increases strictly. Common scaling preserves this, and positive Newton coefficients make the normalized \(d_i\) strictly increasing, ensuring \(a_i>0\) for \(i<N\). [1]

For the recorded counterexample,
\[
(\beta_1,\beta_2,\beta_3)=\frac1{91}(1,-1,1),
\]
so \(\beta_2<0\) excludes it.

For a linear profile \(d_i=i/N\) and strictly increasing affine ratio
\(r_i=r_1+s(i-1)\), \(s>0\),
\[
b_i=\frac{i}{N}(1-r_1-s(i-1)),
\qquad \beta_2=-\frac{2s}{N}<0.
\]
The second exclusion is therefore correct for \(N\ge2\). “Strictly increasing” would make the exclusion unambiguous.

### 7. Independent exact tests

I wrote separate standard-library `Fraction` implementations of direct finite linearization via \(R_m(J)\), the kernel recurrence, and the matching matrices. No author diagnostic was imported. Every direct case checks **all** ordered triples, including terminal/deep products, plus row sums, symmetry, triangle zeros, and the terminal polynomial relation.

| \(N\) | Cases checked | Satisfying Theorem 8.6 | Failures among those | Failures outside mixed hypotheses |
|---:|---:|---:|---:|---:|
| 2 | 1,078 | 1,078 | 0 | 0 |
| 3 | 1,414 | 859 | 0 | 1 |
| 4 | 3,334 | 1,156 | 0 | 1 |
| 15 | 18 | 18 | 0 | 0 |
| 20 | 18 | 18 | 0 | 0 |

These comprise randomized/constructed cases and an exhaustive **finite grid**, not exhaustive testing over real arrays. The grid uses unscaled \(\kappa_1=1\), remaining \(\kappa_k\in\{0,1,2\}\), retaining the required support/log-concavity, and \(\beta_k\in\{0,\tfrac14,1,2\}\).

The randomized cases include \(b=0\), ratios as small as \(1/2000001\), and positive-diagonal ratios within \(2\cdot10^{-6}\) of \(1\). At each of \(N=15,20\), six cases satisfy the theorem but not the corollary; three of those have full \(\kappa\)-support.

Additional checks gave **zero mismatches on 23,250 kernel/direct coefficients**, **zero violations in 26,667 local detour inequalities**, and **zero violations at 7,447 nonzero-\(\mathcal Q\) entries** of \(\mathcal P^2\ge4\mathcal Q\).

#### Exact failure when the mixed assumptions are removed

Take \(N=3\) and
\[
a=\frac1{13}(13,9,5,0),\qquad
b=\frac1{13}(0,0,0,1),\qquad
c=\frac1{13}(0,4,8,12).
\]
Then
\[
\kappa=\frac1{13}(4,0,0),\qquad
\beta=\frac1{13}(0,0,1).
\]
All other theorem assumptions hold. Both mixed inequalities fail already at \(\ell=0\): their relevant instances read \(0\ge4/169\).

Exact linearization gives
\[
\boxed{R_3^2=\frac{128R_0+32R_1+36R_2-R_3}{195}},
\qquad
\boxed{g(3,3;3)=-\frac1{195}}.
\]
I also verified this independently by polynomial division using the terminal relation.

This shows that dropping the mixed assumptions admits genuine failures. **Their failure does not necessarily imply failure of positivity**; positive controls violating them also occurred.

### 8. Replacement text

The essential insertion at the beginning of the corollary proof is:

```tex
Set $w_0=w_1$; since $\kappa_0=0$, this leaves $\beta_0=0$.
```

Add the endpoint convention after the rescaled recurrence:

```tex
The out-of-range terms are omitted: at the endpoints,
$xE_0=c_1E_1$ and $xE_N=b_NE_N+a_{N-1}E_{N-1}$.
```

Replace the detour introduction with:

```tex
For $j\geq1$, $0\leq\ell\leq N-1$ and $a\geq0$, the following
detour inequalities hold, with weights having a negative second
argument interpreted as zero:
```

The expanded pairing and zero-case argument above is suitable replacement text for the compressed corollary passage. None of these edits strengthens the hypotheses.

[Exact-check scripts, results, and reproduction instructions](sandbox:/mnt/data/review17_checks.zip) · [Complete replacement LaTeX fragments](sandbox:/mnt/data/review17/replacement_text.tex)

Sources:
[1] https://raw.githubusercontent.com/skypher/szkraw/551a54e0fd285b2053a546c8a34409691d7dde3c/paper.tex

