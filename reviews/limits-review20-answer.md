## Verdict: PASS WITH MINOR FIXES

The strengthened Theorem 8.9, its new key-inequality proof, and Proposition 8.10 pass. I found no substantive gap in either proof. Two statement-level edits are warranted.

### Required minor edits

**1. Make the “exactly when” refer explicitly to monotonicity of \(b\).** The current last sentence of Theorem 8.9 could instead be read as an iff characterization of nonnegative linearization. That interpretation is false; an exact counterexample appears below.

Replace it with:
```latex
The condition that $b$ be nondecreasing is equivalent to
$\kappa\bigl(N+d_{N-1}/(1-d_{N-1})\bigr)\leq N(1-r)$.
```

**2. Qualify the strictly larger range for curved profiles by \(r<1\).** When \(r=1\), every admitted range is the singleton \(\{0\}\), including for curved profiles.

Replace the beginning of the following paragraph, through the introduction of the example, with:
```latex
For the linear profile $d_i=i/N$ the condition reads
$\kappa\leq\frac N{2N-1}(1-r)$, and these are arrays of
Proposition~\ref{prop:lc-quad}.
For a convex profile $d_{N-1}\leq(N-1)/N$, so the admitted
range of $\kappa$ contains $[0,\frac N{2N-1}(1-r)]$.
When $r<1$, this containment is strict for a nonlinear profile.
For example,
```

## Theorem 8.9: proof audit

### Monotonicity, parameter range, and removal of the old bound

The formula
\[
R_{i+1}-R_i
=\frac{f_1(i)^2-d_if_2(i)}{f_1(i)f_1(i+1)}
\]
is correct for \(0\le i\le N-2\). The denominator is positive, and log-concavity gives the numerator’s sign.

Likewise,
\[
b_{i+1}-b_i=f_1(i)\bigl(s-t(i+1)-tR_i\bigr)
\]
is correct. Its bracket is nonincreasing, giving precisely
\[
b\text{ nondecreasing}
\iff b_N-b_{N-1}\ge0
\iff t(N+R_{N-1})\le s.
\]
Thus \(tN\le s\) follows without the old slope bound.

For the linear profile, \(R_{N-1}=N-1\), giving the stated bound. For a nonlinear convex profile, \(d_{N-1}<(N-1)/N\); this gives strict enlargement when \(s>0\), explaining the second edit.

The supplied \(N=4\) example checks:
\[
R_3=\frac78,\qquad \kappa_{\max}=\frac{16}{39}>\frac25,
\]
and its displayed \(b\)-vector is correct.

There is **no remaining dependence on the old slope restriction** in the submitted proof:

- \(h_n(\ell)\ge0\) follows from \(\ell+n\le N\) and \(tN\le s\).
- The detour factors satisfy \(s-t(\ell+n+2)\ge0\) because \(n\le a-2\) and \(\ell+a\le N\).
- \(A^\psi_0=b_{\ell+a}-b_\ell\ge0\) follows directly from monotonicity.

The Leibniz formulas are correct on the stated index range. The displayed identity proving log-concavity of \(\widehat\kappa\) also expands correctly; its coefficients and sequence-product differences are nonnegative. The support and truncation arguments are valid.

### Moves and preliminary detours

The splitting and signs are correct. In particular,
\[
C_j+C^\psi_j=W^f_{2j+2,j+1}
\]
uses \(\varphi+\psi=f\), not any positivity hypothesis on \(\psi\).

All four coefficient ratios are correct. Their claimed lower bounds \(5,10,6,6\) hold on the respective domains and \(j\)-ranges. The \(V\)-detour correctly incorporates the factor \(n/(n+2)\). No out-of-range Leibniz formula is needed.

### Key inequality: reduction and minimization

The identities for \(X'\), \(Y'\), both \(A_0\) weights, and both lower bounds for \(B_0\) are correct. Multiplying those \(B_0\) bounds is legitimate because both corresponding \(A_0\) weights are nonnegative.

The potentially delicate index shift is correct:
\[
\frac{V_1}{t}
=\sum_{m=3}^{a}(m-2)m\binom am u_{m-1}
=\sum_{n=2}^{a-1}(n-1)(a-n)y_n.
\]
Consequently,
\[
4H_1-2V_1=4\alpha H_*+2tT,
\]
including the negative \(n=2\) contribution to \(T\). This proves the asserted reduction to \(\eqref{eq:affine-red}\).

For \(K\), the selected products are valid applications of the log-concavity lemma. The required binomial identities are
\[
a\binom{a-1}{n-1}=n\binom an,\qquad
\binom a2\binom{a-2}{n-2}=\binom n2\binom an.
\]
They give exactly
\[
K\ge \frac D2\sum_{n\ge3}\bigl((n-3)(n-4)+4\bigr)y_n\ge0.
\]

The next minimization is also sound:
\[
\alpha\ge tR_{\ell+a-1}\ge tR_\ell=t\,u_0/u_1.
\]
The reduced difference is affine in \(\alpha\), with coefficient \(K\ge0\). Therefore evaluating it at the smaller value \(tu_0/u_1\) suffices, even though that artificial value need not describe an admissible original array.

Homogeneity permits \(u_1=1\), since \(u_1>0\). When \(q=u_2=0\), interval support forces every \(u_n\), \(n\ge2\), to vanish. Otherwise log-concavity gives \(0\le z\le1/q\). At \(\alpha=tz\), the two weights are indeed
\[
A_0=tzY,\qquad A_0''=t(z+1)J.
\]

### Key inequality: endpoint estimates

The expression for \(F(z)\) and its interpolation identity are correct. Its quadratic coefficient is \(-4H_*\), so the added interpolation term is nonnegative throughout the required interval.

The \(YJ\) selection does **not** double-count. Different \(n\)'s have different index sums \(n+1\); within a fixed \(n\ge4\), the two pairs are distinct ordered pairs from the two factors.

Their weakened coefficient is exactly
\[
\binom a{n+1}
\left[\binom{n+1}2+\binom{n+1}3\right]
=\binom an(a-n)\frac{n(n+2)}6.
\]
For \(n=3\), the single pair gives
\[
\binom a2\binom{a-2}2
=6\binom a4
=\frac32(a-3)\binom a3.
\]
Thus the stated \(L_n\)'s are correct.

The \(YY'\) estimate follows from
\[
qu_{n-1}\ge u_n,\qquad
\binom a2\binom{a-1}{n-1}
=\frac{n(a-1)}2\binom an.
\]

For the remaining upper bound, shifting \(H_*\) gives coefficient
\[
\frac{4(n-1)}{n+1}+2(n-3)
=\frac{2(n^2-5)}{n+1}=E_n.
\]
The sign of \(E_2=-2/3\) is handled correctly: its contribution becomes nonnegative after subtraction and may then be discarded.

Both endpoint conclusions follow. The numerical facts hold, including the all-\(n\) positivity claim:
\[
n^3-6n^2+5n+60
=(n-4)^3+6(n-4)^2+5(n-4)+48>0
\quad(n\ge4).
\]
The \(a=3\) case and truncated supports are not lost in the summation bounds.

### Resummation

The operator order is correct: right multiplication by \(P\) includes taking \(B_0\) first, as required by the detours. The intermediate denominator is precisely \(c_{\ell+1}\), so the raw inequalities yield the displayed normalized operator inequalities.

The estimate retaining \(\frac23GV_1G\) is valid. The subsequent cancellation also checks:
\[
G\left(A_0-\frac14(A_0P+PA_0)\right)G
=\frac12(GA_0+A_0G).
\]
Thus \(GAG\ge0\), \(M\ge0\), and \(M\) strictly raises \(\ell\). The transformation using \(v=(I-P/2)\omega\) and both finite geometric sums is correct.

## Proposition 8.10: proof audit

The quadratic Leibniz formula is correct. In particular, on the occurring index range,
\[
\varphi_3
=3\bigl(t+\tau(\ell+2)\bigr)w+3\tau v,
\qquad
\varphi_4=6\tau w.
\]

The move inventory and signs are correct:

- \(A^\psi_1\le0\) enters with sign \(-1\), hence contributes positively.
- \(A^\psi_j=0\) for \(j\ge2\), and \(B_j=0\) for \(j\ge2\).
- \(C_0+C^\psi_0=\binom a2w\ge0\), while the combined \(C\)-moves vanish for \(j\ge1\).

Thus \(-B_1\) is the only negative contribution.

Both lower bounds for \(\varphi_2\) are valid. Writing their bracketed quantities as \(A,B\), the argument is
\[
(pw+\tau A)(pw+\tau B)
\ge p\tau w(A+B)
\ge6p\tau w(u+v).
\]
The second inequality follows because
\[
A+B-6(u+v)
=-4u+(4\ell+1)v+(2\ell+4)w
\ge v+(2\ell+4)w\ge0.
\]
Here \(u\le\ell v\) is valid. Whenever \(B_1\) can be nonzero, \(a\ge4\), so every difference index used in this argument is in range.

The resulting detour actually proves the stronger statement
\[
P^2\ge6Q,
\]
hence certainly \(P^2\ge4Q\). With \(H=0\), \(A=A_0+V_1\ge0\), and nonnegative combined \(C\)-moves, the resummation applies directly.

Finally, the monotonicity characterization is correct. Both \(R_i\) and \(t+\tau i\) are nonnegative and nondecreasing, so the increment bracket is nonincreasing. Evaluating its last value gives precisely the displayed condition.

## Independent exact-arithmetic tests

I used new code based on `Fraction`, not the author’s diagnostics. Linearization coefficients were computed directly from the original three-term recurrence, independently of the kernel proof. Symmetry and coefficient sums were also checked.

| Test | Coverage | Result |
|---|---:|---|
| Affine arrays | 143 maximum-slope arrays for \(2\le N\le14\), plus 15 edge cases; 4,241 key-inequality sources | No failures |
| Quadratic-profile arrays | 156 parameter samples for \(2\le N\le14\); 3,432 detour sources | No failures |
| Linearization | 340,251 coefficients across those 314 arrays | All nonnegative |
| Endpoint sequence bounds | 830 nonzero-\(q\) cases and 70 zero-tail cases; \(a\le32\), geometric ratios \(10^{-5}\) through \(10\) | No failures |
| Full operator verification | Both families at \(N=4,6,8\) | \(M\ge0\), resummation identity, and conversion back to linearization all verified |

The affine profiles included full-support geometric Newton sequences, curved nongeometric sequences, quadratic profiles, and randomly truncated log-concave sequences.

[Download the independent scripts, reports, and logs](sandbox:/mnt/data/review20_exact_checks.zip).

## What fails beyond the boundary

The positivity certificate fails immediately when the last increment becomes negative:
\[
M_{(N,0),(N-1,1)}
=\frac{b_N-b_{N-1}}{c_N}<0.
\]
There are no alternative paths contributing to this entry. This does **not** imply failure of (P).

For example, take
\[
N=2,\quad d=(0,\tfrac12,1),\quad r=\tfrac12,\quad\kappa=\tfrac25.
\]
Then \(b=(0,3/20,1/10)\) is not nondecreasing, but all nontrivial linearization vectors are nonnegative:
\[
\begin{aligned}
g(1,1;\cdot)&=(7/20,\ 3/20,\ 1/2),\\
g(1,2;\cdot)&=(0,\ 9/10,\ 1/10),\\
g(2,2;\cdot)&=(63/100,\ 9/50,\ 19/100).
\end{aligned}
\]
This is why the theorem’s “exactly when” must refer to monotonicity, not (P).

The key inequality can also fail outside the boundary while (P) survives. For
\[
N=6,\qquad d_i=i/6,\qquad r=\tfrac12,\qquad t=\tfrac5{88},
\]
its left side minus right side at \((\ell,a)=(3,3)\) is
\[
-\frac5{23232},
\]
although all linearization coefficients are nonnegative.

Actual failure of (P) occurs for
\[
N=3,\quad d=(0,\tfrac17,\tfrac37,1),\quad
r=\tfrac12,\quad\kappa=\tfrac12:
\qquad g(3,3;3)=-\frac1{24}.
\]

The broader outside-boundary tests retained stochasticity and included slope factors \(1.0001,1.01,1.1,1.25\). Among 181 affine arrays, four failed (P) and nine failed the key inequality. All 422 sampled quadratic-profile arrays outside the boundary retained (P); that finite observation does not establish an extension of Proposition 8.10.

**Bottom line:** both proofs pass under their stated monotonicity hypotheses. Apply the two wording edits above; no proof replacement is needed.
