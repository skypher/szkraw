## Verdict: **PASS WITH MINOR FIXES**

Theorem 7.12 and Corollary 7.13 are correct, including the truncated-cone argument. The required corrections concern the surrounding prose: extending only hypothesis (iii) is insufficient, and the Section 8 sentence needs the qualification \(N\geq3\) when excluding Krawtchouk arrays. The pinned source contains both wording issues. [1]

### 1. Theorem 7.12: correct and complete

**The equation \(Hu=0\) holds on the entire square.** Products are expanded as functions on the finite orthogonality support. The terminal recurrence is valid there, so multiplying either factor by \(x\) gives the same function, including when either index equals \(N\). Uniqueness of expansion in the finite polynomial basis gives \(Hu=0\). No unrestricted polynomial identity beyond degree \(N\) is needed. This agrees with the paper’s finite-support convention. [1]

Here is the explicit classification confirming the potentially delicate truncation step. Assume \(m\geq1\), and write
\[
s=n+m,\qquad t=n-m,\qquad p=i+j,\qquad q=i-j.
\]
On the parity \(s-p\) odd,
\[
(H^*v)(i,j)=(\beta_i-\beta_j)v(i,j).
\]
On the parity \(s-p\) even, the potentially nonzero cases are
\[
(H^*v)(i,j)=
\begin{cases}
-\alpha_m,&p=s,\ q=t,\\
\alpha_i-\alpha_j,&p=s,\ q\geq t+2,\\
\gamma_i-\alpha_j,&p\leq s-2,\ q=t,\\
(\alpha_i+\gamma_i)-(\alpha_j+\gamma_j),
   &p\leq s-2,\ q\geq t+2.
\end{cases}
\]
All other values vanish. These formulas are restricted to the finite square and use \(\alpha_0=\gamma_N=0\).

In particular, **truncating at \(i=N\) creates no additional coefficient type**. At a terminal-boundary interior point, the fourth expression becomes
\[
\alpha_N-(\alpha_j+\gamma_j),
\]
which is nonnegative by (ii). At a supported point of the other parity, the coefficient can be \(\beta_N-\beta_j\), explaining why terminal monotonicity of \(\beta\) is also required.

For the potentially problematic edge,
\[
i-j=n-m,\qquad j<m
\quad\Longrightarrow\quad
i=n-m+j\leq n-1\leq N-1.
\]
Thus **no \(\gamma_N-\alpha_j\) edge inequality is needed**.

Every non-apex contribution has \(j<m\) and \(i\geq j\). Starting from \(u(i,0)=\mathbf1_{i=k}\), induction applies, and \(\alpha_m>0\) permits division. Symmetry finishes the proof.

### 2. Corollary 7.13: correct, including the terminal sum

The normalization definitions give
\[
\alpha_n=\sqrt r\,d_n\quad(0\leq n\leq N),\qquad
\gamma_n=\sqrt r(1-d_n)\quad(0\leq n\leq N).
\]
The second formula includes the prescribed \(\gamma_N=0\). In particular,
\[
\alpha_N=\sqrt r,\qquad
\alpha_N+\gamma_N=\sqrt r.
\]
Hence the constant-sum assertion really does hold at **every** index, including both endpoints. [1]

The remaining verification is exactly
\[
\gamma_i-\alpha_j
=\sqrt r(1-d_i-d_j)
\geq\sqrt r(1-2d_{N-1})\geq0
\qquad(j\leq i\leq N-1).
\]
No convexity assumption enters.

### 3. Follow-up remarks

**Non-convex profiles are allowed.** For example, \(d=(0,3/10,2/5,1)\) satisfies the corollary, while its increments \(3/10,1/10,3/5\) are not nondecreasing.

**The geometric and Krawtchouk inclusion claims are correct as stated immediately after the corollary.** For the geometric arrays,
\[
(q^N-1)-2(q^{N-1}-1)=q^{N-1}(q-2)+1>0
\]
when \(q\geq2\), so actually \(d_{N-1}<1/2\). For Krawtchouk, \(d_{N-1}=(N-1)/N\), which exceeds \(1/2\) precisely when \(N\geq3\). The cases \(N=1,2\) are included. [1]

**The sharpness formula is correct.** Put \(d=d_1\). At \(N=2,r=1\),
\[
R_2=\frac{x^2-d}{1-d},\qquad x^3=x
\]
on the support. Consequently,
\[
R_2^2=\frac{d}{1-d}R_0+
       \frac{1-2d}{1-d}R_2.
\]
Thus \(g(2,2;2)=(1-2d)/(1-d)\), negative for every \(d>1/2\). This establishes sharpness of the uniform bound, not necessity for every fixed size and bias.

**The convex-profile edge analysis is correct.** Nondecreasing increments give \(d_i+d_j\leq d_{i+j}\) when \(i+j\leq N\). All non-apex terms other than \(\gamma_i-\alpha_j\) are nonnegative; these edge terms can therefore be negative only when \(i+j>N\).

The Krawtchouk formula \(\sqrt r(N-i-j)/N\) is also correct. The compensation sentence should preferably refer to **negative weighted contributions that actually occur**: a negative edge coefficient can multiply zero, and a deep triple need not produce any negative edge contribution.

### 4. Required replacement text

**Before Theorem 7.12**, replace the two introductory sentences with:

```tex
The cone argument extends to all products if the monotonicity
conditions in (i)--(ii) are imposed through the terminal index $N$
and the edge inequalities in (iii) are imposed for every
$0\leq j\leq i\leq N-1$.
```

The existing claim that the restriction is needed only for (iii) is genuinely false in the general setting, not merely imprecise. For example, take \(N=2,\sigma\equiv1\) and
\[
a=(1,3/10,0),\qquad
b=(0,2/5,2/5),\qquad
c=(0,3/10,3/5).
\]
These satisfy Theorem 7.10 and the enlarged (iii), even with (i) holding through \(N\), but
\[
g(2,2;2)=-2/5.
\]
The missing condition is extended (ii): here \(\alpha+\gamma=(1,3/5,3/5)\).

**In the changed Section 8 passage**, replace its middle sentence with:

```tex
Theorem~\ref{thm:all} supplies such hypotheses for all triples
under its strengthened conditions (i)--(iii), and
Corollary~\ref{cor:heavy} contains the arrays
\eqref{eq:parameters} with $q\geq2$ but not the Krawtchouk
arrays with $N\geq3$.
```

The first and last sentences can remain unchanged. In particular, do not describe (iii) as holding at \(i=N\): its correct terminal range ends at \(N-1\). The current Section 8 wording both omits the strengthened monotonicity assumptions and drops the small-size qualification. [1]

**Suggested precision edit for the compensation remark:**

```tex
For the Krawtchouk arrays these edge coefficients are
$\sqrt r\,(N-i-j)/N$; any negative weighted contributions
they make to the cone identity must be compensated by
its other terms.
```

### Verification scope

I independently checked the exact symbolic stencil classification for all **1,540 cones with \(1\leq m\leq n\leq N\leq20\)**, including terminal truncations, and symbolically verified the \(N=2\) sharpness identity. [Cone-check script](sandbox:/mnt/data/review_round12/cone_check.py)

I inspected the source at the specified commit, but did not independently verify the supplied SHA-256 or rerun `heavy_top_check.py`.

Sources:
[1] https://raw.githubusercontent.com/skypher/szkraw/88c1b4d8cdcc14bcaf0d0e722027faac26ec3b89/paper.tex

