**The affine subclass works with nondecreasing \(b\), without the slope bound.** In particular, Theorem 8.9 can be strengthened to the exact range
\[
\boxed{
0\le t\le
\frac{1-r}{\,N+d_{N-1}/(1-d_{N-1})\,}.
}
\]
For this range, the same operator \(M\) is entrywise nonnegative, so the same resummation proves (P).

For general quadratic ratios, I also obtain the mixed detours with constants
\[
\boxed{\mu_H=10,\qquad \mu_V=\frac92,\qquad \mu_W=3,\qquad \mu_C=6.}
\]
The \(W\)-constant \(3\) is optimal for the particular scalar detour in the question. There is also a complete result for quadratic ratios when \(d\) has Newton degree at most two.

I do **not** establish the \(B\)-detour or the key inequality for unrestricted (Q). The complete arguments for the results above follow.

## 1. Nondecreasing \(b\) is an endpoint condition

Write \(f_n(i)=\Delta^n d(i)\), and put
\[
R_i=\frac{d_i}{f_1(i)}\qquad(0\le i<N).
\]
Shifted Newton log-concavity gives
\[
R_{i+1}-R_i
=
\frac{f_1(i)^2-d_i f_2(i)}
{f_1(i)(f_1(i)+f_2(i))}
\ge0.
\tag{1}
\]
All denominators are positive.

For the quadratic ratio,
\[
\Delta b(i)
=f_1(i)\left[1-\rho(i+1)-(t+\tau i)R_i\right].
\]
The bracket is nonincreasing in \(i\), because both \(\rho(i+1)\) and \((t+\tau i)R_i\) are nondecreasing. Therefore \(b\) is nondecreasing **if and only if its last increment is nonnegative**.

With
\[
R=\frac{d_{N-1}}{1-d_{N-1}},
\]
the exact condition is
\[
\boxed{
t(N+R)+\tau\left[\binom N2+(N-1)R\right]\le1-r.
}
\tag{2}
\]
For \(\tau=0\), this gives the slope range stated above. For a linear profile, \(R=N-1\), recovering the old bound.

## 2. The affine key inequality under nondecreasing \(b\)

Assume \(\tau=0\). Fix an admissible source \((\ell,a)\), \(a\ge3\), and write
\[
u_n=f_n(\ell),\qquad D=u_0+u_1,\qquad
\alpha=1-r-t(\ell+a).
\]

Monotonicity of \(b\) at \(\ell+a-1\), followed by (1), gives
\[
\boxed{
\alpha\ge
t\frac{d_{\ell+a-1}}{f_1(\ell+a-1)}
\ge t\frac{u_0}{u_1}.
}
\tag{3}
\]
This replaces the old estimate \(\alpha\ge t(a-1)\).

Define
\[
\begin{aligned}
X&=\sum_{n=1}^a\binom an u_n,
&
Y&=\sum_{n=2}^a\binom an u_n,\\
X'&=\sum_{n=1}^{a-2}\binom{a-2}n(u_n+u_{n+1}),
&
Y'&=\sum_{n=2}^{a-1}\binom{a-1}n(u_n+u_{n+1}).
\end{aligned}
\]
Then
\[
A:=A_0(\ell,a)=\alpha X-ta u_0,
\]
\[
A'':=A_0(\ell+1,a-2)
=(\alpha+t)X'-t(a-2)D.
\tag{4}
\]

Set
\[
y_n=\binom an u_n,\qquad
H_*=\sum_{n=3}^a(n-2)y_n,\qquad
T=\sum_{n=2}^a(n-3)(a-n)y_n.
\]
Reindexing \(V_1\) gives
\[
V_1=t\sum_{n=2}^a(n-1)(a-n)y_n,
\]
and consequently
\[
4H_1-2V_1=4\alpha H_*+2tT.
\tag{5}
\]

Both \(A\) and \(A''\) are nonnegative. Also,
\[
B_0(\ell,a)\ge \rho(\ell+1)Y,\qquad
B_0(\ell+1,a-1)\ge \rho(\ell+1)Y'.
\]
Thus it suffices to prove
\[
\boxed{
AY'+YA''\ge D(4\alpha H_*+2tT).
}
\tag{6}
\]

### 2.1. The coefficient of \(\alpha\)

Put
\[
K=XY'+YX'-4DH_*.
\]
The shifted log-concavity inequality
\[
u_i(u_j+u_{j+1})\ge D u_{i+j}
\]
and the bounds \(X\ge au_1\), \(Y\ge\binom a2u_2\) give
\[
XY'+YX'
\ge D\sum_{n=3}^a
\left(n+\binom n2\right)y_n.
\]
Therefore
\[
K\ge D\sum_{n=3}^a
\frac{n^2-7n+16}{2}y_n\ge0,
\tag{7}
\]
because
\[
n^2-7n+16=(n-3)(n-4)+4\ge0
\]
for integral \(n\ge3\).

### 2.2. Reduction to two endpoints

By homogeneity, normalize \(u_1=1\). Write
\[
z=u_0,\qquad q=u_2,\qquad
J=\sum_{n=2}^{a-1}\binom{a-1}n u_n.
\]
Then
\[
D=z+1,\quad X=a+Y,\quad X'=a-2+J,\quad
Y'=Y-(a-1)q.
\]

If \(q=0\), all \(u_n\) with \(n\ge2\) vanish, and (6) is immediate. Otherwise, log-concavity gives
\[
0\le z\le\frac1q.
\]

By (3) and (7), it suffices to set \(\alpha=tz\). At that value,
\[
A=tzY,\qquad A''=t(z+1)J.
\]
After factoring out \(t\), the difference in (6) becomes
\[
F(z)=zYY'+(z+1)YJ-(z+1)(4zH_*+2T).
\tag{8}
\]
Its quadratic coefficient is \(-4H_*\). Explicitly,
\[
\boxed{
F(z)=(1-qz)F(0)+qzF(1/q)
+4H_*z(1/q-z).
}
\tag{9}
\]
It remains to prove the two endpoint inequalities.

### 2.3. Two product bounds

Define
\[
L_3=\frac32,\qquad
L_n=\frac{n(n+2)}6\quad(n\ge4),
\qquad
E_n=\frac{2(n^2-5)}{n+1}\quad(n\ge2).
\]

First,
\[
\boxed{
YJ\ge\sum_{n=3}^{a-1}L_n(a-n)y_n.
}
\tag{10}
\]
Here is a verification using only two selected products per order.

For \(n=3\), retain the product with indices \((2,2)\). For \(n\ge4\), retain the products with indices
\[
(2,n-1),\qquad (3,n-2).
\]
Balanced products give
\[
u_2u_{n-1}\ge u_n,\qquad u_3u_{n-2}\ge u_n,
\]
since \(u_1=1\). Using
\[
\binom{a-1}j\ge\binom{a-i}j,
\]
their combined coefficients are at least
\[
\binom a{n+1}
\left[\binom{n+1}2+\binom{n+1}3\right]
=
\binom an(a-n)\frac{n(n+2)}6.
\]
The two selected pairs are distinct, including when \(n=4\).

Second, decreasing adjacent ratios give
\[
q u_{n-1}\ge u_n\qquad(n\ge3).
\]
Retaining the \(\binom a2q\) term of \(Y\), we obtain
\[
\boxed{
\frac{YY'}{q+1}
\ge\sum_{n=3}^a\frac{n(a-1)}2y_n.
}
\tag{11}
\]
Indeed, termwise,
\[
q(u_{n-1}+u_n)\ge(q+1)u_n,
\]
and
\[
\binom a2\binom{a-1}{n-1}
=\frac{n(a-1)}2\binom an.
\]

The numerical inequalities needed below are
\[
L_n\ge2(n-3),\qquad
L_n+\frac n2\ge E_n
\qquad(n\ge3).
\tag{12}
\]
At \(n=3\), these say \(3/2\ge0\) and \(3\ge2\). For \(n\ge4\), the first difference equals
\[
\frac{(n-5)^2+11}{6}>0.
\]
The second difference, multiplied by \(6(n+1)\), equals
\[
n^3-6n^2+5n+60
=(n-4)^3+6(n-4)^2+5(n-4)+48>0.
\]

### 2.4. Endpoint verification

At zero, (10) and (12) give
\[
\begin{aligned}
F(0)
&=YJ-2T\\
&\ge
2(a-2)y_2+
\sum_{n=3}^{a-1}
[L_n-2(n-3)](a-n)y_n
\ge0.
\end{aligned}
\tag{13}
\]

At the other endpoint,
\[
\frac{F(1/q)}{1+1/q}
=
YJ+\frac{YY'}{q+1}-\frac4qH_*-2T.
\tag{14}
\]
Using \(u_n/q\le u_{n-1}\) and reindexing,
\[
\frac4qH_*+2T
\le
\sum_{n=2}^{a-1}E_n(a-n)y_n.
\tag{15}
\]
The \(n=2\) coefficient is negative: \(E_2=-2/3\). For \(n\ge3\), the lower bounds (10)–(12) give
\[
L_n(a-n)+\frac{n(a-1)}2
\ge(a-n)(L_n+n/2)
\ge(a-n)E_n.
\]
Thus (14) is nonnegative.

Equations (7), (9), (13), and (14) prove (6). Restoring the scale \(u_1\), this proves
\[
\boxed{
A_0(\ell,a)B_0(\ell+1,a-1)
+B_0(\ell,a)A_0(\ell+1,a-2)
\ge c_{\ell+1}(4H_1-2V_1).
}
\tag{16}
\]

No slope bound was used.

## 3. Mixed detours for all of (Q)

Primes on weights below mean evaluation at \((\ell+1,a-2)\). All indices are restricted to \(\Omega\).

Since
\[
\varphi_2(\ell)\ge\rho(\ell+1)f_2(\ell),
\]
the usual profile inequality gives
\[
\varphi_2 f_n'\ge c_{\ell+1}f_{n+2},
\qquad
\varphi_2 h_n'\ge c_{\ell+1}h_{n+2}.
\tag{17}
\]
The second also uses
\[
1-\rho(\ell+n+1)\ge1-\rho(\ell+n+2)\ge0.
\]

For \(n\ge3\),
\[
\varphi_2v_n'
\ge
\frac{n^2}{(n+1)(n+2)}
c_{\ell+1}v_{n+2},
\tag{18}
\]
because
\[
(n+1)[t+\tau(\ell+n)]
-n[t+\tau(\ell+n+1)]
=t+\tau\ell\ge0.
\]
Similarly,
\[
\varphi_2w_n'
\ge
\frac{n(n-1)}{(n+1)(n+2)}
c_{\ell+1}w_{n+2}.
\tag{19}
\]
These use the profile products with indices \((2,n-1)\) and \((2,n-2)\), respectively.

Retain \(B_0\ge\binom a2\varphi_2\), expand the second weight, and use
\[
\binom a2\binom{a-2}{m-2}
=\binom am\binom m2.
\]
The coefficient ratios are:

| Target | Coefficient ratio | Range |
|---|---:|---|
| \(H_j\) | \(\dfrac{jm(m-1)}{2(m-j-1)}\) | \(j\ge2,\ m\ge2j+1\) |
| \(V_j\) | \(\dfrac{j(m-2)^2}{2(m-j-1)}\) | \(j\ge2,\ m\ge2j+1\) |
| \(W_j\) | \(\dfrac{j(m-2)(m-3)}{2(m-j-1)}\) | \(j\ge2,\ m\ge2j+1\) |
| \(C_j\) | \(\dfrac{(j+1)m(m-1)}{2(m-j-1)}\) | \(j\ge1,\ m\ge2j+2\) |

Here \(C_j\) denotes the combined profile move \(W^f_{2j+2,j+1}\).

The ratios increase with \(j\) at fixed \(m\). At the smallest permitted \(j\), they satisfy
\[
\frac{m(m-1)}{m-3}\ge10,\qquad
\frac{(m-2)^2}{m-3}\ge\frac92,\qquad
m-2\ge3,
\]
and
\[
\frac{m(m-1)}{m-2}\ge6.
\]
The nontrivial polynomial checks are
\[
(m-5)(m-6)\ge0,\quad
(m-5)(2m-7)\ge0,\quad
(m-3)(m-4)\ge0
\]
on the respective integer ranges. Hence
\[
\boxed{
\begin{aligned}
B_0H_{j-1}'&\ge10c_{\ell+1}H_j,\\
B_0V_{j-1}'&\ge\tfrac92c_{\ell+1}V_j,\\
B_0W_{j-1}'&\ge3c_{\ell+1}W_j,\\
B_0C_{j-1}'&\ge6c_{\ell+1}C_j.
\end{aligned}}
\tag{20}
\]

### Completion of the affine theorem

For \(\tau=0\), Newton\((c)\) is log-concave by the same affine coefficient identity used in the existing proof; that identity requires \(r>0,t\ge0\), not the slope bound. The corresponding \(B\)-detour coefficient ratio is
\[
\frac{jm(m-1)}{2(m-j-2)}
\ge\frac{m(m-1)}{2(m-3)}
\ge5\ge4.
\]
The penultimate inequality is equivalent to
\[
(m-5)(m-6)\ge0
\]
for integral \(m\ge4\). The full Newton-coefficient expansion is included in the proof file linked below. This uses the existing affine \(B\)-argument and finite resummation.

Thus (16) and (20) give
\[
P^2\ge4Q,\quad
H_+P\ge4H_-,\quad
V_+P\ge4V_-,\quad
C_+P\ge4C_-,
\]
\[
A_0P+PA_0+2V_1\ge4H_1.
\]
For \(G=(I-P/2)^{-1}\),
\[
(I-P/4)G=\tfrac12G+\tfrac12I.
\]
Therefore
\[
GCG\ge0,\qquad G(H_+-H_-)G\ge0,\qquad
G(V_+-V_-)G\ge\tfrac12GV_1G,
\]
and
\[
\begin{aligned}
GAG
&\ge G(A_0-H_1+V_1/2)G\\
&\ge G\{A_0-(A_0P+PA_0)/4\}G\\
&=\tfrac12(GA_0+A_0G)\ge0.
\end{aligned}
\]
Together with \(U+P^2/4-Q\ge0\), this proves \(M\ge0\) and hence (P).

A strict extension of the old theorem is
\[
N=4,\qquad d_i=\frac{2^i-1}{15},\qquad r=\frac12,\qquad t=\frac1{10}.
\]
Its Newton coefficients are all \(1/15\), and
\[
b=(0,2/75,3/50,7/75,1/10)
\]
is increasing, although \((2N-1)t=7/10>1/2\).

## 4. A nonlinear subclass: quadratic profiles

Suppose all of (Q) holds and, additionally,
\[
d_i=\nu_1i+\nu_2\binom i2,\qquad \nu_1>0,\quad \nu_2\ge0.
\]
Then **\(M\ge0\) and (P) hold for every admissible convex quadratic ratio**.

At a source, write
\[
u=d_\ell,\quad v=f_1(\ell),\quad w=f_2(\ell)=\nu_2,\quad
p=\rho(\ell+1).
\]
Convexity gives \(u\le\ell v\). The product rule gives
\[
\begin{aligned}
\varphi_2(\ell)&\ge pw+\tau X,
&X&=u+2(\ell+1)v,\\
\varphi_2(\ell+1)&\ge pw+\tau Y,
&Y&=u+v+2(\ell+2)(v+w).
\end{aligned}
\]
Moreover,
\[
X+Y-6(u+v)
=-4u+(4\ell+1)v+(2\ell+4)w\ge0.
\]
Consequently,
\[
\varphi_2(\ell)\varphi_2(\ell+1)
\ge p\tau w(X+Y)
\ge6p\tau w(u+v)
=c_{\ell+1}\varphi_4(\ell),
\]
where \(\varphi_4=6\tau w\).

Only \(B_1=\binom a4\varphi_4\) can be a negative \(B\)-move, and
\[
\begin{aligned}
B_0(\ell,a)B_0(\ell+1,a-2)
&\ge
\binom a2\binom{a-2}2
\varphi_2(\ell)\varphi_2(\ell+1)\\
&\ge6c_{\ell+1}B_1.
\end{aligned}
\]
All \(H_j\) vanish. For orders \(3,4\), \(\psi_n=-v_n-w_n\le0\), so the signed \(A_1\)-move is nonnegative. All \(A_j\), \(j\ge2\), vanish, and only the nonnegative \(C_0\) profile move remains.

Thus \(P=B_0\), \(Q=B_1\), \(P^2\ge6Q\), and every other contribution to the middle operator is nonnegative. This proves the claim.

## 5. The \(W\)-constant is exactly \(3\), not \(4\)

The bound \(\mu_W=3\) in (20) is optimal for the proposed scalar detour.

Take \(a=5\), \(j=2\), \(N=\ell+5\), and
\[
d_i=\frac{(1+\varepsilon)^i-1}{(1+\varepsilon)^N-1}.
\]
Fix \(0<r<1\), set \(t=0\), and let \(\tau\downarrow0\). For each fixed profile, sufficiently small positive \(\tau\) satisfies (2), so these are members of (Q).

At this source,
\[
W_2=10\tau f_3(\ell),\qquad
W_1'=3\tau f_1(\ell+1),
\]
and direct substitution gives
\[
\lim_{\tau\downarrow0}
\frac{B_0W_1'}{c_{\ell+1}W_2}
=
3\left(1+\varepsilon+\frac{\varepsilon^2}{2}
+\frac{\varepsilon^3}{10}\right)
\frac{(1+\varepsilon)^{\ell+1}}
{(1+\varepsilon)^{\ell+1}-1}.
\tag{21}
\]
Taking \(\ell\) large and then \(\varepsilon\) small makes this arbitrarily close to \(3\).

There is an explicit rational obstruction to \(\mu_W=4\) already at
\[
N=18,\qquad
d_i=\frac{(6/5)^i-1}{(6/5)^{18}-1},\qquad
r=\frac12,\quad t=0,\quad\tau=\frac1{10^8}.
\]
This lies in (Q): \(R<5\), so the left side of (2) is less than \(238/10^8<1/2\). At \((\ell,a,j)=(13,5,2)\),
\[
\boxed{
\frac{B_0(13,5)W_1(14,3)}
{c_{14}W_2(13,5)}
=
\frac{2989610709944095234194}
{752716458181043929375}
<4.
}
\]
This refutes only the stronger \(W\)-detour—not (P) or \(M\ge0\).

Under your stated budget, the optimal uniform \(W\)-allowance from this detour is therefore
\[
\gamma_W=4(1-2/3)=\frac43,
\]
rather than \(2\). The improved \(V\)-constant retains \(5/9\) of \(V_1\). Consequently, together with the \(B\)-detour, it would suffice for unrestricted (Q) to prove the weaker key inequality
\[
\boxed{
A_0B_0'+B_0A_0''
\ge c_{\ell+1}
\left(4H_1-\frac{20}{9}V_1-\frac43W_1\right).
}
\tag{22}
\]
I do not prove (22) for arbitrary-degree profiles.

## Files and verification

[Complete proof, including the affine Newton\((c)\) expansion](sandbox:/mnt/data/consult6/consult-round6.md)  
[Self-contained exact-rational audit script](sandbox:/mnt/data/consult6/verify_round6.py)

The deterministic audit passed **25,160 scalar checks**, including 1,269 affine key instances, the intermediate endpoint identities, the stated mixed detours, the quadratic-profile bounds, and the exact obstruction to \(W\)-constant \(4\). These are diagnostics, not a Lean verification.

The remaining general-(Q) gap is the \(B\)-detour and a quadratic-ratio key inequality such as (22). The affine extension, quadratic-profile subclass, mixed detours, and sharp \(W\)-constant above do not depend on resolving that gap.
