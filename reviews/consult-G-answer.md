**The original \(S,Z\) basis works.** The missing step is a two-sided resummation of the even \(B\)-moves, after splitting \(A_j\) into two nonnegative pieces. A negative even \(A_j\) does not need its own positive two-step detour.

In fact, the argument proves the slightly larger slope range
\[
\boxed{\kappa\le \frac{N}{2N-1}(1-r).}
\]

## 1. Statement and difference inequalities

Put
\[
s=1-r,\qquad t=\frac{\kappa}{N}.
\]
Assume
\[
\boxed{(2N-1)t\le s.}\tag{T}
\]
Under your hypotheses on \(d\), every coefficient \(\omega_{\ell,a}\) of every \(K_k\) is nonnegative. Consequently, property (P) holds, including terminal products.

I use your general kernel recurrence, with its stated normalization and finite triangular support. This is also the recurrence recorded in the manuscript’s varying-ratio section.

Write
\[
D_n(\ell)=\Delta^n d(\ell).
\]
The sequences \((D_n(\ell))_n\) are log-concave: the operation \(u_i\mapsto u_i+u_{i+1}\) preserves log-concavity, since its log-concavity difference is
\[
(u_i^2-u_{i-1}u_{i+1})
+(u_{i+1}^2-u_i u_{i+2})
+(u_i u_{i+1}-u_{i-1}u_{i+2})\ge0.
\]
The last term is a balanced-product inequality for a log-concave sequence.

The consequence needed below is
\[
\boxed{
D_i(\ell)D_j(\ell+1)
\ge d_{\ell+1}D_{i+j}(\ell)
\qquad(i,j\ge1).
}\tag{1}
\]
Indeed, for \(u_n=D_n(\ell)\), add
\[
u_i u_j\ge u_0u_{i+j},
\qquad
u_i u_{j+1}\ge u_1u_{i+j}.
\]
These follow by multiplying nonincreasing successive ratios; zero endpoints follow directly or by continuity.

The affine ratio gives
\[
\begin{aligned}
f_n(\ell):=\Delta^n c(\ell)
&=(r+t(\ell+n))D_n(\ell)+tnD_{n-1}(\ell),\\
\Delta^n b(\ell)&=h_n(\ell)-v_n(\ell),\\
h_n(\ell)&=(s-t(\ell+n))D_n(\ell),\\
v_n(\ell)&=tnD_{n-1}(\ell).
\end{aligned}\tag{2}
\]
Here \(n\ge1\). Both \(h_n,v_n\) are nonnegative whenever \(\ell+n\le N\).

### Log-concavity of \(\operatorname{Newton}(c)\) is automatic

Let \(\nu_i=\Delta^i d(0)\), with \(\nu_{-1}=\nu_0=0\). The Newton coefficients of \(c\) are
\[
\eta_i=p_i\nu_i+q_i\nu_{i-1},
\qquad p_i=r+ti,\quad q_i=ti.
\]
Direct expansion gives
\[
\begin{aligned}
\eta_i^2-\eta_{i-1}\eta_{i+1}
={}&p_i^2(\nu_i^2-\nu_{i-1}\nu_{i+1})
+q_i^2(\nu_{i-1}^2-\nu_{i-2}\nu_i)\\
&+q_{i-1}p_{i+1}(\nu_i\nu_{i-1}-\nu_{i-2}\nu_{i+1})\\
&+t^2(\nu_{i-1}\nu_{i+1}+\nu_{i-2}\nu_i+2\nu_i\nu_{i-1})
\ge0.
\end{aligned}\tag{3}
\]
Its positive support is an interval. Thus (1) also holds for \(f\), with \(d_{\ell+1}\) replaced by \(c_{\ell+1}\).

Natural polynomial extension or truncation at Newton order \(N\) gives the same differences used inside the triangle.

Since
\[
f_2(\ell)\ge (r+t(\ell+1))D_2(\ell),
\]
equation (1) further gives
\[
\begin{aligned}
f_2(\ell)D_n(\ell+1)&\ge c_{\ell+1}D_{n+2}(\ell),\\
f_2(\ell)h_n(\ell+1)&\ge c_{\ell+1}h_{n+2}(\ell),\\
f_2(\ell)v_n(\ell+1)&\ge
\frac{n}{n+2}c_{\ell+1}v_{n+2}(\ell).
\end{aligned}\tag{4}
\]
For the second inequality, use
\[
s-t(\ell+n+1)\ge s-t(\ell+n+2)\ge0.
\]
The third follows from (1) with indices \(2,n-1\), multiplied by \(tn(r+t(\ell+1))\); it is only needed for \(n\ge3\).

## 2. Split the \(A\)-moves, but leave \(A_0\) unsplit

Using your \(W\)-notation, define, for \(j\ge1\),
\[
H_j=W^h_{2j+1,j},
\qquad
V_j=W^v_{2j+1,j}.
\]
Then
\[
\boxed{A_j=H_j-V_j,}\tag{5}
\]
with both pieces nonnegative.

Retain
\[
A_0(\ell,a)=b_{\ell+a}-b_\ell
\]
as one move. It is nonnegative under (T). Indeed, put
\[
\alpha=s-t(\ell+a).
\]
Convexity of \(d\), together with \(d_0=0\), gives
\[
d_\ell\le \ell D_1(\ell),
\qquad
d_{\ell+a}-d_\ell\ge aD_1(\ell),
\qquad
\alpha\ge t(\ell+a-1).
\]
Therefore, for \(a\ge1\),
\[
\begin{aligned}
A_0
&=\alpha(d_{\ell+a}-d_\ell)-ta d_\ell\\
&\ge a(\alpha-t\ell)D_1(\ell)
\ge ta(a-1)D_1(\ell)\ge0.
\end{aligned}\tag{6}
\]

Thus all individual \(H_j,V_j,B_j,C_j,A_0\) used below are nonnegative.

## 3. Four ordinary detour inequalities

Suppress \((\ell,a)\) on first factors and right sides. Every second factor in the following display has arguments \((\ell+1,a-2)\):
\[
\begin{aligned}
B_0B_{j-1}&\ge4c_{\ell+1}B_j &&(j\ge1),\\
B_0H_{j-1}&\ge6c_{\ell+1}H_j &&(j\ge2),\\
B_0V_{j-1}&\ge6c_{\ell+1}V_j &&(j\ge2),\\
B_0C_{j-1}&\ge6c_{\ell+1}C_j &&(j\ge1).
\end{aligned}\tag{7}
\]

Here is an explicit coefficient verification. Retain
\[
B_0(\ell,a)\ge\binom a2f_2(\ell),
\]
expand the second weight, apply (1) for \(f\) or apply (4), and use
\[
\binom a2\binom{a-2}{n-2}
=\binom an\binom n2.
\]
The resulting ratios to the target coefficients are respectively
\[
\frac{jn(n-1)}{2(n-j-2)},\quad
\frac{jn(n-1)}{2(n-j-1)},\quad
\frac{j(n-1)(n-2)}{2(n-j-1)},\quad
\frac{(j+1)n(n-1)}{2(n-j-1)}.\tag{8}
\]

The first range is \(n\ge2j+2\), the middle ranges are \(n\ge2j+1\), and the last is \(n\ge2j+2\). Each ratio increases with \(j\) at fixed \(n\).

The first is at least \(5\): at \(j=1\), this is equivalent to
\[
(n-5)(n-6)\ge0
\]
for integer \(n\ge4\). For \(j\ge2\), the third is at least
\[
\frac{(n-1)(n-2)}{n-3}
=n+\frac2{n-3}\ge6,
\]
and the second is larger. The last is at least
\[
\frac{n(n-1)}{n-2}
=n+1+\frac2{n-2}\ge6.
\]
This proves (7).

## 4. The additional lowest-index inequality

The key new inequality is
\[
\boxed{
\begin{aligned}
&A_0(\ell,a)B_0(\ell+1,a-1)
+B_0(\ell,a)A_0(\ell+1,a-2)\\
&\hspace{22mm}\ge
c_{\ell+1}\bigl(4H_1(\ell,a)-2V_1(\ell,a)\bigr).
\end{aligned}
}\tag{9}
\]

Only \(a\ge3\) needs proof. Write
\[
u_n=D_n(\ell),\qquad D=u_0+u_1=d_{\ell+1},
\]
and define
\[
\begin{aligned}
X&=\sum_{i\ge1}\binom aiu_i,
&Y&=\sum_{i\ge2}\binom aiu_i,\\
X'&=\sum_{j\ge1}\binom{a-2}j(u_j+u_{j+1}),
&Y'&=\sum_{j\ge2}\binom{a-1}j(u_j+u_{j+1}).
\end{aligned}
\]
With \(\alpha=s-t(\ell+a)\),
\[
A_0(\ell,a)=\alpha X-ta u_0,
\qquad
A_0(\ell+1,a-2)=(\alpha+t)X'-t(a-2)D.
\]
The two corresponding \(B_0\)'s are at least
\[
(r+t(\ell+1))Y,\qquad (r+t(\ell+1))Y'.
\]
Because both \(A_0\)'s are nonnegative, the left side of (9), divided by \(c_{\ell+1}\), is at least
\[
\alpha\frac{XY'+YX'}D-t\{aY'+(a-2)Y\}.\tag{10}
\]
Here we discarded \(tYX'/D\ge0\) and used \(u_0\le D\).

**Keep all derivative orders in these products**, rather than only their first summands. This gives
\[
\frac{XY'+YX'}D
\ge\sum_{n=3}^a\gamma_n\binom an u_n,
\qquad
\gamma_n=2(2^n-n-2).\tag{11}
\]
To verify this, use \(u_i(u_j+u_{j+1})\ge Du_{i+j}\). In \(XY'\), where \(i\ge1,j\ge2\),
\[
\binom ai\binom{a-1}j
\ge\binom ai\binom{a-i}j.
\]
In \(YX'\), where \(i\ge2,j\ge1\), use
\[
\binom{a-2}j\ge\binom{a-i}j.
\]
At \(i+j=n\), each binomial sum is \(2^n-n-2\). Terms with \(i+j>a\) are nonnegative and can be discarded.

The remaining quantities have the explicit expansions
\[
aY'+(a-2)Y
=2(a-2)\binom a2u_2
+2(a-1)\sum_{n=3}^a\binom an u_n,
\]
\[
H_1=\sum_{n=3}^a(n-2)\binom an
[\alpha+t(a-n)]u_n,
\qquad
V_1=t\sum_{n=2}^a(n-1)(a-n)\binom an u_n.\tag{12}
\]

Subtract \(4H_1-2V_1\) from the lower bound (10)–(11), and remove the nonnegative factors \(\binom an u_n\).

At \(n=2\), the remaining coefficient is zero. At \(n=3\), it is
\[
2\alpha-2t(a-1)\ge2t\ell\ge0.
\]
For \(n\ge4\), use
\[
\gamma_n\ge8(n-2)+2.
\]
This holds at \(n=4\); thereafter \(\gamma_n\) increases by \(2^{n+1}-2\ge8\).

Using also \(\alpha\ge t(a-1)\), and discarding the nonnegative term \(2t(n-1)(a-n)\), the coefficient is at least
\[
\begin{aligned}
&t(a-1)[4(n-2)+2]
-2t(a-1)-4t(a-n)(n-2)\\
&\qquad=4t(n-1)(n-2)\ge0.
\end{aligned}
\]
This proves (9).

## 5. Positive two-sided resummation

Now regard each move as an operator on \(\Omega_N\), divided by \(c\) at its destination level. Every operator strictly raises \(\ell\). All inequalities in this section are entrywise.

Let
\[
P=\sum_{j\ {\rm even}}B_j,\qquad
Q=\sum_{j\ {\rm odd}}B_j,\qquad
C=C_+-C_-,
\]
where \(C_+,C_-\) collect the even and odd \(C_j\). Define
\[
\begin{aligned}
H_+&=\sum_{\substack{j\ge2\\j\ {\rm even}}}H_j,
&H_-&=\sum_{\substack{j\ge3\\j\ {\rm odd}}}H_j,\\
V_+&=\sum_{\substack{j\ge1\\j\ {\rm odd}}}V_j,
&V_-&=\sum_{\substack{j\ge2\\j\ {\rm even}}}V_j,
\end{aligned}
\]
and
\[
A=A_0+H_+-H_--H_1+V_+-V_-.
\]
The original recurrence becomes
\[
\omega=\beta+(U+P-Q+C+A)\omega,
\]
where \(U\ge0\) consists of the straight moves and \(\beta\ge0\) is the initial data.

Equations (7) and (9) give
\[
\boxed{
\begin{gathered}
P^2\ge4Q,\qquad
H_+P\ge6H_-,\qquad
V_+P\ge6V_-,\qquad
C_+P\ge6C_-,\\
A_0P+PA_0+2V_1\ge4H_1.
\end{gathered}
}\tag{13}
\]
For example, \(H_+P\) uses \(B_0\) followed by \(H_{j-1}\). Its extra intermediate denominator is exactly \(c_{\ell+1}\), as in (7). The two paths in (9) give \(A_0P+PA_0\) at displacement \((2,-3)\).

Set
\[
G=(I-P/2)^{-1}
=\sum_{m=0}^{N}(P/2)^m\ge0,
\qquad
R=U+P^2/4-Q\ge0.
\]
Since
\[
(I-P/6)G=\frac23G+\frac13I,
\]
equation (13) implies
\[
GCG\ge0,\qquad
G(H_+-H_-)G\ge0,
\]
and
\[
G(V_+-V_-)G
\ge\frac23GV_+G
\ge\frac23GV_1G.
\]
Consequently,
\[
\begin{aligned}
GAG
&\ge G[A_0-H_1+\tfrac23V_1]G\\
&\ge G[A_0-\tfrac14(A_0P+PA_0)+\tfrac16V_1]G\\
&=\frac12(GA_0+A_0G)+\frac16GV_1G
\ge0.
\end{aligned}\tag{14}
\]
The equality uses \(PG=GP=2(G-I)\).

Thus
\[
M:=G(R+C+A)G
\]
is nonnegative and strictly raises the level. With
\[
v=(I-P/2)\omega,
\]
the original recurrence is equivalent to
\[
v=G\beta+Mv.
\]
Therefore
\[
\boxed{
\omega
=G\left(\sum_{q=0}^{N}M^q\right)G\beta
\ge0.
}\tag{15}
\]
Every sum terminates. This proves positivity throughout \(\Omega_N\), for every initial kernel \(K_k\). Substitution \(S=z+w,\ Z=zw\), followed by the positive normalization back to \(R_i\), proves (P).

## 6. Relation to your questions and Theorem 8.6

Your negative \(A_2\) example is compatible with this proof. The positive piece \(V_1\) of the signed \(A_1\)-move is retained separately: (9) spends at most half of it on \(H_1\), while the \(B\)-resummation retains at least two thirds. Equation (14) makes the remaining margin explicit. No positive two-step detour for the merged negative \(A_2\) entry is required.

The operator conditions (13), with the displayed decomposition, also give a sufficient inequality class **containing Theorem 8.6**. For that theorem, take \(V_j=0\) and \(H_j=A_j^b\). Its mixed inequalities give the \(H\)- and \(C\)-inequalities in (7), and its two ordered \(A_1\)-detours give (9) with \(V_1=0\). The same factorization applies.

No extra hypothesis on \(\operatorname{Newton}(\rho d)\) is needed: (3) shows it is automatic. The proof covers the original slope bound, the larger bound (T), arbitrary permitted profile degree, and the regime \(\rho_N\to1\).

The exact verifier passed **57 full-operator cases**, including your \(N=5\) example and the larger slope endpoint. It checks 398 instances of (9), all inequalities (13), nonnegativity of the entire original Green matrix, and equality with the inverse formula (15). These checks supplement the all-size argument above.

[Proof note](sandbox:/mnt/data/affine_ratio_kernel_proof.md) · [Exact-arithmetic verifier](sandbox:/mnt/data/affine_ratio_kernel_verify.py)
