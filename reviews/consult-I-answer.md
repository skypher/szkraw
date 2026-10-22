**The whole class (Q) works:** the same resummed operator satisfies \(M\ge0\), and hence (P).

There is one important distinction: **the proposed unit-constant scalar \(B\)-detour is false**, but an order-dependent scalar inequality gives exactly the required summed detour. The two new estimates are
\[
\boxed{
(n+1)(n+2)\varphi_2(\ell)\varphi_n(\ell+1)
\ge 8(n-1)c_{\ell+1}\varphi_{n+2}(\ell)
\qquad(n\ge2),
}
\tag{1}
\]
and
\[
\boxed{
A_0(\ell,a)B_0(\ell+1,a-1)
+B_0(\ell,a)A_0(\ell+1,a-2)
\ge c_{\ell+1}(4H_1-2V_1-W_1).
}
\tag{2}
\]
Thus the key inequality holds with \((\gamma_V,\gamma_W)=(2,1)\), stronger than the requested \((20/9,4/3)\).

The complete proof and executable audit are also available as files: [proof](sandbox:/mnt/data/round7/consult-round7.md), [verification script](sandbox:/mnt/data/round7/verify_round7.py), [audit output](sandbox:/mnt/data/round7/audit-output.txt).

I use your existing move definitions, mixed detours, and finite resummation. The arguments below supply the two missing inequalities; they do not assume log-concavity of Newton\((c)\).

## 1. The key inequality

Fix an admissible source with \(a\ge3\). By homogeneity normalize
\[
u_n=f_n(\ell),\qquad u_1=1,
\]
and write
\[
z=u_0,\quad q=u_2,\quad D=z+1,\quad y_n=\binom an u_n.
\]
Use the affine-proof notation
\[
\begin{aligned}
Y&=\sum_{n=2}^a y_n,& X&=a+Y,\\
J&=\sum_{n=2}^{a-1}\binom{a-1}n u_n,& X'&=a-2+J,\\
Y'&=Y-(a-1)q,\\
H_*&=\sum_{n=3}^a(n-2)y_n,&
T_*&=\sum_{n=2}^a(n-3)(a-n)y_n.
\end{aligned}
\]

### 1.1. Retain the affine surplus

The additional fact needed from the affine interpolation is
\[
\boxed{
\begin{aligned}
&(\alpha X-sa z)Y'
+Y\bigl((\alpha+s)X'-s(a-2)D\bigr)
-D(4\alpha H_*+2sT_*)\\
&\hspace{35mm}\ge \frac23sD(a-2)y_2
\qquad(\alpha\ge sz,\ s\ge0).
\end{aligned}}
\tag{3}
\]

Here is the verification, including the surplus that was discarded in round 6.

The coefficient of \(\alpha\) is
\[
K=XY'+YX'-4DH_*.
\]
The profile inequalities
\[
u_i(u_j+u_{j+1})\ge Du_{i+j}
\]
give
\[
K\ge
D\sum_{n=3}^a
\left[n+\binom n2-4(n-2)\right]y_n
=
\frac D2\sum_{n=3}^a
\bigl((n-3)(n-4)+4\bigr)y_n
\ge0.
\tag{4}
\]
It therefore suffices to set \(\alpha=sz\). The resulting expression is \(sF(z)\), where
\[
F(z)=zYY'+(z+1)YJ-(z+1)(4zH_*+2T_*).
\]

If \(q=0\), all \(u_n\), \(n\ge2\), vanish. Otherwise \(0\le z\le1/q\). Put
\[
L_3=\frac32,\qquad L_n=\frac{n(n+2)}6\quad(n\ge4),
\qquad E_n=\frac{2(n^2-5)}{n+1}.
\]
The selected-product bounds from the affine argument are
\[
YJ\ge\sum_{n=3}^{a-1}L_n(a-n)y_n,
\qquad
\frac{YY'}{q+1}\ge
\sum_{n=3}^a\frac{n(a-1)}2y_n.
\tag{5}
\]
For completeness, the first retains \((2,2)\) at order \(3\), and \((2,n-1),(3,n-2)\) thereafter, using \(u_i u_{n+1-i}\ge u_n\). The second retains \(\binom a2q\) in \(Y\), using
\[
q(u_{n-1}+u_n)\ge(q+1)u_n,
\qquad
\binom a2\binom{a-1}{n-1}
=\frac{n(a-1)}2\binom an.
\]

The numerical comparisons are
\[
L_n\ge2(n-3),\qquad L_n+n/2\ge E_n.
\tag{6}
\]
At \(n=3\) these are immediate. For \(n\ge4\),
\[
6[L_n-2(n-3)]=(n-5)^2+11,
\]
\[
6(n+1)[L_n+n/2-E_n]
=(n-4)^3+6(n-4)^2+5(n-4)+48.
\]

Consequently,
\[
F(0)\ge2(a-2)y_2.
\tag{7}
\]
At the other endpoint, \(u_n/q\le u_{n-1}\) gives
\[
\frac4qH_*+2T_*
\le\sum_{n=2}^{a-1}E_n(a-n)y_n.
\]
Since \(E_2=-2/3\), retaining its contribution yields
\[
\frac{F(1/q)}{1+1/q}
=
YJ+\frac{YY'}{q+1}-\frac4qH_*-2T_*
\ge\frac23(a-2)y_2.
\tag{8}
\]
Finally,
\[
F(z)=(1-qz)F(0)+qzF(1/q)+4H_*z(1/q-z).
\]
Subtracting the linear function \(\frac23(z+1)(a-2)y_2\), equations (7)–(8) prove (3).

### 1.2. Compare the quadratic ratio with the right-endpoint affine ratio

Set
\[
s=t+\tau(\ell+a-1),\qquad
\alpha=1-\rho(\ell+a),\qquad p=\rho(\ell+1).
\]
Monotonicity of \(b\), together with monotonicity of \(R_i=d_i/f_1(i)\), gives
\[
\alpha\ge sR_{\ell+a-1}\ge sz,
\qquad s\ge\tau(a-1).
\tag{9}
\]

Write \(A=A_0(\ell,a)\), \(A''=A_0(\ell+1,a-2)\). Exact backward differences give
\[
A=\alpha X-sa z+\tau\binom a2z,
\]
\[
A''=(\alpha+s)X'-s(a-2)D
+\tau\binom{a-1}2D.
\tag{10}
\]
Both are nonnegative. Moreover,
\[
B_0(\ell,a)\ge pY,\qquad
B_0(\ell+1,a-1)\ge pY',\qquad c_{\ell+1}=pD.
\tag{11}
\]
Thus it suffices to prove
\[
AY'+YA''\ge D(4H_1-2V_1-W_1).
\tag{12}
\]

Put
\[
Z=\sum_{n=2}^a\binom{a-n}2y_n.
\]
Reindexing gives the exact identities
\[
4H_1-2V_1=4\alpha H_*+2sT_*+4\tau Z,
\tag{13}
\]
\[
W_1=\tau\sum_{n=1}^a n\binom{a-n}2y_n.
\tag{14}
\]
For (13), use
\[
1-\rho(\ell+n)
=\alpha+(a-n)s-\tau\binom{a-n}2,
\]
while the reindexed \(V_1\)-summand is
\[
(n-1)(a-n)[s-\tau(a-n-1)]y_n.
\]

Let \(\mathcal D\) denote the difference in (12). Applying (3), then \(s\ge\tau(a-1)\), gives the explicit certificate
\[
\boxed{
\begin{aligned}
\mathcal D\ge\tau\Bigg\{
&\binom a2zY'
+D\Bigg[
\binom{a-1}2y_1
+\frac{(a-2)(a+11)}6y_2
+(2a-5)y_3\\
&\qquad\qquad+
\sum_{n=4}^a
\left(
\binom{a-1}2+(n-4)\binom{a-n}2
\right)y_n
\Bigg]\Bigg\}\ge0.
\end{aligned}}
\tag{15}
\]
The two potentially problematic coefficients are exactly
\[
\frac23(a-1)(a-2)+\binom{a-1}2-2\binom{a-2}2
=\frac{(a-2)(a+11)}6,
\]
\[
\binom{a-1}2-\binom{a-3}2=2a-5.
\]
All remaining coefficients are visibly nonnegative.

This proves (2). When \(q=0\), \(H_1=V_1=0\), so the result is immediate.

## 2. The weighted scalar \(B\)-detour

We prove (1). Throughout this section put
\[
K_n=(n+1)(n+2),\qquad L_n=8(n-1).
\]

Normalize \(u_1=1\), and let \(z=u_0\), \(q=u_2\), \(p=\rho(\ell+1)\). Convexity and log-concavity give
\[
u_0\le\ell u_1,\qquad u_0u_2\le u_1^2,
\]
hence
\[
0\le z\le\min(\ell,1/q).
\tag{16}
\]

If \(q=0\), or \(u_n=0\), then \(\varphi_{n+2}=0\). Assume both are positive.

### 2.1. Reduce the tail to a geometric tail

Set \(y=u_{n+1}/u_n\). Log-concavity gives
\[
0\le y\le q,\qquad u_{n+2}\le y^2u_n.
\tag{17}
\]
For \(n\ge3\), it also gives
\[
u_{n-1}\ge u_n/q,\qquad u_{n-2}\ge u_n/q^2.
\]
Therefore
\[
\begin{aligned}
\frac{\varphi_n(\ell+1)}{u_n}\ge\mathcal L(y):={}&
\rho(\ell+n+1)(1+y)\\
&+n[t+\tau(\ell+n)](1+q^{-1})\\
&+\binom n2\tau(q^{-1}+q^{-2}).
\end{aligned}
\tag{18}
\]
For \(n=2\), use instead the exact formula
\[
\mathcal L(y)=
\rho(\ell+3)(1+y)
+2[t+\tau(\ell+2)](1+q^{-1})
+\tau(z+1)/q.
\tag{19}
\]
In both cases \(\mathcal L(y)=A+By\), with \(A\ge B\ge0\).

The target satisfies
\[
\frac{\varphi_{n+2}(\ell)}{u_n}
\le\mathcal T(y):=
\rho(\ell+n+2)y^2
+(n+2)[t+\tau(\ell+n+1)]y
+\binom{n+2}2\tau.
\tag{20}
\]
Consider
\[
\mathcal F(y)=K_n\varphi_2(\ell)\mathcal L(y)
-L_np(z+1)\mathcal T(y).
\]
It is concave. Also,
\[
\mathcal L(0)\ge\frac{\mathcal L(q)}{1+q},
\qquad
\mathcal T(q)\ge(1+q)\mathcal T(0),
\]
the latter because
\[
(n+2)[t+\tau(\ell+n+1)]
\ge(n+2)(n+1)\tau
\ge\binom{n+2}2\tau.
\]
Thus
\[
\mathcal F(0)\ge\frac{\mathcal F(q)}{1+q}.
\]
It suffices to check \(\mathcal F(q)\ge0\), which is precisely the test configuration
\[
u_i=q^{i-1}\quad(i\ge1),\qquad u_0=z.
\tag{21}
\]

### 2.2. Reduce \(z\) to its largest allowed value

For \(n\ge3\), only \(\varphi_2\) and \(c_{\ell+1}\) depend on \(z\), and
\[
\frac{\varphi_2}{z+1}
=\frac{A_2+\tau z}{z+1},
\qquad
A_2=\rho(\ell+2)q+2[t+\tau(\ell+1)]\ge\tau.
\]
This quotient is nonincreasing in \(z\).

For \(n=2\), write
\[
\varphi_2=A_2+\tau z,\qquad
\varphi_2(\ell+1)=G_2+\tau(z+1),
\]
where
\[
G_2=\rho(\ell+3)q(1+q)
+2[t+\tau(\ell+2)](1+q).
\]
For \(z\le Z\le\ell\), the difference between the quotients
\(\varphi_2\varphi_2(\ell+1)/(z+1)\) at \(z\) and \(Z\) is
\[
(Z-z)\left[
\frac{G_2(A_2-\tau)}{(z+1)(Z+1)}-\tau^2
\right]\ge0,
\tag{22}
\]
since
\[
G_2(A_2-\tau)
\ge2(\ell+2)(2\ell+1)\tau^2
\ge(\ell+1)^2\tau^2.
\]
The last difference is \((3\ell^2+8\ell+3)\tau^2\).

Hence in every case it suffices to take
\[
z=\min(\ell,1/q).
\tag{23}
\]

### 2.3. The polynomial certificate

We need the following algebraic lemma.

For integer \(n\ge2\), \(h\ge1\), \(p,\tau\ge0\), and \(s\ge(h-1)\tau\), define
\[
A=p+(2h-1)s+h^2\tau,
\]
\[
B=p+nh(s+\tau)+\binom n2h^2\tau,
\]
\[
C=p+[(n+2)h-1]s+\binom{n+2}2h^2\tau.
\]
Then
\[
\boxed{K_nAB-L_npC\ge0.}
\tag{24}
\]

Here is a finite, explicit certificate. Set
\[
a_n=n^2-5n+10=(n-2)(n-3)+4>0,
\]
\[
U_n=n^4-4n^3-21n^2+12n+60,
\]
\[
C_n(h)=
\frac{h^2U_n+h(10n^2+14n-60)+2a_n}{2},
\]
\[
D_n(h)=
\frac{h^2n(n+1)^2(n+2)(3h^2-3h+1)}2.
\]
The expression in (24) is nondecreasing in \(s\ge0\): its \(ps\)-coefficient is
\[
a_n[(n+2)h-1]\ge0,
\]
and all its other \(s\)-dependent coefficients are nonnegative. At \(s=(h-1)\tau\), it equals
\[
a_np^2+C_n(h)p\tau+D_n(h)\tau^2.
\tag{25}
\]

For \(n\ge7\), all three coefficients are nonnegative. Indeed, with \(k=n-7\),
\[
U_n=k^4+24k^3+189k^2+502k+144>0.
\]

For \(n=2,\ldots,6\), write \(v=h-1\). The coefficients of
\(4a_nD_n-C_n^2\), in increasing powers of \(v\), are:

| \(n\) | \(v^0\) | \(v^1\) | \(v^2\) | \(v^3\) | \(v^4\) |
|---:|---:|---:|---:|---:|---:|
| 2 | 576 | 2880 | 5616 | 4992 | 1664 |
| 3 | 1520 | 6240 | 9744 | 7200 | 2160 |
| 4 | 6300 | 27000 | 42660 | 30600 | 8604 |
| 5 | 25200 | 126000 | 229500 | 184800 | 56000 |
| 6 | 62720 | 376320 | 774144 | 677376 | 216576 |

Thus
\[
a_np^2+C_np\tau+D_n\tau^2
=
a_n\left(p+\frac{C_n\tau}{2a_n}\right)^2
+\frac{4a_nD_n-C_n^2}{4a_n}\tau^2
\ge0.
\]
This proves (24).

### 2.4. Apply the certificate when \(z=1/q\)

Set
\[
h=1+1/q,\qquad s=t+\tau\ell,\qquad p=\rho(\ell+1).
\]
Because \(\ell\ge1/q=h-1\),
\[
s\ge(h-1)\tau.
\]
For the geometric configuration (21), with \(z=1/q\), the difference in (1), divided by \(q^n(1+q)>0\), is exactly
\[
K_nAB-L_npC.
\]
Thus (24) proves this case.

### 2.5. Apply the certificate when \(z=\ell\)

This second boundary needs an explicit extension certificate.

Write
\[
w=q^{-1}-\ell\ge0,\qquad h_0=\ell+1,\qquad h=h_0+w,
\qquad s=t+\ell\tau.
\]
Define
\[
A(w)=p+(2h-1)s+\tau[(\ell+2)h-\ell-1],
\]
\[
B(w)=p+nh(s+\tau)+\binom n2h^2\tau,
\]
\[
C(w)=p+[(n+2)h-1]s+\binom{n+2}2h^2\tau.
\]
For \(n\ge3\), the difference in (1), divided by \(q^{n+1}\), is
\[
\mathcal E_n(w)=K_n(h_0+w)A(w)B(w)-L_nh_0pC(w).
\tag{26}
\]
At \(w=0\), equation (24) applies.

Write
\[
A(w)=A_0+aw,\quad B(w)=B_0+bw+ew^2,\quad
C(w)=C_0+cw+fw^2,
\]
where
\[
\begin{aligned}
a&=2s+(\ell+2)\tau,\\
b&=n(s+\tau)+n(n-1)\tau h_0,&e&=\binom n2\tau,\\
c&=(n+2)s+(n+2)(n+1)\tau h_0,&f&=\binom{n+2}2\tau.
\end{aligned}
\]
Then
\[
\mathcal E_n(w)=\mathcal E_n(0)+J_1w+J_2w^2
+K_n(ab+A_0e+h_0ae)w^3+K_nae\,w^4,
\tag{27}
\]
with
\[
J_1=K_n[A_0B_0+h_0(aB_0+A_0b)]-L_nh_0pc,
\]
\[
J_2=K_n[aB_0+A_0b+h_0(ab+A_0e)]-L_nh_0pf.
\]

Put \(\bar A=A_0-p\ge0\), \(\bar B=B_0-p\ge0\). Expansion gives
\[
J_1=K_np^2+p(a_1t+b_1\tau)
+K_n[\bar A\bar B+h_0(a\bar B+\bar A b)],
\tag{28}
\]
\[
J_2=p(a_2t+b_2\tau)
+K_n[a\bar B+\bar A b+h_0(ab+\bar A e)],
\tag{29}
\]
where
\[
a_1=(n+2)[2\ell(n^2-n+6)+2n^2-3n+11],
\qquad a_2=K_n(n+2),
\]
\[
b_1=\frac{n+2}{2}[\ell^2P_n+\ell Q_n+R_n],
\]
\[
b_2=\frac{K_n}{2}[3n(n-3)(\ell+1)+14\ell+12],
\]
and
\[
\begin{aligned}
P_n&=3n^3-12n^2-3n+44,\\
Q_n&=6n^3-24n^2+2n+64,\\
R_n&=3n^3-12n^2+7n+22.
\end{aligned}
\]
All coefficients are nonnegative for \(n\ge3\). Explicitly, with \(k=n-3\),
\[
\begin{aligned}
P_n&=3k^3+15k^2+6k+8,\\
Q_n&=6k^3+30k^2+20k+16,\\
R_n&=3k^3+15k^2+16k+16.
\end{aligned}
\]
This proves \(\mathcal E_n(w)\ge0\) for \(n\ge3\).

For \(n=2\), the zeroth entry also appears in the shifted \(\varphi_2\). The exact polynomial is
\[
\widetilde{\mathcal E}_2(w)
=\mathcal E_2(w)-12A(w)\tau w(\ell+w)^2.
\]
Its expansion is
\[
\widetilde{\mathcal E}_2(w)=\mathcal E_2(0)
+\widetilde J_1w+\widetilde J_2w^2
+12a[2t+(3\ell+5)\tau]w^3,
\tag{30}
\]
where
\[
\begin{aligned}
\widetilde J_1={}&12p^2+4(16\ell+13)pt
+8(\ell+1)(2\ell+3)p\tau\\
&+48(\ell+1)(3\ell+2)t^2\\
&+12(36\ell^3+92\ell^2+76\ell+21)t\tau\\
&+12(27\ell^4+93\ell^3+114\ell^2+62\ell+13)\tau^2,
\end{aligned}
\]
\[
\begin{aligned}
\widetilde J_2={}&48pt+12(2\ell+3)p\tau
+24(6\ell+5)t^2\\
&+12(36\ell^2+67\ell+29)t\tau\\
&+12(27\ell^3+78\ell^2+67\ell+19)\tau^2.
\end{aligned}
\]
Every coefficient is nonnegative. This completes the proof of (1).

## 3. Sum the scalar bound

Recall
\[
B_j(\ell,a)=
\sum_{m\ge2j+2}\binom{m-j-2}{j}\binom am\varphi_m(\ell).
\]
Retain \(B_0\ge\binom a2\varphi_2\) and apply (1) to the second factor with \(n=m-2\). Since
\[
\binom a2\binom{a-2}{m-2}
=\binom am\binom m2,
\]
and
\[
\binom m2\,\frac{8(m-3)}{m(m-1)}=4(m-3),
\]
we obtain
\[
B_0B'_{j-1}
\ge4c_{\ell+1}
\sum_{m\ge2j+2}
(m-3)\binom{m-j-3}{j-1}\binom am\varphi_m.
\]
The required coefficient comparison is
\[
(m-3)\binom{m-j-3}{j-1}\ge\binom{m-j-2}{j}.
\]
It is equivalent to
\[
j(m-3)\ge m-j-2
\quad\Longleftrightarrow\quad
(j-1)(m-2)\ge0.
\]
Therefore
\[
\boxed{B_0B'_{j-1}\ge4c_{\ell+1}B_j.}
\tag{31}
\]

Notice that this proof did not use monotonicity of \(b\).

## 4. Finish the resummation

Your mixed detours give
\[
H_+P\ge10H_-,\qquad
V_+P\ge\tfrac92V_-,\qquad
W_+P\ge3W_-,\qquad
C_+P\ge6C_-.
\]
Equation (31) gives \(P^2\ge4Q\).

For \(G=(I-P/2)^{-1}\),
\[
(I-P/\mu)G=(1-2/\mu)G+(2/\mu)I.
\]
Consequently,
\[
G(H_+-H_-)G\ge0,\qquad GCG\ge0,
\]
\[
G(V_+-V_-)G\ge\frac59GV_1G,\qquad
G(W_+-W_-)G\ge\frac13GW_1G.
\]
The new key inequality gives
\[
A_0P+PA_0+2V_1+W_1\ge4H_1.
\]
Hence
\[
\begin{aligned}
GAG
&\ge
G\left[
A_0-\frac14(A_0P+PA_0)
+\frac1{18}V_1+\frac1{12}W_1
\right]G\\
&=
\frac12(GA_0+A_0G)
+\frac1{18}GV_1G+\frac1{12}GW_1G
\ge0.
\end{aligned}
\]
Together with \(U+P^2/4-Q\ge0\), this proves
\[
\boxed{M=G(U+P^2/4-Q+C+A)G\ge0.}
\]
The existing finite resummation then gives \(\omega\ge0\) and (P).

## 5. The unit-constant scalar inequality really fails

Take
\[
N=20,\qquad d_i=\frac{2^i-1}{2^{20}-1},
\qquad r=\frac12,\quad t=0,\quad\tau=\frac1{1000}.
\]
All positive-order Newton coefficients are \(1/(2^{20}-1)\). Moreover,
\[
R=\frac{2^{19}-1}{2^{19}},
\]
and
\[
\tau\left[\binom{20}2+19R\right]
=\frac{109576173}{524288000}
<\frac12=1-r.
\]
Thus this is a member of (Q).

At \((\ell,n)=(16,2)\),
\[
\boxed{
\varphi_2(16)\varphi_2(17)-c_{17}\varphi_4(16)
=
-\frac{11121875309909}{366503176875000000}<0.
}
\]
Equivalently, the ratio is
\[
\frac{1394730453871275}{1405852329181184}<1.
\]

This is only a counterexample to the stronger scalar estimate—not to the summed detour, \(M\ge0\), or (P).

## Verification status

The attached script passed **20,874 exact assertions**, including all displayed polynomial certificates, 1,000 relaxed-local-profile checks, 8,428 summed \(B\)-detours, 4,154 quadratic key inequalities, and 30 full-matrix checks each of \(P^2\ge4Q\) and \(M\ge0\). It also verifies the scalar counterexample exactly.

These new arguments are **not yet Lean-verified**. The all-size proof is above; the computational checks are diagnostics.
