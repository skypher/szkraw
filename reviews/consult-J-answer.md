**(C3) holds with \(u=1\).** The same resummed operator \(M\) is entrywise nonnegative. No stronger replacement condition is needed.

The crucial change is that **the cubic version of the weighted scalar inequality (quad-B) is false**, even under \(r\sigma=t\tau\). However, one unused \(\varphi_3\) summand repairs its exceptional case and proves the required **summed B-detour**.

[Complete proof](sandbox:/mnt/data/round8/consult-round8.md) · [Exact-arithmetic verifier](sandbox:/mnt/data/round8/verify_cubic_round8.py) · [Audit output](sandbox:/mnt/data/round8/audit.txt)

The proof reuses your quadratic weighted B lemma and the retained affine-surplus lemma from round 7. All new cubic inequalities, including the polynomial certificates and low-order cases, are derived in the proof file. [1][2]

## 1. The B-detour needs a repair, not an extra hypothesis

Under \(r\sigma\le t\tau\), the proof establishes
\[
(n+1)(n+2)\varphi_2(\ell)\varphi_n(\ell+1)
\ge 8(n-1)c_{\ell+1}\varphi_{n+2}(\ell)
\]
**except possibly at \((\ell,n)=(0,2)\).**

That exception is genuine. Take
\[
N=4,\qquad d_i=\frac{10^i-1}{9999},\qquad
(r,t,\tau,\sigma)=
\left(\frac1{10^6},\frac1{1000},\frac1{10000},\frac1{10}\right).
\]
Then \(r\sigma=t\tau\), and the Newton coefficients of \(d\) are \(9^k/9999\), hence log-concave. Moreover,
\[
R_3=\frac{111}{1000},\qquad
\rho(4)+\Delta\rho(3)R_3=\frac{4380453}{10^7}<1,
\]
so \(b\) is nondecreasing. Nevertheless,
\[
12\varphi_2(0)\varphi_2(1)-8c_1\varphi_4(0)
=-\frac{870421}{3156250000000}<0.
\]

The replacement at this corner is
\[
\boxed{
\bigl(12\varphi_2(0)+\varphi_3(0)\bigr)\varphi_2(1)
\ge 8c_1\varphi_4(0).
}
\tag{1}
\]

Here is the repair mechanism. Write \(u_i=f_i(0)\), so \(u_0=0\). Polarizing the weighted scalar difference in \((r,t,\tau,\sigma)\) leaves only its \(t\sigma\)-coefficient potentially negative at this corner. That coefficient is
\[
\begin{aligned}
F_{13}
={}&-32u_1u_4+24u_2u_3
+72(u_2^2-u_1u_3)+48u_1u_2+40u_1^2\\
\ge{}&-8u_1u_4.
\end{aligned}
\]
Meanwhile,
\[
\varphi_3(0)\ge3\sigma u_2,\qquad
\varphi_2(1)\ge3t u_3,
\]
and therefore
\[
\varphi_3(0)\varphi_2(1)
\ge9t\sigma u_2u_3
\ge9t\sigma u_1u_4.
\]
This proves (1).

For the summed detour, reserve the product
\[
\binom a3\varphi_3(0)\binom{a-2}2\varphi_2(1)
\]
from \(B_0(0,a)B_0(1,a-2)\). Together with the usual \(\varphi_2\)-product, its contribution divided by \(\binom a4\) is
\[
\bigl(6\varphi_2(0)+2(a-2)\varphi_3(0)\bigr)\varphi_2(1),
\]
which exceeds the requirement from (1). The other terms use first factor \(\varphi_2\), so there is no double counting.

Thus, throughout the cubic class,
\[
\boxed{
B_0(\ell,a)B_{j-1}(\ell+1,a-2)
\ge4c_{\ell+1}B_j(\ell,a)
\qquad(j\ge1).
}
\tag{2}
\]

The all-order polarization argument and its explicit nonnegative polynomial certificates are in Sections 2–3 of the proof.

## 2. Group \(W\) and \(X\)

Set
\[
e_n=w_n+x_n,\qquad E_j=W_j+X_j.
\]
Separate detours for \(X\) are unnecessary. Under \(r\sigma\le t\tau\),
\[
\boxed{
\begin{aligned}
(n+1)(n+2)\varphi_2v_n'
&\ge n^2c_{\ell+1}v_{n+2},\\
(n+1)(n+2)\varphi_2e_n'
&\ge n(n-1)c_{\ell+1}e_{n+2}
\end{aligned}
\qquad(n\ge3).
}
\tag{3}
\]

The key coefficient inequality is particularly simple. With
\[
p=\rho(\ell+1),\qquad s=\Delta\rho(\ell+1),\qquad
T=\tau+\sigma(\ell+n-1),
\]
one has
\[
\begin{aligned}
sT-p\sigma
={}&t\tau-r\sigma+t\sigma(n-2)+\tau^2(\ell+1)\\
&+\tau\sigma(\ell+1)(\ell+n-1)
+\frac{\sigma^2}{6}\ell(\ell+1)(2\ell+3n-2)
\ge0.
\end{aligned}
\tag{4}
\]
Retaining both the \(f_2\) and \(f_1\) terms in
\[
\varphi_2=(p+s)f_2+2sf_1+(\tau+\sigma\ell)f_0
\]
then proves (3).

After summation, the constants are exactly those needed:
\[
\boxed{
\mu_H=10,\qquad
\mu_V=\frac92,\qquad
\mu_E=3,\qquad
\mu_C=6.
}
\]

## 3. The key inequality holds with \((2,1,1)\)

For every nonnegative cubic Newton ratio with nondecreasing \(b\), **even without (C3)**, the proof gives
\[
\boxed{
\begin{aligned}
&A_0(\ell,a)B_0(\ell+1,a-1)
+B_0(\ell,a)A_0(\ell+1,a-2)\\
&\qquad\ge
c_{\ell+1}\bigl(4H_1-2V_1-W_1-X_1\bigr)(\ell,a).
\end{aligned}
}
\tag{5}
\]
Thus
\[
(\gamma_V,\gamma_W,\gamma_X)=(2,1,1).
\]

Section 5 supplies the full coefficientwise nonnegative certificate, using the retained affine surplus. In particular, the two potentially troublesome coefficients become
\[
Q_2=\frac{a-2}{6}
\left[
4t+(a+11+4\ell)\tau
+\bigl(2\ell^2+(a+9)\ell+a^2-2a+7\bigr)\sigma
\right]\ge0
\]
and
\[
Q_3=(2a-5)\tau+
\sigma\left[
(2a-5)\ell+\frac{(a-3)^3+11(a-3)+3}{3}
\right]\ge0.
\]

## 4. Signs and resummation

Yes: \(X_j\) has exactly the same sign behavior as \(V_j,W_j\). Since
\[
A_j^\psi=H_j-V_j-W_j-X_j,
\]
the derivative families enter positively for odd \(j\) and negatively for even \(j\). Grouping \(E=W+X\) reduces the bookkeeping to the quadratic pattern.

Equations (2)–(5) yield
\[
\begin{gathered}
P^2\ge4Q,\qquad H_+P\ge10H_-,\qquad
V_+P\ge\tfrac92V_-,\\
E_+P\ge3E_-,\qquad C_+P\ge6C_-,\\
A_0P+PA_0+2V_1+E_1\ge4H_1.
\end{gathered}
\]
Consequently,
\[
\boxed{
GAG\ge
\frac12(GA_0+A_0G)
+\frac1{18}GV_1G+\frac1{12}GE_1G
\ge0.
}
\]
Together with \(GCG\ge0\) and \(U+P^2/4-Q\ge0\), this proves
\[
M=G(U+P^2/4-Q+C+A)G\ge0,
\]
and the existing finite kernel resummation gives (P). [1]

## Scope and verification

The proof settles the cubic question with \(u=1\). The pure and adjacent binomial-multiplier lemmas, and the derivative-family sign rule, extend to higher degree; **the arbitrary-degree conjecture is not established here**.

For every \(0<r<1\), the theorem admits positive cubic terms; an explicit parameter choice is included in Section 7. At \(r=1\) and \(N\ge3\), nondecreasing \(b\) itself forces \(t=\tau=\sigma=0\).

The verifier passed the symbolic certificates and exact-rational checks on **97 arrays, \(N=4\)–\(10\)**, including very small biases and equality in (C3). It also checked full linearization tables for the diagnostic arrays with \(N\le6\), and the full resummed \(M\) on four arrays, including the negative-scalar example above. **The new cubic theorem has not yet been Lean-checked.**

Sources:
[1] https://raw.githubusercontent.com/skypher/szkraw/main/paper.tex
[2] https://raw.githubusercontent.com/skypher/szkraw/main/reviews/consult-I-answer.md

