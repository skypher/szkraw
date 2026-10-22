**Full (D) holds for the quadratic family, for every \(N\).** There is a positive two-coordinate path model, followed by a ballot extraction, that proves it. The argument also proves \((\Gamma)\) directly and gives a closed formula for every quadratic terminal entry.

The general LC case is not proved here.

## 1. A positive kernel for quadratic profiles

Write
\[
D_i=i+x\binom i2,\qquad T=D_N,\qquad h=x/2,
\]
and work initially at \(u=t,v=1\), using the \(H,D\) conventions of your brief.

Define the positive normalizers
\[
A_r=\prod_{j=1}^rD_j,\qquad
Q_r=\prod_{j=0}^{r-1}(T-D_j),\qquad
e_r=\frac{Q_r}{A_r},
\]
with empty products equal to one. Write \(p_i\) for the original polynomial basis, to distinguish it from your fraction-free numerators, and put
\[
E_i=e_ip_i,\qquad Y=TX=E_1.
\]
Its recurrence is
\[
YE_i=D_{i+1}E_{i+1}+tD_iE_i+(T-D_{i-1})E_{i-1},
\]
with the usual endpoint omissions.

Let
\[
E_mE_n=\sum_kL_{mn}^kE_k,\qquad
K_k(z,w)=\sum_{m,n=0}^NL_{mn}^kz^mw^n.
\]
Thus
\[
H_{mn}^k=\frac{e_k}{e_me_n}L_{mn}^k,\qquad K_k(z,0)=z^k.
\]

This is just a change of basis in the terminal polynomial quotient; no positivity has been assumed.

### The kernel equation

For \(F(z)=\sum_{i=0}^NE_i z^i\), summing the recurrence gives
\[
YF(z)=\mathscr L_zF(z),\qquad
\mathscr L_z=(1+tz-z^2)(\partial_z+h z\partial_z^2)+Tz.
\]
The top-degree remainder vanishes because \(T=D_N\). Associativity therefore gives
\[
(\mathscr L_z-\mathscr L_w)K_k=0.
\]

Since \(K_k\) is symmetric, write it in
\[
S=z+w,\qquad Z=zw,
\qquad
K_k(S,Z)=\sum_{r,a\ge0}c_{r,a}S^aZ^r.
\]
Dividing the kernel equation by \(z-w\) and extracting coefficients yields
\[
\boxed{
\begin{aligned}
D_{r+1}c_{r+1,a}
={}&(T-D_{r+a})c_{r,a}\\
&+t(a+1)\bigl(1+h(a+2r)\bigr)c_{r,a+1}\\
&+h(a+1)(a+2)
 \bigl(c_{r,a+2}+c_{r-1,a+2}\bigr).
\end{aligned}}
\tag{1}
\]
The initial conditions are
\[
c_{0,a}=\mathbf1_{a=k},\qquad c_{-1,a}=0.
\]
Because \(D_{r+1}>0\), these conditions uniquely determine the kernel.

The crucial support invariant is
\[
\boxed{c_{r,a}=0\quad\text{when }r+a>N.}
\tag{2}
\]
Indeed, the only move that could increase \(r+a\) beyond \(N\) has multiplier \(T-D_{r+a}\), which vanishes at the boundary. Every other predecessor outside the claimed support is already zero.

### Explicit weighted paths

Set \(C_{r,a}=A_rc_{r,a}\). Clearing the denominators in (1) makes \(C_{r,a}\) the generating function of paths starting at \((0,k)\), staying in
\[
r,a\ge0,\qquad r+a\le N,
\]
with these four moves:

| Move from \((r,a)\) | Weight |
|---|---|
| \((r+1,a)\) | \(T-D_{r+a}\) |
| \((r+1,a-1)\) | \(t\left[a+x\left\{\binom a2+ra\right\}\right]\) |
| \((r+1,a-2)\) | \(x\binom a2\) |
| \((r+2,a-2)\) | \(xD_{r+1}\binom a2\) |

Moves with a negative target coordinate are omitted. Every weight is in \(\mathbb Z_{\ge0}[t,x]\), since
\[
T-D_j=(N-j)+x\left(\binom N2-\binom j2\right)
\]
is coefficientwise nonnegative for \(j\le N\).

Consequently,
\[
A_NK_k(S,Z)
=\sum_{r+a\le N}\frac{A_N}{A_r}C_{r,a}S^aZ^r
\in\mathbb Z_{\ge0}[S,Z,t,x].
\]
Substitution \(S=z+w,\ Z=zw\) preserves positivity, proving
\[
\boxed{
\frac{A_Ne_me_n}{e_k}H_{mn}^k(t)
\in\mathbb Z_{\ge0}[t,x].
}
\tag{3}
\]

This is already a combinatorial model for positively normalized \(H\): take one of the paths, append independent choices with generating functions \(D_{r+1},\ldots,D_N\), and assign \(z\) or \(w\) to each of the \(a\) positions represented by \(S^a\).

## 2. A ballot extraction proves full (D)

Define
\[
W_{mn}^k
=(T-D_{n-1})L_{m,n-1}^k
 -(T-D_{m-1})L_{m-1,n}^k.
\]
The normalizations give the exact identity
\[
\boxed{
D_{mn}^k=\frac{e_k}{Te_me_n}W_{mn}^k.
}
\tag{4}
\]

Write \(D(s)=s+h s(s-1)\), and let \(\theta_z=z\partial_z\). The generating function of these differences is
\[
W_k(z,w)
=w\{T-D(\theta_w)\}K_k
-z\{T-D(\theta_z)\}K_k.
\]
Again, there is no boundary remainder because \(T-D_N=0\).

Introduce the Euler operator
\[
\mathcal E=S\partial_S+Z\partial_Z.
\]
A direct calculation factors the antisymmetric expression:
\[
\boxed{
W_k(z,w)=(w-z)B_k(S,Z),\qquad
B_k=\{T-D(\mathcal E)\}K_k+hZ(K_k)_{SS}.
}
\tag{5}
\]

Both operations defining \(B_k\) are positive on the support (2). On a monomial \(S^aZ^r\), they act respectively as
\[
S^aZ^r\longmapsto (T-D_{a+r})S^aZ^r
\]
and
\[
S^aZ^r\longmapsto x\binom a2S^{a-2}Z^{r+1}.
\]
Hence
\[
A_NB_k\in\mathbb Z_{\ge0}[S,Z,t,x].
\tag{6}
\]

It remains to extract coefficients after multiplication by \(w-z\). For \(m<n\),
\[
[z^mw^n](w-z)(z+w)^a(zw)^r
=
\binom a{m-r}-\binom a{m-r-1}\ge0
\tag{7}
\]
when \(m+n=a+2r+1\), and the coefficient is zero otherwise.

The difference in (7) is a ballot number: it counts words with \(m-r\) letters of one type and \(n-r-1\) of the other, with every prefix containing at least as many letters of the second type.

Combining (4)–(7) proves
\[
\boxed{
\frac{TA_Ne_me_n}{e_k}D_{mn}^k(t)
\in\mathbb Z_{\ge0}[t,x]
\qquad
(1\le m<n\le N,\ 0\le k\le N).
}
\tag{8}
\]

**Thus full (D) holds for quadratic profiles, including every output index—not only \(m<n\le k\).** The objects counted in (8) are the weighted paths above, followed by one of the two positive operations in (5), and a ballot word.

Weighted homogeneity restores the independent parameters \(u,v\): the coefficients of \(H_{mn}^k(t,1)\) are exactly the corresponding \(\Gamma_{mnk,j}\). Thus (3) also proves \((\Gamma)\), and hence the stated consequences \((B)\) and \((P)\).

The normalization in (8) is explicit and positive. I am **not** claiming that this automatically proves coefficientwise positivity of your particular fraction-free numerator with its smaller normalization.

## 3. Closed formulas for the entire quadratic terminal column

For \(x>0\), put
\[
B=N-1+\frac2x,
\]
and use rising factorials \((b)_j\), with \((b)_0=1\). Evaluating the same kernel recurrence gives
\[
\boxed{
H_{m,N}^N(t)=
\sum_{j=0}^{\lfloor m/2\rfloor}
\frac{m!}{j!(m-2j)!(B+m-j)_j}\,t^{m-2j}.
}
\tag{9}
\]
The complete kernel evaluation and its substitution proof are included in the proof note linked below.

For example,
\[
\begin{aligned}
H_{2,N}^N&=t^2+\frac2{B+1},\\
H_{3,N}^N&=t^3+\frac6{B+2}t,\\
H_{4,N}^N&=t^4+\frac{12}{B+3}t^2
+\frac{12}{(B+2)(B+3)}.
\end{aligned}
\]

Using
\[
D_{m,N}^N=a_m\bigl(H_{m+1,N}^N-tH_{m,N}^N\bigr),
\]
the adjacent coefficients in (9) subtract explicitly:
\[
\boxed{
D_{m,N}^N(t)
=
a_m\,m!(2B+m-1)
\sum_{j=1}^{\lfloor(m+1)/2\rfloor}
\frac{t^{m+1-2j}}
{(j-1)!(m+1-2j)!(B+m-j)_{j+1}}.
}
\tag{10}
\]
This holds for \(1\le m<N\). Every displayed coefficient is strictly positive for \(x>0\). At \(x=0\), the limits are
\[
H_{m,N}^N=t^m,\qquad D_{m,N}^N=0.
\]

For \(m=3\), (10) gives
\[
[t^0]D_{3,N}^N=\frac{12(N-3)}{NB(B+2)},
\]
equivalent to your previously verified quadratic certificate.

## Verification and files

I compared the positive-kernel construction and ballot extraction against the original fraction-free matrix recurrence **over \(\mathbb Z[t,x]\)** for every index through \(N=18\). All **36,099 \(H\) identities and 14,535 \(D\) identities** passed, as did the terminal closed formulas. These are checks of the identities and normalizations; the all-size proof is (1)–(8).

[Complete proof, including the terminal-kernel evaluation](sandbox:/mnt/data/consultD/quadratic_D_proof.md) · [Exact checker](sandbox:/mnt/data/consultD/verify_quadratic.py) · [Verification output](sandbox:/mnt/data/consultD/verification.txt)

The remaining gap is extending this positive symmetric-kernel recurrence beyond quadratic profiles; no all-\(m\) terminal theorem for arbitrary LC profiles is asserted here.
