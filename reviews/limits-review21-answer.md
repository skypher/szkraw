## Verdict: **PASS WITH MINOR FIXES**

Taking the previously approved lemmas and recurrence as given, the proof works after **three local text edits**. As printed, the certificate is invoked outside its stated \(h\)-domain, and both boundary evaluations of \(\mathcal F(q)\) have incorrect normalization factors. These errors are repairable without changing any hypothesis, inequality, or resummation constant. I checked the pinned version and independently implemented the tests below, without importing the author’s diagnostics. [1]

## 1. Required corrections

| Location | Printed text | Replacement |
|---|---|---|
| Hypotheses of `eq:quad-cert` | Integers \(n\ge2,\ h\ge1\) | **Integer \(n\ge2\), real \(h\ge1\)** |
| Boundary \(1/q\le\ell\) | Divide \(\mathcal F(q)\) by \(q^n(1+q)\) | Divide by **\(q(1+q)\)** |
| Boundary \(\ell<1/q\) | Divide \(\mathcal F(q)\) by \(q^{n+1}\) | Divide by **\(q^2\)** |

The first correction is necessary because \(h=1+1/q\) need not be integral. The certificate’s existing proof already establishes the stronger statement for real \(h\ge1\): nothing in its argument requires integral \(h\). [2]

For the other two corrections, define the actual geometric-configuration residual
\[
\mathscr D_n
=K_n\varphi_2(\ell)\varphi_n(\ell+1)
-L_nc_{\ell+1}\varphi_{n+2}(\ell).
\]
With the manuscript’s definition of \(\mathcal F\),
\[
\boxed{\mathscr D_n=q^{n-1}\mathcal F(q).}
\]
The printed divisors are correct for \(\mathscr D_n\), **not** for \(\mathcal F(q)\). Thus both printed equality claims are genuinely false, although their intended sign arguments survive the correction. [2]

An optional clarification: at \(w=0\), the second boundary expression equals
\[
h_0(K_nAB-L_npC),
\]
not the bare certificate. “Reduce to” is acceptable because \(h_0>0\), but displaying the factor would prevent another normalization ambiguity.

A [validated replacement script](sandbox:/mnt/data/round21/apply_round21_fixes.py) implements exactly the three required edits; it prints a diff unless invoked with `--write`.

## 2. Monotonicity, Leibniz formulas, and move signs — PASS

The increment identity
\[
b_{i+1}-b_i
=f_1(i)\bigl[1-\rho(i+1)-\Delta\rho(i)R_i\bigr]
\]
is correct. Since \(f_1(i)>0\), nondecreasing \(b\) gives the claimed pointwise inequality. Also, \(b_0=0\) implies \(b_i\ge0\), hence \(\rho(i)\le1\) for \(i\ge1\); \(\rho(0)=r\le\rho(1)\le1\).

The bracket is nonincreasing: \(\rho(i+1)\), \(\Delta\rho(i)\), and \(R_i\) are nondecreasing, and the latter two are nonnegative. Consequently, the stated final-increment characterization of nondecreasing \(b\) is correct.

The Leibniz formula has the correct shifts and coefficients:
\[
\rho(\ell+n),\qquad
n\Delta\rho(\ell+n-1),\qquad
\binom n2\tau.
\]
All occurring indices stay within \(\ell+n\le N\), so truncation of the Newton coefficients causes no problem. The nonnegative quantities are \(\varphi_n,h_n,v_n,w_n\), **not necessarily \(\psi_n\)**. Replacing “all of these” by that explicit list would improve clarity.

The split \(A^\psi_j=H_j-V_j-W_j\) is correct. Multiplication by \((-1)^j\) makes \(V_j,W_j\) positive for odd \(j\) and negative for even \(j\). Also,
\[
C'_j=W^f_{2j+2,j+1}\ge0.
\]
The example showing that the Newton coefficients of \(c\) need not be log-concave is correct.

## 3. Four mixed detours — PASS

The uses of Lemma 8.3 have valid indices:

| Family | Lemma indices | Relevant occurring range |
|---|---|---|
| \(f,h\) | \((2,n)\) | \(n\ge2\) for \(C'\), \(n\ge3\) for \(H\) |
| \(v\) | \((2,n-1)\) | \(n\ge3\) |
| \(w\) | \((2,n-2)\) | \(n\ge3\) |

In particular,
\[
(n+1)\Delta\rho(\ell+n)-n\Delta\rho(\ell+n+1)
=t+\tau\ell
\]
is exact. It gives precisely the claimed loss \(n^2/((n+1)(n+2))\) for \(v\). For \(w\), the loss is exactly
\[
\frac{\binom n2}{\binom{n+2}2}
=\frac{n(n-1)}{(n+1)(n+2)}.
\]

The four coefficient ratios are correct and increase with \(j\) for fixed \(m\). Their minima are:

| Family | Minimum | Attained at |
|---|---:|---|
| \(H\) | \(10\) | \(j=2,\ m=5,6\) |
| \(V\) | \(9/2\) | \(j=2,\ m=5\) |
| \(W\) | \(3\) | \(j=2,\ m=5\) |
| \(C'\) | \(6\) | \(j=1,\ m=4\) |

The \(H\)-argument uses integrality of \(m\): \((m-5)(m-6)\ge0\) is valid on the integer range \(m\ge5\), although not throughout the corresponding real interval. That is legitimate here.

## 4. Summing `eq:quad-B` — PASS

The substitution \(n=m-2\) gives exactly
\[
\binom m2\frac{8(m-3)}{m(m-1)}=4(m-3).
\]
The remaining identity is also exact:
\[
(m-3)\binom{m-j-3}{j-1}-\binom{m-j-2}{j}
=
\binom{m-j-3}{j-1}\frac{(j-1)(m-2)}j.
\]
Its domain \(j\ge1,\ m\ge2j+2\) makes every factor nonnegative. For \(j=1\), this coefficient comparison is equality. There is no missing factor or index shift.

## 5. Proof of `eq:quad-B` — PASS after the corrections above

### Tail reduction

The zero cases are valid: if \(q=0\) or \(u_n=0\), interval support forces all terms contributing to \(\varphi_{n+2}\) to vanish.

Otherwise, log-concavity gives all three asserted bounds:
\[
u_{n+2}\le y^2u_n,\qquad
u_{n-1}\ge u_n/q,\qquad
u_{n-2}\ge u_n/q^2.
\]
The last two are used only for \(n\ge3\). The special \(n=2\) expression for \(\mathcal L(y)\) is exact.

Both endpoint comparisons have the correct direction. More explicitly,
\[
\begin{aligned}
\mathcal F(0)-\frac{\mathcal F(q)}{1+q}
={}&K_n\varphi_2
 \left(\mathcal L(0)-\frac{\mathcal L(q)}{1+q}\right)\\
&+L_np(z+1)
 \left(\frac{\mathcal T(q)}{1+q}-\mathcal T(0)\right)
\ge0.
\end{aligned}
\]
Here \(A\ge B\ge0\) proves the first bracket nonnegative, and the stated lower bound on \(\Delta\rho(\ell+n+1)\) proves the second.

Since \(\mathcal F\) is concave, nonnegative endpoint values imply nonnegativity throughout \([0,q]\). Therefore \(\mathcal F(q)\ge0\) suffices. There is no reversed concavity argument.

### Reduction in \(z\)

For \(n\ge3\),
\[
\frac{d}{dz}\frac{A_2+\tau z}{z+1}
=\frac{\tau-A_2}{(z+1)^2}\le0,
\]
so increasing \(z\) makes the desired inequality harder.

For \(n=2\), I verified the displayed quotient-difference identity exactly. Its lower bound follows from
\[
G_2\ge2(\ell+2)\tau,\qquad A_2-\tau\ge(2\ell+1)\tau,
\]
and
\[
2(\ell+2)(2\ell+1)-(\ell+1)^2
=3\ell^2+8\ell+3\ge0.
\]
Thus the reduction again has the correct direction.

**The interval \(0\le z\le\min(\ell,1/q)\) is an admissible relaxation, not a characterization of all realizable shifted Newton profiles.** Some boundary configurations need not arise from an actual profile. This is harmless: the argument proves the inequality on the larger class satisfying the constraints it uses.

### Polynomial certificate

I independently verified the identity at \(s=(h-1)\tau\), the expressions for \(C_n,D_n,U_n\), the expansion of \(U_n\) at \(n=7+k\), and all 25 entries in the discriminant table.

Monotonicity in \(s\) is valid: the \(ps\), \(s^2\), and \(s\tau\) coefficients are nonnegative for real \(h\ge1\). For \(n\ge7\), the displayed coefficient argument works. For \(2\le n\le6\), the table and square completion work for every real \(v=h-1\ge0\). Thus the only problem here is the unnecessarily restrictive printed quantifier.

### Boundary evaluations and \(w\)-coefficients

The correct identities are
\[
\boxed{\frac{\mathcal F(q)}{q(1+q)}=K_nAB-L_npC}
\]
in the first case, and
\[
\boxed{
\frac{\mathcal F(q)}{q^2}
=
\begin{cases}
\mathcal E_n(w),&n\ge3,\\
\mathcal E_2(w)-12A(w)\tau w(\ell+w)^2,&n=2
\end{cases}}
\]
in the second.

In the first case, \(s=t+\tau\ell\ge(h-1)\tau\) is justified. In the second, the certificate is needed only at \(w=0\), where \(h=h_0\); no unjustified assumption \(s\ge(h_0+w-1)\tau\) is required.

Every displayed \(w\)-coefficient identity checked symbolically for general \(n\), with \(n=2\) handled separately. In particular,
\[
\bar A=(2h_0-1)s+h_0^2\tau\ge0,\qquad
\bar B=nh_0(s+\tau)+\binom n2h_0^2\tau\ge0.
\]
The remaining factors have the asserted signs. For \(n=2\), the quartic coefficient cancels **exactly to zero**, and the three listed coefficients are correct.

## 6. Key inequality — PASS

The monotonicity bound is used at a valid index:
\[
\ell+a-1\le N-1.
\]
Hence
\[
\alpha\ge sR_{\ell+a-1}\ge su_0/u_1,\qquad
s=t+\tau(\ell+a-1)\ge\tau(a-1).
\]

Both backward-difference formulas are correct, including the potentially easy-to-miss coefficient \(\binom{a-1}{2}\) in the second \(A_0\). The identities for \(1-\rho(\ell+n)\), \(4H_1-2V_1\), and \(W_1\) are also exact.

The refined affine surplus is valid. To make its interpolation fully explicit, after normalizing \(u_1=1\), subtract
\[
S(z)=\frac23(z+1)(a-2)y_2
\]
from the affine proof’s \(F(z)\). The difference remains concave, and
\[
F(0)-S(0)\ge\frac43(a-2)y_2\ge0,\qquad
F(1/q)-S(1/q)\ge0.
\]
This proves the surplus throughout the interval. The nonnegative coefficient of \(\alpha\) then extends the result from \(\alpha=sz\) to all \(\alpha\ge sz\). The cases \(q=0\) and \(s=0\) require no division and are covered separately by the same elementary bounds. The manuscript’s retained \(E_2=-2/3\) term is exactly what supplies the second endpoint surplus. [2]

The final certificate coefficients check:
\[
\binom{a-1}{2}-2\binom{a-2}{2}
+\frac23(a-1)(a-2)
=\frac{(a-2)(a+11)}6,
\]
\[
\binom{a-1}{2}-\binom{a-3}{2}=2a-5.
\]
For \(n\ge4\), both terms in the remaining coefficient are nonnegative.

Importantly, replacing the actual \(B_0\)’s by \(pY,pY'\) is legitimate because the **actual, unsplit \(A^\psi_0\)’s** multiplying them are nonnegative. The proof does not improperly discard terms multiplied by negative quantities.

## 7. Resummation constants and composition — PASS

With column-vector action, the rightmost operator acts first. Thus the local path “\(B_0\), then \(H_{j-1}\)” produces \(H_+P\), not \(PH_+\). The same ordering applies to \(V,W,C'\). The intermediate denominator is precisely \(c_{\ell+1}\), matching the local inequalities.

The retained fractions are correct:
\[
1-\frac{2}{9/2}=\frac59,\qquad
1-\frac23=\frac13.
\]
After using the key inequality,
\[
\frac59-\frac12=\frac1{18},\qquad
\frac13-\frac14=\frac1{12}.
\]
These match the printed resummation. [2]

The cancellation
\[
G\left(A_0-\frac14(A_0P+PA_0)\right)G
=\frac12(GA_0+A_0G)
\]
uses \(PG=GP=2(G-I)\); it does **not** assume that \(A_0\) commutes with \(P\). Nonnegativity and strict level increase of \(M\) then justify the finite inverse and the conclusion (P).

## 8. Independent exact testing

All executed checks passed.

| Test | Coverage |
|---|---|
| Full members | **216 cases:** 120 random through \(N=16\), plus 96 adversarial cases through \(N=20\) |
| Adversarial parameters | Geometric Newton ratios \(10^{-3},1,10^3\); truncated supports; \(t=0\); \(\tau/t=10^6\); boundary monotonicity; \(r=0.999999\) |
| Linearization | **396,226 coefficients**, computed directly from the finite multiplication recurrence; nonnegativity, product sums, and symmetry checked |
| Operators | **12 full checks**, at \(N=4,8,14,16\): detours, \(M\ge0\), resummation identity, and agreement with independently computed products |
| Local weighted detour | **10,000 random configurations**, \(\ell\le200,\ 2\le n\le30\), plus **5,000 targeted boundary configurations**, with \(\ell\) up to \(10^6\) |
| Symbolic algebra | **24 identity checks**, including general-\(n\) boundary expansions and every discriminant-table entry |

The smallest weighted-detour ratio in these local tests was approximately \(1.0399310026\). This is a tested minimum, not a claimed global bound.

The supplied unit-constant counterexample reproduces exactly:
\[
\varphi_2(16)\varphi_2(17)-c_{17}\varphi_4(16)
=
-\frac{11121875309909}{366503176875000000}<0.
\]
Its \(b\) is nondecreasing, while the weighted inequality remains strictly positive.

[Download the independent audit bundle](sandbox:/mnt/data/round21_audit.zip), including reproducible scripts, exact results, and the three-edit replacement script.

**Bottom line:** accept Theorem 8.11 after correcting the real-\(h\) domain and both \(\mathcal F(q)\) divisors. I found no remaining gap in the weighted detour, key inequality, or resummation.

Sources:
[1] szkraw/paper.tex at 3ed42a4d8a2b9ae8196a6e4c6cd09f64d20675d7 · skypher/szkraw · GitHub — https://github.com/skypher/szkraw/blob/3ed42a4d8a2b9ae8196a6e4c6cd09f64d20675d7/paper.tex
[2] https://raw.githubusercontent.com/skypher/szkraw/3ed42a4d8a2b9ae8196a6e4c6cd09f64d20675d7/paper.tex

