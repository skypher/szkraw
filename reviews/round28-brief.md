# Review round 28: P2 proofs of Theorems 5.5 and 5.6 rewritten along the Lean route

Repository: github.com/skypher/szkraw, commit 911524a, file papers/p2.tex (P2 = "A log-concave ratio criterion …"; Theorem 5.5 = paper.tex Theorem 8.16, Theorem 5.6 = paper.tex Theorem 8.17). Both theorems are machine-verified in Lean: `Szkraw.lc_general` and `Szkraw.cubic_ratio_matrix`, axiom audit clean, statement fidelity rounds 18 and 19 PASS. The Lean proofs use simpler certificates than the printed proofs you reviewed in rounds 24–26. P2's proofs have now been rewritten to follow the Lean route. The theorem statements and all other proof steps are unchanged.

Task: review the rewritten passages below as a referee. Check that each step is correct, that nothing used is missing, and that the certificate claims are accurate. Rerun the cited scripts from the repository at this commit:
- runs/lean_plan/edge_exact.py 60
- runs/lean_plan/forms_iii_v.py
- runs/lean_plan/window_cert.py
- runs/lean_plan/gen_cubicB.py CASE OUT for CASE in gen, 2, 3, 4, 5, corner
- runs/lean_plan/gen_cubicE.py CASE OUT for CASE in gen, 3, 4, 5, 6
- runs/lean_plan/phi3_edge.py 40
- runs/lean_plan/phi3_generic.py

The generators assert nonnegativity of every tail and coefficient and write the Lean certificates; Lean then checks the identities. You may also inspect lean/Szkraw/GenForm*.lean, GenWindows.lean, CubicB.lean, CubicE.lean, CubicKeyForms.lean, CubicKeyRed.lean, CubicKey.lean. Also check that the 7/4 remark is correctly supported: for B with n ≤ 5 it now relies on the earlier regime certificates runs/cubic/bdetour_u.py and edetour_u.py.

Answer format: PASS / PASS WITH MINOR FIXES / FAIL, a list of issues with exact replacement text, and a list of what you independently checked. Terse.

## Theorem 5.5: new steps (vi) and (vii) (steps (i)–(v) unchanged)

```latex
\emph{(vi) Edge bounds.} Steps (ii)--(v) reduce \eqref{eq:G-key} to the nonnegativity of the quadratic forms $K$, $L$, $R$, $R_2$, $K''$, $Q_s$ $(3\leq s\leq a)$, $K_a$, $\Psi$ and $\widehat Q$ in the sequence $u$. For $Q_s$, first remove the dependence on $s$: by $\nu_s\geq0$, $Z_s\leq\binom asH_*$, $\binom as\leq\frac a3\binom{a-1}{s-1}$ and $\binom{a-1}s\leq\frac{a-3}3\binom{a-1}{s-1}$ for $s\geq3$, one has $Q_s\geq\binom{a-1}{s-1}Q^*$ with
\[
Q^*=Y'X''+YX'-4u_0H_*-\tfrac{4a}3u_1H_*-\tfrac{a-3}3u_1(Y+Y').
\]
Each of these forms is a sum of products $xy$ of linear forms $x=\sum_{i\geq1}x_iu_i$ and $y=\sum_{j\geq1}y_ju_j$ with nonnegative coefficients, plus $u_1$ times a linear form, minus $u_0$ times a linear form with nonnegative coefficients. Since $u$ is log-concave without internal zeros, $u_iu_j\geq u_1u_{i+j-1}$ for $i,j\geq1$ and $u_0u_{n+1}\leq u_1u_n$. Keeping in $xy$ only the pairs with $i\leq2$ or $j\leq2$ gives
\[
xy\geq u_1\sum_ne_n(x,y)u_n,\qquad e_n(x,y)=x_1y_n+x_2y_{n-1}+[n\geq3]\,y_1x_n+[n\geq4]\,y_2x_{n-1},
\]
and $u_0\sum_{n\geq1}h_nu_n\leq u_1\sum_{n\geq0}h_{n+1}u_n$. So each form is at least $u_1\sum_ne_nu_n$ with explicit coefficients $e_n$, and it suffices that every $e_n\geq0$.
\begin{itemize}
\item For $4\leq n\leq a$ write $n=4+p$ and $a=n+k$. Then $e_n/\binom an$ is a rational function of $(p,k)$ whose numerator has nonnegative coefficients.
\item For $n\leq3$, $e_n$ is a polynomial in $a$ whose coefficients are nonnegative after $a\mapsto a+a_0$, with $a_0=6$ for $R_2$, $a_0=5$ for $K_a$ and $a_0=3$ otherwise.
\item For $n\geq a+1$ only nonnegative products remain.
\end{itemize}
These certificates are formalized in Lean, and \path{runs/lean_plan/edge_exact.py} checks every $e_n$ in exact arithmetic for $a\leq60$.

\emph{(vii) Small windows.} Steps (iii$'$) and (v) need $a\geq6$ and $a\geq5$. For $3\leq a\leq5$, each sum $M_{1,m}+M_{m,1}$ $(2\leq m\leq a)$ and, for $a\leq4$, $S_{2,0}$ is a cubic form in $u$ that is an exact nonnegative rational combination of the products $u_k(u_{i+1}u_{j-1}-u_iu_j)$ $(i+1\leq j-1)$ and of monomials (\path{runs/lean_plan/window_cert.py}). This proves \eqref{eq:G-key} and the theorem.
```

## Theorem 5.6: new proof of the detour inequalities and of the key inequality (the statements of eq. cubic-B, cubic-corner, cubic-E and cubic-key, and the resummation, are unchanged)

```latex
\emph{Proof of \eqref{eq:cubic-B}, \eqref{eq:cubic-corner} and \eqref{eq:cubic-E}.} In each, the difference of the two sides is a quadratic form $\sum\kappa_{\beta\gamma}\rho_\beta\rho_\gamma$ in $(\rho_0,\rho_1,\rho_2,\rho_3)=(r,t,\tau,\sigma)$. Its coefficients are bilinear forms in the $u_k$, with coefficients polynomial in $\ell$ and $n$.
\begin{itemize}
\item Since $t\tau\kappa_{t\tau}+r\sigma\kappa_{r\sigma}=(t\tau-r\sigma)\kappa_{t\tau}+r\sigma(\kappa_{t\tau}+\kappa_{r\sigma})$ and $r\sigma\leq t\tau$, the form is nonnegative if $\kappa_{t\tau}$, $\kappa_{t\tau}+\kappa_{r\sigma}$ and all coefficients other than $\kappa_{r\sigma}$ are nonnegative as forms in $u$.
\item For \eqref{eq:cubic-B} the coefficients $\kappa_{rr}$, $\kappa_{r\tau}$, $\kappa_{\tau\tau}$ need not be checked: the form with $t=\sigma=0$ is \eqref{eq:quad-B} for the ratio $r+\tau\binom x2$. The same holds for \eqref{eq:cubic-corner}, whose left side exceeds that of \eqref{eq:cubic-B} at $(0,2)$ by $8\varphi_3(0)\varphi_2(1)\geq0$.
\item Every remaining coefficient is a sum $\sum c_{ij}u_iu_j$ over $i\leq j$. Group its terms by $i+j=m$. Within a group, $u_iu_{m-i}$ is nondecreasing in $i$ by log-concavity, so with the tail sums $T_k=\sum_{i\geq k}c_{i,m-i}$ and the smallest index $k_0$ of the group,
\[
\sum_ic_{i,m-i}u_iu_{m-i}=T_{k_0}u_{k_0}u_{m-k_0}+\sum_{k>k_0}T_k\,(u_ku_{m-k}-u_{k-1}u_{m-k+1}),
\]
and the coefficient is nonnegative if all $T_k\geq0$.
\item The tail sums are polynomials in $(\ell,n)$. For \eqref{eq:cubic-B} with $n\geq6$ and for \eqref{eq:cubic-E} with $n\geq7$ they have nonnegative coefficients in $(\ell,n-6)$, respectively $(\ell,n-7)$. For each $n$ in $3\leq n\leq5$ (\eqref{eq:cubic-B}) and $3\leq n\leq6$ (\eqref{eq:cubic-E}) they are polynomials in $\ell$ with nonnegative coefficients. The same holds for \eqref{eq:cubic-B} with $n=2$ and $\ell\geq1$ after $\ell\mapsto\ell+1$, and for \eqref{eq:cubic-corner}, where $u_0=0$.
\end{itemize}
The certificates are generated and checked in exact arithmetic by \path{runs/lean_plan/gen_cubicB.py} and \path{runs/lean_plan/gen_cubicE.py}.

\emph{Key inequality.} We show, for $(\ell,a)\in\Omega$ with $a\geq3$,
\begin{equation}\label{eq:cubic-key}
A^\psi_0(\ell,a)B_0(\ell+1,a-1)+B_0(\ell,a)A^\psi_0(\ell+1,a-2)\geq c_{\ell+1}\bigl(4H_1-2V_1-E_1\bigr)(\ell,a).
\end{equation}
Use the notation of the proof of Theorem~\ref{thm:lc-quadratic}, and put $P_1=\Delta\rho(\ell)$ and $P_2=\Delta^2\rho(\ell)=\tau+\sigma\ell$, so that $\rho(\ell+k)=\rho(\ell)+kP_1+\binom k2P_2+\binom k3\sigma$. Put $\alpha=1-\rho(\ell+a)$, $s_q=P_1+(a-1)P_2$ and $s=\Delta\rho(\ell+a-1)=s_q+\binom{a-1}2\sigma$. Then $\alpha\geq su_0/u_1$ and $s_q\geq(a-1)P_2$. Backward differences give
\[
\begin{aligned}
A^\psi_0(\ell,a)&=\alpha X-s_qau_0+P_2\tbinom a2u_0-\sigma\tbinom a3u_0,\\
A^\psi_0(\ell+1,a-2)&=(\alpha+s)X'-s_q(a-2)D+P_2\tbinom{a-1}2D-\sigma\tbinom{a-1}3D,
\end{aligned}
\]
and, reindexing as before, $4H_1-2V_1-E_1=4\alpha H_*+2s_qT+4P_2Z-P_2\sum_{n\geq1}n\binom{a-n}2y_n+\sigma(4T_3-E_3)$, where $T_3=\sum_{n\geq3}(n-2)\bigl(\binom a3-\binom n3\bigr)y_n$ and $E_3=\sum_{n\geq3}(n-2)\binom n3\binom an(3u_{n-1}+3u_{n-2}+u_{n-3})$. With $B_0(\ell,a)\geq pY$, $B_0(\ell+1,a-1)\geq pY'$ and $c_{\ell+1}=pD$, it suffices that $R=A^\psi_0(\ell,a)Y'+YA^\psi_0(\ell+1,a-2)-D(4H_1-2V_1-E_1)\geq0$. $R$ is affine in $\alpha$, with coefficient $XY'+YX'-4DH_*$. Its part without $\sigma$ is the expression bounded in the proof of Theorem~\ref{thm:lc-quadratic}, with $s_q$ and $P_2$ in place of $s$ and $\tau$; that bound holds for every value $\alpha'$ of $\alpha$ with $\alpha'u_1\geq s_qu_0$. Apply it with $\alpha'=\alpha-\binom{a-1}2\sigma z$, where $z=u_0/u_1$. This gives $R\geq\sigma\Phi^{\mathrm{loc}}_3$ with
\[
\Phi^{\mathrm{loc}}_3=\tbinom{a-1}2z\,(XY'+YX'-4DH_*)-\tbinom a3u_0Y'+Y\Bigl(\tbinom{a-1}2X'-\tbinom{a-1}3D\Bigr)-D(4T_3-E_3).
\]

\emph{$\Phi^{\mathrm{loc}}_3\geq0$.} Write $E_3=\binom a3u_0+E_3^0$ and $H_*^+=\sum_{n\geq2}(n-1)\binom a{n+1}u_n$, so that $u_0H_*\leq u_1H_*^+$. Bounding the only term quadratic in $u_0$, $-4\binom{a-1}2u_0^2H_*$, this way and dropping $\binom a3u_0^2u_1\geq0$ gives $u_1\Phi^{\mathrm{loc}}_3\geq u_1A+u_0B$ with
\[
\begin{aligned}
A&=\tbinom{a-1}2YX'-u_1\Bigl(\tbinom{a-1}3Y+4T_3-E^0_3\Bigr),\\
B&=\tbinom{a-1}2\bigl(XY'+YX'-4u_1H_*-4u_1H_*^+\bigr)-u_1\Bigl(\tbinom a3Y'+\tbinom{a-1}3Y+4T_3-E^0_3-\tbinom a3u_1\Bigr).
\end{aligned}
\]
These are forms of the kind treated in step (vi) of the proof of Theorem~\ref{thm:lc-general}: the edge bounds give $A\geq u_1\sum_ne^A_nu_n$ and $B\geq u_1\sum_ne^B_nu_n$. Their coefficients are nonnegative by the same three kinds of certificates: for $4\leq n\leq a$ the numerators in $(p,k)$ have nonnegative coefficients, for $n\leq3$ the polynomials in $a$ have nonnegative coefficients after $a\mapsto a+3$, and for $n\geq a+1$ only nonnegative terms remain (\path{runs/lean_plan/phi3_generic.py}, \path{runs/lean_plan/phi3_edge.py}). Hence $R\geq0$.

```

## Theorem 5.6: the remark after the proof (7/4)

```latex
In fact \eqref{eq:cubic-B} and \eqref{eq:cubic-E} also hold with $\kappa_{t\tau}+\frac74\kappa_{r\sigma}\geq0$ in place of $\kappa_{t\tau}+\kappa_{r\sigma}\geq0$; the other coefficients and the key inequality do not involve the condition. For \eqref{eq:cubic-E}, and for \eqref{eq:cubic-B} with $n\geq6$, the tail sums above stay nonnegative. For \eqref{eq:cubic-B} with $n\leq5$ the transfers alone do not suffice. There the coefficient forms are certified after the substitution $u_0=zu_1$, $0\leq z\leq\min(\ell,1/q)$ with $q=u_2/u_1$, in the regimes $z=0$, $z=\ell$ and $z=1/q$ (\path{runs/cubic/bdetour_u.py}, \path{runs/cubic/edetour_u.py}). Hence Theorem~\ref{thm:lc-cubic} holds with $r\sigma\leq\frac74t\tau$ in place of $r\sigma\leq t\tau$. With $\frac95$ the certificate of \path{runs/cubic/bdetour_u.py} fails. ```
