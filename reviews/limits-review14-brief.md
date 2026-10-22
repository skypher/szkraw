# Review round 14: Section 8 (Log-concave profiles), Theorem 8.1 and Lemmas 8.2-8.4

Please give an adversarial, line-by-line review of Section 8 of paper.tex at commit aadd5209952eec0c453cad1a891529d86cb4f33f (github.com/skypher/szkraw; paper.tex SHA-256 e3e33ee0a0937df0768601dca74dfe80eb58b356b3d9f2403a8c38c9d921d8b6). Theorem 8.1 claims nonnegative linearization for every N, every 0 < r <= 1, and every constant-ratio array whose profile has nonnegative log-concave Newton coefficients without internal zeros. This would settle a problem that is open in the literature for these arrays (Szwarc's Problem 2 for finite systems, deep products), so please try hard to break it. Earlier sections of the paper (Sections 1-7, 9) were reviewed in previous rounds; the setting is in Section 2 (equation (2.1): a_0 = 1, b_0 = c_0 = 0, a_N = 0, a_i + b_i + c_i = 1, polynomials R_i with R_i(1) = 1, linearization on the finite orthogonality support).

Please check in particular:
1. The rescaling to y p_i = a_i p_{i+1} + t d_i p_i + d_i p_{i-1} with t = (1-r)/sqrt(r), the formula g(m,n;k) = r^((m+n-k)/2) H_{mn}^k, the normalization E_i = e_i p_i and its three-term relation including i = N (terminal relation).
2. The kernel equation (L_z - L_w) K_k = 0: the generating-function identity y F = L_z F with L_z = (z^-1 + t - z) d(theta_z) + z (exactness at both ends), the use of the basis E_k, symmetry of K_k, the initial values, and the support claim omega_{l,a} = 0 for l + a > N.
3. Lemma 8.2: the Vandermonde step, the expansion chi_n = sum_j (-1)^j C(n-j, j) S^(n-2j) Z^j, the conventions chi_-1 = 0 and (z^-1 - w^-1)/(z - w) = -Z^-1, the identification of the three families with W_{2j+1,j}, W_{2j+2,j}, W_{2j+2,j+1}, and the signs (-1)^j.
4. Lemma 8.3: preservation of log-concavity without internal zeros under v_i = u_i + u_{i+1}, the start sequence (0, nu_1, nu_2, ...), the balanced-product inequalities used, and the final addition.
5. Lemma 8.4: the lower bounds A_0 >= a f_1, B_0 >= C(a,2) f_2, the binomial identities, the coefficients gamma_m and gamma'_m, the three quotients, their ranges and minima (5, 5, 6), and the claim that they increase with j.
6. The proof of Theorem 8.1: nonnegativity of the straight move on Omega, the operator decomposition, the matching argument for P^2 >= 4Q (entrywise, same power of t, intermediate nodes in Omega, denominators), and the induction omega >= (1/2) P omega.
7. Remark 8.5 (coefficientwise in t, weighted homogeneity, Bernstein coefficients).
8. The statements around the theorem: which arrays satisfy the hypotheses (Krawtchouk, Theorem 2.1, quadratic profiles) and which known counterexamples are excluded and why.
9. If you can, test the theorem numerically yourself on log-concave profiles at sizes N >= 20 (exact or high-precision linearization), and test that it fails for some non-log-concave convex profiles.
10. Verdict: PASS, PASS WITH MINOR FIXES (give replacement text), or FAIL (give the failing step or a counterexample).

The author's exact diagnostics (lc_kernel_check.py, tracked) check Lemma 8.3 on 19,440 instances, Lemma 8.4 for j = 1..4 on 70,560 instances, P^2 >= 4Q entrywise on 8 random log-concave profiles (N = 6-10), and the whole chain (recurrence (8.1), kernel, reduction to g) against direct linearization on 9,435 coefficients (N = 3-7, r in {1/4, 4/9, 1}). These are finite checks; the claim rests on the proof.

## Section 8 as submitted

\section{Log-concave profiles}\label{sec:lc}

Theorem~\ref{thm:criterion} requires the increments of the profile $d_i=b_i+c_i$ to be geometric. This section replaces that equality by inequalities on the Newton coefficients of the profile, for arrays with constant ratio $b_i/c_i$. Write
\[
\nu_k=\sum_{i=0}^k(-1)^{k-i}\binom ki d_i\qquad(k\geq1),\qquad\text{so that}\qquad d_n=\sum_{k=1}^n\binom nk\nu_k\quad(0\leq n\leq N).
\]
We say that $(\nu_k)_{1\leq k\leq N}$ is \emph{log-concave without internal zeros} if all $\nu_k\geq0$, the indices with $\nu_k>0$ form an interval $\{1,\ldots,K\}$, and $\nu_k^2\geq\nu_{k-1}\nu_{k+1}$ for $2\leq k\leq N-1$. Note $\nu_1=d_1>0$.

\begin{theorem}[Log-concave Newton criterion]\label{thm:lc}
Let $0=d_0<d_1<\cdots<d_N=1$ have Newton coefficients that are log-concave without internal zeros, let $0<r\leq1$, and put $a_i=1-d_i$, $b_i=(1-r)d_i$, $c_i=rd_i$. Then the system has nonnegative linearization.
\end{theorem}

The hypotheses are inequalities in the profile. They hold for the Krawtchouk arrays ($\nu=(1/N,0,\ldots,0)$), for all arrays of Theorem~\ref{thm:criterion} ($\nu_k$ proportional to $(q-1)^{k-1}$, log-concave with equality), and for every profile with $\nu_k=0$ for $k\geq3$, that is, every convex quadratic profile. The hypotheses exclude the known counterexamples: the convex counterexamples of Section~\ref{sec:open} have Newton coefficients of both signs, and the combinations $(1-\lambda)K_{N,r}+\lambda G_{N,q,r}$ of Section~\ref{sec:limits} with $0<\lambda<1$ have $\nu_k$ proportional to $(q-1)^k$ for $k\geq2$ but $\nu_1$ larger than $\nu_2/(q-1)$, so $\nu_2^2<\nu_1\nu_3$.

\paragraph{A rescaled system and a kernel.}
Fix $r$ and put $t=(1-r)/\sqrt r\geq0$. If $p_i$ is defined by $p_0=1$ and $yp_i=a_ip_{i+1}+td_ip_i+d_ip_{i-1}$ $(0\leq i<N)$, then $R_i(x)=r^{i/2}p_i(x/\sqrt r)$, so the coefficients $H_{mn}^k$ in $p_mp_n=\sum_kH_{mn}^kp_k$ on the support satisfy $g(m,n;k)=r^{(m+n-k)/2}H_{mn}^k$. It suffices to show $H_{mn}^k\geq0$. Put
\[
e_i=\prod_{j=0}^{i-1}\frac{a_j}{d_{j+1}},\qquad E_i=e_ip_i.
\]
Then $yE_i=d_{i+1}E_{i+1}+td_iE_i+a_{i-1}E_{i-1}$ on the support for $0\leq i\leq N$, with the terms $d_{N+1}E_{N+1}$ and $a_{-1}E_{-1}$ omitted; at $i=N$ this is the terminal relation. Write $E_mE_n=\sum_kL_{mn}^kE_k$, so that $H_{mn}^k=L_{mn}^ke_k/(e_me_n)$, and
\[
K_k(z,w)=\sum_{m,n=0}^NL_{mn}^kz^mw^n.
\]
Let $\theta_z=z\,\partial_z$ and let $d(\theta)=\sum_k\nu_k\binom\theta k$ act on polynomials by $d(\theta_z)z^i=d_iz^i$. For $F(z)=\sum_{i=0}^NE_iz^i$ the recurrence reads $yF(z)=\mathcal L_zF(z)$ with
\[
\mathcal L_z=(z^{-1}+t-z)\,d(\theta_z)+z,
\]
because $d_0=0$ removes the term $z^{-1}E_0$ and $1-d_N=0$ removes the term $z^{N+1}E_N$. Applying this to $F(z)F(w)=\sum_kK_k(z,w)E_k$ in the two variables separately and comparing coefficients of the basis $E_k$ gives $(\mathcal L_z-\mathcal L_w)K_k=0$. Since $K_k$ is symmetric, $K_k=\sum_{\ell,a\geq0}\omega_{\ell,a}S^aZ^\ell$ with $S=z+w$, $Z=zw$, and $K_k(z,0)=z^k$ gives $\omega_{0,a}=\mathbf1_{a=k}$. As $K_k$ has degree at most $N$ in $z$, comparing the coefficients of $z^{\ell+a}w^\ell$ by induction on $\ell$ gives $\omega_{\ell,a}=0$ whenever $\ell+a>N$.

\paragraph{The kernel recurrence.}
Put $f_n(\ell)=\sum_{h\geq0}\binom\ell h\nu_{n+h}$ with $\nu_0=0$ and $\nu_k=0$ for $k>N$, so $f_0(\ell)=d_\ell$, and
\[
W_{p,q}(\ell,a)=\sum_{n\geq p}\binom{n-p+q}q\binom an f_n(\ell)\geq0,
\]
and $A_j=W_{2j+1,j}$, $B_j=W_{2j+2,j}$, $C_j=W_{2j+2,j+1}$.

\begin{lemma}\label{lem:kernel-rec}
For all $\ell,a\geq0$,
\begin{equation}\label{eq:kernel-rec}
\begin{aligned}
d_{\ell+1}\omega_{\ell+1,a}={}&a_{\ell+a}\,\omega_{\ell,a}+\sum_{j\geq0}(-1)^j\Big(t\,A_j(\ell-j,a+2j+1)\,\omega_{\ell-j,a+2j+1}\\
&+B_j(\ell-j,a+2j+2)\,\omega_{\ell-j,a+2j+2}\\
&+C_j(\ell-j-1,a+2j+2)\,\omega_{\ell-j-1,a+2j+2}\Big),
\end{aligned}
\end{equation}
where $a_i=1-d_i$ is extended by the polynomial $d_i$ for $i>N$ and terms with a negative index are omitted.
\end{lemma}
\begin{proof}
Since $S^aZ^\ell=\sum_i\binom ai z^{\ell+i}w^{\ell+a-i}$, Vandermonde's identity $\binom{\ell+i}k=\sum_{p+q=k}\binom\ell q\binom ip$ and $\binom ai\binom ip=\binom ap\binom{a-p}{i-p}$ give
\[
d(\theta_z)\,S^aZ^\ell=\sum_{p,q\geq0}\nu_{p+q}\binom\ell q\binom ap\,z^pS^{a-p}Z^\ell .
\]
Hence $(\mathcal L_z-\mathcal L_w)S^aZ^\ell$ equals $(z-w)S^aZ^\ell$ plus $\sum_{p,q}\nu_{p+q}\binom\ell q\binom ap S^{a-p}Z^\ell$ times $(z^{p-1}-w^{p-1})+t(z^p-w^p)-(z^{p+1}-w^{p+1})$. Divide by $z-w$, using $\chi_n=(z^{n+1}-w^{n+1})/(z-w)=\sum_{j\geq0}(-1)^j\binom{n-j}jS^{n-2j}Z^j$ for $n\geq0$, $\chi_{-1}=0$ and $(z^{-1}-w^{-1})/(z-w)=-Z^{-1}$. Since $\sum_q\binom\ell q\nu_{p+q}=f_p(\ell)$, the quotient is
\[
\begin{aligned}
&-d_\ell S^aZ^{\ell-1}+a_{\ell+a}S^aZ^\ell\\
&+\sum_{j\geq0}(-1)^j\Big(tA_j(\ell,a)S^{a-2j-1}Z^{\ell+j}+B_j(\ell,a)S^{a-2j-2}Z^{\ell+j}+C_j(\ell,a)S^{a-2j-2}Z^{\ell+j+1}\Big).
\end{aligned}
\]
Here $-d_\ell S^aZ^{\ell-1}$ comes from $p=0$; the term $a_{\ell+a}S^aZ^\ell$ combines $S^aZ^\ell$ with the parts $j=0$ of $-\chi_p$, which sum to $-d_{\ell+a}S^aZ^\ell$ by Vandermonde; and the three families from $\chi_{p-2}$, $t\chi_{p-1}$ and $-(\chi_p-S^p)$, whose coefficients $\binom{p-2-j}j$, $\binom{p-1-j}j$ and $\binom{p-1-j}{j+1}$ are those of $B_j$, $A_j$ and $C_j$. Summing over $\ell,a$ with weights $\omega_{\ell,a}$ and taking the coefficient of $S^aZ^\ell$ gives \eqref{eq:kernel-rec}, because the monomials $S^aZ^\ell$ are linearly independent.
\end{proof}

\paragraph{The log-concavity inequality.}
\begin{lemma}\label{lem:lc-ineq}
Under the hypotheses of Theorem~\ref{thm:lc}, for $i,l\geq1$ and $\ell\geq0$,
\[
f_i(\ell)\,f_l(\ell+1)\geq d_{\ell+1}\,f_{i+l}(\ell).
\]
\end{lemma}
\begin{proof}
For a nonnegative finitely supported sequence $u$ that is log-concave without internal zeros, $v_i=u_i+u_{i+1}$ has the same property, since
$v_i^2-v_{i-1}v_{i+1}=(u_i^2-u_{i-1}u_{i+1})+(u_{i+1}^2-u_iu_{i+2})+(u_iu_{i+1}-u_{i-1}u_{i+2})$
and the last term is nonnegative by log-concavity. The sequence $(0,\nu_1,\nu_2,\ldots)$ has this property, and $f_i(\ell)$ is obtained from it by applying $u\mapsto v$ $\ell$ times. For such a sequence $g$, balanced products dominate: $g_ig_l\geq g_0g_{i+l}$ and $g_ig_{l+1}\geq g_1g_{i+l}$ for $i,l\geq1$. Adding these with $g=f(\ell)$ and using $g_l+g_{l+1}=f_l(\ell+1)$ and $g_0+g_1=f_0(\ell+1)=d_{\ell+1}$ gives the claim.
\end{proof}

\begin{lemma}\label{lem:detours}
Under the hypotheses of Theorem~\ref{thm:lc}, for all $j\geq1$ and $\ell,a\geq0$,
\[
\begin{aligned}
A_0(\ell,a)B_{j-1}(\ell+1,a-1)+B_0(\ell,a)A_{j-1}(\ell+1,a-2)&\geq4d_{\ell+1}A_j(\ell,a),\\
B_0(\ell,a)B_{j-1}(\ell+1,a-2)&\geq4d_{\ell+1}B_j(\ell,a),\\
B_0(\ell,a)C_{j-1}(\ell+1,a-2)&\geq4d_{\ell+1}C_j(\ell,a),
\end{aligned}
\]
with $W_{p,q}(\ell,a)=0$ for $a<0$.
\end{lemma}
\begin{proof}
Use $A_0(\ell,a)\geq af_1(\ell)$ and $B_0(\ell,a)\geq\binom a2f_2(\ell)$, expand the second factor, apply Lemma~\ref{lem:lc-ineq} to $f_1(\ell)f_n(\ell+1)$ and $f_2(\ell)f_n(\ell+1)$, and use $a\binom{a-1}n=(n+1)\binom a{n+1}$ and $\binom a2\binom{a-2}n=\binom{n+2}2\binom a{n+2}$. After division by $d_{\ell+1}$ the three left sides are bounded below by $\sum_m\gamma_m\binom amf_m(\ell)$ with
\[
\gamma_m=\binom{m+1}2\binom{m-j-2}{j-1},\qquad\binom m2\binom{m-j-3}{j-1},\qquad\binom m2\binom{m-j-2}j,
\]
while the right sides are $4\sum_m\gamma'_m\binom amf_m(\ell)$ with $\gamma'_m=\binom{m-j-1}j$, $\binom{m-j-2}j$ and $\binom{m-j-1}{j+1}$. Where $\gamma'_m>0$ the quotients are
\[
\frac{jm(m+1)}{2(m-j-1)},\qquad\frac{jm(m-1)}{2(m-j-2)},\qquad\frac{(j+1)m(m-1)}{2(m-j-1)},
\]
on $m\geq2j+1$, $m\geq2j+2$ and $m\geq2j+2$ respectively. They increase with $j$ for fixed $m$; at $j=1$ their minima over integers are $5$, $5$ and $6$. All quotients exceed $4$, and $f_m(\ell)\geq0$.
\end{proof}

\begin{proof}[Proof of Theorem~\ref{thm:lc}]
Let $\Omega=\{(\ell,a):\ell,a\geq0,\ \ell+a\leq N\}$, on which $\omega$ is supported. Read \eqref{eq:kernel-rec} as moves into the node $(\ell+1,a)$, each divided by $d_{\ell+1}>0$: the straight move from $(\ell,a)$ with weight $a_{\ell+a}\geq0$ on $\Omega$, and for each $j$ the three moves from $(\ell-j,a+2j+1)$, $(\ell-j,a+2j+2)$, $(\ell-j-1,a+2j+2)$ with weights $tA_j$, $B_j$, $C_j$. Every move raises $\ell$. Let $\mathcal U$ be the straight moves, $\mathcal P$ the moves with $j$ even and $\mathcal Q$ the moves with $j$ odd, all with nonnegative weights, so that $\omega=\beta+(\mathcal U+\mathcal P-\mathcal Q)\omega$ with $\beta=\omega|_{\ell=0}$.

We claim $\mathcal P^2\geq4\mathcal Q$ entrywise. A move of $\mathcal Q$ with index $j$ from $x=(\ell,a)$ is matched by the two-step paths in $\mathcal P^2$ that start with $A_0$ or $B_0$ from $x$ (index $0$, landing at $(\ell+1,a-1)$ or $(\ell+1,a-2)$, which lie in $\Omega$) and continue with the move of the same type and index $j-1$ (even), as in Lemma~\ref{lem:detours}: $A_j$ by $A_0$ then $B_{j-1}$ and $B_0$ then $A_{j-1}$; $B_j$ by $B_0$ then $B_{j-1}$; $C_j$ by $B_0$ then $C_{j-1}$. These paths end at the target of the matched move, carry the same power of $t$, and have the extra denominator $d_{\ell+1}$ of the intermediate node. Distinct moves of $\mathcal Q$ have distinct displacements, so their paths are distinct, and Lemma~\ref{lem:detours} gives the claim.

Now show by induction on the level that $\omega\geq0$ and $\omega\geq\frac12\mathcal P\omega$. Both hold at $\ell=0$. If they hold below a node $y$ at level $\ell+1\geq1$, then, all weights being nonnegative, $(\mathcal P\omega)(y)\geq\frac12(\mathcal P^2\omega)(y)\geq2(\mathcal Q\omega)(y)$, and
\[
\omega(y)=(\mathcal U\omega)(y)+(\mathcal P\omega)(y)-(\mathcal Q\omega)(y)\geq\tfrac12(\mathcal P\omega)(y)\geq0.
\]
Hence all $\omega_{\ell,a}\geq0$, so $K_k$ has nonnegative coefficients in $z,w$, so $L_{mn}^k\geq0$, $H_{mn}^k\geq0$ and $g(m,n;k)\geq0$.
\end{proof}

\begin{remark}
The argument is valid coefficientwise in $t$. With independent parameters in $yp_i=a_ip_{i+1}+ud_ip_i+vd_ip_{i-1}$, weighted homogeneity ($\deg y=\deg u=1$, $\deg v=2$) then shows that each linearization coefficient is a polynomial in $(u,v)$ with nonnegative coefficients. Consequently every $g(m,n;k)$ of the array of Theorem~\ref{thm:lc}, as a function of $r$, has nonnegative Bernstein coefficients. The diagnostics \path{lc_kernel_check.py} verify Lemmas~\ref{lem:kernel-rec}--\ref{lem:detours} and the matching $\mathcal P^2\geq4\mathcal Q$ in exact arithmetic on random log-concave profiles.
\end{remark}


