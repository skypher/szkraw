# Review round 17: Section 8, new Theorem 8.6 (varying ratio) and Corollary 8.7

Please give an adversarial, line-by-line review of the new part of Section 8 of paper.tex at commit 551a54e0fd285b2053a546c8a34409691d7dde3c (github.com/skypher/szkraw; paper.tex SHA-256 d7370714132bdf33f79766c3f1e0cab06dab603fd09ed2960a3c0e9f7dba3ca0), from the paragraph "Varying ratio" to the end of the section. Theorem 8.1 and Lemmas 8.2–8.4 passed your rounds 14–16 and are quoted for reference.

Theorem 8.6 claims nonnegative linearization for every stochastic finite array (a + b + c = 1, b_0 = c_0 = 0, a_N = 0, a_i > 0 for i < N, c_i > 0 for i ≥ 1) whose downward coefficients c have log-concave Newton coefficients without internal zeros, and whose diagonal coefficients b have nonnegative Newton coefficients satisfying two mixed inequalities. Corollary 8.7 says the mixed inequalities hold when β_k = w_k κ_k with w nonincreasing; the ratio c_i/(b_i + c_i) is then nondecreasing, and constant w gives Theorem 8.1. This would settle the varying-ratio question left open in Section 10 for a natural class of increasing ratios, so please try hard to break it.

Please check in particular:
1. The normalization E_i = e_i R_i with e_{i+1}/e_i = a_i/c_{i+1}, the relation x E_i = c_{i+1} E_{i+1} + b_i E_i + a_{i-1} E_{i-1} (including i = 0 and the terminal i = N), and the generator L_z = z^-1 c(θ) + b(θ) + z(1 − b(θ) − c(θ)), exactness at both ends.
2. The displayed formula for (L_z − L_w) S^a Z^ℓ/(z − w) with χ_-2 = −Z^-1, χ_-1 = 0, including the p = 0 terms of both parts.
3. The kernel recurrence: the identification of the four families A^ψ_j, B_j, C_j, C^ψ_j with W^ψ_{2j+1,j}, W_{2j+2,j}, W_{2j+2,j+1}, W^ψ_{2j+2,j+1}, the signs (−1)^j, the straight weight a_{ℓ+a}, the left-hand coefficient c_{ℓ+1}, the support ℓ + a ≤ N, and that β_0 = 0 / the constant term of b plays no role.
4. The detour inequalities: that the proof of Lemma 8.4 transfers with the stated lower bounds, which index ranges of n actually occur (n ≥ 2 in the first mixed inequality, n ≥ 1 in the second), and the merged move C_j + C^ψ_j (same displacement) in the matching argument for P² ≥ 4Q.
5. The proof of Corollary 8.7: the double-sum identity for H_i G_{i+1} − H_{i+1} G_i, the pairing (x, y) ↔ (y+1, x−1) and its bijectivity onto the terms with x ≤ y (unpaired terms), the log-concavity of binomial coefficients used, the chaining with zero cases, the two applications of Lemma 8.3, the case i = 0 giving monotonicity of the ratio, and the identification of constant w with Theorem 8.1.
6. The example (convex quadratic c, b with w_1 > w_2) and the two exclusions stated after Corollary 8.7.
7. If you can, test Theorem 8.6 / Corollary 8.7 numerically yourself (exact linearization) at small N (N = 2, 3, 4 exhaustively random, including ratios near 1 and near 0) and at N ≥ 15, and test that it fails when the mixed inequalities fail.
8. Verdict: PASS, PASS WITH MINOR FIXES (give replacement text), or FAIL (give the failing step or a counterexample).

The author's exact diagnostics (runs/varratio/kernel_check.py, stoch.py, mixed.py, tracked) check the kernel recurrence against direct linearization on 3,670 coefficients of arbitrary stochastic arrays (N = 2–6, 0 mismatches), P² ≥ 4Q entrywise for Corollary 8.7 members at N = 4–10 (1,075 entries, 0 violations; spike controls violating the mixed inequalities give 60 violations), and property (P) directly on about 6,900 members satisfying the mixed inequalities at N = 2–5 and 2,842 at N = 6–12 (0 failures; all failures in the controls violate the mixed inequalities). These are finite checks; the claim rests on the proof.

## Section 8 as submitted

\section{Log-concave profiles}\label{sec:lc}

Theorem~\ref{thm:criterion} requires the increments of the profile $d_i=b_i+c_i$ to be geometric. This section replaces that equality by inequalities on the Newton coefficients of the profile, for arrays with constant ratio $b_i/c_i$. Write
\[
\nu_k=\sum_{i=0}^k(-1)^{k-i}\binom ki d_i\quad(1\leq k\leq N),\qquad d_n=\sum_{k=1}^n\binom nk\nu_k\quad(0\leq n\leq N);
\]
below we put $\nu_0=0$ and $\nu_k=0$ for $k>N$.
We say that $(\nu_k)_{1\leq k\leq N}$ is \emph{log-concave without internal zeros} if all $\nu_k\geq0$, the indices with $\nu_k>0$ form an interval $\{1,\ldots,K\}$, and $\nu_k^2\geq\nu_{k-1}\nu_{k+1}$ for $2\leq k\leq N-1$. Note $\nu_1=d_1>0$.

\begin{theorem}[Log-concave Newton criterion]\label{thm:lc}
Let $0=d_0<d_1<\cdots<d_N=1$ have Newton coefficients that are log-concave without internal zeros, let $0<r\leq1$, and put $a_i=1-d_i$, $b_i=(1-r)d_i$, $c_i=rd_i$. Then the system has nonnegative linearization.
\end{theorem}

The hypotheses are inequalities in the profile. They hold for the Krawtchouk arrays ($\nu=(1/N,0,\ldots,0)$), for all arrays of Theorem~\ref{thm:criterion} ($\nu_k$ proportional to $(q-1)^{k-1}$, log-concave with equality). The hypotheses also hold for every admissible convex quadratic profile: $\nu_1>0$, $\nu_2\geq0$ when $N\geq2$, and $\nu_k=0$ for $3\leq k\leq N$. The hypotheses exclude the known counterexamples with constant ratio. The convex counterexamples recorded in Section~\ref{sec:open} have Newton coefficients of both signs. For the combinations $(1-\lambda)K_{N,r}+\lambda G_{N,q,r}$ discussed there, with $q>1$, $N\geq3$ and $0<\lambda<1$, one has $\nu_1=(1-\lambda)/N+\lambda/[N]_q$ and $\nu_k=\lambda(q-1)^{k-1}/[N]_q$ for $2\leq k\leq N$, so $\nu_2^2-\nu_1\nu_3=-\lambda(1-\lambda)(q-1)^2/(N[N]_q)<0$.

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
Hence $(\mathcal L_z-\mathcal L_w)S^aZ^\ell$ equals $(z-w)S^aZ^\ell$ plus $\sum_{p,q}\nu_{p+q}\binom\ell q\binom ap S^{a-p}Z^\ell$ times $(z^{p-1}-w^{p-1})+t(z^p-w^p)-(z^{p+1}-w^{p+1})$. Divide by $z-w$, using $\chi_n=(z^{n+1}-w^{n+1})/(z-w)=\sum_{0\leq j\leq\lfloor n/2\rfloor}(-1)^j\binom{n-j}jS^{n-2j}Z^j$ for $n\geq0$, $\chi_{-1}=0$ and $(z^{-1}-w^{-1})/(z-w)=-Z^{-1}$. Since $\sum_q\binom\ell q\nu_{p+q}=f_p(\ell)$, the quotient is
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
The argument is valid coefficientwise in $t$. With independent parameters in $yp_i=a_ip_{i+1}+ud_ip_i+vd_ip_{i-1}$, weighted homogeneity ($\deg y=\deg u=1$, $\deg v=2$) then shows that each linearization coefficient is a polynomial in $(u,v)$ with nonnegative coefficients: for $D=m+n-k\geq0$ it has the form $\sum_{0\leq j\leq\lfloor D/2\rfloor}h_ju^{D-2j}v^j$ with $h_j\geq0$, and it vanishes for $D<0$. Consequently every $g(m,n;k)$ of the array of Theorem~\ref{thm:lc}, as a function of $r$, equals $\sum_jh_jr^j(1-r)^{D-2j}$; multiplying the $j$-th term by $(r+(1-r))^j=1$ shows that its coefficients in the Bernstein basis of degree $D$ are $\binom Ds^{-1}\sum_{j\leq s\leq2j}h_j\binom j{s-j}\geq0$. The diagnostics \path{lc_kernel_check.py} verify Lemmas~\ref{lem:kernel-rec}--\ref{lem:detours} and the matching $\mathcal P^2\geq4\mathcal Q$ in exact arithmetic on random log-concave profiles.
\end{remark}

\paragraph{Varying ratio.}
The kernel argument also works in the stochastic normalization itself, with independent diagonal and downward coefficients. Let $a_i+b_i+c_i=1$ for $0\leq i\leq N$, with $b_0=c_0=0$, $a_N=0$, $a_i>0$ for $i<N$ and $c_i>0$ for $i\geq1$. Write
\[
\kappa_k=\sum_{i=0}^k(-1)^{k-i}\binom kic_i,\qquad\beta_k=\sum_{i=0}^k(-1)^{k-i}\binom kib_i\qquad(1\leq k\leq N),
\]
with $\kappa_k=\beta_k=0$ for $k=0$ and $k>N$, and put $\varphi_n(\ell)=\sum_{h\geq0}\binom\ell h\kappa_{n+h}$ and $\psi_n(\ell)=\sum_{h\geq0}\binom\ell h\beta_{n+h}$, so that $\varphi_0(\ell)=c_\ell$ and $\psi_0(\ell)=b_\ell$ for $\ell\leq N$.

\begin{theorem}[Varying ratio]\label{thm:lc-vary}
Let $(\kappa_k)$ be log-concave without internal zeros and $\beta_k\geq0$ for all $k$. Suppose that for $0\leq\ell\leq N-1$
\[
\psi_1(\ell)\,\varphi_n(\ell+1)\geq c_{\ell+1}\,\psi_{n+1}(\ell)\quad(n\geq2),\qquad\varphi_2(\ell)\,\psi_n(\ell+1)\geq c_{\ell+1}\,\psi_{n+2}(\ell)\quad(n\geq1).
\]
Then the system has nonnegative linearization.
\end{theorem}

\begin{corollary}\label{cor:lc-vary}
If $(\kappa_k)$ is log-concave without internal zeros and $\beta_k=w_k\kappa_k$ for $k\geq1$ with $w_1\geq w_2\geq\cdots\geq0$, then the system has nonnegative linearization. The ratio $c_i/(b_i+c_i)$ is nondecreasing in $i\geq1$, and it is constant when $w$ is constant on the support of $\kappa$; these are the arrays of Theorem~\ref{thm:lc}.
\end{corollary}

For example, if $c$ is a convex quadratic in $i$ ($\kappa_1,\kappa_2>0$, $\kappa_k=0$ for $k\geq3$) and $b_i=w_1\kappa_1i+w_2\kappa_2\binom i2$ with $w_1>w_2\geq0$, scaled so that $b_N+c_N=1$, the ratio $c_i/(b_i+c_i)$ increases strictly. The hypotheses exclude the counterexample recorded in Section~\ref{sec:open}, whose diagonal coefficients $b=(0,1,1,1)/91$ have Newton coefficients of both signs. They also exclude linearly increasing ratios $c_i/(b_i+c_i)$ with a linear profile, whose diagonal coefficients are concave.

\begin{proof}[Proof of Theorem~\ref{thm:lc-vary}]
Put $e_i=\prod_{j<i}a_j/c_{j+1}$ and $E_i=e_iR_i$. Then $xE_i=c_{i+1}E_{i+1}+b_iE_i+a_{i-1}E_{i-1}$ on the support, and $F=\sum_iE_iz^i$ satisfies $xF=\mathcal L_zF$ with
\[
\mathcal L_z=z^{-1}c(\theta_z)+b(\theta_z)+z\bigl(1-b(\theta_z)-c(\theta_z)\bigr),
\]
where $c(\theta)=\sum_k\kappa_k\binom\theta k$ and $b(\theta)=\sum_k\beta_k\binom\theta k$. As in Section~\ref{sec:lc}, $K_k=\sum_{m,n}L_{mn}^kz^mw^n$, with $E_mE_n=\sum_kL_{mn}^kE_k$, satisfies $(\mathcal L_z-\mathcal L_w)K_k=0$, and $K_k=\sum\omega_{\ell,a}S^aZ^\ell$ with $\omega_{0,a}=\mathbf1_{a=k}$ and $\omega_{\ell,a}=0$ for $\ell+a>N$. The computation in the proof of Lemma~\ref{lem:kernel-rec} gives
\[
\frac{(\mathcal L_z-\mathcal L_w)S^aZ^\ell}{z-w}=S^aZ^\ell+\sum_{p\geq0}\binom apS^{a-p}Z^\ell\Bigl(\varphi_p(\ell)(\chi_{p-2}-\chi_p)+\psi_p(\ell)(\chi_{p-1}-\chi_p)\Bigr),
\]
with $\chi_{-2}=-Z^{-1}$ and $\chi_{-1}=0$. Collecting terms as there, with $W_{p,q}$ formed from $\varphi$ and $W^\psi_{p,q}$ from $\psi$, gives
\[
\begin{aligned}
c_{\ell+1}\omega_{\ell+1,a}={}&a_{\ell+a}\,\omega_{\ell,a}+\sum_{j\geq0}(-1)^j\Big(A^\psi_j(\ell-j,a+2j+1)\,\omega_{\ell-j,a+2j+1}+B_j(\ell-j,a+2j+2)\,\omega_{\ell-j,a+2j+2}\\
&+\bigl(C_j+C^\psi_j\bigr)(\ell-j-1,a+2j+2)\,\omega_{\ell-j-1,a+2j+2}\Big),
\end{aligned}
\]
where $A^\psi_j=W^\psi_{2j+1,j}$, $C^\psi_j=W^\psi_{2j+2,j+1}$, and $B_j=W_{2j+2,j}$, $C_j=W_{2j+2,j+1}$. The straight weight is $1-c_{\ell+a}-b_{\ell+a}=a_{\ell+a}$, extended polynomially beyond $N$, and $\beta_0=0$. All weights are nonnegative on $\Omega$.

The detours of Lemma~\ref{lem:detours} hold with $d_{\ell+1}$ replaced by $c_{\ell+1}$:
\[
\begin{aligned}
A^\psi_0(\ell,a)B_{j-1}(\ell+1,a-1)+B_0(\ell,a)A^\psi_{j-1}(\ell+1,a-2)&\geq4c_{\ell+1}A^\psi_j(\ell,a),\\
B_0(\ell,a)B_{j-1}(\ell+1,a-2)&\geq4c_{\ell+1}B_j(\ell,a),\\
B_0(\ell,a)\bigl(C_{j-1}+C^\psi_{j-1}\bigr)(\ell+1,a-2)&\geq4c_{\ell+1}\bigl(C_j+C^\psi_j\bigr)(\ell,a).
\end{aligned}
\]
The proof of Lemma~\ref{lem:detours} applies, with the lower bounds $A^\psi_0(\ell,a)\geq a\psi_1(\ell)$ and $B_0(\ell,a)\geq\binom a2\varphi_2(\ell)$. Lemma~\ref{lem:lc-ineq} for $\varphi$ handles the products $\varphi_2(\ell)\varphi_n(\ell+1)$. The two hypotheses of the theorem handle $\psi_1(\ell)\varphi_n(\ell+1)$ for $n\geq2$ and $\varphi_2(\ell)\psi_n(\ell+1)$ for $n\geq1$, which are the indices that occur. The moves $C_j$ and $C^\psi_j$ have the same displacement and are treated as one move. With this, the proof of Theorem~\ref{thm:lc} gives $\omega\geq0$, hence $L_{mn}^k\geq0$ and $g(m,n;k)=L_{mn}^ke_k/(e_me_n)\geq0$.
\end{proof}

\begin{proof}[Proof of Corollary~\ref{cor:lc-vary}]
Fix $\ell$ and write $G_i=\varphi_i(\ell)$, $H_i=\psi_i(\ell)$ and $u_x=\binom\ell{x-i}$. For $i\geq0$,
\[
H_iG_{i+1}-H_{i+1}G_i=\sum_{x,y\geq i}u_xu_y\kappa_x\kappa_{y+1}(w_x-w_{y+1}).
\]
Terms with $x\leq y$ are nonnegative. Each term with $x\geq y+2$ pairs with the term at $(y+1,x-1)$. The pair sums to $\kappa_x\kappa_{y+1}(w_{y+1}-w_x)(u_{y+1}u_{x-1}-u_xu_y)\geq0$, because $w$ is nonincreasing and the binomial coefficients are log-concave. Hence $H_{i+1}G_i\leq H_iG_{i+1}$.

Since the support of $(G_i)$ is an interval and $\beta_k=0$ where $\kappa_k=0$, chaining gives $H_{n+1}G_1\leq H_1G_{n+1}$, $H_{n+2}G_n\leq H_nG_{n+2}$ and $H_{n+2}G_{n+1}\leq H_{n+1}G_{n+2}$. Lemma~\ref{lem:lc-ineq} with $(i,l)=(1,n)$ and $(2,n)$ reads $G_1(G_n+G_{n+1})\geq(G_0+G_1)G_{n+1}$ and $G_2(G_n+G_{n+1})\geq(G_0+G_1)G_{n+2}$, where $G_0+G_1=c_{\ell+1}$ and $G_n+G_{n+1}=\varphi_n(\ell+1)$. Multiplying gives the two hypotheses of Theorem~\ref{thm:lc-vary}. The case $i=0$ of the first display, with $\beta_0=\kappa_0=0$, reads $b_{\ell+1}c_\ell\leq b_\ell c_{\ell+1}$, so $b_i/c_i$ is nonincreasing and $c_i/(b_i+c_i)$ is nondecreasing. If $w$ is constant on the support of $\kappa$, then $b$ is proportional to $c$, and with $d=b+c$ the array is that of Theorem~\ref{thm:lc}.
\end{proof}

