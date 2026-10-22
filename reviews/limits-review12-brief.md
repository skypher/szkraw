# Review round 12: Theorem 7.12 (All products) and Corollary 7.13 (Heavy top step)

Please review a new passage in paper.tex at commit 88c1b4d8cdcc14bcaf0d0e722027faac26ec3b89 (github.com/skypher/szkraw; paper.tex SHA-256 080b21a33dd50cd854798c25f691d4fadea2402e568a50a8c454af8179d273c1). It extends the finite version of Szwarc's cone argument (Theorem 7.10, quoted below for reference) from products with n + m <= N to all products, under hypotheses that hold up to the terminal index. A corollary gives an inequality criterion for constant-ratio arrays. There is also a changed sentence in Section 8.

Please check:
1. Is the proof of Theorem 7.12 correct and complete? In particular: Hu = 0 on all of {0..N}^2 (terminal relation on the support); the boundary convention gamma_N = 0 at i = N; the classification of the nonzero values of H*v for pairs with n + m > N (truncation of the cone at i = N); and the claim that the gamma_i - alpha_j terms occur only with i <= N - 1.
2. Is Corollary 7.13 correct, including the claim that alpha_n + gamma_n = sqrt(r) for every 0 <= n <= N?
3. Are the follow-up remarks correct: non-convex profiles allowed; arrays (eq:parameters) with q >= 2 included (d_(N-1) <= 1/2); Krawtchouk with N >= 3 excluded; sharpness g(2,2;2) = (1 - 2 d_1)/(1 - d_1) at N = 2, r = 1; the remark on the edge terms for convex profiles and for Krawtchouk.
4. Is the changed Section 8 sentence accurate?
5. Verdict: PASS, PASS WITH MINOR FIXES (give replacement text), or FAIL.

Exact diagnostics (heavy_top_check.py, tracked): 360 full tables for random increasing non-convex profiles with d_(N-1) <= 1/2 (N = 3..10, r in {1, 1/2, 1/7}) have no negative coefficient; the N = 2 formula is checked at four values of d_1; 113 random non-constant-ratio arrays satisfying (i)-(iii) with sigma_n = s^n (N = 2..4) have no negative coefficient. Separately, the cone identity behind the proof was checked exactly (2540 identities, N = 3..8, deep pairs included).

## Theorem 7.10 and its proof (unchanged, for reference)

\begin{theorem}[Low products]\label{thm:low}
Let $a,b,c$ satisfy \eqref{eq:basic}. Suppose that for some positive $\sigma$,
\begin{enumerate}
\item $\beta_n$ is nondecreasing for $0\leq n\leq N-1$, and $\alpha_n$ is nondecreasing for $0\leq n\leq N$;
\item $\alpha_n+\gamma_n$ is nondecreasing for $0\leq n\leq N-2$;
\item $\gamma_i\geq\alpha_j$ whenever $0\leq j\leq i$ and $i+j\leq N-2$.
\end{enumerate}
Then $g(n,m;k)\geq0$ whenever $n+m\leq N$. Consequently a product coefficient can be negative only for a triple $(n,m,k)$ in which each two indices have sum greater than $N$.
\end{theorem}
\begin{proof}
Coefficients in two positive normalizations differ by positive factors, so we may work with the polynomials $\widetilde P_n$ of~\cite[(3.9)]{szwarc}, which satisfy $x\widetilde P_n=\alpha_{n+1}\widetilde P_{n+1}+\beta_n\widetilde P_n+\gamma_{n-1}\widetilde P_{n-1}$ with $\alpha_{N+1}=0$. Fix $k$ and let $u(n,m)$ be the coefficient of $\widetilde P_k$ in $\widetilde P_n\widetilde P_m$. Multiplying the product by $x$ in the two ways shows $Hu=0$ at every point of $\{0,\ldots,N\}^2$, where $H=L_1-L_2$ is the operator of~\cite[\S3.4]{szwarc} built from these coefficients, and $u(n,0)=\boldsymbol1_{n=k}$, $u(n,m)=u(m,n)$.

We prove $u(n,m)\geq0$ for $n\geq m$, $n+m\leq N$, by induction on $m$, following~\cite[Theorem~3.4]{szwarc}. Let $v$ be the indicator of the points $(i,j)$ with $j<m$, $|i-n|<m-j$ and $n+m-i-j$ odd. Every point in the support of $v$ satisfies $j<i$ and $i+j\leq n+m-1\leq N-1$, so $\langle Hu,v\rangle=0$ involves only rows where the finite recurrence holds. Hence $0=\langle u,H^*v\rangle$, and every point in the support of $H^*v$ has $i+j\leq n+m\leq N$. With $\alpha_0=0$ and $v$ set to zero outside its support, transposition gives
\[
(H^*v)(i,j)=\alpha_iv(i-1,j)+\gamma_iv(i+1,j)+(\beta_i-\beta_j)v(i,j)-\alpha_jv(i,j-1)-\gamma_jv(i,j+1),
\]
as in~\cite[\S3.4]{szwarc}. At $(n,m)$ it is $-\alpha_m<0$. At the other points it is one of
\[
\beta_i-\beta_j,\quad (\alpha_i+\gamma_i)-(\alpha_j+\gamma_j),\quad \alpha_i-\alpha_j,\quad \gamma_i-\alpha_j,
\]
with $j\leq i$. The first occurs only for $i\leq N-1$. The second occurs only at interior points, where $i+j\leq n+m-2\leq N-2$. The third occurs on the edge $i+j=n+m$. The last occurs on the edge $i-j=n-m$, where $i+j\leq N-2$. Hypotheses (i)--(iii) make all of these nonnegative, and all such points have second coordinate less than $m$. By the induction hypothesis and $u(i,0)\geq0$, $\alpha_mu(n,m)=\sum_{(i,j)\neq(n,m)}(H^*v)(i,j)u(i,j)\geq0$. For the last statement, $g(n,m;k)$, $g(n,k;m)$ and $g(m,k;n)$ are positive multiples of $\int R_nR_mR_k\,d\mu$.
\end{proof}

## New passage (after Corollary 7.11)

The restriction $n+m\leq N$ in Theorem~\ref{thm:low} is needed only for hypothesis (iii). If the inequalities hold up to the terminal index, the same argument controls every product.

\begin{theorem}[All products]\label{thm:all}
Let $a,b,c$ satisfy \eqref{eq:basic}, and put $\gamma_N=0$. Suppose that for some positive $\sigma$,
\begin{enumerate}
\item $\beta_n$ and $\alpha_n$ are nondecreasing for $0\leq n\leq N$;
\item $\alpha_n+\gamma_n$ is nondecreasing for $0\leq n\leq N$;
\item $\gamma_i\geq\alpha_j$ whenever $0\leq j\leq i\leq N-1$.
\end{enumerate}
Then the system has nonnegative linearization.
\end{theorem}
\begin{proof}
Use the notation of the proof of Theorem~\ref{thm:low}. Since $\alpha_{N+1}=0$, the relation $x\widetilde P_N=\beta_N\widetilde P_N+\gamma_{N-1}\widetilde P_{N-1}$ is the terminal relation, which holds on the support. So $Hu=0$ at every point of $\{0,\ldots,N\}^2$, as noted there. We prove $u(n,m)\geq0$ for all $n\geq m$ by induction on $m$. Let $v$ be the indicator of the points $(i,j)$ with $0\leq i\leq N$, $j<m$, $|i-n|<m-j$ and $n+m-i-j$ odd. Then $0=\langle Hu,v\rangle=\langle u,H^*v\rangle$, and $H^*v$ is given by the formula in that proof. At $i=N$ the term $\gamma_Nv(N+1,j)$ is absent; this is the convention $\gamma_N=0$. Hence $H^*v(n,m)=-\alpha_m$, and at every other point $(i,j)$ with $H^*v(i,j)\neq0$ we have $j<m$, $j\leq i\leq N$, and $H^*v(i,j)$ is one of
\[
\beta_i-\beta_j,\quad (\alpha_i+\gamma_i)-(\alpha_j+\gamma_j),\quad \alpha_i-\alpha_j,\quad \gamma_i-\alpha_j.
\]
The last one occurs only on the edge $i-j=n-m$, where $i\leq n-1\leq N-1$. Hypotheses (i)--(iii) make all of these nonnegative. The induction hypothesis then gives $\alpha_mu(n,m)\geq0$, and the case $n<m$ follows by symmetry.
\end{proof}

\begin{corollary}[Heavy top step]\label{cor:heavy}
Let $b_i=(1-r)d_i$, $c_i=rd_i$, $a_i=1-d_i$ with $0<r\leq1$ and an increasing profile $0=d_0<d_1<\cdots<d_N=1$ with $d_{N-1}\leq\tfrac12$. Then the system has nonnegative linearization.
\end{corollary}
\begin{proof}
Take $\sigma_n=r^{n/2}$. Then $\alpha_n=\sqrt r\,d_n$ and $\gamma_n=\sqrt r\,(1-d_n)$ for $n<N$, $\gamma_N=0$, and $\beta_n=(1-r)d_n$. So $\alpha$ and $\beta$ are nondecreasing, and $\alpha_n+\gamma_n=\sqrt r$ for every $0\leq n\leq N$, because $d_N=1$. For $j\leq i\leq N-1$, $\gamma_i-\alpha_j=\sqrt r\,(1-d_i-d_j)\geq\sqrt r\,(1-2d_{N-1})\geq0$. Theorem~\ref{thm:all} applies.
\end{proof}

The profile need not be convex. The corollary contains the arrays \eqref{eq:parameters} with $q\geq2$, since then $d_{N-1}=(q^{N-1}-1)/(q^N-1)\leq\tfrac12$, but not the Krawtchouk arrays with $N\geq3$. The bound $d_{N-1}\leq\tfrac12$ cannot be relaxed in general: for $N=2$ and $r=1$, $g(2,2;2)=(1-2d_1)/(1-d_1)$. For constant-ratio arrays with a convex profile, $d_i+d_j\leq d_{i+j}\leq1$ whenever $i+j\leq N$, so the only terms that can be negative in the proof are the edge terms $\gamma_i-\alpha_j=\sqrt r\,(1-d_i-d_j)$ with $i+j>N$. For the Krawtchouk arrays they equal $\sqrt r\,(N-i-j)/N$, and on deep triples they must be compensated by the other terms.

## Changed sentence in Section 8

Theorem~\ref{thm:low} supplies such hypotheses for all triples except those whose pairwise sums all exceed $N$. Theorem~\ref{thm:all} supplies them for all triples when hypothesis (iii) holds up to the terminal index, and Corollary~\ref{cor:heavy} contains the arrays \eqref{eq:parameters} with $q\geq2$ but not the Krawtchouk arrays. The remaining task is to control the deep triples by inequalities that contain the whole geometric criterion, in particular the Krawtchouk arrays.
