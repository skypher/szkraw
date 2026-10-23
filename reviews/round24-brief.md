# Independent review, round 24: Lemma 8.15 and Theorem 8.16 (log-concave ratios on log-concave Newton profiles)

Repository: github.com/skypher/szkraw, commit c145f1f (paper.tex; scripts under runs/varratio/).

Theorem 8.16 is new. It was found and proved here, without research consultation. Its proof is computer-assisted. Please review completely and independently, including the certificate scripts. This is a mathematics review, not a Lean review.

The proof reuses the move/detour/resummation framework of Theorems 8.6, 8.9 and 8.11 and Lemmas 8.3–8.4 (read them in paper.tex), Proposition 8.14 (Walkup), and the proof of Theorem 8.9 for steps (ii)–(iii).

Check in particular:
1. Setup: the truncation remark; log-concavity of x ↦ ρ(x); both inequalities (8.7); the Leibniz expansion of φ_n and ψ_n.
2. Detours:
   - V: the pointwise bound with factor n/(n+2), and the quotient j(m−1)(m−2)/(2(m−j−1)) ≥ 6.
   - Ŵ: the three-term pairing, the θ_{n,i} (collect them yourself), and the quotient bound > 2, for every i including i = m.
   - That H, C′ and B carry over verbatim.
   - The resummation constants: μ_V = 6, μ_W = 2, key with γ_V = 2.
3. Key inequality (8.8):
   - the linear-in-P coefficients β, β′, χ, χ′, δ, ζ, ν and l_k;
   - the reduction (i) (Key ≥ 0 from l_k ≥ 0 and Φ ≥ 0, using Δc ≤ F);
   - the formulas for E¹, E², E³ and M_{k,m};
   - the Abel central-sum criterion in P;
   - the four inequalities (8.9).
4. Step (ii) (l_k, i ≥ 2) and step (iii): the reduction of M_{0,1}, M_{1,1} ≥ 0 to Theorem 8.9's inequality (8.3) at the scaled linear ratio, in particular that α ≥ t u₀/u₁ and the weights are as required.
5. Steps (iii′), (iv), (v):
   - the identities M_{0,s} = c′BK″ + FG_s and c′u₀K″ + u₁G_s = DQ_s + c″u₁²Y′;
   - the S_{2,0} identity;
   - each inequality chain, including signs and where u₁ > 0 and K″ ≥ 0, K_a ≥ 0 are used.
6. Step (vi):
   - that each listed form satisfies the sign hypotheses of Lemma 8.15;
   - the generating functions at u_n = rⁿ (including G^{(s)} and the s = 1 correction, rν_s ↦ sG^{(s)}, Z_s ↦ C(a,s)H_* − G^{(s)});
   - the crude bound for Q_s;
   - the W = 3 formula;
   - the Vandermonde certificate (distinct indices for W ≥ 6; positivity of denominators);
   - the treatment of W ≥ a+2 and W ≤ 2.
   Please re-derive the closed forms independently and check runs/varratio/key_weight_cert.py and key_weight_closed.py (do the polynomial certificates really prove what is claimed, for every a ≥ a₀ and W?).
7. Step (vii): runs/varratio/key_phi_ustep.py, key_lin_cert.py, key_cert_exact.py. Are the LP certificates exact and do they cover every central sum and every l_k for a = 3, 4, 5? Rerun them if you can.
8. Anything missing for a complete proof of (P), e.g. windows with ℓ + a = N, the case P₁ = 0, or zero P_k.
9. Literature: is Theorem 8.16, or the key inequality technique, known?

Answer format: PASS / PASS WITH MINOR FIXES / FAIL, every defect with an exact fix, and your independent checks. Be terse.

## Paper text

```latex
\paragraph{Log-concave ratios on log-concave profiles.}
Corollary~\ref{cor:lc-lowdeg} extends to every log-concave Newton profile. Besides Proposition~\ref{prop:np}, the proof uses a sign criterion for quadratic forms in log-concave sequences.

\begin{lemma}\label{lem:abel-weights}
Let $Q(u)=\sum_{0\leq i\leq j}q_{ij}u_iu_j$ with $q_{0j}\leq0$ for all $j$ and $q_{ij}\geq0$ for $2\leq i\leq j$, and put $N_W(Q)=\sum_{i\leq j,\,i+j=W}q_{ij}$. If $N_W(Q)\geq0$ for every $W$, then $Q(u)\geq0$ for every nonnegative sequence $(u_n)_{n\geq0}$ that is log-concave without internal zeros.
\end{lemma}

\begin{proof}
Fix $W$ and put $p_i=u_iu_{W-i}$ for $0\leq i\leq W/2$ and $p_{-1}=0$. Log-concavity without internal zeros makes $p$ nondecreasing. With $T_k=\sum_{k\leq i\leq W/2}q_{i,W-i}$ we get $\sum_{i\leq W/2}q_{i,W-i}p_i=\sum_{k\leq W/2}T_k(p_k-p_{k-1})$. Here $T_0=N_W(Q)\geq0$, $T_1=N_W(Q)-q_{0W}\geq0$, and $T_k\geq0$ for $k\geq2$.
\end{proof}

The weight sums are the coefficients of $Q$ on geometric sequences: $Q(1,r,r^2,\ldots)=\sum_WN_W(Q)r^W$.

\begin{theorem}[Log-concave ratio]\label{thm:lc-general}
Let $0=d_0<d_1<\cdots<d_N=1$ have Newton coefficients that are log-concave without internal zeros. Let $\rho(x)=\sum_k\rho_k\binom xk$, where $(\rho_k)_{k\geq0}$ is nonnegative and log-concave without internal zeros and $\rho_0>0$. Put $a_i=1-d_i$, $b_i=(1-\rho(i))d_i$ and $c_i=\rho(i)d_i$. If $b$ is nondecreasing, then the system has nonnegative linearization.
\end{theorem}

This contains Theorem~\ref{thm:lc-affine} and Corollary~\ref{cor:lc-lowdeg}. It also contains the case $t^2\geq r\tau$ of Theorem~\ref{thm:lc-quadratic}. The exponential ratios $\rho(x)=r(1+\varepsilon)^x$ are admitted on every log-concave Newton profile. The proof is computer-assisted in two places, both by exact rational arithmetic:
\begin{itemize}
\item the signs of finitely many explicit polynomials in the weight-sum certificates of step~(vi);
\item the key inequality \eqref{eq:G-key} for windows $a\leq5$, where step~(vii) uses exact linear-programming certificates.
\end{itemize}

\begin{proof}
\emph{Setup.} Only $\rho_0,\ldots,\rho_N$ enter, and truncating $(\rho_k)$ after index $N$ keeps it log-concave without internal zeros, so we may assume it finitely supported. Write $f_n(\ell)=\Delta^nd(\ell)$, $R_i=d_i/f_1(i)$, which is nondecreasing as in the proof of Theorem~\ref{thm:lc-affine}, and $P_k(x)=\Delta^k\rho(x)=\sum_h\binom xh\rho_{k+h}$. As in the proof of Theorem~\ref{thm:lc-quadratic}, $1-\rho(m+1)\geq\Delta\rho(m)R_m$ for $0\leq m<N$, and $0<\rho_0\leq\rho(i)\leq1$ for $i\leq N$; $\rho$ is nondecreasing.

For every $x\geq0$, the sequence $(P_k(x))_k$ arises from $(\rho_k)$ by the shifts of Lemma~\ref{lem:lc-ineq}, so it is log-concave without internal zeros. Since $\rho(x+1)^2-\rho(x)\rho(x+2)=P_1(x)^2-P_0(x)P_2(x)\geq0$, the positive sequence $x\mapsto\rho(x)$ is log-concave. Log-concavity in $k$ gives $\rho(y)P_{k+1}(y)\leq P_1(y)P_k(y)$. Combining these facts, for integers $0\leq x\leq y$ and $k\geq1$,
\begin{equation}\label{eq:G-ratio}
\rho(x)P_{k-1}(y+1)\leq\rho(x+1)P_{k-1}(y),\qquad\rho(x)P_k(y)\leq\Delta\rho(x)P_{k-1}(y).
\end{equation}
Indeed, log-concavity of $x\mapsto\rho(x)$ gives $\rho(x)\rho(y+1)\leq\rho(x+1)\rho(y)$, equivalently $\rho(x)P_1(y)\leq\Delta\rho(x)\rho(y)$. For the first inequality, $\rho(y)P_{k-1}(y+1)=\rho(y)P_{k-1}(y)+\rho(y)P_k(y)\leq\rho(y+1)P_{k-1}(y)$; multiply by $\rho(x)$ and divide by $\rho(y)>0$. For the second, $\rho(x)\rho(y)P_k(y)\leq\rho(x)P_1(y)P_{k-1}(y)\leq\Delta\rho(x)\rho(y)P_{k-1}(y)$. By Proposition~\ref{prop:np}, the Newton coefficients of $c=\rho d$ are log-concave without internal zeros, and so is $(\varphi_n(\ell))_n$ for every $\ell$. For $\ell+n\leq N$ the Leibniz rule gives, all at $\ell$,
\[
\varphi_n=\sum_{j=0}^n\binom njP_j(\ell+n-j)f_{n-j},\qquad\psi_n=h_n-v_n-\widehat w_n,
\]
with $h_n=(1-\rho(\ell+n))f_n$, $v_n=n\Delta\rho(\ell+n-1)f_{n-1}$ and $\widehat w_n=\sum_{j=2}^nw^{(j)}_n$, where $w^{(j)}_n=\binom njP_j(\ell+n-j)f_{n-j}$; all of these are nonnegative.

\emph{Moves and detours.} Split the moves as in the proof of Theorem~\ref{thm:lc-quadratic}, with $W_j$ now formed from $\widehat w_n$. Lemma~\ref{lem:lc-ineq} for $\varphi$ gives $B_0(\ell,a)B_{j-1}(\ell+1,a-2)\geq4c_{\ell+1}B_j(\ell,a)$ for $j\geq1$, as in Lemma~\ref{lem:detours}. The detours of $H$ and $C'$, with constants $10$ and $6$, hold verbatim: they used only $\varphi_2(\ell)\geq\rho(\ell+1)f_2(\ell)$, Lemma~\ref{lem:lc-ineq} for $f$, and $0\leq\rho\leq1$ nondecreasing.

For $V$, the term $\rho(\ell+2)f_2$ of $\varphi_2$, the first inequality of \eqref{eq:G-ratio} with $k=2$, $x=\ell+1$, $y=\ell+n$, and Lemma~\ref{lem:lc-ineq} for $f$ with indices $(2,n-1)$ give
\[
\varphi_2(\ell)v_n(\ell+1)\geq\tfrac n{n+2}\,c_{\ell+1}v_{n+2}(\ell).
\]

For $\widehat w$, expand $\varphi_2(\ell)=\rho(\ell+2)f_2+2\Delta\rho(\ell+1)f_1+P_2(\ell)f_0$, and pair its three terms with the components of $\widehat w_n(\ell+1)$:
\begin{itemize}
\item $\rho(\ell+2)f_2$ with component $i\leq n$, by the first inequality of \eqref{eq:G-ratio} and indices $(2,n-i)$, gives at least $\binom ni\binom{n+2}i^{-1}c_{\ell+1}w^{(i)}_{n+2}(\ell)$;
\item $2\Delta\rho(\ell+1)f_1$ with component $i\leq n$, by the second inequality of \eqref{eq:G-ratio} and indices $(1,n-i)$, gives at least $2\binom ni\binom{n+2}{i+1}^{-1}c_{\ell+1}w^{(i+1)}_{n+2}(\ell)$;
\item $P_2(\ell)f_0$ with component $n$ gives at least $c_{\ell+1}w^{(n+2)}_{n+2}(\ell)$, since $P_2(\ell)P_n(\ell+1)\geq(P_0+P_1)(\ell)P_{n+2}(\ell)$ by log-concavity in $k$, and $f_0(\ell+1)=d_{\ell+1}$.
\end{itemize}
When $n-i=0$ the index condition is trivial. Collecting by target,
\[
\varphi_2(\ell)\widehat w_n(\ell+1)\geq c_{\ell+1}\sum_{i=2}^{n+2}\theta_{n,i}w^{(i)}_{n+2}(\ell),
\]
where $\theta_{n,2}=\binom n2\binom{n+2}2^{-1}$, $\theta_{n,i}=1-\frac{i(i-1)}{(n+1)(n+2)}$ for $3\leq i\leq n$, $\theta_{n,n+1}=\frac2{n+2}$ and $\theta_{n,n+2}=1$.

As in the proof of Theorem~\ref{thm:lc-quadratic}, the coefficient quotients are $\frac{j(m-1)(m-2)}{2(m-j-1)}$ for $V$, and $\theta_{m-2,i}\frac{jm(m-1)}{2(m-j-1)}$ for $\widehat W$, on $m\geq2j+1$, $j\geq2$. The first is at least $6$, by $(m-4)(m-5)\geq0$ at $j=2$. The second exceeds $2$: it is at least $\frac{j(m-2)(m-3)}{2(m-j-1)}\geq m-2$ for $i=2$, at least $\frac{j(2m-3)}{m-j-1}$ for $3\leq i\leq m-2$, equal to $\frac{j(m-1)}{m-j-1}$ for $i=m-1$, and at least $10$ for $i=m$. Hence
\[
B_0V_{j-1}'\geq6c_{\ell+1}V_j\qquad\text{and}\qquad B_0W_{j-1}'\geq2c_{\ell+1}W_j\qquad(j\geq2).
\]

\emph{Resummation.} We prove below, for $(\ell,a)\in\Omega$ with $a\geq3$,
\begin{equation}\label{eq:G-key}
A^\psi_0(\ell,a)B_0(\ell+1,a-1)+B_0(\ell,a)A^\psi_0(\ell+1,a-2)\geq c_{\ell+1}\bigl(4H_1-2V_1\bigr)(\ell,a).
\end{equation}
With the notation of the proof of Theorem~\ref{thm:lc-quadratic}, the inequalities above give $P^2\geq4Q$, $H_+P\geq10H_-$, $V_+P\geq6V_-$, $W_+P\geq2W_-$, $C_+P\geq6C_-$ and $A_0P+PA_0+2V_1\geq4H_1$. Since $(I-P/\mu)G=(1-\frac2\mu)G+\frac2\mu I$, one has $G(H_+-H_-)G\geq0$, $GCG\geq0$, $G(W_+-W_-)G\geq0$ and $G(V_+-V_-)G\geq\frac23GV_1G$, so
\[
GAG\geq G\bigl(A_0-\tfrac14(A_0P+PA_0)+\tfrac16V_1\bigr)G=\tfrac12(GA_0+A_0G)+\tfrac16GV_1G\geq0,
\]
and (P) follows as before.

\emph{Proof of \eqref{eq:G-key}: notation.} Use the notation of the proof of Theorem~\ref{thm:lc-affine}: $u_n=f_n(\ell)$, which is log-concave without internal zeros, $y_n$, $D$, $X$, $X'$, $Y$, $Y'$, $J$, $H_*$. Put also $A=d_{\ell+a}$, $B=d_{\ell+a-1}$, $F=A-B=f_1(\ell+a-1)$, $X''=B-d_\ell$ and $P_k=P_k(\ell)$. Since $c_{\ell+n}=d_{\ell+n}\sum_k\binom nkP_k$ for $n\leq a$, the following are linear in $P$:
\begin{itemize}
\item $B_0(\ell,a)=\sum_k\beta_kP_k$ and $B_0(\ell+1,a-1)=\sum_k\beta'_kP_k$, where
\[
\begin{aligned}
&\beta_0=Y,\quad\beta_1=a(A-D),\quad\beta_k=\tbinom akA\ (k\geq2),\\
&\beta'_0=Y',\quad\beta'_1=aA-2(a-1)d_{\ell+2}+(a-2)D,\quad\beta'_2=\tbinom a2A-(a-1)d_{\ell+2},\quad\beta'_k=\tbinom akA\ (k\geq3);
\end{aligned}
\]
\item $c_{\ell+a}-c_\ell=\sum_k\chi_kP_k$ and $c_{\ell+a-1}-c_{\ell+1}=\sum_k\chi'_kP_k$;
\item $c_{\ell+a}-c_{\ell+a-1}=\sum_k\delta_kP_k$ with $\delta_k=\binom akF+\binom{a-1}{k-1}B$;
\item $H_1=H_*-\sum_k\zeta_kP_k$ with $\zeta_k=\sum_{n\geq3}(n-2)\binom nky_n$, and $V_1=\sum_k\nu_kP_k$ with $\nu_k=\sum_{n\geq3}(n-2)n\binom{n-1}{k-1}\binom anu_{n-1}$;
\item $c_{\ell+1}=D(P_0+P_1)$.
\end{itemize}
As $A^\psi_0(\ell,a)=X-(c_{\ell+a}-c_\ell)$ and $A^\psi_0(\ell+1,a-2)=X'-(c_{\ell+a-1}-c_{\ell+1})$, the difference of the two sides of \eqref{eq:G-key} is $\mathrm{Key}(P)=\mathrm{Lin}(P)-\mathrm{Quad}(P)$. Here $\mathrm{Lin}(P)=\sum_kl_kP_k$ with $l_k=X\beta'_k+\beta_kX'-4[k\leq1]DH_*$, and $\mathrm{Quad}$ is a quadratic form. We use repeatedly:
\begin{equation}\label{eq:G-basic}
AX''\geq(a-1)d_\ell F,\qquad AX'\geq(a-2)DF,\qquad u_0F\leq u_1B,\qquad FD\leq u_1A.
\end{equation}
The first two hold because $A/F\geq R_{\ell+a-1}\geq R_{\ell+i}$ gives $(A/F)f_1(\ell+i)\geq d_{\ell+i}$ for $i\leq a-1$; summing over $0\leq i\leq a-2$, respectively $1\leq i\leq a-2$, gives them. The last two follow from $u_0u_{m+1}\leq u_1u_m$, as $F=\sum_m\binom{a-1}mu_{m+1}$, $B=\sum_m\binom{a-1}mu_m$ and $D=u_0+u_1$.

\emph{(i) Reduction to a quadratic form in $P$.} By monotonicity of $b$ at $\ell+a-1$, $\Delta c:=c_{\ell+a}-c_{\ell+a-1}\leq F$. Suppose every $l_k\geq0$ and $\Phi(P):=\Delta c\cdot\mathrm{Lin}(P)-F\,\mathrm{Quad}(P)\geq0$. If $\mathrm{Quad}(P)\leq0$, then $\mathrm{Key}\geq\mathrm{Lin}\geq0$. Otherwise $\mathrm{Quad}\leq(\Delta c/F)\mathrm{Lin}\leq\mathrm{Lin}$. With $\chi_k=\binom akA-[k=0]d_\ell$ and $\chi'_k=\binom{a-1}kB-\binom1kD$, so that $E^1_m=X\delta_m-F\chi_m$, $E^2_m=X'\delta_m-F\chi'_m$ and $E^3_m=2F\nu_m-4(H_*\delta_m-F\zeta_m)$, expansion gives $\Phi(P)=\sum_{k,m}M_{k,m}P_kP_m$ with
\[
M_{k,m}=\beta'_kE^1_m+\beta_kE^2_m+[k\leq1]D\,E^3_m,
\]
and explicitly $E^1_0=E^2_0=E^3_0=0$ and, for $m\geq1$,
\[
\begin{aligned}
E^1_m&=\tbinom{a-1}{m-1}AX''-\tbinom{a-1}md_\ell F,\qquad E^2_m=\tbinom{a-1}{m-1}AX'-\Bigl(\tbinom{a-1}m-[m=1]\Bigr)DF,\\
E^3_m&=2F\nu_m-4\tbinom{a-1}{m-1}BH_*-4FZ_m,\qquad Z_m=\sum_{n\geq3}(n-2)\Bigl(\tbinom am-\tbinom nm\Bigr)y_n.
\end{aligned}
\]
Since $(P_k)$ is log-concave without internal zeros, the Abel summation in the proof of Lemma~\ref{lem:abel-weights}, applied to every anti-diagonal of $\Phi$, shows $\Phi\geq0$ if every central sum $S_{\sigma,i}=\sum_{k=i}^{\sigma-i}M_{k,\sigma-k}$, $0\leq i\leq\sigma/2$, is nonnegative. As $M_{k,0}=0$, for $\sigma\geq3$
\[
S_{\sigma,0}=S_{\sigma,1}+M_{0,\sigma}\qquad\text{and}\qquad S_{\sigma,1}=S_{\sigma,2}+M_{1,\sigma-1}+M_{\sigma-1,1}.
\]
Since $\binom{a-1}m=\frac{a-m}m\binom{a-1}{m-1}$ and $\frac{a-m}{m(a-1)}\leq\frac{a-m}{m(a-2)}\leq\frac12$ for $m\geq2$, \eqref{eq:G-basic} gives, for $m\geq2$,
\[
E^1_m\geq\tfrac12\tbinom{a-1}{m-1}AX''\geq0\qquad\text{and}\qquad E^2_m\geq\tfrac12\tbinom{a-1}{m-1}AX'\geq0.
\]
Also every $\beta_k\geq0$ and $\beta'_k\geq0$; for $\beta'_2$ use $\binom a2A\geq(a-1)d_{\ell+2}$. Finally $E^1_1=AX''-(a-1)d_\ell F\geq0$ and $E^2_1=AX'-(a-2)DF\geq0$.

\emph{(ii) The central sums with $i\geq2$, and the coefficients $l_k$.} For $k,m\geq2$, $M_{k,m}=\beta'_kE^1_m+\beta_kE^2_m\geq0$, so $S_{\sigma,i}\geq0$ for $i\geq2$. Next, $l_0=K\geq0$ by the proof of Theorem~\ref{thm:lc-affine}, and $l_k\geq0$ for $k\geq2$ termwise. By convexity, $A-D\geq(a-1)f_1(\ell+1)=(a-1)(d_{\ell+2}-D)$, so $\beta'_1\geq(a-2)(A-D)$ and
\[
l_1\geq L:=(A-D)\bigl((a-2)X+aX'\bigr)-4DH_*.
\]

\emph{(iii) The central sums with $\sigma\leq2$.} Take $P=(P_0,P_1,0,\ldots)$ with $P_0\geq0$ and $P_1>0$, and put $\lambda=F/\Delta c(P)$. Then $\mathrm{Key}(\lambda P)=(\lambda/\Delta c)\Phi(P)$, and $\lambda P$ is the linear ratio $\tilde\rho(\ell+x)=\lambda(P_0+P_1x)$. Its $\tilde b=(1-\tilde\rho)d$ satisfies $\Delta\tilde b(\ell+a-1)=0$. So $\alpha:=1-\tilde\rho(\ell+a)=tR_{\ell+a-1}\geq tu_0/u_1$ with $t=\lambda P_1$. For such $\alpha$ and $t$, the proof of Theorem~\ref{thm:lc-affine} shows \eqref{eq:affine-red}. Its two weights $A^\psi_0$ are nonnegative, since $X\geq au_1$ and $X'\geq(a-2)u_1$, and $B_0(\ell,a)\geq\tilde\rho(\ell+1)Y$, $B_0(\ell+1,a-1)\geq\tilde\rho(\ell+1)Y'$, since $\beta_1\geq Y$ and $\beta'_1\geq Y'$. Hence $\mathrm{Key}(\lambda P)\geq0$, that is, $\Phi(P)=P_1(M_{0,1}P_0+M_{1,1}P_1)\geq0$. This gives $S_{1,0}=M_{0,1}\geq0$ and $S_{2,1}=M_{1,1}\geq0$. The sum $S_{2,0}=M_{0,2}+M_{1,1}$ is treated in~(v).

\emph{(iii$'$) $M_{1,m}+M_{m,1}\geq0$ for $m\geq2$ and $a\geq6$.} Put $c'_m=\binom{a-1}{m-1}$. Then
\[
M_{1,m}+M_{m,1}=\bigl[\beta_1E^2_m-4c'_mDBH_*\bigr]+\bigl[\beta'_1E^1_m-DF(4Z_m-2\nu_m)\bigr]+\beta'_mE^1_1+\beta_mE^2_1,
\]
and the last two terms are nonnegative.
\begin{itemize}
\item First bracket: $E^2_m\geq\frac12c'_mAX'$ and $A\geq B$, so it is nonnegative if $R:=a(A-D)X'-8DH_*\geq0$.
\item Second bracket: $Z_m\leq\binom amH_*\leq\frac a2c'_mH_*$, $\nu_m\geq0$, $F\leq A$, $E^1_m\geq\frac12c'_mAX''$ and $\beta'_1\geq(a-2)(A-D)$. So it is nonnegative if $R_2:=(a-2)(A-D)X''-4aDH_*\geq0$.
\end{itemize}

\emph{(iv) $M_{0,s}\geq0$ for $s\geq3$.} Put $c'=\binom{a-1}{s-1}$ and $c''=\binom{a-1}s$. Then
\[
M_{0,s}=Y'E^1_s+YE^2_s+DE^3_s=c'BK''+FG_s,
\]
where
\[
K''=Y'X''+YX'-4DH_*,\qquad G_s=c'(Y'X''+YX')-c''(d_\ell Y'+DY)+D(2\nu_s-4Z_s).
\]
Note $u_1=d_{\ell+1}-d_\ell>0$. If $K''\geq0$, then $u_1B\geq u_0F$ gives $u_1M_{0,s}\geq F(c'u_0K''+u_1G_s)$, and
\[
c'u_0K''+u_1G_s=D\,Q_s+c''u_1^2Y',\qquad Q_s=c'(Y'X''+YX')-4c'u_0H_*+u_1(2\nu_s-4Z_s)-c''u_1(Y+Y').
\]
So $M_{0,s}\geq0$ once $K''\geq0$ and $Q_s\geq0$.

\emph{(v) $S_{2,0}\geq0$ for $a\geq5$.} With $c''=\binom{a-1}2$, the definitions give the identity
\[
S_{2,0}=\beta'_1E^1_1+\bigl[\beta_1E^2_1-c''F(d_\ell Y'+DY)\bigr]+B\,K_a+F\,W,
\]
where $K_a=(a-1)K''-4DH_*$ and $W=(a-1)(Y'X''+YX')+D(2\nu_1+2\nu_2-4Z_1-4Z_2)$.
\begin{itemize}
\item Since $\beta_1=a(X'+F)$, $E^2_1=AX'-(a-2)DF$, $d_\ell\leq D$ and $FD\leq u_1A$, the bracket is at least $A\Psi$, where $\Psi=a(A-D)J-c''u_1(Y+Y')$. Recall $J=X'-(a-2)u_1$ and $X'+F=A-D$.
\item If $K_a\geq0$, then $u_1(BK_a+FW)\geq F(u_0K_a+u_1W)=FD\widehat Q$, where $\widehat Q=(a-1)(Y'X''+YX')-4au_0H_*+u_1(2\nu_1+2\nu_2-4Z_1-4Z_2)$.
\end{itemize}
Hence $u_1S_{2,0}\geq u_1\beta'_1E^1_1+u_1A\Psi+FD\widehat Q\geq0$ once $K_a$, $\Psi$ and $\widehat Q$ are nonnegative.

\emph{(vi) Weight sums.} Steps (ii)--(v) reduce \eqref{eq:G-key} to the nonnegativity of the quadratic forms $L$, $R$, $R_2$, $K''$, $Q_s$ $(3\leq s\leq a)$, $K_a$, $\Psi$ and $\widehat Q$ in the sequence $u$. In each of them:
\begin{itemize}
\item the only negative coefficients come from multiples of $u_0H_*$, $u_1H_*$, $u_1Z_s$ and $u_1(Y+Y')$, so they sit at index pairs $(0,j)$ and $(1,j)$;
\item the positive parts $X$, $X'$, $X''$, $J$, $Y$, $Y'$ and $A-D$ contain no $u_0$.
\end{itemize}
So Lemma~\ref{lem:abel-weights} applies, and it suffices that every weight sum be nonnegative. At $u_n=r^n$, with $p=1+r$, one has $d_{\ell+n}\mapsto p^n$. Hence
\[
X\mapsto p^a-1,\quad X'\mapsto p^{a-1}-p,\quad X''\mapsto p^{a-1}-1,\quad Y\mapsto p^a-1-ar,\quad H_*\mapsto arp^{a-1}-2p^a+2+ar,
\]
and $r\nu_s\mapsto sG^{(s)}$, $Z_s\mapsto\binom asH_*-G^{(s)}$, where
\[
G^{(s)}=\tbinom as\bigl((s-2)r^sp^{a-s}+(a-s)r^{s+1}p^{a-s-1}\bigr)+[s=1]ar.
\]
So each weight sum is a finite combination of binomial coefficients. For $W\geq3$ it has the form $N_W=\pi\binom{2a-1}W+\binom a{W-1}\varrho(a,W)$, with $\pi>0$ and $\varrho$ rational. For $Q_s$ we bound $N_W(Q_s)/c'$ below, for $W\geq4$, by its value with the nonnegative $G^{(s)}$-terms omitted and $s=3$ in the two remaining $s$-dependent negative terms, which only decrease as $s$ grows. For $W=3$,
\[
N_3(Q_s)=c'\tfrac{(a-1)(a-2)(2a-3)}6+6\tbinom a3[s=3]-c''(a-1)^2,
\]
which is $(a-1)(a-2)\bigl(\frac{a(a-1)}{12}+a\bigr)$ for $s=3$ and at least $c'(a-1)\frac{a^2+a}{12}$ for $s\geq4$. The certificates are as follows.
\begin{itemize}
\item For $W\geq a+2$, all negative terms vanish.
\item For $6\leq W\leq a+1$, bound $\binom{2a-1}W$ below by the Vandermonde terms $\binom ak\binom{a-1}{W-k}$ with $k\in\{W,W-1,W-2,W-3,0,1,2\}$. These are distinct. Substituting $a=W-1+x$ and $W=6+y$, the cleared numerator of the resulting lower bound for $N_W/\binom a{W-1}$ is a polynomial in $(x,y)$ with nonnegative coefficients.
\item For $W\in\{3,4,5\}$, $N_W$ is a polynomial in $a$ whose coefficients are nonnegative after $a\mapsto a+a_0$. Here $a_0=5$ for $K_a$, $a_0=6$ for $R_2$, and $a_0=3$ otherwise.
\item For $W\leq2$, the weight sums are $0$ or positive.
\end{itemize}
The closed forms and the coefficient signs are verified in exact arithmetic by \path{runs/varratio/key_weight_closed.py} and \path{runs/varratio/key_weight_cert.py}. For $L$, the bound $\binom{2a}W\geq\binom{2a-1}W$ gives $N_W(L)\geq\frac{2(a-1)}aN_W(R)\geq0$ for $W\geq3$; also $N_2(L)=2a(a-1)(a-2)>0$, and $N_W(L)=0$ for $W\leq1$.

\emph{(vii) Small windows.} Steps (iii$'$) and (v) need $a\geq6$ and $a\geq5$. For $3\leq a\leq5$, every central sum $S_{\sigma,i}$, a cubic polynomial in $u$, and every $l_k$ is certified nonnegative on log-concave $u$. The certificates are exact rational combinations of $u_k(u_{i+1}u_{j-1}-u_iu_j)$, respectively $u_{i+1}u_{j-1}-u_iu_j$ ($i+1\leq j-1$), and monomials (\path{runs/varratio/key_phi_ustep.py}, \path{runs/varratio/key_lin_cert.py}; these cover all $a\leq10$). This proves \eqref{eq:G-key} and the theorem.
\end{proof}

The diagnostics check in exact arithmetic the following.
\begin{itemize}
\item The closed forms of the central sums: \path{runs/varratio/key_S_high.py} and \path{runs/varratio/key_S_low.py}, symbolically for $a\leq8$.
\item The identities and reductions of steps (iii$'$)--(v) on random log-concave $u$: \path{runs/varratio/key_L1_decomp.py}, \path{runs/varratio/key_L1_quad.py}, \path{runs/varratio/key_S20_proof.py} and \path{runs/varratio/key_L2_chain.py}.
\item The Abel tails of every form: \path{runs/varratio/key_L1_quad.py} ($a\leq70$), \path{runs/varratio/key_S20_quad.py} and \path{runs/varratio/key_S20_proof.py} ($a\leq40$).
\item The $\widehat w$ detour: \path{runs/varratio/what_pointwise.py}.
\item (P) on random members, including steep exponential ratios: \path{runs/varratio/steep_exp_test.py} and \path{runs/varratio/g_farfield.py}.
\end{itemize}

```
