# Review round 18: Proposition 8.8 (quadratic arrays)

Please review Proposition 8.8 of paper.tex at commit 244a607e412a7624f9fc1eba7e886c8a7066e823 (github.com/skypher/szkraw), adversarially, together with the sentence after its proof. Theorem 8.6 and its proof passed your round 17 and are quoted below for reference. The proposition rests on the recurrence in that proof, which holds for every array in the stochastic normalization.

Check in particular:
1. That the recurrence of the proof of Theorem 8.6 is valid without that theorem's hypotheses, as now stated there.
2. That φ_n = ψ_n = 0 for n ≥ 3 makes every move with j ≥ 1 vanish.
3. The j = 0 weights: A^ψ_0(ℓ,a) = b_{ℓ+a} − b_ℓ, B_0 = C(a,2)κ_2, C_0 + C^ψ_0 = C(a,2)(κ_2 + β_2). Note that the source of the A-move into (ℓ+1, a) is (ℓ, a+1).
4. That their nonnegativity on Ω, together with a_{ℓ+a} ≥ 0 there, gives ω ≥ 0 by induction on ℓ, using the support property. Do moves from nodes outside Ω matter?
5. The claims of the following paragraph:
   - a linear profile with ratio r + κn/N has κ_2 = 2κ/N² and κ_2 + β_2 = 0;
   - b is nondecreasing iff κ ≤ (1 − r)N/(2N − 1);
   - each hypothesis is needed. The author's script runs/varratio/quadratic.py reports failures at N ≤ 3 when one hypothesis is dropped.
6. If you can, test the proposition in exact arithmetic (N = 2–10, random parameters including boundary cases).

Verdict: PASS, PASS WITH MINOR FIXES (with replacement text), or FAIL (failing step or counterexample).

## Context: Theorem 8.6 and its proof

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

For example, if $c$ is a convex quadratic in $i$ ($\kappa_1,\kappa_2>0$, $\kappa_k=0$ for $k\geq3$) and $b_i=w_1\kappa_1i+w_2\kappa_2\binom i2$ with $w_1>w_2\geq0$, scaled so that $b_N+c_N=1$, the ratio $c_i/(b_i+c_i)$ increases strictly. The hypotheses exclude the counterexample recorded in Section~\ref{sec:open}, whose diagonal coefficients $b=(0,1,1,1)/91$ have Newton coefficients of both signs. They also exclude strictly increasing linear ratios $c_i/(b_i+c_i)$ with a linear profile, whose diagonal coefficients are concave; Proposition~\ref{prop:lc-quad} below covers these.

\begin{proof}[Proof of Theorem~\ref{thm:lc-vary}]
Put $e_i=\prod_{j<i}a_j/c_{j+1}$ and $E_i=e_iR_i$. Then $xE_i=c_{i+1}E_{i+1}+b_iE_i+a_{i-1}E_{i-1}$ on the support. The out-of-range terms are omitted: at the endpoints, $xE_0=c_1E_1$ and $xE_N=b_NE_N+a_{N-1}E_{N-1}$. The series $F=\sum_iE_iz^i$ satisfies $xF=\mathcal L_zF$ with
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
where $A^\psi_j=W^\psi_{2j+1,j}$, $C^\psi_j=W^\psi_{2j+2,j+1}$, and $B_j=W_{2j+2,j}$, $C_j=W_{2j+2,j+1}$. The straight weight is $1-c_{\ell+a}-b_{\ell+a}=a_{\ell+a}$, extended polynomially beyond $N$, and $\beta_0=0$. Up to this point no hypothesis of the theorem has been used: the recurrence holds for every array in the stochastic normalization. Under the hypotheses, all weights are nonnegative on $\Omega$.

For $j\geq1$, $0\leq\ell\leq N-1$ and $a\geq0$, the following detour inequalities hold, with weights having a negative second argument interpreted as zero:
\[
\begin{aligned}
A^\psi_0(\ell,a)B_{j-1}(\ell+1,a-1)+B_0(\ell,a)A^\psi_{j-1}(\ell+1,a-2)&\geq4c_{\ell+1}A^\psi_j(\ell,a),\\
B_0(\ell,a)B_{j-1}(\ell+1,a-2)&\geq4c_{\ell+1}B_j(\ell,a),\\
B_0(\ell,a)\bigl(C_{j-1}+C^\psi_{j-1}\bigr)(\ell+1,a-2)&\geq4c_{\ell+1}\bigl(C_j+C^\psi_j\bigr)(\ell,a).
\end{aligned}
\]
The proof of Lemma~\ref{lem:detours} applies, with the lower bounds $A^\psi_0(\ell,a)\geq a\psi_1(\ell)$ and $B_0(\ell,a)\geq\binom a2\varphi_2(\ell)$. Lemma~\ref{lem:lc-ineq} for $\varphi$ handles the products $\varphi_2(\ell)\varphi_n(\ell+1)$. The two hypotheses of the theorem handle $\psi_1(\ell)\varphi_n(\ell+1)$ for $n\geq2$ and $\varphi_2(\ell)\psi_n(\ell+1)$ for $n\geq1$, which are the indices that occur. The moves $C_j$ and $C^\psi_j$ have the same displacement and are treated as one move. With this, the proof of Theorem~\ref{thm:lc} gives $\omega\geq0$, hence $L_{mn}^k\geq0$ and $g(m,n;k)=L_{mn}^ke_k/(e_me_n)\geq0$.
\end{proof}



## Proposition 8.8 as submitted

For arrays that are quadratic in the index, concave diagonal coefficients are allowed.

\begin{proposition}[Quadratic arrays]\label{prop:lc-quad}
Let $b_n=\beta_1n+\beta_2\binom n2$ and $c_n=\kappa_1n+\kappa_2\binom n2$ $(0\leq n\leq N)$ define an array as above. If $\kappa_2\geq0$, $\kappa_2+\beta_2\geq0$ and $b_0\leq b_1\leq\cdots\leq b_N$, then the system has nonnegative linearization.
\end{proposition}

\begin{proof}
In the recurrence of the proof of Theorem~\ref{thm:lc-vary}, which holds for every array, $\varphi_n=\psi_n=0$ for $n\geq3$. So all moves with $j\geq1$ vanish, and the moves with $j=0$ have the weights $A^\psi_0(\ell,a)=\sum_{n\geq1}\binom an\psi_n(\ell)=b_{\ell+a}-b_\ell$, $B_0(\ell,a)=\binom a2\kappa_2$ and $(C_0+C^\psi_0)(\ell,a)=\binom a2(\kappa_2+\beta_2)$. These and the straight weights $a_{\ell+a}$ are nonnegative on $\Omega$, so $\omega\geq0$ by induction on $\ell$, and $g(m,n;k)\geq0$ as in the proof of Theorem~\ref{thm:lc-vary}.
\end{proof}

With the linear profile $d_n=n/N$ and the ratio $c_n/d_n=r+\kappa n/N$ $(r>0$, $\kappa\geq0)$, one has $\kappa_2=2\kappa/N^2$ and $\kappa_2+\beta_2=0$. So every linearly increasing ratio with a linear profile and nondecreasing $b$ has property (P); $b$ is nondecreasing exactly when $\kappa\leq(1-r)N/(2N-1)$. Exact computations (\path{runs/varratio/quadratic.py}) show that each of the three hypotheses is needed: dropping any one of them gives quadratic arrays with a negative coefficient at $N\leq3$.


