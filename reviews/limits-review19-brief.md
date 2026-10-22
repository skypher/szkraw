# Review round 19: Theorem 8.9 (linearly increasing ratio)

Please give an adversarial, line-by-line review of Theorem 8.9 of paper.tex at commit 7b382debcf76c4c0afbf4892997039788a718557 (github.com/skypher/szkraw), from the paragraph "Linearly increasing ratio" to the end of Section 8.

Theorem 8.9 claims nonnegative linearization for every N, every profile with log-concave Newton coefficients without internal zeros, 0 < r ≤ 1 and 0 ≤ κ ≤ N(1−r)/(2N−1), with ratio c_i/d_i = r + κi/N.

Independence caveat: the proof's key steps (the split of the A-moves and the resummation through G = (I − P/2)⁻¹) came from your consult round 5. Please review it as if it were someone else's, and try hard to break it.

Check in particular:
1. The Leibniz-rule formulas for φ_n, ψ_n, and the nonnegativity of h_n, v_n on Ω. Which (ℓ, n) actually occur?
2. The four-term identity for κ_i² − κ_{i−1}κ_{i+1}, the sign of each term (including the balanced products), and the interval support of κ.
3. A^ψ_0 ≥ 0: the bounds α ≥ t(ℓ+a−1) on Ω, d_ℓ ≤ ℓf_1(ℓ) and d_{ℓ+a} − d_ℓ ≥ af_1(ℓ).
4. The three inequalities for φ_2 against f, h and v, and the four detour inequalities with their coefficient ratios, ranges, minima (5, 10, 6, 6) and monotonicity in j.
5. Inequality (eq:affine-key):
   - the formulas for the two A^ψ_0, and the lower bounds for the two B_0;
   - the bound γ_n = 2(2^n − n − 2), including the binomial comparisons and the dropped terms with i + j > a;
   - the expansions of aY' + (a−2)Y, H_1 and V_1;
   - the coefficient comparison at n = 2, 3 and n ≥ 4.
6. The resummation:
   - that the recurrence splits as stated (A = A_0 + H_+ − H_− − H_1 + V_+ − V_−);
   - the five operator inequalities, including composition order and denominators;
   - G ≥ 0 and the identities PG = GP = 2(G − I), (I − P/6)G = (2/3)G + (1/3)I;
   - the chain for GAG and GCG, R ≥ 0, and (I − P/2)²ω = β + (R + C + A)ω;
   - v = Gβ + Mv and the final formula.
7. Whether the bound on κ is used correctly everywhere (s − t(ℓ+n+2) ≥ 0 where needed).
8. The relation to Proposition 8.8 stated after the theorem.
9. If you can, test numerically in exact arithmetic:
   - small N exhaustively random, including κ at the bound;
   - N ≥ 12;
   - a slope beyond the bound, to see whether (P) or the proof's inequalities fail.
10. Verdict: PASS, PASS WITH MINOR FIXES (with replacement text), or FAIL (failing step or counterexample).

The author's independent exact verifier (runs/varratio/affine_verify.py) checks every inequality of the proof, M ≥ 0, ω = G Σ M^q G β, ω ≥ 0 and (P) on 200 members, N = 3–10, a third at the κ bound, with 0 failures. These are finite checks; the claim rests on the proof.

## Context: Lemmas 8.3–8.4 (passed rounds 14–16)

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



## Context: Theorem 8.6 and its recurrence (passed round 17)

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



## Theorem 8.9 as submitted

\paragraph{Linearly increasing ratio.}
For curved profiles, linearly increasing ratios violate the hypotheses of Theorem~\ref{thm:lc-vary}: the Newton coefficients of $b$ of order at least $3$ can be negative, and then some moves of even index in the recurrence of its proof have negative weight and no two-step detour. A resummation of the positive moves handles this.

\begin{theorem}[Linearly increasing ratio]\label{thm:lc-affine}
Let $0=d_0<d_1<\cdots<d_N=1$ have Newton coefficients that are log-concave without internal zeros, let $0<r\leq1$ and $0\leq\kappa\leq\frac{N}{2N-1}(1-r)$, and put $\rho_i=r+\kappa i/N$, $a_i=1-d_i$, $b_i=(1-\rho_i)d_i$ and $c_i=\rho_id_i$. Then the system has nonnegative linearization.
\end{theorem}

For the linear profile $d_i=i/N$ these are arrays of Proposition~\ref{prop:lc-quad}, and the bound on $\kappa$ is exactly the condition that $b$ be nondecreasing there.

\begin{proof}
Write $s=1-r$ and $t=\kappa/N$, so that $(2N-1)t\leq s$, and let $f_n(\ell)=\Delta^nd(\ell)$ and $\nu_i=\Delta^id(0)$ be as in Section~\ref{sec:lc}, with $\nu_{-1}=\nu_0=0$. Since $c_i=(r+ti)d_i$ and $b_i=(s-ti)d_i$, the Leibniz rule for differences gives, for $n\geq1$,
\[
\varphi_n(\ell)=(r+t(\ell+n))f_n(\ell)+tnf_{n-1}(\ell),\qquad\psi_n(\ell)=h_n(\ell)-v_n(\ell),
\]
with $h_n(\ell)=(s-t(\ell+n))f_n(\ell)$ and $v_n(\ell)=tnf_{n-1}(\ell)$; both are nonnegative when $\ell+n\leq N$. The Newton coefficients $\kappa_i=p_i\nu_i+q_i\nu_{i-1}$ of $c$, with $p_i=r+ti$ and $q_i=ti$, satisfy
\[
\kappa_i^2-\kappa_{i-1}\kappa_{i+1}=p_i^2(\nu_i^2-\nu_{i-1}\nu_{i+1})+q_i^2(\nu_{i-1}^2-\nu_{i-2}\nu_i)+q_{i-1}p_{i+1}(\nu_i\nu_{i-1}-\nu_{i-2}\nu_{i+1})+t^2(\nu_{i-1}\nu_{i+1}+\nu_{i-2}\nu_i+2\nu_i\nu_{i-1}),
\]
and each term is nonnegative by log-concavity of $\nu$; their positive support is an interval. So Lemma~\ref{lem:lc-ineq} applies to $f$ and to $\varphi$.

\emph{Moves.} We use the recurrence of the proof of Theorem~\ref{thm:lc-vary}, which holds for every array. For $j\geq1$ split $A^\psi_j=H_j-V_j$, where $H_j=W^h_{2j+1,j}$ and $V_j=W^v_{2j+1,j}$ are formed from $h_n$ and $v_n$ in place of $\psi_n$; both are nonnegative on $\Omega$. Keep $A^\psi_0(\ell,a)=b_{\ell+a}-b_\ell$ as one move. With $\alpha=s-t(\ell+a)\geq t(\ell+a-1)$ on $\Omega$, convexity of $d$ and $d_0=0$ give $d_\ell\leq\ell f_1(\ell)$ and $d_{\ell+a}-d_\ell\geq af_1(\ell)$, so
\[
A^\psi_0(\ell,a)=\alpha(d_{\ell+a}-d_\ell)-tad_\ell\geq a(\alpha-t\ell)f_1(\ell)\geq0.
\]
The weights $B_j$, formed from $\varphi$, and $C_j+C^\psi_j=W^f_{2j+2,j+1}$, formed from $f$, are nonnegative. Write $C'_j=C_j+C^\psi_j$.

\emph{Detours.} Since $\varphi_2(\ell)\geq(r+t(\ell+1))f_2(\ell)$ and $c_{\ell+1}=(r+t(\ell+1))d_{\ell+1}$, Lemma~\ref{lem:lc-ineq} for $f$ gives
\[
\varphi_2(\ell)f_n(\ell+1)\geq c_{\ell+1}f_{n+2}(\ell),\quad\varphi_2(\ell)h_n(\ell+1)\geq c_{\ell+1}h_{n+2}(\ell),\quad\varphi_2(\ell)v_n(\ell+1)\geq\tfrac{n}{n+2}\,c_{\ell+1}v_{n+2}(\ell)\ (n\geq2),
\]
using $s-t(\ell+n+1)\geq s-t(\ell+n+2)\geq0$ for the second and Lemma~\ref{lem:lc-ineq} with indices $(2,n-1)$ for the third. As in the proof of Lemma~\ref{lem:detours}, with $B_0(\ell,a)\geq\binom a2\varphi_2(\ell)$, for $0\leq\ell\leq N-1$ and second factors at $(\ell+1,a-2)$,
\[
B_0B_{j-1}\geq4c_{\ell+1}B_j\ (j\geq1),\quad B_0H_{j-1}\geq6c_{\ell+1}H_j\ (j\geq2),\quad B_0V_{j-1}\geq6c_{\ell+1}V_j\ (j\geq2),\quad B_0C'_{j-1}\geq6c_{\ell+1}C'_j\ (j\geq1).
\]
The first uses Lemma~\ref{lem:lc-ineq} for $\varphi$. The coefficient ratios are, on $m\geq2j+2$, $2j+1$, $2j+1$ and $2j+2$ respectively,
\[
\frac{jm(m-1)}{2(m-j-2)},\qquad\frac{jm(m-1)}{2(m-j-1)},\qquad\frac{j(m-1)(m-2)}{2(m-j-1)},\qquad\frac{(j+1)m(m-1)}{2(m-j-1)};
\]
they increase with $j$ and are at least $5$, $10$, $6$ and $6$. Finally,
\begin{equation}\label{eq:affine-key}
A^\psi_0(\ell,a)B_0(\ell+1,a-1)+B_0(\ell,a)A^\psi_0(\ell+1,a-2)\geq c_{\ell+1}\bigl(4H_1(\ell,a)-2V_1(\ell,a)\bigr).
\end{equation}
Only $a\geq3$ needs proof. Put $u_n=f_n(\ell)$, $D=u_0+u_1=d_{\ell+1}$, $X=\sum_{i\geq1}\binom aiu_i$, $Y=\sum_{i\geq2}\binom aiu_i$, $X'=\sum_{j\geq1}\binom{a-2}j(u_j+u_{j+1})$ and $Y'=\sum_{j\geq2}\binom{a-1}j(u_j+u_{j+1})$. Then $A^\psi_0(\ell,a)=\alpha X-tau_0$, $A^\psi_0(\ell+1,a-2)=(\alpha+t)X'-t(a-2)D$, and the two weights $B_0$ are at least $(r+t(\ell+1))Y'$ and $(r+t(\ell+1))Y$. As both $A^\psi_0$ are nonnegative, the left side of \eqref{eq:affine-key} divided by $c_{\ell+1}$ is at least $\alpha(XY'+YX')/D-t(aY'+(a-2)Y)$. By $u_i(u_j+u_{j+1})\geq Du_{i+j}$ (Lemma~\ref{lem:lc-ineq}) and $\binom ai\binom{a-1}j,\binom ai\binom{a-2}j\geq\binom an\binom ni$ for $i+j=n$ in the relevant ranges,
\[
\frac{XY'+YX'}D\geq\sum_{n=3}^a\gamma_n\binom anu_n,\qquad\gamma_n=2(2^n-n-2).
\]
Also $aY'+(a-2)Y=2(a-2)\binom a2u_2+2(a-1)\sum_{n\geq3}\binom anu_n$, $H_1=\sum_{n\geq3}(n-2)\binom an(\alpha+t(a-n))u_n$ and $V_1=t\sum_{n\geq2}(n-1)(a-n)\binom anu_n$. Comparing coefficients of $\binom anu_n$: at $n=2$ the difference is $0$; at $n=3$ it is $2\alpha-2t(a-1)\geq0$; for $n\geq4$, by $\gamma_n\geq8(n-2)+2$ and $\alpha\geq t(a-1)$, it is at least $t(a-1)(4(n-2)+2)-2t(a-1)-4t(n-2)(a-n)=4t(n-1)(n-2)\geq0$.

\emph{Resummation.} Regard the moves as operators on functions on $\Omega$, each divided by $c$ at the destination level; all strictly raise $\ell$, and inequalities between operators are entrywise. Let $P$ and $Q$ be the sums of the $B_j$ with $j$ even and odd, $C=C_+-C_-$ with $C_\pm$ the sums of the $C'_j$ with $j$ even and odd, $H_+$ and $H_-$ the sums of the $H_j$ with $j\geq2$ even and $j\geq3$ odd, $V_+$ and $V_-$ the sums of the $V_j$ with $j$ odd and $j\geq2$ even, $A_0$ the operator of $A^\psi_0$, and $U$ the straight moves. The recurrence reads $\omega=\beta+(U+P-Q+C+A)\omega$ with $A=A_0+H_+-H_--H_1+V_+-V_-$ and $\beta=\omega|_{\ell=0}\geq0$. The inequalities above give
\[
P^2\geq4Q,\qquad H_+P\geq6H_-,\qquad V_+P\geq6V_-,\qquad C_+P\geq6C_-,\qquad A_0P+PA_0+2V_1\geq4H_1.
\]
Let $G=(I-P/2)^{-1}=\sum_{m=0}^N(P/2)^m\geq0$. Then $PG=GP=2(G-I)$ and $(I-P/6)G=\frac23G+\frac13I$, so $G(H_+-H_-)G\geq GH_+(I-P/6)G\geq0$, $GCG\geq0$ and $G(V_+-V_-)G\geq\frac23GV_1G$. Hence
\[
GAG\geq G\bigl(A_0-H_1+\tfrac23V_1\bigr)G\geq G\bigl(A_0-\tfrac14(A_0P+PA_0)+\tfrac16V_1\bigr)G=\tfrac12(GA_0+A_0G)+\tfrac16GV_1G\geq0.
\]
With $R=U+P^2/4-Q\geq0$, the operator $M=G(R+C+A)G$ is nonnegative and strictly raises $\ell$. Since $(I-P/2)^2\omega=\beta+(R+C+A)\omega$, the function $v=(I-P/2)\omega$ satisfies $v=G\beta+Mv$. Therefore $\omega=G\sum_{q=0}^NM^qG\beta\geq0$, and $g(m,n;k)\geq0$ as in the proof of Theorem~\ref{thm:lc-vary}.
\end{proof}

The diagnostics \path{runs/varratio/affine_verify.py} check, in exact arithmetic, every inequality of this proof, the nonnegativity of $M$, the identity $\omega=G\sum_qM^qG\beta$ and property (P) on random profiles with $3\leq N\leq10$, including $\kappa$ at its upper bound.


