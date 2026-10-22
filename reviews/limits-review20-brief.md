# Review round 20: Theorem 8.9 strengthened, and Proposition 8.10

Please give an adversarial, line-by-line review of paper.tex at commit 1708d373e827d0684011c138000ffd5f4572ffb3 (github.com/skypher/szkraw). The scope runs from the paragraph "Linearly increasing ratio" to the end of Section 8. The full text is reproduced below, so no fetch is needed.

**What changed since round 19.** In round 19 you passed Theorem 8.9 with the hypothesis 0 ≤ κ ≤ N(1−r)/(2N−1); the fixes are applied.
- *Theorem 8.9.* The hypothesis is now only that b is nondecreasing. The text shows this is equivalent to κ(N + d_{N−1}/(1−d_{N−1})) ≤ N(1−r).
  - A₀ ≥ 0 now comes directly from monotonicity of b.
  - The key inequality (eq:affine-key) has a new proof. It reduces to (eq:affine-red), uses α ≥ t u₀/u₁ (monotone d_i/f_1(i)), and a concave-quadratic interpolation in z = u₀/u₁ with two endpoint bounds.
- *Proposition 8.10 (new).* Quadratic profiles (Newton degree ≤ 2), any convex quadratic ratio ρ(x) = r + tx + τC(x,2), and nondecreasing b give (P).
- *Open-problems paragraph.* Its new sentences about nonlinear ratios are outside the scope of this round.

**Independence caveat.** The new key-inequality proof and Proposition 8.10 came from your consult round 6. Please review them as if they were someone else's, and try hard to break them.

**Check in particular:**
1. The equivalence "b nondecreasing ⇔ last increment ≥ 0 ⇔ κ(N+R) ≤ N(1−r)":
   - monotonicity of R_i = d_i/f_1(i);
   - the formula for b_{i+1} − b_i;
   - the consequence tN ≤ s;
   - the claims after the theorem: the linear profile, the convex profile range, and the N = 4 example.
2. Every use of the old slope bound is gone or replaced: h_n ≥ 0, s − t(ℓ+n+2) ≥ 0 in the detours, and A₀ ≥ 0.
3. The key inequality:
   - the reduction to (eq:affine-red): the formulas for the two A₀, the bounds for the two B₀, 4H₁ − 2V₁ = 4αH_* + 2tT, and the index shift for V₁;
   - K ≥ 0, including the products used and the binomial identities;
   - α ≥ tR_{ℓ+a−1} ≥ tu₀/u₁, and why the minimum over α suffices;
   - homogeneity and the normalization u₁ = 1, the case q = 0, and z ≤ 1/q;
   - the values A₀ = tzY and A₀'' = t(z+1)J at α = tz;
   - the formula for F(z) and the interpolation identity;
   - the lower bound for YJ (the selected products, the coefficient C(a,n+1)[C(n+1,2)+C(n+1,3)] = C(a,n)(a−n)n(n+2)/6 for n ≥ 4 and 3/2 for n = 3, and distinctness of the selected pairs);
   - the bound for YY′;
   - the bound for (4/q)H_* + 2T;
   - the endpoint inequalities and the numerical facts.
4. Proposition 8.10:
   - the Leibniz formula for quadratic ρ and the occurring indices;
   - the list of moves and their signs (A₁ ≤ 0 entering with sign −1; which B, C vanish);
   - the bounds for φ₂(ℓ), φ₂(ℓ+1) and the inequality φ₂(ℓ)φ₂(ℓ+1) ≥ c_{ℓ+1}φ₄(ℓ);
   - P² ≥ 4Q;
   - that the resummation applies with H = 0 and V₁ = −A₁;
   - the stated equivalence for nondecreasing b.
5. If you can, test numerically in exact arithmetic:
   - Theorem 8.9 at the new maximal κ, for N up to 12 or more and curved profiles;
   - Proposition 8.10 for random parameters;
   - just beyond the boundary (b not monotone), to see what fails.
6. Verdict: PASS, PASS WITH MINOR FIXES (with replacement text), or FAIL (failing step or counterexample).

**Author's checks.** runs/varratio/verify_consultH.py, exact, 0 failures:
- 5,088 checks of the sequence inequalities, including geometric sequences with ratios 10^{−5} to 3;
- 450 random arrays at the new maximal slope: monotone R, monotone b, α ≥ tu₀/u₁, and the key inequality at 4,526 sources;
- (P) for N ≤ 8;
- the N = 4 example;
- 72 quadratic-profile arrays: (P) and M ≥ 0.

These are finite checks; the claims rest on the proofs.

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



## Section 8 from "Linearly increasing ratio" to the end, as submitted

```latex
\paragraph{Linearly increasing ratio.}
For curved profiles, linearly increasing ratios need not satisfy the hypotheses of Theorem~\ref{thm:lc-vary}: the Newton coefficients of $b$ of order at least $3$ can be negative, and then some moves of even index in the recurrence of its proof have negative weight and no two-step detour. A resummation of the positive moves handles this.

\begin{theorem}[Linearly increasing ratio]\label{thm:lc-affine}
Let $0=d_0<d_1<\cdots<d_N=1$ have Newton coefficients that are log-concave without internal zeros, let $0<r\leq1$ and $\kappa\geq0$, and put $\rho_i=r+\kappa i/N$, $a_i=1-d_i$, $b_i=(1-\rho_i)d_i$ and $c_i=\rho_id_i$. If $b$ is nondecreasing, then the system has nonnegative linearization. This is the case exactly when $\kappa\bigl(N+d_{N-1}/(1-d_{N-1})\bigr)\leq N(1-r)$.
\end{theorem}

For the linear profile $d_i=i/N$ the condition reads $\kappa\leq\frac N{2N-1}(1-r)$, and these are arrays of Proposition~\ref{prop:lc-quad}. For a convex profile $d_{N-1}\leq(N-1)/N$, so the admitted range of $\kappa$ contains $[0,\frac N{2N-1}(1-r)]$, and it is larger for curved profiles: $N=4$, $d_i=(2^i-1)/15$, $r=1/2$ and $\kappa=2/5$ are admitted, with $b=(0,2/75,3/50,7/75,1/10)$, although $(2N-1)\kappa/N=7/10>1-r$.

\begin{proof}
Write $s=1-r$ and $t=\kappa/N$, and let $f_n(\ell)=\Delta^nd(\ell)$ and $\nu_i=\Delta^id(0)$ be as in Section~\ref{sec:lc}, with $\nu_{-1}=\nu_0=0$. For $0\leq i<N$ put $R_i=d_i/f_1(i)$; then $f_1(i)\geq\nu_1>0$, and log-concavity of $(f_n(i))_{n\geq0}$ gives $R_{i+1}-R_i=\bigl(f_1(i)^2-d_if_2(i)\bigr)/\bigl(f_1(i)f_1(i+1)\bigr)\geq0$. Since $b_{i+1}-b_i=f_1(i)\bigl(s-t(i+1)-tR_i\bigr)$ and the bracket is nonincreasing in $i$, $b$ is nondecreasing exactly when its last increment is nonnegative, that is, when $t(N+R_{N-1})\leq s$ with $R_{N-1}=d_{N-1}/(1-d_{N-1})$; this is the stated condition. In particular $tN\leq s$. Since $c_i=(r+ti)d_i$ and $b_i=(s-ti)d_i$, the Leibniz rule for differences gives, for $\ell\geq0$ and $1\leq n\leq N-\ell$, which includes every index occurring in the moves on $\Omega$,
\[
\varphi_n(\ell)=(r+t(\ell+n))f_n(\ell)+tnf_{n-1}(\ell),\qquad\psi_n(\ell)=h_n(\ell)-v_n(\ell),
\]
with $h_n(\ell)=(s-t(\ell+n))f_n(\ell)$ and $v_n(\ell)=tnf_{n-1}(\ell)$; both are nonnegative when $\ell+n\leq N$. (Outside this range the formulas need not hold, because the Newton coefficients of $b$ and $c$ are set to zero beyond $N$.) Extend $\nu$ by zero outside $1\leq i\leq N$ and put $\widehat\kappa_i=p_i\nu_i+q_i\nu_{i-1}$ $(i\geq1)$, $\widehat\kappa_0=0$, with $p_i=r+ti$ and $q_i=ti$; the Newton sequence $\kappa$ of $c$ is the truncation of $\widehat\kappa$ at $N$. Then
\[
\widehat\kappa_i^2-\widehat\kappa_{i-1}\widehat\kappa_{i+1}=p_i^2(\nu_i^2-\nu_{i-1}\nu_{i+1})+q_i^2(\nu_{i-1}^2-\nu_{i-2}\nu_i)+q_{i-1}p_{i+1}(\nu_i\nu_{i-1}-\nu_{i-2}\nu_{i+1})+t^2(\nu_{i-1}\nu_{i+1}+\nu_{i-2}\nu_i+2\nu_i\nu_{i-1}),
\]
and each term is nonnegative by log-concavity of $\nu$. The positive support of $\widehat\kappa$ is that of $\nu$ when $t=0$ and extends it by one index when $t>0$, an interval in both cases. Truncation at $N$ preserves log-concavity and interval support, so $\kappa$ is log-concave without internal zeros, and Lemma~\ref{lem:lc-ineq} applies to $f$ and to $\varphi$.

\emph{Moves.} We use the recurrence of the proof of Theorem~\ref{thm:lc-vary}, which holds for every array. For $j\geq1$ split $A^\psi_j=H_j-V_j$, where $H_j=W^h_{2j+1,j}$ and $V_j=W^v_{2j+1,j}$ are formed from $h_n$ and $v_n$ in place of $\psi_n$; both are nonnegative on $\Omega$. Keep $A^\psi_0(\ell,a)=b_{\ell+a}-b_\ell$ as one move; it is nonnegative because $b$ is nondecreasing. The weights $B_j$, formed from $\varphi$, and $C_j+C^\psi_j=W^f_{2j+2,j+1}$, formed from $f$, are nonnegative. Write $C'_j=C_j+C^\psi_j$.

\emph{Detours.} All detour inequalities below are asserted for source nodes $(\ell,a)\in\Omega$; in the mixed products the occurring indices satisfy $n\leq a-2$, hence $\ell+n+2\leq N$. Since $\varphi_2(\ell)\geq(r+t(\ell+1))f_2(\ell)$ and $c_{\ell+1}=(r+t(\ell+1))d_{\ell+1}$, Lemma~\ref{lem:lc-ineq} for $f$ gives
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
Only $a\geq3$ needs proof. Put $u_n=f_n(\ell)$, $y_n=\binom anu_n$, $D=u_0+u_1=d_{\ell+1}$, $\alpha=s-t(\ell+a)$, $X=\sum_{n\geq1}y_n$, $Y=\sum_{n\geq2}y_n$, $X'=\sum_{j\geq1}\binom{a-2}j(u_j+u_{j+1})$, $Y'=\sum_{j\geq2}\binom{a-1}j(u_j+u_{j+1})$ and $J=\sum_{n=2}^{a-1}\binom{a-1}nu_n$, so that $X=au_1+Y$, $X'=(a-2)u_1+J$ and $Y'=Y-(a-1)u_2$. Then $A^\psi_0(\ell,a)=\alpha X-tau_0$ and $A^\psi_0(\ell+1,a-2)=(\alpha+t)X'-t(a-2)D$; both are nonnegative, and the two weights $B_0$ are at least $(r+t(\ell+1))Y'$ and $(r+t(\ell+1))Y$. With $H_*=\sum_{n\geq3}(n-2)y_n$ and $T=\sum_{n\geq2}(n-3)(a-n)y_n$ one has $H_1=\sum_{n\geq3}(n-2)(\alpha+t(a-n))y_n$ and, after a shift of index, $V_1=t\sum_{n\geq2}(n-1)(a-n)y_n$, so $4H_1-2V_1=4\alpha H_*+2tT$. Since $c_{\ell+1}=(r+t(\ell+1))D$, it suffices to show
\begin{equation}\label{eq:affine-red}
(\alpha X-tau_0)Y'+Y\bigl((\alpha+t)X'-t(a-2)D\bigr)\geq D(4\alpha H_*+2tT).
\end{equation}
The coefficient of $\alpha$ in the difference of the two sides is $K=XY'+YX'-4DH_*$. By Lemma~\ref{lem:lc-ineq}, $u_i(u_j+u_{j+1})\geq Du_{i+j}$ for $i,j\geq1$, so $XY'\geq au_1Y'\geq D\sum_{n\geq3}ny_n$ and $YX'\geq\binom a2u_2X'\geq D\sum_{n\geq3}\binom n2y_n$; hence $K\geq\frac D2\sum_{n\geq3}\bigl((n-3)(n-4)+4\bigr)y_n\geq0$, and \eqref{eq:affine-red} holds when $t=0$. Let $t>0$. Monotonicity of $b$ at $\ell+a-1$ gives $\alpha\geq tR_{\ell+a-1}\geq tR_\ell=tu_0/u_1$, so it suffices to prove \eqref{eq:affine-red} at $\alpha=tu_0/u_1$. Both sides are homogeneous of degree two in $(u_n)$; take $u_1=1$ and write $z=u_0$ and $q=u_2$. If $q=0$, then $u_n=0$ for $n\geq2$ and both sides vanish. Otherwise $0\leq z\leq1/q$ by log-concavity. At $\alpha=tz$ the two weights $A^\psi_0$ are $tzY$ and $t(z+1)J$, and \eqref{eq:affine-red} divided by $t$ reads $F(z)\geq0$, where
\[
F(z)=zYY'+(z+1)YJ-(z+1)(4zH_*+2T)=(1-qz)F(0)+qzF(1/q)+4H_*z(1/q-z),
\]
the second form holding because $F$ is quadratic with leading coefficient $-4H_*$. It remains to show $F(0)\geq0$ and $F(1/q)\geq0$. Put $L_3=\frac32$, $L_n=\frac{n(n+2)}6$ for $n\geq4$, and $E_n=\frac{2(n^2-5)}{n+1}$. In $YJ$ keep, for each $n$, the product with indices $(2,2)$ if $n=3$, and the products with indices $(2,n-1)$ and $(3,n-2)$ if $n\geq4$; by log-concavity with $u_1=1$, $u_iu_{n+1-i}\geq u_n$, and $\binom{a-1}j\geq\binom{a-i}j$, so $YJ\geq\sum_{n=3}^{a-1}L_n(a-n)y_n$. In $Y$ keep the term $\binom a2q$; as $q(u_{n-1}+u_n)\geq(q+1)u_n$ for $n\geq3$, $YY'\geq(q+1)\sum_{n=3}^a\frac{n(a-1)}2y_n$. Since $L_n\geq2(n-3)$,
\[
F(0)=YJ-2T\geq2(a-2)y_2+\sum_{n=3}^{a-1}\bigl(L_n-2(n-3)\bigr)(a-n)y_n\geq0.
\]
Using $u_n\leq qu_{n-1}$ and a shift of index, $\frac4qH_*+2T\leq\sum_{n=2}^{a-1}E_n(a-n)y_n$, where $E_2<0$. As $L_n+\frac n2\geq E_n$ for $n\geq3$,
\[
\frac{F(1/q)}{1+1/q}=YJ+\frac{YY'}{q+1}-\frac4qH_*-2T\geq\sum_{n=3}^{a-1}\Bigl(L_n+\frac n2-E_n\Bigr)(a-n)y_n\geq0.
\]
The numerical facts used are $L_3=\frac32\geq0$, $L_3+\frac32=3\geq E_3=2$, and, for $n\geq4$, $6(L_n-2(n-3))=(n-5)^2+11$ and $6(n+1)(L_n+\frac n2-E_n)=n^3-6n^2+5n+60>0$.

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

The diagnostics \path{runs/varratio/affine_verify.py} and \path{runs/varratio/verify_consultH.py} check in exact arithmetic the steps of this proof, the nonnegativity of $M$, the identity $\omega=G\sum_qM^qG\beta$ and property (P) on random profiles with $3\leq N\leq11$, including $\kappa$ at the largest value for which $b$ is nondecreasing.

For profiles whose Newton coefficients vanish from order $3$ on, every increasing convex quadratic ratio with nondecreasing $b$ is admissible.

\begin{proposition}[Quadratic profiles]\label{prop:lc-quadprof}
Let $d_i=\nu_1i+\nu_2\binom i2$ with $\nu_1>0$, $\nu_2\geq0$ and $d_N=1$, let $\rho(x)=r+tx+\tau\binom x2$ with $r>0$ and $t,\tau\geq0$, and put $a_i=1-d_i$, $b_i=(1-\rho(i))d_i$ and $c_i=\rho(i)d_i$. If $b$ is nondecreasing, then the system has nonnegative linearization.
\end{proposition}

As in the proof of Theorem~\ref{thm:lc-affine}, $b_{i+1}-b_i=f_1(i)\bigl(1-\rho(i+1)-(t+\tau i)R_i\bigr)$ with a nonincreasing bracket, so $b$ is nondecreasing exactly when $t(N+R)+\tau\bigl(\binom N2+(N-1)R\bigr)\leq1-r$, where $R=d_{N-1}/(1-d_{N-1})$.

\begin{proof}
We use the recurrence of the proof of Theorem~\ref{thm:lc-vary}. Here $f_2=\nu_2$ and $f_n=0$ for $n\geq3$. Fix $\ell$ and write $u=d_\ell$, $v=f_1(\ell)$, $w=\nu_2$ and $p=\rho(\ell+1)$, so that $c_{\ell+1}=p(u+v)$ and, by convexity, $u\leq\ell v$. For $\ell+n\leq N$ the Leibniz rule gives $\varphi_n(\ell)=\rho(\ell+n)f_n+n(t+\tau(\ell+n-1))f_{n-1}+\binom n2\tau f_{n-2}$, all at $\ell$. Hence $\varphi_n=\psi_n=0$ for $n\geq5$, $\varphi_3\geq0$, $\varphi_4=6\tau w\geq0$, and $\psi_n=f_n-\varphi_n=-\varphi_n\leq0$ for $n=3,4$. On $\Omega$ the moves are therefore: $A^\psi_0=b_{\ell+a}-b_\ell\geq0$; $A^\psi_1=\sum_{n=3,4}(n-2)\binom an\psi_n\leq0$, which enters with the sign $-1$; $A^\psi_j=0$ for $j\geq2$; $B_0\geq0$, $B_1=\binom a4\varphi_4\geq0$, and $B_j=0$ for $j\geq2$; $C_0+C^\psi_0=W^f_{2,1}\geq0$, and $C_j+C^\psi_j=W^f_{2j+2,j+1}=0$ for $j\geq1$; and the straight moves are nonnegative. The only negative contribution comes from $B_1$. Now $\varphi_2(\ell)\geq pw+\tau\bigl(u+2(\ell+1)v\bigr)$ and $\varphi_2(\ell+1)\geq pw+\tau\bigl(u+v+2(\ell+2)(v+w)\bigr)$, and the two brackets together exceed $6(u+v)$ by $-4u+(4\ell+1)v+(2\ell+4)w\geq0$. Hence $\varphi_2(\ell)\varphi_2(\ell+1)\geq6p\tau w(u+v)=c_{\ell+1}\varphi_4(\ell)$, and with $B_0\geq\binom a2\varphi_2$ and $\binom a2\binom{a-2}2=6\binom a4$, $B_0(\ell,a)B_0(\ell+1,a-2)\geq6c_{\ell+1}B_1(\ell,a)$. In the notation of the resummation above, $P=B_0$, $Q=B_1$, $P^2\geq4Q$, $H_j=0$, $V_1=-A^\psi_1\geq0$, and all other operators are nonnegative, so $M\geq0$, $\omega\geq0$, and (P) follows as before.
\end{proof}

```
