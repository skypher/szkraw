# Independent review, round 23: Proposition 8.14 (products of Newton sequences)

Repository: github.com/skypher/szkraw (paper.tex; diagnostics runs/np/two_step.py, runs/np/case_proofs.py, runs/np/trinomial_boxes.py).

Proposition 8.14 is new. It was found and proved here, without consultation. Please check the proof completely and independently. This is a mathematics review, not a Lean review.

Check in particular:
1. The product rule C(x,i)C(x,j) = Σ_k C(k,i)C(i,k−j)C(x,k), the support claim, and that κ_k = Σ_p H_k(p)ρ_{p1}ν_{p2}.
2. The layer-cake reduction. Do the symmetry and monotonicity of u_c and w_c really reduce κ_k² − κ_{k−1}κ_{k+1} to nonnegativity of D_c(B) for centred boxes? This includes the boundary terms (a = 0; u_c(−1) = 0), the diagonal terms, and the double-counting of ordered pairs.
3. The identity D_c(B) = Σ_{e,e′}[V_{e+e′}(B−e) − V_{e+e′}(B)].
4. The closed form of V and its use in (T1); the RR2 claim and the derived pointwise inequality in (T2); the argument in (T3), including zeros and interval supports.
5. Each of the five case reductions: the telescoping, the use of central symmetry (with the stated centres μ), the claimed brackets and their signs, the position of a−1 and b−1 relative to μ, and the reduction of the other four ordered pairs by transposition.
6. Whether the result is known. Search the literature: log-concavity in the binomial basis {C(x,k)} under multiplication, or ultra-log-concavity of unions of exchangeable random sets. Give references if it is known.

Answer format: PASS / PASS WITH MINOR FIXES / FAIL, every defect with an exact fix, and your independent checks. Be terse.

## Paper text

```latex
\paragraph{Products of Newton sequences.}
The proof of Corollary~\ref{cor:lc-lowdeg} used only that the Newton coefficients of $c=\rho d$ are log-concave. This holds for every profile.

\begin{proposition}[Products]\label{prop:np}
Let $(\rho_i)_{i\geq0}$ and $(\nu_j)_{j\geq0}$ be nonnegative and log-concave without internal zeros, and let $f(x)=\sum_i\rho_i\binom xi$ and $g(x)=\sum_j\nu_j\binom xj$. Then the Newton coefficients $\kappa_k=\Delta^k(fg)(0)$ of $fg$ are nonnegative and log-concave without internal zeros.
\end{proposition}

\begin{proof}
The product rule $\binom xi\binom xj=\sum_k\binom ki\binom i{k-j}\binom xk$ gives $\kappa_k=\sum_pH_k(p)\rho_{p_1}\nu_{p_2}$, where $H_k(i,j)=\binom ki\binom i{k-j}=[y^iw^j](y+w+yw)^k$ vanishes unless $i,j\leq k\leq i+j$. If $\rho$ and $\nu$ are supported on $[p_0,p_1]$ and $[q_0,q_1]$, then $\kappa_k>0$ exactly for $\max(p_0,q_0)\leq k\leq p_1+q_1$, so $\kappa$ has no internal zeros. For log-concavity fix $k\geq1$; then
\[
\kappa_k^2-\kappa_{k-1}\kappa_{k+1}=\sum_{c\in\mathbb Z^2}\sum_{p\in\mathbb Z^2}T_c(p)\,u_c(p_1)\,w_c(p_2),\qquad T_c(p)=H_k(p)H_k(c-p)-H_{k-1}(p)H_{k+1}(c-p),
\]
with $u_c(i)=\rho_i\rho_{c_1-i}$ and $w_c(j)=\nu_j\nu_{c_2-j}$. By log-concavity without internal zeros, $u_c$ is symmetric about $c_1/2$ and nondecreasing on $i\leq c_1/2$, so $u_c=\sum_{0\leq a\leq c_1/2}(u_c(a)-u_c(a-1))\mathbf 1_{[a,c_1-a]}$ with nonnegative coefficients, and likewise $w_c$. It therefore suffices to show $D_c(B)=\sum_{p\in B}T_c(p)\geq0$ for every box $B=[a,c_1-a]\times[b,c_2-b]$ with $a\leq c_1/2$, $b\leq c_2/2$.

Let $E=\{(1,0),(0,1),(1,1)\}$, so that $H_k=\sum_{e\in E}H_{k-1}(\cdot-e)$. Expanding $H_k(p)$, $H_k(c-p)$ and $H_{k+1}(c-p)$ in this way gives
\[
D_c(B)=\sum_{e,e'\in E}\bigl(V_{e+e'}(B-e)-V_{e+e'}(B)\bigr),\qquad V_s(p)=H_{k-1}(p)H_{k-1}(c-s-p),
\]
where $V_s(X)=\sum_{p\in X}V_s(p)$. Fix $s=e+e'$, write $V=V_s$, $m=c-s$, $t=k-1$ and $\mu=m/2$. With $n_1=2t-m_2$, $n_2=2t-m_1$, $n_3=m_1+m_2-2t$ one has $V(x,y)=\frac{t!^2}{n_1!n_2!n_3!}\binom{n_1}{t-y}\binom{n_2}{t-x}\binom{n_3}{x+y-t}$ (and $V=0$ if some $n_i<0$). Three properties follow.
\begin{enumerate}
\item[(T1)] For every interval $W$, the marginal $G_W(x)=\sum_{y\in W}V(x,y)$ is a constant times $\binom{n_2}{t-x}\sum_{z\in t-W}\binom{n_1}z\binom{n_3}{x-z}$, a product of a binomial row and a convolution of two log-concave sequences without internal zeros; so $G_W$ is log-concave without internal zeros. The same holds with the roles of the coordinates exchanged.
\item[(T2)] $V(c-s-p)=V(p)$, and $V$ is reverse regular of order two: $V(x,y)V(x',y')\leq V(x,y')V(x',y)$ for $x\leq x'$, $y\leq y'$, by log-concavity of $\binom{n_3}{\cdot}$. Taking $x'=2\mu_1-x$ and $y,y'$ symmetric about $\mu_2$, central symmetry turns this into $V(x,y)^2\leq V(x,y')^2$. Hence $V(x,y')\geq V(x,y)$ whenever $x\leq\mu_1$, $y\leq y'$ and $y+y'=2\mu_2$; and symmetrically in the coordinates.
\item[(T3)] If $G$ is log-concave without internal zeros and $G(x)\leq G(2\mu_1-x)$ for all $x\leq\mu_1$, then $G$ is nondecreasing on $x\leq\mu_1$: otherwise $G(x-1)>G(x)$ for some $x\leq\mu_1$, and log-concavity makes $G$ nonincreasing from $x-1$ on, so $G(2\mu_1-x+1)\leq G(x)<G(x-1)$.
\end{enumerate}
Write $I=[a,c_1-a]$, $J=[b,c_2-b]$, $X(I',J')=V(I'\times J')$, and telescope along rows or columns. By the symmetry $H_k(i,j)=H_k(j,i)$ it suffices to treat five ordered pairs.

\emph{$e=e'=(1,0)$}: $\mu=c/2-(1,0)$ and $V(B-e)-V(B)=G_J(a-1)-G_J(a-2)$ by central symmetry. Since $J$ is symmetric about $\mu_2$, $G_J$ is symmetric about $\mu_1$, hence nondecreasing on $x\leq\mu_1$ by (T1) and (T3); and $a-1\leq\mu_1$.

\emph{$e=(1,0)$, $e'=(0,1)$}: $\mu=(c-(1,1))/2$ and $V(B-e)-V(B)=V(a-1,c_2-b)-V(a-1,b-1)\geq0$ by (T2), since $a-1<\mu_1$ and $(c_2-b)+(b-1)=2\mu_2$.

\emph{$e=(1,0)$, $e'=(1,1)$}: $\mu=c/2-(1,\tfrac12)$ and
\[
V(B-e)-V(B)=\bigl[V(a-1,c_2-b)-V(a-1,b-1)\bigr]+\bigl[G_{J-1}(a-1)-G_{J-1}(a-2)\bigr].
\]
The first bracket is nonnegative by (T2), as $a-1\leq\mu_1$. For the second, $G_{J-1}(2\mu_1-x)-G_{J-1}(x)=V(x,c_2-b)-V(x,b-1)\geq0$ for $x\leq\mu_1$ by (T2), so (T1) and (T3) apply.

\emph{$e=(1,1)$, $e'=(1,0)$}: the same $V$, and $V(B-e)-V(B)=\bigl[X(I-1,J-1)-X(I-1,J)\bigr]+\bigl[V(B-(1,0))-V(B)\bigr]$. The first bracket vanishes by central symmetry, since $I-1$ is symmetric about $\mu_1$; the second is the previous case.

\emph{$e=e'=(1,1)$}: $\mu=c/2-(1,1)$ and $V(B-e)-V(B)=\bigl[K(b-1)-K(b-2)\bigr]+\bigl[X(a-1,J)-X(a-1,J-2)\bigr]+\bigl[G_{J-2}(a-1)-G_{J-2}(a-2)\bigr]$ with $K(y)=\sum_{x\in I-1}V(x,y)$. Since $I-1$ is symmetric about $\mu_1$, $K$ is symmetric about $\mu_2$ and nondecreasing on $y\leq\mu_2$ by (T1) and (T3); and $b-1\leq\mu_2$. The second bracket is a sum of two differences of the form in (T2). For the third, $G_{J-2}(2\mu_1-x)-G_{J-2}(x)=X(x,J)-X(x,J-2)\geq0$ for $x\leq\mu_1$ by (T2), so (T1) and (T3) give $G_{J-2}(a-1)\geq G_{J-2}(a-2)$.

All terms of $D_c(B)$ are nonnegative, which proves the proposition.
\end{proof}

In the language of random sets: if $S$ and $T$ are independent random subsets of $[n]$ whose laws are invariant under permutations and whose cardinalities are ultra-log-concave of order $n$, then so is $|S\cup T|$, since $\Pr(|S\cup T|=k)=\binom nk\kappa_k$ for $\Pr(S=A)=\rho_{|A|}$ and $\Pr(T=A)=\nu_{|A|}$. We did not find Proposition~\ref{prop:np} in the literature; Hoggar's theorem is its analogue for the power basis. The diagnostics \path{runs/np/two_step.py} and \path{runs/np/case_proofs.py} check in exact arithmetic the identity for $D_c(B)$, the sign of each of its nine terms for $k\leq9$, and every bracket of the case analysis, (T1) and (T2) for $k\leq6$.
```
