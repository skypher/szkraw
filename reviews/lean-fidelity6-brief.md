# Independent review, round 6: do the Lean statements of Section 9 say what the paper says?

As in rounds 1–5 (all PASS WITH MINOR FIXES, fixes applied), **do not check proofs**. Check only whether each Lean statement faithfully expresses the paper statement, under the acceptance rule: Lean hypotheses equivalent to or weaker than the paper's, and Lean conclusion equivalent to or stronger. Where the Lean statement covers less than the paper claims, say exactly what is missing.

This round covers the new Section 9 declarations:
- **Lemma 9.2** (corner identity): `corner_identity`. Section 9's coordinates `b_1..b_{N-1}, c_1..c_N` are `stochArray`; `krawDir N δb δc r ε` is `K_{N,r} + ε v` for `v = (δb, δc)`, where `δb_N` is ignored because `b_N = 1 - c_N`. `stochDir` holds the paper's conventions `δb_0 = δc_0 = 0` and `δb_N = -δc_N`, and `cornerF` is F. The first-order change is stated as a `HasDerivAt` at `ε = 0`, with `Fin.last N` the index N.
- **Definition 9.3 and Theorem 9.4**: `AdmitsRule`, `ruleArray`, `Leven`, `Lodd`, `forced_equalities` and `forced_vanishing`. "A set of arrays with property (P)" is a family `S N` of sets whose members satisfy `MatrixPositivity`. `Polynomial ℝ` gives the polynomial rules.
- **Lemma 9.7**: `lower_measure`, `lower_rates` and `lower_triple`, for the spectral measure (`spectralNode`, `spectralWeight`) of any array satisfying (2.1). `spectral_top_node` shows that x₀ = 1 is a node. The lowered system's coefficients in the fixed coordinate x are `epsRaw … (-ε)`: `lower_measure` identifies its polynomials as orthogonal for μ − εδ_{x₀} with value 1 at x₀. `piw` is π_n = 1/∫R_n² dμ and `tailG` is T_x(y,z).
- **Proposition 9.9**: first statement and part (1) only (`families_sign`, `families_weak_sign`, `families_no_strict_sign`). Part (2) is not formalized and is declared so in the scope text. `altSum vb vc N` is A_N for `v_N = (vb N, vc N)`.
- **Proposition 9.10**: `thinness`; "lacks property (P)" is formalized as `Admissible ∧ ¬MatrixPositivity ∧ g(N,N;N) < 0`.
- **Corollary 9.11**: `radius_order`. ρ_N(r) is `stabilityRadius`, the supremum of `stableRadii`, and `WithinKraw` is the norm (5.2).
- **Proposition 9.12**: `raise_measure`, `raise_corner`, `raise_sign` and `raise_bound`. `kv N r = geometricCoefficients N (1/r) 1` coincides with `krawCoefficients N r` on 0..N. `kx` and `kw` are the nodes x_n = 1 − (1+r)n/N and masses w_n = C(N,n) r^{N−n}/(1+r)^N. `raisedKraw N r τ` is the affinely normalized raised system with ε = τ w_0, and its nodes are y = (1+ε)x − ε. `raise_measure` identifies it as the system of the raised measure.
- **Corollary 9.13**: `radius_exp` and `radius_exp_asymp`; `tauStar` is τ_N^*.
- Also check the updated scope sentences of the code-and-formalization section for these results.

Conventions:
- `Admissible v` is (2.1), and `productMatrix v m` has entry (n,k) = g(m,n;k).
- `Fin (N + 1)` indices run over 0..N, and `Fin.last N` is N.
- `Finset.range n` is {0,…,n−1}. Natural-number subtraction truncates at 0, and Lean's 0⁻¹ = 0.

Answer format: a table (paper claim | Lean declaration | MATCH / MATCH, SCOPE NOTED / MISMATCH | reason), exact fixes, and an overall verdict (PASS / PASS WITH MINOR FIXES / FAIL). Be terse.

## Part A. Paper statements

#### Section 9 setting
```latex
Theorems~\ref{thm:low} and~\ref{thm:palindromic} control every triple except the deep ones by inequalities, Theorem~\ref{thm:lc} controls all triples of constant-ratio arrays with log-concave Newton profiles, and Section~\ref{sec:open} records shape conditions that fail on deep triples. This section shows that part of the failure is structural near the symmetric endpoint. For uniformly sampled polynomial deformation directions, and for the analytic and boundary-layer extensions specified below, admission at every sufficiently large symmetric Krawtchouk system imposes two first-order boundary equalities. This does not exclude arbitrary uniform inequality criteria, nor families of admissible arrays that are not of these forms. Write $K_{N,r}$ for the Krawtchouk array \eqref{eq:parameters} with $q=1$, and use the coordinates $b_1,\ldots,b_{N-1},c_1,\ldots,c_N$ of a stochastic array with $b_0=0$, $a_0=1$, $a_N=0$, $b_N=1-c_N$ and $a_n=1-b_n-c_n$ otherwise. An affine change of $x$, together with the positive normalization $R_n(x_0)=1$ at the largest support point $x_0$, reduces every finite system to this form. A direction $v=(\delta b_1,\ldots,\delta b_{N-1},\delta c_1,\ldots,\delta c_N)$ changes these coordinates; we put $\delta b_0=\delta c_0=0$ and $\delta b_N=-\delta c_N$.
```

```latex
\begin{lemma}[Corner value]\label{lem:corner-value}
For $0<r\leq1$, the array $K_{N,r}$ has $g(N,N;N)=(1-r)^N$.
\end{lemma}
```

```latex
\begin{lemma}[Corner identity]\label{lem:corner}
Let $N\geq2$ and $s_N=(-1)^{\lfloor N/2\rfloor+1}\binom{N-1}{\lfloor(N-1)/2\rfloor}^{-1}$. Put $F=\delta b+2\delta c$ if $N$ is even and $F=\delta b$ if $N$ is odd. Then
\[
\frac{d}{d\varepsilon}\,g(N,N;N)\Big|_{K_{N,1}+\varepsilon v,\ \varepsilon=0}=s_N\sum_{n=0}^N(-1)^n\binom NnF(n).
\]
\end{lemma}
```

```latex
\begin{definition}\label{def:rule}
A \emph{uniform rule} is a pair of real functions $\beta,\gamma$ on $[0,1]$. It defines, for each $N$, the direction $v_N$ with $\delta b_n=\beta(n/N)$ for $1\leq n<N$ and $\delta c_n=\gamma(n/N)$ for $1\leq n\leq N$. A set of arrays \emph{admits} the rule at the symmetric endpoint if there is $N_0$ such that for every $N\geq N_0$ there is $\varepsilon_N>0$ with $K_{N,1}+\varepsilon v_N$ in the set for all $0<\varepsilon<\varepsilon_N$. Put
\[
L_{\mathrm{even}}=\beta(0)+2\gamma(0)+\beta(1)+\gamma(1),\qquad L_{\mathrm{odd}}=\beta(0)-\beta(1)-\gamma(1).
\]
\end{definition}
```

```latex
\begin{theorem}[Forced equalities for uniform criteria]\label{thm:uniform}
Let $\beta,\gamma$ be polynomials. If a set of arrays with property (P) admits the rule $(\beta,\gamma)$ at the symmetric endpoint, then $L_{\mathrm{even}}=L_{\mathrm{odd}}=0$. If $L_{\mathrm{even}}=L_{\mathrm{odd}}=0$, the first-order change of $g(N,N;N)$ along $v_N$ vanishes for every $N$ above the degrees of $\beta$ and $\gamma$.
\end{theorem}
```

```latex
\begin{lemma}[Lowering the top mass]\label{lem:topmass}
Let $0\leq\varepsilon<\mu(\{x_0\})$, let $\mu_\varepsilon=\mu-\varepsilon\delta_{x_0}$, and let $R_n^\varepsilon$ be its polynomials, normalized at $x_0$. Put $\pi_n^\varepsilon=\bigl(\int(R_n^\varepsilon)^2\,d\mu_\varepsilon\bigr)^{-1}$ and $\pi_n=\pi_n^0$; these inverse norms are not rescaled to impose $\pi_0^\varepsilon=1$. The recurrence coefficients in~(1) are taken in the fixed coordinate $x$, without an $\varepsilon$-dependent affine normalization.
\begin{enumerate}
\item The recurrence coefficients change at rate $(\dot a_n,\dot b_n,\dot c_n)=\pi_n(a_n,\,c_n-a_n,\,-c_n)$.
\item If $\int R_xR_yR_z\,d\mu=0$, then
\begin{gather*}
\frac{d}{d\varepsilon}\Big|_{\varepsilon=0}\int R^\varepsilon_xR^\varepsilon_yR^\varepsilon_z\,d\mu_\varepsilon=2-T_x(y,z)-T_y(x,z)-T_z(x,y),\\
T_x(y,z)=\sum_{k\geq x}g(y,z;k).
\end{gather*}
\end{enumerate}
\end{lemma}
```

```latex
\begin{proposition}[Families depending on $N$]\label{prop:families}
Let $v_N$ be directions such that a set with property (P) contains $K_{N,1}+\varepsilon v_N$ for all large $N$ and small $\varepsilon>0$, and let $A_N$ be the alternating sum in Lemma~\ref{lem:corner} for $v_N$. Then $s_NA_N\geq0$ for all large $N$.
\begin{enumerate}
\item Along either parity class, $A_N$ is not eventually strictly positive and not eventually strictly negative. If $A_N$ has an eventual weak sign along a parity class, it vanishes for all large $N$ of the residue class modulo $4$ on which that sign conflicts with the sign of $s_N$.
\item Suppose $\delta b_n=\beta(n/N)+p_n+q_{N-n}$ and $\delta c_n=\gamma(n/N)+p'_n+q'_{N-n}$, with $\beta,\gamma$ as in Corollary~\ref{cor:analytic-rules} and finitely supported boundary layers $p,q,p',q'$ independent of $N$. Then $q'_0=L_{\mathrm{even}}=L_{\mathrm{odd}}$, $p_k=q_k$ and $p'_k+q'_k=-p_k$ for $k\geq1$.
\end{enumerate}
\end{proposition}
```

```latex
\begin{proposition}[Thinness near the symmetric endpoint]\label{prop:thin}
Fix $N\geq2$ and a direction $v$ along which the first-order change $\dot g$ of $g(N,N;N)$ at $K_{N,1}$ is negative. There are $r_*<1$ and $C,c>0$ such that $K_{N,r}+\varepsilon v$ lacks property (P) whenever $r_*<r<1$ and $C(1-r)^N\leq\varepsilon\leq c$.
\end{proposition}
```

```latex
\begin{corollary}[Optimal order of the stability radius]\label{cor:radius-order}
For $N\geq2$ let $\rho_N(r)$ be the largest $\rho$ such that every array satisfying \eqref{eq:basic} with $\widetilde b_i\geq0$ and with left side of \eqref{eq:closeness} at most $\rho$ has property (P). Then $\rho_N(r)$ is of exact order $(1-r)^N$ as $r\to1$.
\end{corollary}
```

```latex
\begin{proposition}[Raising the top mass]\label{prop:raise}
Let $N\geq1$ and $0<r<1$. The measure of $K_{N,r}$ has nodes $x_n=1-(1+r)n/N$ and masses $w_n=\binom Nnr^{N-n}/(1+r)^N$. For $\tau>0$ let $\mu^\tau$ be this measure with the mass at $x_0=1$ raised to $(1+\tau)w_0$. Then $\mu^\tau$ has
\[
g(N,N;N)=\frac{(1+\tau)^2(I-w_0)+w_0}{(1+\tau)(h-w_0)+w_0},\qquad I=\bigl(r(1-r)\bigr)^N,\quad h=r^N,
\]
which is negative exactly when $\tau>\tau_N^*=\bigl(1-(1-r^2)^N\bigr)^{-1/2}-1$. After the affine normalization of Section~\ref{sec:criterion}, its recurrence coefficients differ from those of $K_{N,r}$ by at most $3\tau\max_nw_n$.
\end{proposition}
```

```latex
\begin{corollary}[Exponentially small stability radius]\label{cor:radius-exp}
Let $0<r<1$, and let $\rho_N(r)$ be as in Corollary~\ref{cor:radius-order}. If $(1-r^2)^N\leq\tfrac12$ and $3(1-r^2)^N\leq(1-r)/N$, then
\[
\rho_N(r)\leq3\tau_N^*\max_nw_n\leq3(1-r^2)^N.
\]
In particular $\rho_N(r)=O\bigl((1-r^2)^N\bigr)$ as $N\to\infty$, for every fixed $r\in(0,1)$.
\end{corollary}
```

#### Theorem 5.3 radius (for Corollary 9.11)
```latex
\begin{theorem}[Explicit perturbation inequalities]\label{thm:perturbation}
Let $N\geq1$, $0<r<1$, $s=\min(r,1-r)$, and
\begin{equation}\label{eq:radius}
\eta_N(r)=\frac12\left(\frac{s}{32N}\right)^N.
\end{equation}
Suppose coefficients $\widetilde a_i,\widetilde b_i,\widetilde c_i$ satisfy \eqref{eq:basic}, with $\widetilde b_i\geq0$ for every $i$, and
\begin{equation}\label{eq:closeness}
\max_{0\leq i\leq N}\left\{
\left|\widetilde a_i-\frac{N-i}{N}\right|,
\left|\widetilde b_i-\frac{(1-r)i}{N}\right|,
\left|\widetilde c_i-\frac{ri}{N}\right|\right\}\leq\eta_N(r).
\end{equation}
```

#### Code-and-formalization section (current)
```latex
\section*{Code and formalization}

The companion source tree contains \path{probe.py} and \path{verify.py}. The command
\begin{quote}\verb|python3 -u verify.py --max-n 7|\end{quote}
compares recurrence-matrix multiplication with direct multiplication modulo the terminal polynomial on exact rational inputs, checks the perturbation lower bounds, and replays two rejected coefficient-profile tests. It also checks Theorem~\ref{thm:szwarc}, the margin of Lemma~\ref{lem:qmargin} and the negative coefficient for $p_0>1/2$ on exact Szwarc arrays, the identities of Lemma~\ref{lem:qthree} in the graded model, and the lower bound of Theorem~\ref{thm:symmetric} on rational symmetric perturbations. These computations are diagnostics and do not replace the proofs at arbitrary size. For Section~\ref{sec:limits}, \path{rigidity_probe.py} checks Lemma~\ref{lem:corner} exactly for $N\leq20$, the predicted failures of Theorem~\ref{thm:uniform}, the boundary layers of Proposition~\ref{prop:families}, the region of Lemma~\ref{lem:nr} and the fixed-$r$ computations, and \path{smallr_probe.py} replays the small-$r$ counterexamples.

The Lean development formalizes the following criteria:
\begin{center}
\begin{tabular}{@{}p{0.36\linewidth}p{0.59\linewidth}@{}}
Paper result & Lean declaration\\[3pt]
Theorem~\ref{thm:criterion}: geometric criterion & \path{Szkraw.geometric_criterion}\\[3pt]
Theorem~\ref{thm:perturbation}: perturbation & \path{Szkraw.perturbation_criterion}\\[3pt]
Theorem~\ref{thm:szwarc}: Szwarc's quadratic system & \path{Szkraw.szwarc_full}, \path{Szkraw.szwarc_sharp}\\[3pt]
Lemma~\ref{lem:edge}: edge idempotents & \path{Szkraw.edge_idempotents}, \path{Szkraw.cube_model}\\[3pt]
Lemma~\ref{lem:qthree}: three-term action & \path{Szkraw.three_term_action}, \path{Szkraw.Uvec_top}\\[3pt]
Lemma~\ref{lem:qmargin}: margin for the quadratic system & \path{Szkraw.szwarc_margin}\\[3pt]
Lemma~\ref{lem:stability}: stability of a reference with a margin & \path{Szkraw.stability}\\[3pt]
Theorem~\ref{thm:symmetric}: symmetric criterion & \path{Szkraw.symmetric_criterion}\\[3pt]
Corollary~\ref{cor:symmetric-new}: symmetric systems outside both families & \path{Szkraw.symmetric_new}\\[3pt]
Theorem~\ref{thm:decomp}: quadratic decomposition & \path{Szkraw.decomp_positivity}, \path{Szkraw.decomp_converse}, \path{Szkraw.even_block}, \path{Szkraw.odd_block}, \path{Szkraw.evenComp_admissible}, \path{Szkraw.oddComp_admissible}\\[3pt]
Corollary~\ref{cor:parity}: parity-split criterion & \path{Szkraw.parity_split}, \path{Szkraw.parity_split_sharp}, \path{Szkraw.ps_even_params}, \path{Szkraw.ps_odd_params}\\[3pt]
Theorem~\ref{thm:low}: low products & \path{Szkraw.low_products}\\[3pt]
Corollary~\ref{cor:convex-low}: convex profiles & \path{Szkraw.convex_low}, \path{Szkraw.geometric_convex}\\[3pt]
Theorem~\ref{thm:all}: all products & \path{Szkraw.all_products}\\[3pt]
Corollary~\ref{cor:heavy}: heavy top step & \path{Szkraw.heavy_top}\\[3pt]
Lemma~\ref{lem:reversal}: reversal identity & \path{Szkraw.reversal_identity}\\[3pt]
Theorem~\ref{thm:deep}: deep reduction & \path{Szkraw.deep_formula}, \path{Szkraw.top_expansion}, \path{Szkraw.deep_reduction}\\[3pt]
Theorem~\ref{thm:palindromic}: palindromic criterion & \path{Szkraw.palindromic}\\[3pt]
Corollary~\ref{cor:palin}: monotone palindromic systems & \path{Szkraw.palin_mono}, \path{Szkraw.palin_mono_kraw}\\[3pt]
Theorem~\ref{thm:lc}: log-concave Newton criterion & \path{Szkraw.logconcave_criterion}\\[3pt]
Remark after Theorem~\ref{thm:lc}: two-parameter and Bernstein coefficients & \path{Szkraw.lc_twoParam}, \path{Szkraw.lc_bernstein}, \path{Szkraw.constantRatio_twoParam}\\[3pt]
Lemma~\ref{lem:corner-value}: corner value & \path{Szkraw.corner_value}\\[3pt]
Lemma~\ref{lem:corner}: corner identity & \path{Szkraw.corner_identity}\\[3pt]
Theorem~\ref{thm:uniform}: forced equalities for uniform criteria & \path{Szkraw.forced_equalities}, \path{Szkraw.forced_vanishing}\\[3pt]
Proposition~\ref{prop:families}, first statement and part (1) & \path{Szkraw.families_sign}, \path{Szkraw.families_weak_sign}, \path{Szkraw.families_no_strict_sign}\\[3pt]
Lemma~\ref{lem:topmass}: lowering the top mass & \path{Szkraw.lower_measure}, \path{Szkraw.lower_rates}, \path{Szkraw.lower_triple}\\[3pt]
Proposition~\ref{prop:thin}: thinness near the symmetric endpoint & \path{Szkraw.thinness}\\[3pt]
Corollary~\ref{cor:radius-order}: optimal order of the stability radius & \path{Szkraw.radius_order}\\[3pt]
Proposition~\ref{prop:raise}: raising the top mass & \path{Szkraw.raise_measure}, \path{Szkraw.raise_corner}, \path{Szkraw.raise_sign}, \path{Szkraw.raise_bound}\\[3pt]
Corollary~\ref{cor:radius-exp}: exponentially small stability radius & \path{Szkraw.radius_exp}, \path{Szkraw.radius_exp_asymp}
\end{tabular}
\end{center}
The first includes a positive finite orthogonality measure, distinct support points, the terminal relation, and all finite product identities. The second includes the explicit radius, positive triangle margin, and exact zeros outside the triangle. The entries for Section~\ref{sec:szwarc} state nonnegativity of the coefficients $g(m,n;k)$: for Theorem~\ref{thm:low} and Corollary~\ref{cor:convex-low} on all triples with two indices of sum at most $N$, and for Theorems~\ref{thm:all}, \ref{thm:deep} and~\ref{thm:palindromic} and Corollaries~\ref{cor:heavy} and~\ref{cor:palin} on all triples. Lemma~\ref{lem:reversal} and the identities of Theorem~\ref{thm:deep} are stated for the matrices $R_m(J)$ and $R'_t(J)=\Pi R'_t(\Pi J\Pi)\Pi$. Theorem~\ref{thm:szwarc} is proved in Lean through Corollary~\ref{cor:parity} with $q=1$, and Lemma~\ref{lem:qmargin} through the decomposition, whose components are Krawtchouk arrays; the symmetry of its measure holds for every finite realization of an array satisfying \eqref{eq:basic} with $b\equiv0$ (\path{Szkraw.realization_symmetric}). In Corollary~\ref{cor:symmetric-new}, ``not of the form \eqref{eq:parameters}'' is formalized as the failure of the hypotheses of Theorem~\ref{thm:criterion} and as disagreement with every array \eqref{eq:parameters} in the Lean parametrization; its last sentence follows from the explicit coefficient box of positive radius in \path{Szkraw.symmetric_criterion}; openness and dimension are not stated separately in Lean. For Corollary~\ref{cor:parity}, when $N\geq2$, Lean proves that both normalized components satisfy the hypotheses of Theorem~\ref{thm:criterion} and are the arrays \eqref{eq:parameters} with parameters $(N,q,r)$ and $(N-1,q,r/q)$ (\path{Szkraw.ps_even_params}, \path{Szkraw.ps_odd_params}); \path{Szkraw.parity_split} also covers $N=1$, where the odd component is the constant polynomial alone. In Theorem~\ref{thm:decomp} the identity for $g(2a,2b+1;2c+1)$ is stated with the unnormalized odd component, which has the same product coefficients (\path{Szkraw.product_normalize}). The finite realization holds for every array satisfying \eqref{eq:basic} (\path{Szkraw.finite_realization}). The proofs formalize the cone argument and the identity $g(m,n;k)\int R_k^2\,d\mu=g(m,k;n)\int R_n^2\,d\mu$ in matrix form. The entry for Theorem~\ref{thm:lc} includes the same finite realization as the first and the nonnegativity of every coefficient $g(m,n;k)$; its proof formalizes Lemmas~\ref{lem:lc-ineq} and~\ref{lem:detours}, the operator induction, and Lemma~\ref{lem:kernel-rec} in converse form: the solution of~\eqref{eq:kernel-rec} yields the linearization coefficients. The remark after the proof of Theorem~\ref{thm:lc} is formalized as identities for all real $u$ and $v$ (two-parameter form, \path{Szkraw.lc_twoParam}) and for all real $r$ (Bernstein form, \path{Szkraw.lc_bernstein}, whose coefficients $B_s$ are $\binom Ds$ times the Bernstein coefficients); \path{Szkraw.constantRatio_twoParam} identifies the arrays of Theorem~\ref{thm:lc} with this family, and the proof formalizes the operator induction coefficientwise in $t$. All of them have compiled proofs without added axioms or admitted goals; the axiom audit reports only \path{propext}, \path{Classical.choice} and \path{Quot.sound}. Lemma~\ref{lem:edge} is stated for every commutative real algebra with elements $y_1,\ldots,y_N$ satisfying $y_j^2=(1-r)y_j+r$ whose squarefree monomials form a basis, which determines $A$ up to isomorphism, and for $r\neq-1$; \path{Szkraw.cube_model} shows that the real functions on $\{1,-r\}^N$ form such an algebra. Its basis assertion is stated as linear independence of the $f_ly_S$ together with equality of their span and the ideal $f_lA$. Lemma~\ref{lem:qthree} is stated for $N\geq1$, $p_0<1$ and $r=p_0/(1-p_0)$, in every commutative real algebra satisfying these relations, without a basis hypothesis; its recurrence is an equality in $A\times A^N$, which restricts to $V$, and \path{Szkraw.Uvec_top} states $U_{2N+1}=0$ separately. Lemma~\ref{lem:corner} is stated for $N\geq2$ as the derivative at $\varepsilon=0$ of $g(N,N;N)$ along $K_{N,1}+\varepsilon v$. Its Lean proof replaces the beta integrals by an explicit matrix: the derivative $X$ of $R_N^\varepsilon(J_\varepsilon)$ satisfies $[J,X]=[\Pi,E]$ and $e_0^\mathsf TX=0$, and $Z_{mn}=\binom Nn(-1)^{n+s}/(2\binom{N-1}s)$ for $m+n=2s+1$, $Z_{mn}=0$ for $m+n$ even, satisfies $ZJ-JZ=e_Ne_N^\mathsf T$ on the columns $n\geq1$; hence the derivative equals $\operatorname{tr}((Z\Pi-\Pi Z)E)$, which is evaluated entry by entry. In Theorem~\ref{thm:uniform} the set of arrays is a family of sets indexed by $N$ whose members satisfy $g(m,n;k)\geq0$, admission is Definition~\ref{def:rule}, and the second statement is the vanishing of the derivative for every $N\geq1$ above the degrees. In Proposition~\ref{prop:thin} the direction is given in the coordinates $b_1,\ldots,b_{N-1},c_1,\ldots,c_N$ of Section~\ref{sec:limits}, the hypothesis is that the derivative of $g(N,N;N)$ at $\varepsilon=0$ is negative, and the conclusion is that $K_{N,r}+\varepsilon v$ satisfies \eqref{eq:basic} and has $g(N,N;N)<0$; \path{Szkraw.productMatrix_contDiffAt} gives the smoothness used in its proof. In Corollary~\ref{cor:radius-order}, $\rho_N(r)$ is the supremum of the radii with the stated property, and exact order means $c_1(1-r)^N\leq\rho_N(r)\leq c_2(1-r)^N$ for all $r$ in an interval $(r_0,1)$. Lemma~\ref{lem:topmass} is stated for the spectral measure of every array satisfying \eqref{eq:basic}, whose node $x_0=1$ exists by \path{Szkraw.spectral_top_node}; the polynomials of $\mu_\varepsilon$ are identified by orthogonality and their value $1$ at $x_0$ (\path{Szkraw.lower_measure}), and both parts are derivatives at $\varepsilon=0$. In Proposition~\ref{prop:raise}, Lean states that the normalized array satisfies \eqref{eq:basic}, that its polynomials are orthogonal for the raised measure transported to $y=(1+\varepsilon)x-\varepsilon$ and equal $1$ at the top node, and then the corner formula, its sign and the coefficient bound; the proof uses the polynomials $(1+\varepsilon S_n)R_n-\varepsilon\sum_{j<n}\pi_jR_j$ for any finite system (\path{TopMass.lean}). The results of Section~\ref{sec:limits} other than Lemmas~\ref{lem:corner-value} and~\ref{lem:corner}, Theorem~\ref{thm:uniform}, Proposition~\ref{prop:thin}, Corollaries~\ref{cor:radius-order} and~\ref{cor:radius-exp}, Lemma~\ref{lem:topmass}, Proposition~\ref{prop:raise} and the first statement and part (1) of Proposition~\ref{prop:families} have not yet been formalized; formalizing them is planned.

```

## Part B. Lean statements

### lean/Szkraw/Statements.lean
```lean
def Admissible {N : ℕ} (v : Coefficients N) : Prop :=
  1 ≤ N ∧ v.a 0 = 1 ∧ v.b 0 = 0 ∧ v.c 0 = 0 ∧ v.a N = 0 ∧
  (∀ i, i ≤ N → v.a i + v.b i + v.c i = 1) ∧
  (∀ i, i < N → 0 < v.a i) ∧
  (∀ i, 0 < i → i ≤ N → 0 < v.c i)

def recurrenceMatrix {N : ℕ} (v : Coefficients N) :
    Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ := fun i j =>
  if j.val = i.val + 1 then v.a i.val
  else if j = i then v.b i.val
  else if i.val = j.val + 1 then v.c i.val else 0

noncomputable def productMatrix {N : ℕ} (v : Coefficients N) (m : ℕ) :
    Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ := (matrixPair v m).2

def MatrixPositivity {N : ℕ} (v : Coefficients N) : Prop :=
  ∀ m, m ≤ N → ∀ i j, 0 ≤ productMatrix v m i j

noncomputable def perturbationRadius (N : ℕ) (r : ℝ) : ℝ :=
  (1 / 2 : ℝ) * (min r (1-r) / (32 * N)) ^ N

```
### lean/Szkraw/Krawtchouk.lean
```lean
noncomputable def krawCoefficients (N : ℕ) (r : ℝ) : Coefficients N where
  a i := ((N : ℝ)-i)/N
  b i := (1-r)*i/N
  c i := r*i/N

```
### lean/Szkraw/Parameters.lean
```lean
noncomputable def geometricCoefficients (N : ℕ) (p q : ℝ) : Coefficients N where
  a i := q^i*qInteger q (N-i)/qInteger q N
  b i := (p-1)*qInteger q i/(p*qInteger q N)
  c i := qInteger q i/(p*qInteger q N)

```
### lean/Szkraw/BinomialMeasure.lean
```lean
noncomputable def binomialMass (p : ℝ) (N j : ℕ) : ℝ :=
  (N.choose j : ℝ)*(1/(p+1))^(N-j)*(p/(p+1))^j

noncomputable def binomialNode (p : ℝ) (N j : ℕ) : ℝ := 1-(p+1)*(j : ℝ)/(p*N)

```
### lean/Szkraw/Thinness.lean
```lean
/-- The stochastic array with coordinates `b_1, …, b_{N-1}, c_1, …, c_N`. -/
def stochArray (N : ℕ) (b c : ℕ → ℝ) : Coefficients N where
  a i := if i = 0 then 1 else if i = N then 0 else 1 - b i - c i
  b i := if i = 0 then 0 else if i = N then 1 - c N else b i
  c i := if i = 0 then 0 else c i

/-- `K_{N,r} + ε v` for the direction `v = (δb, δc)` in the coordinates of `stochArray`. -/
noncomputable def krawDir (N : ℕ) (δb δc : ℕ → ℝ) (r ε : ℝ) : Coefficients N :=
  stochArray N (fun n => (1 - r) * n / N + ε * δb n) (fun n => r * n / N + ε * δc n)

/-- **Proposition 9.10** (Thinness near the symmetric endpoint): if the first-order change of
`g(N,N;N)` along `v` at `K_{N,1}` is negative, there are `r_* < 1` and `C, c > 0` such that
`K_{N,r} + ε v` is an admissible array lacking property (P), with `g(N,N;N) < 0`, whenever
`r_* < r < 1` and `C (1 - r)^N ≤ ε ≤ c`. -/
theorem thinness (hN : 2 ≤ N)
    (hneg : deriv (fun ε => productMatrix (krawDir N δb δc 1 ε) N (Fin.last N) (Fin.last N)) 0 < 0) :
    ∃ rstar < 1, ∃ C > 0, ∃ c > 0, ∀ r ε : ℝ, rstar < r → r < 1 → C * (1 - r) ^ N ≤ ε → ε ≤ c →
      Admissible (krawDir N δb δc r ε) ∧ ¬ MatrixPositivity (krawDir N δb δc r ε) ∧
        productMatrix (krawDir N δb δc r ε) N (Fin.last N) (Fin.last N) < 0 := …

```
### lean/Szkraw/CornerIdentity.lean
```lean
/-- The direction `v = (δb, δc)` as a coefficient array: `δa = -(δb + δc)` inside, with
`δa_0 = δb_0 = δc_0 = 0`, `δa_N = 0` and `δb_N = -δc_N`. -/
def stochDir (N : ℕ) (δb δc : ℕ → ℝ) : Coefficients N where
  a i := if i = 0 then 0 else if i = N then 0 else -(δb i) - δc i
  b i := if i = 0 then 0 else if i = N then -(δc N) else δb i
  c i := if i = 0 then 0 else δc i

/-- `s_N = (-1)^{⌊N/2⌋+1} / C(N-1, ⌊(N-1)/2⌋)`. -/
noncomputable def sN (N : ℕ) : ℝ := (-1) ^ (N / 2 + 1) / ((N - 1).choose ((N - 1) / 2) : ℝ)

/-- `F = δb + 2 δc` for even `N` and `F = δb` for odd `N`, with `δb_0 = δc_0 = 0`, `δb_N = -δc_N`. -/
noncomputable def cornerF (N : ℕ) (δb δc : ℕ → ℝ) (n : ℕ) : ℝ :=
  if N % 2 = 0 then (stochDir N δb δc).b n + 2 * (stochDir N δb δc).c n else (stochDir N δb δc).b n

/-- **Lemma 9.2** (Corner identity): for `N ≥ 2` the first-order change of `g(N,N;N)` at `K_{N,1}`
along `v = (δb, δc)` is `s_N Σ_{n=0}^N (-1)^n C(N,n) F(n)`. -/
theorem corner_identity (hN : 2 ≤ N) :
    HasDerivAt (fun ε => productMatrix (krawDir N δb δc 1 ε) N (Fin.last N) (Fin.last N))
      (sN N * ∑ n ∈ range (N + 1), (-1) ^ n * (N.choose n : ℝ) * cornerF N δb δc n) 0 := …

```
### lean/Szkraw/UniformRules.lean
```lean
/-- `K_{N,1} + ε v_N` for the uniform rule `(β, γ)`. -/
noncomputable def ruleArray (β γ : ℝ → ℝ) (N : ℕ) (ε : ℝ) : Coefficients N :=
  krawDir N (fun n => β (n / N)) (fun n => γ (n / N)) 1 ε

/-- **Definition 9.3**: a family of sets of arrays admits the rule `(β, γ)` at the symmetric
endpoint if for all large `N` there is `ε_N > 0` with `K_{N,1} + ε v_N` in the set for
`0 < ε < ε_N`. -/
def AdmitsRule (S : (N : ℕ) → Set (Coefficients N)) (β γ : ℝ → ℝ) : Prop :=
  ∃ N₀, ∀ N, N₀ ≤ N → ∃ εN > 0, ∀ ε, 0 < ε → ε < εN → ruleArray β γ N ε ∈ S N

/-- `L_even = β(0) + 2γ(0) + β(1) + γ(1)`. -/
def Leven (β γ : ℝ → ℝ) : ℝ := β 0 + 2 * γ 0 + β 1 + γ 1

/-- `L_odd = β(0) - β(1) - γ(1)`. -/
def Lodd (β γ : ℝ → ℝ) : ℝ := β 0 - β 1 - γ 1

/-- **Theorem 9.4** (Forced equalities for uniform criteria), first part: if a set of arrays with
property (P) admits a polynomial rule `(β, γ)` at the symmetric endpoint, then
`L_even = L_odd = 0`. -/
theorem forced_equalities (β γ : ℝ[X]) (S : (N : ℕ) → Set (Coefficients N))
    (hS : ∀ N, ∀ v ∈ S N, MatrixPositivity v) (hadm : AdmitsRule S β.eval γ.eval) :
    Leven β.eval γ.eval = 0 ∧ Lodd β.eval γ.eval = 0 := …

/-- **Theorem 9.4**, second part: if `L_even = L_odd = 0`, the first-order change of `g(N,N;N)`
along `v_N` vanishes for every `N` above the degrees of `β` and `γ`. -/
theorem forced_vanishing (β γ : ℝ[X]) (hL : Leven β.eval γ.eval = 0 ∧ Lodd β.eval γ.eval = 0)
    {N : ℕ} (hβ : β.natDegree < N) (hγ : γ.natDegree < N) :
    HasDerivAt (fun ε => productMatrix (ruleArray β.eval γ.eval N ε) N (Fin.last N) (Fin.last N)) 0 0 := …

```
### lean/Szkraw/Families.lean
```lean
/-- The alternating sum `A_N` of Lemma 9.2 for the direction `v_N = (vb N, vc N)`. -/
noncomputable def altSum (vb vc : ℕ → ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ range (N + 1), (-1 : ℝ) ^ n * (N.choose n : ℝ) * cornerF N (vb N) (vc N) n

/-- A family of sets contains `K_{N,1} + ε v_N` for all large `N` and small `ε > 0`. -/
def ContainsFamily (S : (N : ℕ) → Set (Coefficients N)) (vb vc : ℕ → ℕ → ℝ) : Prop :=
  ∃ N₀, ∀ N, N₀ ≤ N → ∃ εN > 0, ∀ ε, 0 < ε → ε < εN → krawDir N (vb N) (vc N) 1 ε ∈ S N

/-- **Proposition 9.9** (Families depending on `N`), first statement: `s_N A_N ≥ 0` for all
large `N`. -/
theorem families_sign (S : (N : ℕ) → Set (Coefficients N)) (hS : ∀ N, ∀ v ∈ S N, MatrixPositivity v)
    {vb vc : ℕ → ℕ → ℝ} (hfam : ContainsFamily S vb vc) :
    ∃ M, ∀ N, M ≤ N → 0 ≤ sN N * altSum vb vc N := …

/-- **Proposition 9.9 (1)**: if `A_N ≥ 0` eventually along the parity class `p`, then `A_N = 0`
for all large `N` of that class with `s_N < 0`; if `A_N ≤ 0` eventually, then `A_N = 0` for all
large `N` of that class with `s_N > 0`. -/
theorem families_weak_sign (S : (N : ℕ) → Set (Coefficients N)) (hS : ∀ N, ∀ v ∈ S N, MatrixPositivity v)
    {vb vc : ℕ → ℕ → ℝ} (hfam : ContainsFamily S vb vc) (p : ℕ) :
    ((∃ M, ∀ N, M ≤ N → N % 2 = p → 0 ≤ altSum vb vc N) →
      ∃ M, ∀ N, M ≤ N → N % 2 = p → sN N < 0 → altSum vb vc N = 0) ∧
    ((∃ M, ∀ N, M ≤ N → N % 2 = p → altSum vb vc N ≤ 0) →
      ∃ M, ∀ N, M ≤ N → N % 2 = p → 0 < sN N → altSum vb vc N = 0) := …

/-- **Proposition 9.9 (1)**: along either parity class, `A_N` is neither eventually strictly
positive nor eventually strictly negative. -/
theorem families_no_strict_sign (S : (N : ℕ) → Set (Coefficients N))
    (hS : ∀ N, ∀ v ∈ S N, MatrixPositivity v) {vb vc : ℕ → ℕ → ℝ} (hfam : ContainsFamily S vb vc)
    (p : ℕ) (hp : p < 2) :
    ¬(∃ M, ∀ N, M ≤ N → N % 2 = p → 0 < altSum vb vc N) ∧
      ¬(∃ M, ∀ N, M ≤ N → N % 2 = p → altSum vb vc N < 0) := …

```
### lean/Szkraw/RadiusOrder.lean
```lean
/-- `v` is within `ρ` of `K_{N,r}` in the norm (5.2). -/
def WithinKraw {N : ℕ} (v : Coefficients N) (r ρ : ℝ) : Prop :=
  ∀ i, i ≤ N → |v.a i - ((N : ℝ) - i) / N| ≤ ρ ∧ |v.b i - ((1 - r) * i) / N| ≤ ρ ∧ |v.c i - (r * i) / N| ≤ ρ

/-- The radii `ρ ≥ 0` for which every array satisfying (2.1) with `b_i ≥ 0` within `ρ` of
`K_{N,r}` has property (P). -/
def stableRadii (N : ℕ) (r : ℝ) : Set ℝ :=
  {ρ | 0 ≤ ρ ∧ ∀ v : Coefficients N, Admissible v → (∀ i, i ≤ N → 0 ≤ v.b i) → WithinKraw v r ρ →
    MatrixPositivity v}

/-- `ρ_N(r)`, the stability radius of Corollary 9.11. -/
noncomputable def stabilityRadius (N : ℕ) (r : ℝ) : ℝ := sSup (stableRadii N r)

/-- **Corollary 9.11** (Optimal order of the stability radius): for `N ≥ 2`, `ρ_N(r)` is of exact
order `(1 - r)^N` as `r → 1`. -/
theorem radius_order (hN : 2 ≤ N) :
    ∃ c₁ > 0, ∃ c₂ > 0, ∃ r₀ < 1, ∀ r, r₀ < r → r < 1 →
      c₁ * (1 - r) ^ N ≤ stabilityRadius N r ∧ stabilityRadius N r ≤ c₂ * (1 - r) ^ N := …

```
### lean/Szkraw/TopMass.lean
```lean
/-- The values `u_n(t) = R_n(x_t)`. -/
noncomputable def uval (n : ℕ) (t : Fin (N + 1)) : ℝ := (recurrencePolynomial v n).eval (x t)

/-- `‖R_n‖² = Σ_t w_t u_n(t)^2`. -/
noncomputable def nrm (n : ℕ) : ℝ := ∑ t, w t * uval v x n t ^ 2

/-- `π_n = 1/‖R_n‖²`. -/
noncomputable def piw (n : ℕ) : ℝ := (nrm v x w n)⁻¹

/-- `K_n(t) = Σ_{k<n} π_k u_k(t)`. -/
noncomputable def kerT (n : ℕ) (t : Fin (N + 1)) : ℝ := ∑ k ∈ range n, piw v x w k * uval v x k t

/-- `S_n = Σ_{k<n} π_k`. -/
noncomputable def Ssum (n : ℕ) : ℝ := ∑ k ∈ range n, piw v x w k

/-- `A_n = 1 + ε S_n`. -/
noncomputable def Aeps (ε : ℝ) (n : ℕ) : ℝ := 1 + ε * Ssum v x w n

/-- `ũ_n(t) = A_n u_n(t) - ε K_n(t)`. -/
noncomputable def ueps (ε : ℝ) (n : ℕ) (t : Fin (N + 1)) : ℝ :=
  Aeps v x w ε n * uval v x n t - ε * kerT v x w n t

/-- The recurrence coefficients of the changed measure in the coordinate `x`:
`a'_n = a_n A_n / A_{n+1}`, `c'_n = c_n A_{n+1} / A_n`, `b'_n = 1 - a'_n - c'_n`. -/
noncomputable def epsRaw (ε : ℝ) : Coefficients N where
  a n := v.a n * Aeps v x w ε n / Aeps v x w ε (n + 1)
  b n := 1 - v.a n * Aeps v x w ε n / Aeps v x w ε (n + 1) - v.c n * Aeps v x w ε (n + 1) / Aeps v x w ε n
  c n := v.c n * Aeps v x w ε (n + 1) / Aeps v x w ε n

/-- The changed system after the affine normalization `y = (1 + ε) x - ε`. -/
noncomputable def epsNorm (ε : ℝ) : Coefficients N where
  a n := (1 + ε) * (epsRaw v x w ε).a n
  b n := (1 + ε) * (epsRaw v x w ε).b n - ε
  c n := (1 + ε) * (epsRaw v x w ε).c n

```
### lean/Szkraw/RaiseTopMass.lean
```lean
/-- The array of `K_{N,r}` in the parametrization (2.3), `p = 1/r`. -/
noncomputable abbrev kv (N : ℕ) (r : ℝ) : Coefficients N := geometricCoefficients N (1 / r) 1

/-- The nodes `x_n = 1 - (1 + r) n / N`. -/
noncomputable def kx (N : ℕ) (r : ℝ) (j : Fin (N + 1)) : ℝ := binomialNode (1 / r) N j.val

/-- The masses `w_n = C(N,n) r^{N-n} / (1+r)^N`. -/
noncomputable def kw (N : ℕ) (r : ℝ) (j : Fin (N + 1)) : ℝ := binomialMass (1 / r) N j.val

/-- The normalized array of `K_{N,r}` with the top mass raised to `(1 + τ) w_0`. -/
noncomputable def raisedKraw (N : ℕ) (r τ : ℝ) : Coefficients N :=
  epsNorm (kv N r) (kx N r) (kw N r) (τ * kw N r 0)

/-- **Proposition 9.12**, the raised measure: the raised array satisfies (2.1), and its
polynomials are orthogonal for the measure with masses `w_t + τ w_0 [t = 0]` at the nodes
`y_t = (1 + ε) x_t - ε` (`ε = τ w_0`), with value `1` at the top node `y_0 = 1`. -/
theorem raise_measure (hN : 1 ≤ N) (hr : 0 < r) (hr1 : r < 1) {τ : ℝ} (hτ : 0 < τ) :
    Admissible (raisedKraw N r τ) ∧
      (∀ n, n ≤ N → (recurrencePolynomial (raisedKraw N r τ) n).eval
        ((1 + τ * kw N r 0) * kx N r 0 - τ * kw N r 0) = 1) ∧
      ∀ m n, m ≤ N → n ≤ N → m ≠ n →
        ∑ t, (kw N r t + if t = 0 then τ * kw N r 0 else 0) *
          (recurrencePolynomial (raisedKraw N r τ) m).eval ((1 + τ * kw N r 0) * kx N r t - τ * kw N r 0) *
          (recurrencePolynomial (raisedKraw N r τ) n).eval ((1 + τ * kw N r 0) * kx N r t - τ * kw N r 0) = 0 := …

/-- **Proposition 9.12**, corner formula: the raised measure has
`g(N,N;N) = ((1+τ)^2 (I - w_0) + w_0) / ((1+τ)(h - w_0) + w_0)`, `I = (r(1-r))^N`, `h = r^N`,
`w_0 = (r/(1+r))^N`. -/
theorem raise_corner (hN : 1 ≤ N) (hr : 0 < r) (hr1 : r < 1) {τ : ℝ} (hτ : 0 < τ) :
    productMatrix (raisedKraw N r τ) N (Fin.last N) (Fin.last N) =
      ((1 + τ) ^ 2 * ((r * (1 - r)) ^ N - (r / (1 + r)) ^ N) + (r / (1 + r)) ^ N) /
        ((1 + τ) * (r ^ N - (r / (1 + r)) ^ N) + (r / (1 + r)) ^ N) := …

/-- **Proposition 9.12**, sign: the corner coefficient of the raised measure is negative exactly
when `τ > τ_N^* = (1 - (1 - r^2)^N)^{-1/2} - 1`. -/
theorem raise_sign (hN : 1 ≤ N) (hr : 0 < r) (hr1 : r < 1) {τ : ℝ} (hτ : 0 < τ) :
    productMatrix (raisedKraw N r τ) N (Fin.last N) (Fin.last N) < 0 ↔
      (Real.sqrt (1 - (1 - r ^ 2) ^ N))⁻¹ - 1 < τ := …

/-- **Proposition 9.12**, coefficients: after the affine normalization the coefficients of the
raised measure differ from those of `K_{N,r}` by at most `3 τ max_n w_n`. -/
theorem raise_bound (hN : 1 ≤ N) (hr : 0 < r) (hr1 : r < 1) {τ : ℝ} (hτ : 0 < τ) (n : ℕ) (hn : n ≤ N) :
    |(raisedKraw N r τ).a n - (krawCoefficients N r).a n| ≤ 3 * τ * univ.sup' univ_nonempty (kw N r) ∧
      |(raisedKraw N r τ).b n - (krawCoefficients N r).b n| ≤ 3 * τ * univ.sup' univ_nonempty (kw N r) ∧
        |(raisedKraw N r τ).c n - (krawCoefficients N r).c n| ≤ 3 * τ * univ.sup' univ_nonempty (kw N r) := …

```
### lean/Szkraw/RadiusExp.lean
```lean
/-- `τ_N^* = (1 - (1 - r^2)^N)^{-1/2} - 1`. -/
noncomputable def tauStar (N : ℕ) (r : ℝ) : ℝ := (Real.sqrt (1 - (1 - r ^ 2) ^ N))⁻¹ - 1

/-- **Corollary 9.13** (Exponentially small stability radius). -/
theorem radius_exp (hN : 1 ≤ N) (hr : 0 < r) (hr1 : r < 1) (hx : (1 - r ^ 2) ^ N ≤ 1 / 2)
    (hx2 : 3 * (1 - r ^ 2) ^ N ≤ (1 - r) / N) :
    stabilityRadius N r ≤ 3 * tauStar N r * univ.sup' univ_nonempty (kw N r) ∧
      3 * tauStar N r * univ.sup' univ_nonempty (kw N r) ≤ 3 * (1 - r ^ 2) ^ N := …

/-- **Corollary 9.13**, asymptotics: for fixed `0 < r < 1`, `ρ_N(r) ≤ 3 (1 - r^2)^N` for all large `N`. -/
theorem radius_exp_asymp (hr : 0 < r) (hr1 : r < 1) :
    ∃ N₀, ∀ N, N₀ ≤ N → stabilityRadius N r ≤ 3 * (1 - r ^ 2) ^ N := …

```
### lean/Szkraw/LowerTopMass.lean
```lean
/-- The point `1` is a node of the spectral measure of every admissible array. -/
theorem spectral_top_node (v : Coefficients N) (hv : Admissible v) : ∃ t₀, spectralNode v hv t₀ = 1 := …

/-- The tail `T_x(y, z) = Σ_{l ≥ x} g(y, z; l)`. -/
noncomputable def tailG (v : Coefficients N) (x y z : Fin (N + 1)) : ℝ :=
  ∑ l : Fin (N + 1), if x.val ≤ l.val then productMatrix v y z l else 0

/-- **Lemma 9.7**, the lowered measure: for `0 ≤ ε < μ({x₀})` the polynomials of the coefficients
`epsRaw v x w (-ε)` are orthogonal for `μ - ε δ_{x₀}` and equal `1` at `x₀ = 1`. -/
theorem lower_measure {t₀ : Fin (N + 1)} (hx0 : spectralNode v hv t₀ = 1) {ε : ℝ} (hε0 : 0 ≤ ε)
    (hε : ε < spectralWeight v hv t₀) :
    (∀ t, 0 < spectralWeight v hv t - if t = t₀ then ε else 0) ∧
      (∀ n, n ≤ N →
        (recurrencePolynomial (epsRaw v (spectralNode v hv) (spectralWeight v hv) (-ε)) n).eval 1 = 1) ∧
      ∀ m n, m ≤ N → n ≤ N → m ≠ n →
        ∑ t, (spectralWeight v hv t - if t = t₀ then ε else 0) *
          (recurrencePolynomial (epsRaw v (spectralNode v hv) (spectralWeight v hv) (-ε)) m).eval
            (spectralNode v hv t) *
          (recurrencePolynomial (epsRaw v (spectralNode v hv) (spectralWeight v hv) (-ε)) n).eval
            (spectralNode v hv t) = 0 := …

/-- **Lemma 9.7 (1)**: lowering the top mass changes the recurrence coefficients, in the fixed
coordinate `x`, at the rates `(ȧ_n, ḃ_n, ċ_n) = π_n (a_n, c_n - a_n, -c_n)`. -/
theorem lower_rates (n : ℕ) :
    let x := spectralNode v hv; let w := spectralWeight v hv
    HasDerivAt (fun ε => (epsRaw v x w (-ε)).a n) (piw v x w n * v.a n) 0 ∧
      HasDerivAt (fun ε => (epsRaw v x w (-ε)).b n) (piw v x w n * (v.c n - v.a n)) 0 ∧
        HasDerivAt (fun ε => (epsRaw v x w (-ε)).c n) (-(piw v x w n * v.c n)) 0 := …

/-- **Lemma 9.7 (2)**: if `∫ R_x R_y R_z dμ = 0`, then lowering the top mass changes
`∫ R^ε_x R^ε_y R^ε_z dμ_ε` at the rate `2 - T_x(y,z) - T_y(x,z) - T_z(x,y)`,
`T_x(y,z) = Σ_{k ≥ x} g(y,z;k)`. -/
theorem lower_triple {t₀ : Fin (N + 1)} (hx0 : spectralNode v hv t₀ = 1) (i j k : Fin (N + 1))
    (h0 : ∑ t, spectralWeight v hv t * uval v (spectralNode v hv) i t * uval v (spectralNode v hv) j t *
      uval v (spectralNode v hv) k t = 0) :
    HasDerivAt (fun ε => ∑ t, (spectralWeight v hv t - if t = t₀ then ε else 0) *
        (recurrencePolynomial (epsRaw v (spectralNode v hv) (spectralWeight v hv) (-ε)) i).eval (spectralNode v hv t) *
        (recurrencePolynomial (epsRaw v (spectralNode v hv) (spectralWeight v hv) (-ε)) j).eval (spectralNode v hv t) *
        (recurrencePolynomial (epsRaw v (spectralNode v hv) (spectralWeight v hv) (-ε)) k).eval (spectralNode v hv t))
      (2 - tailG v i j k - tailG v j i k - tailG v k i j) 0 := …

```