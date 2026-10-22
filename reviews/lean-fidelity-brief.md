# Independent review: do the Lean statements say what the paper says?

You are an independent reviewer for a mathematics paper on nonnegative linearization of finite orthogonal polynomial systems. Its Lean 4 development (Mathlib) claims machine-verified proofs of several results. Lean has checked every proof, and the axiom audit shows only propext, Classical.choice and Quot.sound. **Your task is not to check proofs.** Check whether each Lean *statement* faithfully expresses the corresponding *paper statement*, and whether the paper's "Code and formalization" section and AI-use disclosure describe the formalized scope accurately.

For each paper result listed in the table of the code-and-formalization section:
- In particular for Theorems 7.1, 7.8, 7.10, 7.12, 7.15, 7.16, 8.1, Corollaries 7.9, 7.11, 7.13, 7.17 and Lemma 7.14, compare hypotheses and conclusion.
- A Lean statement is acceptable if its hypotheses are equivalent to or weaker than the paper's, and its conclusion is equivalent to or stronger than the paper's. Both comparisons are under the stated conventions.
- Report every place where the Lean hypotheses are stronger than the paper's, or the conclusion weaker, or where an index range, normalization or convention differs in a way that matters.
- Report also any part of a paper statement the Lean development does not cover where the paper does not say so.

Conventions you may rely on:
- `Coefficients N` holds functions a, b, c : ℕ → ℝ; only the indices 0..N matter.
- `Admissible v` is the paper's (2.1) ("eq:basic").
- `productMatrix v m = p_m(J)` is the paper's R_m(J), computed by the recurrence in matrix form. Its entry (n,k) is g(m,n;k) (Lemma 5.1, eq. (5.1)).
- `MatrixPositivity v` is nonnegative linearization: all g(m,n;k) ≥ 0 for m, n, k ≤ N.
- `FiniteRealization v` packages the positive measure on N+1 points, the terminal relation, the product identities on the support, and Σ_k g(m,n;k) = 1.
- Section variables: in `Reversal.lean`, theorems such as `reversal_identity`, `deep_formula` and `top_expansion` take `(v : Coefficients N) (hv : Admissible v)` as section variables. In `QuadDecomp.lean`, `v : Coefficients (2 * N)` is a section variable.
- `Gk v k m n` is g(m,n;k) for m, n ≤ N, extended by 0.

Answer format:
1. A table: paper result | Lean declaration(s) | verdict (MATCH / MATCH, SCOPE NOTED / MISMATCH) | reason.
2. For each MISMATCH or undisclosed gap: the exact fix, either to the Lean statement or to the paper's scope text.
3. A check of the scope sentences in the code-and-formalization section and the AI-use disclosure.
4. Overall verdict: PASS / PASS WITH MINOR FIXES / FAIL.

Be specific and terse.

## Part A. Paper statements

#### Conventions (Section 2)
```latex
\section{Statement and conventions}\label{sec:criterion}
For integers $j\geq0$ put $[j]_q=1+q+\cdots+q^{j-1}$, with $[0]_q=0$; in particular $[j]_1=j$.
Consider real coefficients indexed by $0\leq i\leq N$, where $N\geq1$, satisfying
\begin{equation}\label{eq:basic}
\begin{gathered}
a_0=1,\quad b_0=c_0=0,\quad a_N=0,\quad a_i+b_i+c_i=1,\\
a_i>0\ (i<N),\qquad c_i>0\ (i>0).
\end{gathered}
\end{equation}
Set $R_{-1}=0$, $R_0=1$, and determine $R_1,\ldots,R_N$ by
\begin{equation}\label{eq:recurrence}
xR_i=a_iR_{i+1}+b_iR_i+c_iR_{i-1}\qquad(0\leq i<N).
\end{equation}
At $i=0$, \eqref{eq:recurrence} gives $R_1=x$; induction at $x=1$, using the row sums and $a_i>0$ for $i<N$, gives $R_i(1)=1$ for $0\leq i\leq N$.
The terminal relation is $(x-b_N)R_N-c_NR_{N-1}=0$ on the orthogonality support. Linearization means equality of functions on this support, rather than an unrestricted polynomial identity when the degree sum exceeds $N$.
```

#### Lemma 2.2 (parametrization) and Theorem 2.1
```latex
\begin{theorem}[Geometric increment criterion]\label{thm:criterion}
Assume \eqref{eq:basic}. Set $d_i=b_i+c_i$. Suppose
\begin{enumerate}
\item $b_i/c_i=\beta$ for every $1\leq i\leq N$, where $\beta\geq0$;
\item $\delta_i=d_i-d_{i-1}>0$ for $1\leq i\leq N$;
\item for some $q\geq1$, $\delta_{i+1}=q\delta_i$ whenever $1\leq i<N$.
\end{enumerate}
Then the recurrence has a positive orthogonality measure on exactly $N+1$ distinct real points. Its normalized polynomials satisfy
\begin{equation}\label{eq:positive}
R_mR_n=\sum_{k=0}^N g(m,n;k)R_k,
\qquad g(m,n;k)\geq0,\qquad\sum_{k=0}^N g(m,n;k)=1
\end{equation}
on that support for all $0\leq m,n\leq N$.
\end{theorem}

\begin{lemma}[Coefficient parametrization]\label{lem:parameters}
The hypotheses of Theorem~\ref{thm:criterion} are equivalent to
\begin{equation}\label{eq:parameters}
a_i=\frac{q^i[N-i]_q}{[N]_q},\qquad
b_i=(1-r)\frac{[i]_q}{[N]_q},\qquad
c_i=r\frac{[i]_q}{[N]_q}
\end{equation}
for $q\geq1$, $0<r\leq1$. When $N=1$, one may choose $q=1$.
\end{lemma}
```

#### Lemma 5.1 (finite realization; the matrix convention g(m,n;k) = [R_m(J)]_{n,k})
```latex
\begin{lemma}[Finite recurrence realization and triangle support]\label{lem:finite}
Every recurrence satisfying \eqref{eq:basic} has a positive orthogonality measure on exactly $N+1$ real points. If $J$ is its tridiagonal recurrence matrix, then its finite product coefficients satisfy
\begin{equation}\label{eq:matrix-product}
g(m,n;k)=[R_m(J)]_{n,k}.
\end{equation}
They vanish unless $|m-n|\leq k\leq\min(m+n,N)$, regardless of their signs inside this interval.
\end{lemma}
```

#### Section 7 setup and Theorem 7.1
```latex
Problem~2 of~\cite[\S5]{szwarc} does not stop at the Krawtchouk recurrence. With his parameter written as $p_0$, Szwarc introduces the symmetric recurrence of length $2N+1$
Put $M=2N$, $R_{2n}(t)=Q_{2n}(\sqrt Nt)$ and $R_{2n-1}(t)=\sqrt N\,Q_{2n-1}(\sqrt Nt)$. Substitution in \eqref{eq:szwarc-q} shows that the $R_k$ satisfy \eqref{eq:recurrence}, with $N$ replaced by $M$, for the array
\begin{equation}\label{eq:qarray}
b_k=0,\qquad
(a_{2n},c_{2n})=\Big(\frac{N-n}{N},\frac nN\Big),\qquad
(a_{2n-1},c_{2n-1})=(1-p_0,\,p_0).
\end{equation}
It satisfies \eqref{eq:basic} with $M$ in place of $N$ whenever $0<p_0<1$. The two normalizations differ by positive factors and a positive dilation, so they have the same product coefficients up to positive factors.

\begin{theorem}[Szwarc's quadratic system]\label{thm:szwarc}
Let $N\geq1$ and $0<p_0\leq1/2$. The array \eqref{eq:qarray} has a symmetric positive orthogonality measure on $2N+1$ points, and for all $0\leq m,n\leq 2N$
\[
R_mR_n=\sum_{k=0}^{2N}g(m,n;k)R_k,\qquad g(m,n;k)\geq0,\qquad\sum_k g(m,n;k)=1
\]
on that support. If $1/2<p_0<1$, then $g(2,2;2)<0$.
\end{theorem}
```

#### thm:decomp
```latex
\begin{theorem}[Quadratic decomposition]\label{thm:decomp}
Let $N\geq2$, and let $a_k,c_k$ $(0\leq k\leq2N)$ with $b\equiv0$ satisfy \eqref{eq:basic} with $2N$ in place of $N$. Put $a_k=c_k=0$ for $k\notin[0,2N]$, and define the even component
\[
\hat a_n=a_{2n}a_{2n+1},\quad \hat b_n=c_{2n}a_{2n-1}+a_{2n}c_{2n+1},\quad \hat c_n=c_{2n}c_{2n-1}\qquad(0\leq n\leq N)
\]
and the odd component
\[
\check a_n=a_{2n+1}a_{2n+2},\quad \check b_n=a_{2n+1}c_{2n+2}+c_{2n+1}a_{2n},\quad \check c_n=c_{2n+1}c_{2n}\qquad(0\leq n<N).
\]
After the affine normalization $(\hat a_n,\hat b_n,\hat c_n)\mapsto(\hat a_n,\hat b_n-\hat b_0,\hat c_n)/\hat a_0$, and likewise for the odd component, these arrays satisfy \eqref{eq:basic} on the indices $0,\ldots,N$ and $0,\ldots,N-1$. If both have nonnegative linearization, so does the symmetric array. More precisely, with $\hat g$ and $\check g$ the product coefficients of the components and terms with indices out of range omitted,
\[
g(2a,2b;2c)=\hat g(a,b;c),\qquad
g(2a,2b+1;2c+1)=a_{2a}\,\check g(a,b;c)+c_{2a}\,\check g(a-1,b;c),
\]
the coefficients with $m+n+k$ odd vanish, and $g(2a+1,2b+1;2c)\int R_{2c}^2\,d\mu=g(2c,2a+1;2b+1)\int R_{2b+1}^2\,d\mu$. Conversely, nonnegative linearization of the symmetric array implies that of its even component.
\end{theorem}
```

#### cor:parity
```latex
\begin{corollary}[Parity-split criterion]\label{cor:parity}
Let $N\geq1$ and let a symmetric array $(b\equiv0)$ on the indices $0,\ldots,2N$ satisfy \eqref{eq:basic}. Suppose that
\begin{enumerate}
\item the odd downward coefficients are constant, $c_{2n+1}=p_0$, with $0<p_0\leq1/2$;
\item the even downward coefficients $d_n=c_{2n}$ have positive increments $d_n-d_{n-1}$, $1\leq n\leq N$, forming a geometric progression with ratio $q\geq1$.
\end{enumerate}
Then the array has nonnegative linearization. With $r=p_0/(1-p_0)$ and $N\geq2$, its normalized even and odd components are \eqref{eq:parameters} with parameters $(N,q,r)$ and $(N-1,q,r/q)$, respectively. For $N=1$ the odd component consists only of $L_0=1$, the array is \eqref{eq:qarray}, and positivity follows directly from Theorem~\ref{thm:szwarc}. If $1/2<p_0<1$ in (i) and (ii) holds, then $g(2,2;2)<0$.
\end{corollary}
```

#### Renormalization used by Theorems 7.10 and 7.12
```latex
Szwarc's inequality method~\cite[Theorems~3.2 and~3.4]{szwarc} survives the passage to finite systems for all products whose two factors have total degree at most $N$. Only the terminal coefficients are excluded from its hypotheses. Write a finite system in a positive renormalization $P_n=R_n/\sigma_n$ $(\sigma_0=1)$ as $xP_n=\gamma_nP_{n+1}+\beta_nP_n+\alpha_nP_{n-1}$, so that $\gamma_n=a_n\sigma_{n+1}/\sigma_n$, $\beta_n=b_n$, $\alpha_n=c_n\sigma_{n-1}/\sigma_n$ and $\gamma_N=0$.
```

#### thm:low
```latex
\begin{theorem}[Low products]\label{thm:low}
Let $a,b,c$ satisfy \eqref{eq:basic}. Suppose that for some positive $\sigma$,
\begin{enumerate}
\item $\beta_n$ is nondecreasing for $0\leq n\leq N-1$, and $\alpha_n$ is nondecreasing for $0\leq n\leq N$;
\item $\alpha_n+\gamma_n$ is nondecreasing for $0\leq n\leq N-2$;
\item $\gamma_i\geq\alpha_j$ whenever $0\leq j\leq i$ and $i+j\leq N-2$.
\end{enumerate}
Then $g(n,m;k)\geq0$ whenever $n+m\leq N$. Consequently a product coefficient can be negative only for a triple $(n,m,k)$ in which each two indices have sum greater than $N$.
\end{theorem}
```

#### cor:convex-low
```latex
\begin{corollary}[Convex profiles]\label{cor:convex-low}
Let $b_i=(1-r)d_i$, $c_i=rd_i$, $a_i=1-d_i$ with $0<r\leq1$ and a convex profile $0=d_0<d_1<\cdots<d_N=1$, that is, with nondecreasing increments. Then $g(n,m;k)\geq0$ whenever two of $n,m,k$ have sum at most $N$. This includes every array \eqref{eq:parameters}.
\end{corollary}
```

#### thm:all
```latex
\begin{theorem}[All products]\label{thm:all}
Let $a,b,c$ satisfy \eqref{eq:basic}, and put $\gamma_N=0$. Suppose that for some positive $\sigma$,
\begin{enumerate}
\item $\beta_n$ and $\alpha_n$ are nondecreasing for $0\leq n\leq N$;
\item $\alpha_n+\gamma_n$ is nondecreasing for $0\leq n\leq N$;
\item $\gamma_i\geq\alpha_j$ whenever $0\leq j\leq i\leq N-1$.
\end{enumerate}
Then the system has nonnegative linearization.
\end{theorem}
```

#### cor:heavy
```latex
\begin{corollary}[Heavy top step]\label{cor:heavy}
Let $b_i=(1-r)d_i$, $c_i=rd_i$, $a_i=1-d_i$ with $0<r\leq1$ and an increasing profile $0=d_0<d_1<\cdots<d_N=1$ with $d_{N-1}\leq\tfrac12$. Then the system has nonnegative linearization.
\end{corollary}
```

#### Reversed array (before Lemma 7.14)
```latex
Call $(n,m,k)$ deep if each two of its indices have sum greater than $N$. The reversed array $a'_i=c_{N-i}$, $b'_i=b_{N-i}$, $c'_i=a_{N-i}$ need not satisfy $a'_0=1$, $b'_0=0$. Its polynomials $R'_i$ are defined by the reversed recurrence from $R'_0=1$, so $R'_1=(x-b_N)/c_N$, and they still satisfy $R'_i(1)=1$; its matrix is $\Pi J\Pi$, where $\Pi$ reverses the order of the indices. Write $g'$ for its product coefficients.
```

#### lem:reversal
```latex
\begin{lemma}[Reversal identity]\label{lem:reversal}
On the support, $R_NR'_t=R_{N-t}$ for $0\leq t\leq N$.
\end{lemma}
```

#### thm:deep
```latex
\begin{theorem}[Deep reduction]\label{thm:deep}
For every array satisfying \eqref{eq:basic} and every deep triple $(x,y,z)$,
\[
g(x,y;z)=\sum_{t=0}^Ng'(N-x,N-y;t)\,g(N,N-t;z).
\]
Moreover $g(N,N;N-l)$ is the coefficient of $R'_l$ in $R_N$. Hence all coefficients are nonnegative if (a) $g\geq0$ on non-deep triples, (b) $g'(i,j;t)\geq0$ whenever $i+j<N$, and (c) $R_N$ is a nonnegative combination of $R'_0,\ldots,R'_N$.
\end{theorem}
```

#### thm:palindromic
```latex
\begin{theorem}[Palindromic criterion]\label{thm:palindromic}
Let $a,b,c$ satisfy \eqref{eq:basic} with $a_n=c_{N-n}$ and $b_n=b_{N-n}$ for all $n$, and satisfy the hypotheses of Theorem~\ref{thm:low} for some positive $\sigma$. Then the system has nonnegative linearization.
\end{theorem}
```

#### cor:palin
```latex
\begin{corollary}[Monotone palindromic systems]\label{cor:palin}
Let $b\equiv0$, $a_n=1-c_n$, and let $0=c_0<c_1\leq c_2\leq\cdots\leq c_N=1$ satisfy $c_n+c_{N-n}=1$. Then the system has nonnegative linearization. This includes the symmetric Krawtchouk array $c_n=n/N$.
\end{corollary}
```

#### Section 8, Theorem 8.1
```latex
\begin{theorem}[Log-concave Newton criterion]\label{thm:lc}
Let $0=d_0<d_1<\cdots<d_N=1$ have Newton coefficients that are log-concave without internal zeros, let $0<r\leq1$, and put $a_i=1-d_i$, $b_i=(1-r)d_i$, $c_i=rd_i$. Then the system has nonnegative linearization.
\end{theorem}
```

#### Remark after the proof of Theorem 8.1 (declared NOT formalized)
```latex
The argument is valid coefficientwise in $t$. With independent parameters in $yp_i=a_ip_{i+1}+ud_ip_i+vd_ip_{i-1}$, weighted homogeneity ($\deg y=\deg u=1$, $\deg v=2$) then shows that each linearization coefficient is a polynomial in $(u,v)$ with nonnegative coefficients: for $D=m+n-k\geq0$ it has the form $\sum_{0\leq j\leq\lfloor D/2\rfloor}h_ju^{D-2j}v^j$ with $h_j\geq0$, and it vanishes for $D<0$. Consequently every $g(m,n;k)$ of the array of Theorem~\ref{thm:lc}, as a function of $r$, equals $\sum_jh_jr^j(1-r)^{D-2j}$; multiplying the $j$-th term by $(r+(1-r))^j=1$ shows that its coefficients in the Bernstein basis of degree $D$ are $\binom Ds^{-1}\sum_{j\leq s\leq2j}h_j\binom j{s-j}\geq0$. The diagnostics \path{lc_kernel_check.py} verify Lemmas~\ref{lem:kernel-rec}--\ref{lem:detours} and the matching $\mathcal P^2\geq4\mathcal Q$ in exact arithmetic on random log-concave profiles.
```

#### The paper's code-and-formalization section (the claims under review)
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
Theorem~\ref{thm:szwarc}: Szwarc's quadratic system & \path{Szkraw.szwarc_system}, \path{Szkraw.szwarc_sharp}\\[3pt]
Theorem~\ref{thm:decomp}: quadratic decomposition & \path{Szkraw.decomp_positivity}, \path{Szkraw.decomp_converse}, \path{Szkraw.even_block}, \path{Szkraw.odd_block}, \path{Szkraw.evenComp_admissible}, \path{Szkraw.oddComp_admissible}\\[3pt]
Corollary~\ref{cor:parity}: parity-split criterion & \path{Szkraw.parity_split}, \path{Szkraw.parity_split_sharp}\\[3pt]
Theorem~\ref{thm:low}: low products & \path{Szkraw.low_products}\\[3pt]
Corollary~\ref{cor:convex-low}: convex profiles & \path{Szkraw.convex_low}, \path{Szkraw.geometric_convex}\\[3pt]
Theorem~\ref{thm:all}: all products & \path{Szkraw.all_products}\\[3pt]
Corollary~\ref{cor:heavy}: heavy top step & \path{Szkraw.heavy_top}\\[3pt]
Lemma~\ref{lem:reversal}: reversal identity & \path{Szkraw.reversal_identity}\\[3pt]
Theorem~\ref{thm:deep}: deep reduction & \path{Szkraw.deep_formula}, \path{Szkraw.top_expansion}, \path{Szkraw.deep_reduction}\\[3pt]
Theorem~\ref{thm:palindromic}: palindromic criterion & \path{Szkraw.palindromic}\\[3pt]
Corollary~\ref{cor:palin}: monotone palindromic systems & \path{Szkraw.palin_mono}, \path{Szkraw.palin_mono_kraw}\\[3pt]
Theorem~\ref{thm:lc}: log-concave Newton criterion & \path{Szkraw.logconcave_criterion}
\end{tabular}
\end{center}
The first includes a positive finite orthogonality measure, distinct support points, the terminal relation, and all finite product identities. The second includes the explicit radius, positive triangle margin, and exact zeros outside the triangle. The entries for Section~\ref{sec:szwarc} state nonnegativity of the coefficients $g(m,n;k)$: for Theorem~\ref{thm:low} and Corollary~\ref{cor:convex-low} on all triples with two indices of sum at most $N$, and for Theorems~\ref{thm:all}, \ref{thm:deep} and~\ref{thm:palindromic} and Corollaries~\ref{cor:heavy} and~\ref{cor:palin} on all triples. Lemma~\ref{lem:reversal} and the identities of Theorem~\ref{thm:deep} are stated for the matrices $R_m(J)$ and $R'_t(J)=\Pi R'_t(\Pi J\Pi)\Pi$. Theorem~\ref{thm:szwarc} is proved in Lean through Corollary~\ref{cor:parity} with $q=1$; the symmetry of its measure is not formalized. For Corollary~\ref{cor:parity} Lean proves that both normalized components satisfy the hypotheses of Theorem~\ref{thm:criterion}; the identification of their parameters through Lemma~\ref{lem:parameters} is not formalized. In Theorem~\ref{thm:decomp} the identity for $g(2a,2b+1;2c+1)$ is stated with the unnormalized odd component, which has the same product coefficients (\path{Szkraw.product_normalize}). The finite realization holds for every array satisfying \eqref{eq:basic} (\path{Szkraw.finite_realization}). The proofs formalize the cone argument and the identity $g(m,n;k)\int R_k^2\,d\mu=g(m,k;n)\int R_n^2\,d\mu$ in matrix form. The entry for Theorem~\ref{thm:lc} includes the same finite realization as the first and the nonnegativity of every coefficient $g(m,n;k)$; its proof formalizes Lemmas~\ref{lem:lc-ineq} and~\ref{lem:detours}, the operator induction, and Lemma~\ref{lem:kernel-rec} in converse form: the solution of~\eqref{eq:kernel-rec} yields the linearization coefficients. The remark after the proof of Theorem~\ref{thm:lc} (nonnegative coefficients of the two-parameter system and nonnegative Bernstein coefficients in $r$) is not formalized. All of them have compiled proofs without added axioms or admitted goals. The other results of Section~\ref{sec:szwarc} have not yet been formalized; formalizing them is planned.

```

#### AI-use disclosure (the scope sentences)
```latex
\section*{AI-use disclosure}

OpenAI Codex was used to develop the proof arguments, search and check source passages, construct exact-arithmetic diagnostics, draft and revise this manuscript, and prepare the Lean translation. Separate AI-assisted reviews checked the algebraic proof, boundary cases, normalizations, and quantitative estimates; these reviews are not human peer review. Anthropic Claude was used to analyse Szwarc's Problem~2 against the survey text, to explore discrete hyperbolic certificates numerically, and to develop and draft Sections~\ref{sec:szwarc}, \ref{sec:lc} and~\ref{sec:limits} together with their exact diagnostics. The kernel recurrence and the operator inequality of Section~\ref{sec:lc} arose in research consultations with ChatGPT Pro; the closed form of the recurrence for every degree and the exact checks were completed with Claude, which also prepared the Lean formalizations of Theorem~\ref{thm:lc} and of the results of Section~\ref{sec:szwarc} listed in the section on code and formalization. The review of Section~\ref{sec:lc} was therefore carried out by the same system that proposed its key steps. These sections were then reviewed in fourteen rounds by ChatGPT Pro (an AI review with independent exact checks, not human peer review); the first round failed, the corrections are recorded in \path{REVIEW.md}, and for each section the final confirmation round on the corrected text returned PASS. The author set the research objective and retains responsibility for publication decisions and the final mathematical claims. No independent human verification is asserted here. ``Machine-verified'' refers only to the Lean theorems listed in the section on code and formalization, with the axioms stated there. Other results, including Theorem~\ref{thm:symmetric}, Corollary~\ref{cor:symmetric-new} and Lemmas~\ref{lem:edge}--\ref{lem:stability} of Section~\ref{sec:szwarc}, the symmetry of the measure in Theorem~\ref{thm:szwarc}, the parameter identification in Corollary~\ref{cor:parity}, and the remark after the proof of Theorem~\ref{thm:lc}, are supported by written proofs, AI review and exact numerical checks, but are not machine-verified.
```

## Part B. Lean statements (definitions and theorem types; proofs omitted)

### lean/Szkraw/Statements.lean
```lean
structure Coefficients (N : ℕ) where
  a : ℕ → ℝ
  b : ℕ → ℝ
  c : ℕ → ℝ


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


noncomputable def matrixPair {N : ℕ} (v : Coefficients N) :
    ℕ → Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ ×
      Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ
  | 0 => (0, 1)
  | n + 1 => let t := matrixPair v n
      (t.2, (v.a n)⁻¹ •
        ((recurrenceMatrix v - v.b n • (1 : Matrix _ _ ℝ)) * t.2 - v.c n • t.1))


noncomputable def productMatrix {N : ℕ} (v : Coefficients N) (m : ℕ) :
    Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ := (matrixPair v m).2


noncomputable def polynomialPair {N : ℕ} (v : Coefficients N) :
    ℕ → Polynomial ℝ × Polynomial ℝ
  | 0 => (0, 1)
  | n + 1 => let t := polynomialPair v n
      (t.2, Polynomial.C (v.a n)⁻¹ *
        ((Polynomial.X - Polynomial.C (v.b n)) * t.2 - Polynomial.C (v.c n) * t.1))


noncomputable def recurrencePolynomial {N : ℕ} (v : Coefficients N) (m : ℕ) :
    Polynomial ℝ := (polynomialPair v m).2


/-- A positive discrete orthogonality measure on exactly N+1 points together
with the terminal relation and matrix-to-polynomial product identity. -/
def FiniteRealization {N : ℕ} (v : Coefficients N) : Prop :=
  ∃ x w : Fin (N+1) → ℝ, Function.Injective x ∧
    (∀ t, 0 < w t) ∧ (∑ t, w t) = 1 ∧
    (∀ m, m ≤ N → (recurrencePolynomial v m).eval 1 = 1) ∧
    (∀ (m : ℕ) (n : Fin (N+1)), m ≤ N →
      ∑ k : Fin (N+1), productMatrix v m n k = 1) ∧
    (∀ m n, m ≤ N → n ≤ N → m ≠ n →
      ∑ t, w t * (recurrencePolynomial v m).eval (x t) *
        (recurrencePolynomial v n).eval (x t) = 0) ∧
    (∀ m, m ≤ N → 0 < ∑ t, w t * ((recurrencePolynomial v m).eval (x t))^2) ∧
    (∀ t, (x t-v.b N) * (recurrencePolynomial v N).eval (x t) -
      v.c N * (recurrencePolynomial v (N-1)).eval (x t) = 0) ∧
    (∀ (m : ℕ) (n t : Fin (N+1)), m ≤ N →
      (recurrencePolynomial v m).eval (x t) *
        (recurrencePolynomial v n.val).eval (x t) =
      ∑ k : Fin (N+1), productMatrix v m n k *
        (recurrencePolynomial v k.val).eval (x t))


def Geometric {N : ℕ} (v : Coefficients N) : Prop :=
  ∃ β q : ℝ, 0 ≤ β ∧ 1 ≤ q ∧
    (∀ i, 0 < i → i ≤ N → v.b i = β * v.c i) ∧
    (∀ i, 0 < i → i ≤ N → 0 < (v.b i + v.c i) - (v.b (i-1) + v.c (i-1))) ∧
    (∀ i, 0 < i → i < N →
      (v.b (i+1) + v.c (i+1)) - (v.b i + v.c i) =
        q * ((v.b i + v.c i) - (v.b (i-1) + v.c (i-1))))


def MatrixPositivity {N : ℕ} (v : Coefficients N) : Prop :=
  ∀ m, m ≤ N → ∀ i j, 0 ≤ productMatrix v m i j


```
### lean/Szkraw/LogConcaveStatement.lean
```lean
/-- The profile `d i = b i + c i` of an array. -/
def profile {N : ℕ} (v : Coefficients N) (i : ℕ) : ℝ := v.b i + v.c i


/-- Newton coefficients `ν k = Σ_{i ≤ k} (-1)^(k-i) C(k,i) d i`, i.e. `Δ^k d (0)`. -/
noncomputable def newtonCoeff (d : ℕ → ℝ) (k : ℕ) : ℝ :=
  ∑ i ∈ range (k + 1), (-1 : ℝ) ^ (k - i) * (k.choose i : ℝ) * d i


/-- `(ν k)_{1 ≤ k ≤ N}` is nonnegative and log-concave without internal zeros, with `ν 1 > 0`. -/
def LogConcaveNoInternalZeros (N : ℕ) (ν : ℕ → ℝ) : Prop :=
  0 < ν 1 ∧
  (∀ k, 1 ≤ k → k ≤ N → 0 ≤ ν k) ∧
  (∀ k, 2 ≤ k → k + 1 ≤ N → ν (k - 1) * ν (k + 1) ≤ ν k ^ 2) ∧
  (∀ k, 1 ≤ k → k < N → ν k = 0 → ν (k + 1) = 0)


/-- Hypotheses of Theorem 8.1: constant ratio `c i = r d i` with `0 < r ≤ 1`, and a profile
whose Newton coefficients are log-concave without internal zeros. -/
def ConstantRatioLogConcave {N : ℕ} (v : Coefficients N) : Prop :=
  ∃ r : ℝ, 0 < r ∧ r ≤ 1 ∧
    (∀ i, i ≤ N → v.c i = r * profile v i) ∧
    LogConcaveNoInternalZeros N (newtonCoeff (profile v))


/-- Theorem 8.1 (log-concave Newton criterion), matrix-positivity conclusion: every
linearization coefficient `g(m,n;k) = productMatrix v m n k` is nonnegative. -/
def Stmt_logconcave_matrix : Prop :=
  ∀ (N : ℕ) (v : Coefficients N), Admissible v → ConstantRatioLogConcave v →
    MatrixPositivity v


/-- Theorem 8.1 in the form of the geometric criterion: finite realization (orthogonality
measure, terminal relation, product identities) together with matrix positivity. -/
def Stmt_logconcave : Prop :=
  ∀ (N : ℕ) (v : Coefficients N), Admissible v → ConstantRatioLogConcave v →
    FiniteRealization v ∧ MatrixPositivity v


```
### lean/Szkraw/LCAssembly.lean
```lean
/-- **Theorem 8.1** (log-concave Newton criterion), matrix form. -/
theorem logconcave_matrix : Stmt_logconcave_matrix := …

/-- **Theorem 8.1**, with the finite realization: the array has a positive finite orthogonality
measure, the terminal relation and the product identities, and nonnegative linearization. -/
theorem logconcave_criterion : Stmt_logconcave := …

```
### lean/Szkraw/AllProducts.lean
```lean
/-- `α_n = c_n σ_{n-1}/σ_n`, with `α_0 = 0`. -/
noncomputable def alphaS (v : Coefficients N) (σ : ℕ → ℝ) (n : ℕ) : ℝ :=
  if n = 0 then 0 else v.c n * σ (n - 1) / σ n


/-- `γ_n = a_n σ_{n+1}/σ_n`. -/
noncomputable def gammaS (v : Coefficients N) (σ : ℕ → ℝ) (n : ℕ) : ℝ := v.a n * σ (n + 1) / σ n


/-- Theorem 7.12 (All products). -/
def Stmt_all_products : Prop :=
  ∀ (N : ℕ) (v : Coefficients N), Admissible v → ∀ σ : ℕ → ℝ, (∀ n, n ≤ N → 0 < σ n) →
    (∀ j i, j ≤ i → i ≤ N → v.b j ≤ v.b i) →
    (∀ j i, j ≤ i → i ≤ N → alphaS v σ j ≤ alphaS v σ i) →
    (∀ j i, j ≤ i → i ≤ N → alphaS v σ j + gammaS v σ j ≤ alphaS v σ i + gammaS v σ i) →
    (∀ j i, j ≤ i → i + 1 ≤ N → alphaS v σ j ≤ gammaS v σ i) →
    MatrixPositivity v


theorem all_products : Stmt_all_products := …

/-- Hypotheses of Corollary 7.13: constant ratio `c_i = r d_i` (`0 < r ≤ 1`), an increasing
profile, and `d_{N-1} ≤ 1/2`. -/
def HeavyTop (v : Coefficients N) : Prop :=
  ∃ r : ℝ, 0 < r ∧ r ≤ 1 ∧ (∀ i, i ≤ N → v.c i = r * profile v i) ∧
    (∀ i, i < N → profile v i < profile v (i + 1)) ∧ profile v (N - 1) ≤ 1 / 2


/-- Corollary 7.13 (Heavy top step). -/
def Stmt_heavy_top : Prop :=
  ∀ (N : ℕ) (v : Coefficients N), Admissible v → HeavyTop v → MatrixPositivity v


theorem heavy_top : Stmt_heavy_top := …

```
### lean/Szkraw/LowProducts.lean
```lean
/-- `π_i = Π_{j<i} a_j / c_{j+1}`. -/
noncomputable def piW (v : Coefficients N) (i : ℕ) : ℝ := ∏ j ∈ range i, v.a j / v.c (j + 1)


/-- `π_n g(m,n;k) = π_k g(m,k;n)`. -/
theorem piW_entry (v : Coefficients N) (hv : Admissible v) (m : ℕ) (n k : Fin (N + 1)) :
    piW v n * productMatrix v m n k = piW v k * productMatrix v m k n := …

/-- Theorem 7.10 (Low products), including the consequence for triples with two indices of sum
at most `N`. -/
def Stmt_low_products : Prop :=
  ∀ (N : ℕ) (v : Coefficients N), Admissible v → ∀ σ : ℕ → ℝ, (∀ n, n ≤ N → 0 < σ n) →
    (∀ j i, j ≤ i → i + 1 ≤ N → v.b j ≤ v.b i) →
    (∀ j i, j ≤ i → i ≤ N → alphaS v σ j ≤ alphaS v σ i) →
    (∀ j i, j ≤ i → i + 2 ≤ N → alphaS v σ j + gammaS v σ j ≤ alphaS v σ i + gammaS v σ i) →
    (∀ j i, j ≤ i → i + j + 2 ≤ N → alphaS v σ j ≤ gammaS v σ i) →
    ∀ m, m ≤ N → ∀ n k : Fin (N + 1), (m + n.val ≤ N ∨ m + k.val ≤ N ∨ n.val + k.val ≤ N) →
      0 ≤ productMatrix v m n k


theorem low_products : Stmt_low_products := …

/-- Hypotheses of Corollary 7.11: constant ratio `c_i = r d_i` (`0 < r ≤ 1`) and a convex
profile (nondecreasing increments). -/
def ConvexProfile (v : Coefficients N) : Prop :=
  ∃ r : ℝ, 0 < r ∧ r ≤ 1 ∧ (∀ i, i ≤ N → v.c i = r * profile v i) ∧
    (∀ i, 1 ≤ i → i + 1 ≤ N → profile v i - profile v (i - 1) ≤ profile v (i + 1) - profile v i)


/-- Corollary 7.11 (Convex profiles). -/
def Stmt_convex_low : Prop :=
  ∀ (N : ℕ) (v : Coefficients N), Admissible v → ConvexProfile v →
    ∀ m, m ≤ N → ∀ n k : Fin (N + 1), (m + n.val ≤ N ∨ m + k.val ≤ N ∨ n.val + k.val ≤ N) →
      0 ≤ productMatrix v m n k


theorem convex_low : Stmt_convex_low := …

/-- Corollary 7.11 includes every array of Theorem 2.1 (the arrays (2.3)). -/
theorem geometric_convex (v : Coefficients N) (hv : Admissible v) (hg : Geometric v) :
    ConvexProfile v := …

```
### lean/Szkraw/Reversal.lean
```lean
/-- The reversed array `a'_i = c_{N-i}`, `b'_i = b_{N-i}`, `c'_i = a_{N-i}`. -/
def revCoeff (v : Coefficients N) : Coefficients N :=
  ⟨fun i => v.c (N - i), fun i => v.b (N - i), fun i => v.a (N - i)⟩


/-- The reversal permutation matrix `Π`. -/
def revPerm (N : ℕ) : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ :=
  fun i j => if i.val + j.val = N then 1 else 0


/-- `p'_t(J) = Π p'_t(J') Π`. -/
noncomputable def Rp (v : Coefficients N) (t : ℕ) : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ :=
  revPerm N * productMatrix (revCoeff v) t * revPerm N


/-- **Lemma 7.14** (Reversal identity): `R_N R'_t = R_{N-t}` on the support. -/
theorem reversal_identity (t : ℕ) (ht : t ≤ N) :
    productMatrix v N * Rp v t = productMatrix v (N - t) := …

/-- **Theorem 7.15**, the reduction formula
`g(x,y;z) = Σ_t g'(N-x,N-y;t) g(N,N-t;z)` (valid for all `x, y ≤ N`). -/
theorem deep_formula (x y : ℕ) (hx : x ≤ N) (hy : y ≤ N) (z : Fin (N + 1)) :
    productMatrix v x ⟨y, by omega⟩ z = ∑ t : Fin (N + 1),
      productMatrix (revCoeff v) (N - x) ⟨N - y, by omega⟩ t *
        productMatrix v N ⟨N - t.val, by omega⟩ z := …

/-- **Theorem 7.15**: `g(N,N;N-l)` is the coefficient of `R'_l` in `R_N`. -/
theorem top_expansion :
    productMatrix v N = ∑ l : Fin (N + 1), productMatrix v N ⟨N, by omega⟩ ⟨N - l.val, by omega⟩ • Rp v l := …

/-- A deep triple: each two indices have sum greater than `N`. -/
def Deep (N m n k : ℕ) : Prop := N < m + n ∧ N < m + k ∧ N < n + k


/-- **Theorem 7.15** (Deep reduction), positivity criterion. -/
def Stmt_deep_reduction : Prop :=
  ∀ (N : ℕ) (v : Coefficients N), Admissible v →
    (∀ m, m ≤ N → ∀ n k : Fin (N + 1), ¬Deep N m n k → 0 ≤ productMatrix v m n k) →
    (∀ i j, (h : i + j < N) → ∀ t : Fin (N + 1), 0 ≤ productMatrix (revCoeff v) i ⟨j, by omega⟩ t) →
    (∃ e : Fin (N + 1) → ℝ, (∀ l, 0 ≤ e l) ∧ productMatrix v N = ∑ l, e l • Rp v l) →
    MatrixPositivity v


theorem deep_reduction : Stmt_deep_reduction := …

/-- `a_n = c_{N-n}` and `b_n = b_{N-n}`. -/
def Palindromic (v : Coefficients N) : Prop :=
  ∀ n, n ≤ N → v.a n = v.c (N - n) ∧ v.b n = v.b (N - n)


/-- **Theorem 7.16** (Palindromic criterion). -/
def Stmt_palindromic : Prop :=
  ∀ (N : ℕ) (v : Coefficients N), Admissible v → Palindromic v →
    ∀ σ : ℕ → ℝ, (∀ n, n ≤ N → 0 < σ n) →
    (∀ j i, j ≤ i → i + 1 ≤ N → v.b j ≤ v.b i) →
    (∀ j i, j ≤ i → i ≤ N → alphaS v σ j ≤ alphaS v σ i) →
    (∀ j i, j ≤ i → i + 2 ≤ N → alphaS v σ j + gammaS v σ j ≤ alphaS v σ i + gammaS v σ i) →
    (∀ j i, j ≤ i → i + j + 2 ≤ N → alphaS v σ j ≤ gammaS v σ i) →
    MatrixPositivity v


theorem palindromic : Stmt_palindromic := …

/-- **Corollary 7.17** (Monotone palindromic systems). -/
def Stmt_palin_mono : Prop :=
  ∀ (N : ℕ) (v : Coefficients N), Admissible v → (∀ n, n ≤ N → v.b n = 0) →
    (∀ j i, j ≤ i → i ≤ N → v.c j ≤ v.c i) → (∀ n, n ≤ N → v.c n + v.c (N - n) = 1) →
    MatrixPositivity v


theorem palin_mono : Stmt_palin_mono := …

/-- Corollary 7.17 includes the symmetric Krawtchouk array `c_n = n/N`. -/
theorem palin_mono_kraw (N : ℕ) (hN : 1 ≤ N) : MatrixPositivity (krawCoefficients N 1) := …

```
### lean/Szkraw/AllProducts.lean
```lean
/-- The product coefficients `g(m,n;k)` for fixed `k`, extended by zero off the square. -/
noncomputable def Gk (v : Coefficients N) (k : Fin (N + 1)) (m n : ℕ) : ℝ :=
  if h : m ≤ N ∧ n ≤ N then productMatrix v m ⟨n, by omega⟩ k else 0


```
### lean/Szkraw/QuadDecomp.lean
```lean
/-- Parity: `g(m,n;k) = 0` when `m + n + k` is odd. -/
theorem Gk_parity (hv : Admissible v) (hb : ∀ i, i ≤ M → v.b i = 0) (k : Fin (M + 1)) :
    ∀ m n, (m + n + k.val) % 2 = 1 → Gk v k m n = 0 := …

/-- The even component before normalization: `â_n = a_{2n}a_{2n+1}`,
`b̂_n = c_{2n}a_{2n-1} + a_{2n}c_{2n+1}`, `ĉ_n = c_{2n}c_{2n-1}`. -/
def evenRaw : Coefficients N :=
  ⟨fun n => v.a (2 * n) * v.a (2 * n + 1),
   fun n => v.c (2 * n) * v.a (2 * n - 1) + v.a (2 * n) * v.c (2 * n + 1),
   fun n => v.c (2 * n) * v.c (2 * n - 1)⟩


/-- The odd component before normalization: `ǎ_n = a_{2n+1}a_{2n+2}`,
`b̌_n = a_{2n+1}c_{2n+2} + c_{2n+1}a_{2n}`, `č_n = c_{2n+1}c_{2n}`. -/
def oddRaw : Coefficients (N - 1) :=
  ⟨fun n => v.a (2 * n + 1) * v.a (2 * n + 2),
   fun n => v.a (2 * n + 1) * v.c (2 * n + 2) + v.c (2 * n + 1) * v.a (2 * n),
   fun n => v.c (2 * n + 1) * v.c (2 * n)⟩


/-- The even-column coefficients as a function of the halved indices. -/
noncomputable def Geven (a b c : ℕ) : ℝ :=
  if h : c ≤ N then Gk v ⟨2 * c, by omega⟩ (2 * a) (2 * b) else 0


/-- `g(2a,2b;2c) = ĝ(a,b;c)` (with the unnormalized even component). -/
theorem even_block (hv : Admissible v) (hb : ∀ i, i ≤ 2 * N → v.b i = 0) :
    ∀ a, a ≤ N → ∀ b c : Fin (N + 1),
      productMatrix (evenRaw v) a b c = Geven v a b.val c.val := …

/-- The candidate odd-column array: `H(2a,2b+1) = a_{2a}ǧ(a,b) + c_{2a}ǧ(a-1,b)`,
`H(2a+1,2b) = a_{2b}ǧ(a,b) + c_{2b}ǧ(a,b-1)`, zero otherwise. -/
noncomputable def Hodd (c : Fin (N - 1 + 1)) (m n : ℕ) : ℝ :=
  if m % 2 = 0 ∧ n % 2 = 1 then
    v.a m * Gk (oddRaw v) c (m / 2) (n / 2) + v.c m * Gk (oddRaw v) c (m / 2 - 1) (n / 2)
  else if m % 2 = 1 ∧ n % 2 = 0 then
    v.a n * Gk (oddRaw v) c (m / 2) (n / 2) + v.c n * Gk (oddRaw v) c (m / 2) (n / 2 - 1)
  else 0


/-- The odd-column coefficients: `g(m,n;2c+1) = H(m,n)`. -/
theorem odd_block (hv : Admissible v) (hb : ∀ i, i ≤ 2 * N → v.b i = 0) (hN : 1 ≤ N)
    (c : Fin (N - 1 + 1)) :
    ∀ m, m ≤ 2 * N → ∀ n : Fin (2 * N + 1),
      productMatrix v m n ⟨2 * c.val + 1, by omega⟩ = Hodd v c m n.val := …

/-- The affine normalization `(a, b, c) ↦ (a, b - b_0, c)/a_0`. -/
noncomputable def normalize {K : ℕ} (w : Coefficients K) : Coefficients K :=
  ⟨fun n => w.a n / w.a 0, fun n => (w.b n - w.b 0) / w.a 0, fun n => w.c n / w.a 0⟩


/-- Normalization describes the same polynomials in the variable `(x - b_0)/a_0`. -/
theorem product_normalize {K : ℕ} (w : Coefficients K) (h0 : w.a 0 ≠ 0) :
    ∀ m, productMatrix (normalize w) m = productMatrix w m := …

/-- The normalized even component. -/
noncomputable def evenComp : Coefficients N := normalize (evenRaw v)


/-- The normalized odd component. -/
noncomputable def oddComp : Coefficients (N - 1) := normalize (oddRaw v)


/-- The normalized even component satisfies (basic). -/
theorem evenComp_admissible (hv : Admissible v) (hb : ∀ i, i ≤ 2 * N → v.b i = 0) (hN : 1 ≤ N) :
    Admissible (evenComp v) := …

/-- The normalized odd component satisfies (basic), for `N ≥ 2`. -/
theorem oddComp_admissible (hv : Admissible v) (hb : ∀ i, i ≤ 2 * N → v.b i = 0) (hN : 2 ≤ N) :
    Admissible (oddComp v) := …

/-- **Theorem 7.8**, positivity transfer: if both normalized components have nonnegative
linearization, so does the symmetric array. -/
theorem decomp_positivity (hv : Admissible v) (hb : ∀ i, i ≤ 2 * N → v.b i = 0) (hN : 1 ≤ N)
    (he : MatrixPositivity (evenComp v)) (ho : MatrixPositivity (oddComp v)) : MatrixPositivity v := …

/-- **Theorem 7.8**, converse: nonnegative linearization of the symmetric array implies that of
its even component. -/
theorem decomp_converse (hv : Admissible v) (hb : ∀ i, i ≤ 2 * N → v.b i = 0) (hN : 1 ≤ N)
    (hp : MatrixPositivity v) : MatrixPositivity (evenComp v) := …

```
### lean/Szkraw/ParitySplit.lean
```lean
/-- Hypotheses (i)–(ii) of Corollary 7.9 with parameters `p_0` and `q`. -/
def ParitySplit (v : Coefficients (2 * N)) (p₀ q : ℝ) : Prop :=
  1 ≤ q ∧ (∀ n, 2 * n + 1 ≤ 2 * N → v.c (2 * n + 1) = p₀) ∧
    (∀ n, 1 ≤ n → n ≤ N → 0 < v.c (2 * n) - v.c (2 * (n - 1))) ∧
    (∀ n, 1 ≤ n → n < N → v.c (2 * (n + 1)) - v.c (2 * n) = q * (v.c (2 * n) - v.c (2 * (n - 1))))


/-- **Corollary 7.9** (Parity-split criterion). -/
def Stmt_parity_split : Prop :=
  ∀ (N : ℕ) (v : Coefficients (2 * N)), 1 ≤ N → Admissible v → (∀ i, i ≤ 2 * N → v.b i = 0) →
    ∀ p₀ q : ℝ, ParitySplit v p₀ q → p₀ ≤ 1 / 2 → MatrixPositivity v


theorem parity_split : Stmt_parity_split := …

/-- Corollary 7.9, sharpness: for `1/2 < p_0 < 1`, `g(2,2;2) < 0`. -/
theorem parity_split_sharp (N : ℕ) (v : Coefficients (2 * N)) (hN : 1 ≤ N) (hv : Admissible v)
    (hb : ∀ i, i ≤ 2 * N → v.b i = 0) (p₀ q : ℝ) (hp : ParitySplit v p₀ q) (hp0 : 1 / 2 < p₀) :
    productMatrix v 2 ⟨2, by omega⟩ ⟨2, by omega⟩ < 0 := …

/-- Szwarc's array (7.2): `b ≡ 0`, `(a_{2n}, c_{2n}) = ((N-n)/N, n/N)`, `(a_{2n-1}, c_{2n-1}) = (1-p_0, p_0)`. -/
noncomputable def szwarcCoefficients (N : ℕ) (p : ℝ) : Coefficients (2 * N) :=
  ⟨fun k => if k % 2 = 0 then ((N : ℝ) - ((k / 2 : ℕ) : ℝ)) / N else 1 - p,
   fun _ => 0,
   fun k => if k % 2 = 0 then ((k / 2 : ℕ) : ℝ) / N else p⟩


and coefficient sums one. -/
def Stmt_szwarc : Prop :=
  ∀ (N : ℕ), 1 ≤ N → ∀ p : ℝ, 0 < p → p ≤ 1 / 2 →
    FiniteRealization (szwarcCoefficients N p) ∧ MatrixPositivity (szwarcCoefficients N p)


theorem szwarc_system : Stmt_szwarc := …

/-- **Theorem 7.1**, sharpness: for `1/2 < p_0 < 1`, `g(2,2;2) < 0`. -/
theorem szwarc_sharp (N : ℕ) (hN : 1 ≤ N) (p : ℝ) (hp : 1 / 2 < p) (hp1 : p < 1) :
    productMatrix (szwarcCoefficients N p) 2 ⟨2, by omega⟩ ⟨2, by omega⟩ < 0 :=
  parity_split_sharp N _ hN (szwarc_admissible N hN p (by linarith) hp1) (fun _ _ => rfl) p 1
    (szwarc_parity N hN p) hp


```
### lean/Szkraw/Krawtchouk.lean
```lean
noncomputable def krawCoefficients (N : ℕ) (r : ℝ) : Coefficients N where
  a i := ((N : ℝ)-i)/N
  b i := (1-r)*i/N
  c i := r*i/N


```