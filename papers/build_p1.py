"""Assemble papers/p1.tex (the paper answering Szwarc's Problem 2) from paper.tex.
Mathematical text is copied verbatim by line ranges of paper.tex at the commit noted below; every change to a copied
block is an exact string replacement that must match once (assert). New prose is written out in this file.
Source: paper.tex at f2f2b8f/ad5eb72 (identical in the copied ranges)."""
import os
HERE = os.path.dirname(os.path.abspath(__file__))
L = open(os.path.join(HERE, '..', 'paper.tex')).read().split('\n')
def lines(a, b):  # 1-based inclusive
    return '\n'.join(L[a - 1:b])
def edit(text, *pairs):
    for old, new in pairs:
        assert text.count(old) == 1, ('edit does not match exactly once', old[:90])
        text = text.replace(old, new)
    return text
out = []
out.append(r"""\newcommand{\papertitle}{A log-concavity criterion for finite nonnegative linearization}
\newcommand{\papershort}{A LOG-CONCAVITY CRITERION FOR FINITE LINEARIZATION}
\newcommand{\paperdate}{October 23, 2026}
\input{preamble}
\begin{document}
\maketitle

\begin{abstract}
Szwarc asked for criteria, stated in the recurrence coefficients, that give nonnegative linearization (property (P)) for finite systems of orthogonal polynomials such as the Krawtchouk polynomials, and for a criterion that handles his symmetric quadratic system $Q_n$. For a finite stochastic three-term recurrence whose diagonal and downward coefficients have a constant ratio, we prove that property (P) holds for every product, including products beyond the terminal degree, whenever the Newton coefficients of the profile $d_i=b_i+c_i$ are log-concave without internal zeros. The criterion contains the full positive Krawtchouk range and the geometric (dual $q$-Krawtchouk) arrays. Through a quadratic decomposition of symmetric finite systems it gives a parity-split criterion that covers $Q_n$ for every size and every $p_0\leq1/2$, which is sharp. For every fixed ratio, no criterion valid for all sizes contains coefficient balls of a fixed radius around the Krawtchouk arrays. Positivity of the Newton coefficients does not suffice, while log-concavity is not necessary; we pose the exact boundary as a problem. Its theorems, corollaries and propositions are formalized in Lean.
\vskip5pt
\noindent\textbf{Keywords.}\enspace Finite orthogonal polynomials; nonnegative linearization; Krawtchouk polynomials; log-concave sequences; quadratic transformation; polynomial hypergroups.
\vskip5pt
\noindent\textbf{MSC2020 Classification.}\enspace 33C45; 42C05; 05A20.
\end{abstract}

\vskip50pt
\baselineskip=13.5pt
\section{Introduction}\label{sec:introduction}

Nonnegative linearization (property (P)) asks whether the product of two orthogonal polynomials is a nonnegative linear combination of polynomials of the same family. For a finite system $R_0,\ldots,R_N$ the identity is understood on the orthogonality support, so it includes products whose degree sum exceeds $N$. In the normalization $R_i(1)=1$ the coefficients then sum to one and define a finite polynomial hypergroup.

In his survey, Szwarc~\cite[\S5, Problem~2]{szwarc} asks: ``Find any criteria for the property (P) for finite systems of orthogonal polynomials, like the Krawtchouk polynomials.'' He then introduces a symmetric system $Q_n$ built from the Krawtchouk recurrence, notes that it has property (P) for $p_0\leq1/2$, and asks for a general criterion that would handle this case. His criteria for infinite systems~\cite[Theorems~3.2 and~3.3]{szwarc} are monotonicity conditions on the recurrence coefficients; for a finite system some of them fail near the terminal index, whose upward coefficient vanishes (Section~\ref{sec:szwarc}). Askey~\cite[Part~II, Theorem~1 and Corollary~1]{askey} gave finite recurrence conditions for products of degree sum at most $N$, through a maximum principle for a hyperbolic difference equation, and Szwarc~\cite[Theorem~1]{szwarc2003} characterized property (P) for finite and infinite systems through an auxiliary discrete hyperbolic problem. Miclo~\cite[Proposition~3.3]{miclo} characterizes the hypergroup property of a finite birth--death chain at a boundary point spectrally. None of these gives a coefficient criterion that covers all products of the finite Krawtchouk systems.

We work with a stochastic three-term recurrence \eqref{eq:recurrence} with diagonal coefficients $b_i$, downward coefficients $c_i$ and profile $d_i=b_i+c_i$. The main result, Theorem~\ref{thm:lc}, concerns arrays with a constant ratio $b_i/c_i$: property (P) holds for every product whenever the Newton coefficients $\nu_k=\Delta^kd(0)$ of the profile are nonnegative and log-concave without internal zeros. This is a set of inequalities on the coefficients; checking it does not involve any product coefficient. It contains the full positive Krawtchouk range (Corollary~\ref{cor:kraw}; property (P) is classical there, see Eagleson~\cite{eagleson} and~\cite[\S5]{szwarc}) and the geometric arrays of Corollary~\ref{cor:additional}, the dual $q$-Krawtchouk systems of Koelink's construction on the Hecke algebra of type~B~\cite{koelink}. Section~\ref{sec:szwarc} answers the second part of the problem: a quadratic decomposition reduces property (P) of a symmetric finite system to two nonsymmetric ones (Theorem~\ref{thm:decomp}), and Theorem~\ref{thm:lc} then gives a parity-split criterion (Corollary~\ref{cor:parity}) that covers $Q_n$ for every $N$ and $0<p_0\leq1/2$; this range is sharp (Theorem~\ref{thm:szwarc}).

Section~\ref{sec:limits} discusses how far criteria of this kind can go. For every fixed $r<1$, no set of arrays with property (P) contains coefficient balls of a radius independent of $N$ around the Krawtchouk arrays (Corollary~\ref{cor:radius-exp}), so a criterion valid for all $N$ must place them near its boundary; the log-concavity condition places them on its edge. Positivity of the Newton coefficients does not suffice, but log-concavity is not necessary; we record exact examples and pose the exact boundary as a problem.

Every theorem, corollary and proposition, and Lemmas~\ref{lem:finite} and~\ref{lem:corner-value}, is formalized in Lean~4 with Mathlib; the lemmas of Section~\ref{sec:lc} are formalized within the proof of Theorem~\ref{thm:lc} (see the section on code and formalization). Two companion papers continue this work: \cite{P2} treats ratios $c_i/d_i$ that increase with the index, and \cite{P3} treats the algebraic geometric-increment criterion, explicit perturbation neighbourhoods and the constraints at the symmetric Krawtchouk endpoint.

\section{Setting}\label{sec:criterion}
""")
# --- setting: lines 79-92, J convention 250-254, Lemma finite 256-275 (edited)
out.append(lines(79, 92))
out.append('')
out.append(edit(lines(250, 254), ("Write the tridiagonal recurrence matrix", "Write the tridiagonal recurrence matrix of such an array")))
out.append('')
out.append(edit(lines(256, 275),
    ("The same finite spectral argument as in Theorem~\\ref{thm:criterion} gives $N+1$ distinct eigenvalues and positive spectral masses at $e_0$, and",
     "In an orthogonal eigenspace decomposition of $H$, the cyclic span of $e_0$ has dimension at most the number of distinct eigenvalues; here it is all of $\\mathbb R^{N+1}$, so $H$ has $N+1$ distinct eigenvalues and the projection of $e_0$ on each eigenspace is nonzero. The spectral measure $\\mu$ of $H$ at $e_0$ therefore has positive mass at each of $N+1$ real points, and")))
out.append(r"""
We say that the array has \emph{nonnegative linearization}, or \emph{property (P)}, if $g(m,n;k)\geq0$ for all $0\leq m,n,k\leq N$. The coefficients $g(m,n;\cdot)$ then sum to one, since $R_i(1)=1$ and $1$ lies in the support, because $J\boldsymbol1=\boldsymbol1$.
""")
out.append(r"""
For $q\geq1$ and $0<r\leq1$ let $G_{N,q,r}$ be the array
\begin{equation}\label{eq:parameters}
a_i=\frac{q^i[N-i]_q}{[N]_q},\qquad
b_i=(1-r)\frac{[i]_q}{[N]_q},\qquad
c_i=r\frac{[i]_q}{[N]_q},
\end{equation}
with $[j]_q$ as above; it satisfies \eqref{eq:basic}, since $[N]_q-[i]_q=q^i[N-i]_q$. Its profile $d_i=[i]_q/[N]_q$ has geometric increments with ratio $q$, and $b_i/c_i=(1-r)/r$ is constant. The Krawtchouk array is $K_{N,r}=G_{N,1,r}$, with $a_i=(N-i)/N$, $b_i=(1-r)i/N$ and $c_i=ri/N$.
""")
# --- Newton coefficients, Theorem lc, kernel, lemmas, proof
out.append(r"\section{Log-concave profiles}\label{sec:lc}")
out.append('')
out.append(edit(lines(683, 688),
    ("Theorem~\\ref{thm:criterion} requires the increments of the profile $d_i=b_i+c_i$ to be geometric. This section replaces that equality by inequalities on the Newton coefficients of the profile, for arrays with constant ratio $b_i/c_i$. Write",
     "For an array satisfying \\eqref{eq:basic} with profile $d_i=b_i+c_i$ write")))
out.append('')
out.append(edit(lines(690, 694),
    ("They hold for the Krawtchouk arrays ($\\nu=(1/N,0,\\ldots,0)$), for all arrays of Theorem~\\ref{thm:criterion} ($\\nu_k$ proportional to $(q-1)^{k-1}$, log-concave with equality).",
     "They hold for the Krawtchouk arrays ($\\nu=(1/N,0,\\ldots,0)$) and for all arrays $G_{N,q,r}$ ($\\nu_k$ proportional to $(q-1)^{k-1}$, log-concave with equality)."),
    ("The hypotheses exclude the known counterexamples with constant ratio. The convex counterexamples recorded in Section~\\ref{sec:open} have Newton coefficients of both signs. For the combinations $(1-\\lambda)K_{N,r}+\\lambda G_{N,q,r}$ discussed there,",
     "The hypotheses exclude the known counterexamples with constant ratio: the convex counterexamples recorded in~\\cite{P3} have Newton coefficients of both signs, and for the combinations $(1-\\lambda)K_{N,r}+\\lambda G_{N,q,r}$ of Section~\\ref{sec:limits},")))
out.append('')
out.append(lines(696, 791))
out.append(edit(lines(792, 794),
    (" The diagnostics \\path{lc_kernel_check.py} verify Lemmas~\\ref{lem:kernel-rec}--\\ref{lem:detours} and the matching $\\mathcal P^2\\geq4\\mathcal Q$ in exact arithmetic on random log-concave profiles.", "")))
out.append('')
# --- Krawtchouk and geometric corollaries
out.append(edit(lines(350, 366),
    ("Apply Theorem~\\ref{thm:criterion} with $q=1$.",
     "This is the array $K_{N,r}$; its profile $d_i=i/N$ has Newton coefficients $(1/N,0,\\ldots,0)$, so Theorem~\\ref{thm:lc} applies.")))
out.append('')
out.append(edit(lines(368, 373),
    ("\\begin{corollary}[The dual $q$-Krawtchouk case]\\label{cor:additional}\nFor every $N\\geq2$, $q>1$, and $0<r\\leq1$, the recurrence \\eqref{eq:parameters} has nonnegative linearization.",
     "\\begin{corollary}[Geometric arrays]\\label{cor:additional}\nFor every $N\\geq2$, $q>1$, and $0<r\\leq1$, the array $G_{N,q,r}$ of \\eqref{eq:parameters} has nonnegative linearization."),
    ("Its increments are $d_i-d_{i-1}=q^{i-1}/[N]_q$, so all hypotheses hold.",
     "Its increments are $d_i-d_{i-1}=q^{i-1}/[N]_q$, so its Newton coefficients $\\nu_k=(q-1)^{k-1}/[N]_q$ are log-concave without internal zeros and Theorem~\\ref{thm:lc} applies.")))
out.append(r"""
The arrays $G_{N,q,r}$ are the normalized recurrences of Koelink's construction~\cite[Theorems~3.1(ii) and~7.1]{koelink} with $r=1/p$; their polynomial interpretation is the dual $q$-Krawtchouk interpretation described after his Theorem~7.8. A proof of Corollary~\ref{cor:additional} by a finite algebra with positive multiplication, which needs only the geometric increments, is given in~\cite{P3}.
""")
# --- Szwarc's quadratic system
out.append(r"\section{Szwarc's quadratic system}\label{sec:szwarc}")
out.append('')
out.append(edit(lines(393, 406),
    ("This section proves the positivity of \\eqref{eq:szwarc-q} by a graded version of the algebra of Section~\\ref{sec:algebra}, and then gives an explicit coefficient criterion for symmetric finite systems near \\eqref{eq:szwarc-q}.",
     "We derive the positivity of \\eqref{eq:szwarc-q} from Theorem~\\ref{thm:lc} through a quadratic decomposition of symmetric finite systems.")))
out.append('')
out.append(lines(524, 524))
out.append('')
out.append(edit(lines(526, 555),
    ("By symmetry $R_{2n}(t)=P_n(t^2)$",
     "Since $b\\equiv0$, the matrix $J$ is conjugate to $-J$ by $\\operatorname{diag}((-1)^i)$, which fixes $e_0$; hence the measure of Lemma~\\ref{lem:finite} is symmetric and $R_k(-t)=(-1)^kR_k(t)$. By symmetry $R_{2n}(t)=P_n(t^2)$"),
    ("follow from the symmetry of the measure and from $g(m,n;k)\\int R_k^2\\,d\\mu=\\int R_mR_nR_k\\,d\\mu$, exactly as in the proof of Theorem~\\ref{thm:szwarc}.",
     "follow from the symmetry of the measure and from $g(m,n;k)\\int R_k^2\\,d\\mu=\\int R_mR_nR_k\\,d\\mu$.")))
out.append('')
out.append(edit(lines(557, 557), ("Combined with Theorem~\\ref{thm:criterion},", "Combined with Theorem~\\ref{thm:lc},")))
out.append('')
out.append(edit(lines(559, 573),
    ("For $N=1$ the odd component consists only of $L_0=1$, the array is \\eqref{eq:qarray}, and positivity follows directly from Theorem~\\ref{thm:szwarc}.",
     "For $N=1$ the odd component consists only of $L_0=1$ and the array is \\eqref{eq:qarray}."),
    ("For $N=1$ this is Theorem~\\ref{thm:szwarc}. Let $N\\geq2$.",
     "For $N=1$ the array is $a_0=1$, $c_1=p_0$, $a_1=1-p_0$, $c_2=1$, with support $\\{-1,0,1\\}$ and $R_1=t$, $R_2=(t^2-p_0)/(1-p_0)$. On the support $R_1^2=(1-p_0)R_2+p_0$, $R_1R_2=R_1$ and $R_2^2=\\frac{p_0}{1-p_0}+\\frac{1-2p_0}{1-p_0}R_2$, as evaluation at $t=0,\\pm1$ shows; all coefficients are nonnegative for $p_0\\leq1/2$, and $g(2,2;2)<0$ for $p_0>1/2$. Let $N\\geq2$."),
    ("This satisfies Theorem~\\ref{thm:criterion} with $\\beta=(1-r)/r\\geq0$.",
     "Its profile $d_n$ has geometric increments, so its Newton coefficients are proportional to $(q-1)^{k-1}$ and log-concave without internal zeros, and $0<r\\leq1$."),
    ("Its ratio $\\beta=(q-r)/r$ is constant and nonnegative, and its profile $qd_n/(1-d_1)$ has geometric increments with ratio $q$. Theorem~\\ref{thm:criterion} applies to both components, and Theorem~\\ref{thm:decomp} concludes. Lemma~\\ref{lem:parameters} identifies the parameters.",
     "Its profile $qd_n/(1-d_1)$ has geometric increments with ratio $q$, and its downward coefficients are $r/q\\leq1$ times the profile. Theorem~\\ref{thm:lc} applies to both components, and Theorem~\\ref{thm:decomp} concludes. Comparison with \\eqref{eq:parameters}, using $d_n=[n]_q/[N]_q$ and $1-d_1=q[N-1]_q/[N]_q$, identifies the parameters."),
    ("(for $N=1$ see Theorem~\\ref{thm:szwarc})", "(for $N=1$ see above)")))
out.append(r"""
\begin{theorem}[Szwarc's quadratic system]\label{thm:szwarc}
Let $N\geq1$ and $0<p_0\leq1/2$. The array \eqref{eq:qarray} has a symmetric positive orthogonality measure on $2N+1$ points, and for all $0\leq m,n\leq 2N$
\[
R_mR_n=\sum_{k=0}^{2N}g(m,n;k)R_k,\qquad g(m,n;k)\geq0,\qquad\sum_k g(m,n;k)=1
\]
on that support. If $1/2<p_0<1$, then $g(2,2;2)<0$.
\end{theorem}
\begin{proof}
Lemma~\ref{lem:finite} gives a positive measure on $2N+1$ points, and it is symmetric because $b\equiv0$ (proof of Theorem~\ref{thm:decomp}). The array \eqref{eq:qarray} satisfies the hypotheses of Corollary~\ref{cor:parity} with $c_{2n+1}=p_0$ and $d_n=n/N$, that is, with $q=1$, which gives nonnegative linearization for $p_0\leq1/2$ and $g(2,2;2)<0$ for $1/2<p_0<1$. The coefficients sum to one because $R_k(1)=1$ and $1$ lies in the support, since $J\boldsymbol1=\boldsymbol1$.
\end{proof}

The even component of \eqref{eq:qarray} is the Krawtchouk array $K_{N,r}$ with $r=p_0/(1-p_0)$, so that $Q_{2n}(y)$ is a Krawtchouk polynomial in $y^2$, as Szwarc notes, and its odd component is $K_{N-1,r}$. A second proof of Theorem~\ref{thm:szwarc}, by a graded version of the algebra of~\cite{P3}, and explicit coefficient neighbourhoods of \eqref{eq:qarray} are given there.
""")
# --- limits and sharpness
out.append(r"""\section{How far can such criteria go?}\label{sec:limits}

A criterion valid for all $N$ cannot leave a margin of fixed size around the Krawtchouk arrays. Let
\[
\operatorname{dist}(\widetilde a,\widetilde b,\widetilde c)=\max_{0\leq i\leq N}\max\Bigl(\Bigl|\widetilde a_i-\frac{N-i}N\Bigr|,\Bigl|\widetilde b_i-\frac{(1-r)i}N\Bigr|,\Bigl|\widetilde c_i-\frac{ri}N\Bigr|\Bigr)
\]
be the coefficient distance to $K_{N,r}$.
""")
out.append(r"""\begin{lemma}[Corner value]\label{lem:corner-value}
For $0<r\leq1$, the array $K_{N,r}$ has $g(N,N;N)=(1-r)^N$.
\end{lemma}
\begin{proof}
Use the model in the proof of Corollary~\ref{cor:kraw}, with $p_0=r/(1+r)$. There $R_N=K_N=Y_1\cdots Y_N$ and $K_k=\binom Nk^{-1}\sum_{|S|=k}Y_S$, where $Y_S=\prod_{l\in S}Y_l$. Since $Y_l^2=(1-r)Y_l+r$,
\[
R_N^2=\prod_{l=1}^N\bigl((1-r)Y_l+r\bigr)=\sum_S(1-r)^{|S|}r^{N-|S|}Y_S.
\]
Both sides of $R_N^2=\sum_kg(N,N;k)R_k$ depend only on the number $j$ of negative coordinates, and the identity holds on the support, that is, for every $j$; so it holds as an identity of functions of $(Y_1,\ldots,Y_N)$. The $2^N$ monomials $Y_S$ are orthogonal for the product measure, with $\mathbb E[Y_S^2]=r^{|S|}>0$, hence linearly independent. The monomial $Y_{\{1,\ldots,N\}}$ occurs only in $K_N$, with coefficient one, which gives $g(N,N;N)=(1-r)^N$.
\end{proof}

Thus the corner coefficient vanishes at $r=1$. The next proposition raises the top mass of the orthogonality measure.
""")
out.append(edit(lines(1609, 1637),
    ("After the affine normalization of Section~\\ref{sec:criterion}, its recurrence coefficients",
     "After the affine normalization $R_n(1)=1$, $R_1=x$, its recurrence coefficients"),
    ("comparing leading coefficients and using detailed balance as in Lemma~\\ref{lem:topmass} gives",
     "comparing leading coefficients and using detailed balance, $\\pi_na_n=\\pi_{n+1}c_{n+1}$, for both measures gives"),
    ("By Lemma~\\ref{lem:corner-value} and $\\pi_N=r^{-N}$,", "By Lemma~\\ref{lem:corner-value} and $\\pi_N=r^{-N}$ (Lemma~\\ref{lem:finite}),")))
out.append('')
out.append(edit(lines(1639, 1652),
    ("Let $0<r<1$, and let $\\rho_N(r)$ be as in Corollary~\\ref{cor:radius-order}.",
     "Let $0<r<1$, and let $\\rho_N(r)$ be the supremum of the $\\rho$ such that every array satisfying \\eqref{eq:basic}, with $\\widetilde b_i\\geq0$ for all $i$ and with $\\operatorname{dist}(\\widetilde a,\\widetilde b,\\widetilde c)\\leq\\rho$, has property (P).")))
out.append(r"""
Thus, for every fixed $r\in(0,1)$, no set of arrays with property (P) contains coefficient balls of a positive radius independent of $N$ around all $K_{N,r}$. For each fixed $N$, in contrast, $\rho_N(r)>0$ for $0<r<1$: explicit perturbation inequalities give $\rho_N(r)\geq\frac12(\min(r,1-r)/(32N))^N$, and $\rho_N(r)$ is of exact order $(1-r)^N$ as $r\to1$; at the symmetric endpoint $r=1$, criteria given by uniform deformation rules must satisfy two first-order equalities. These results are proved in~\cite{P3}.

\paragraph{How sharp is log-concavity?}
In Theorem~\ref{thm:lc} the Krawtchouk arrays lie on the edge of the hypothesis on the profile, and the arrays $G_{N,q,r}$ lie on its boundary, with equality in every log-concavity inequality. Positivity of the Newton coefficients of the profile does not suffice. For $q>1$ and $0<\lambda<1$ the combination $(1-\lambda)K_{N,r}+\lambda G_{N,q,r}$ is a stochastic array with constant ratio $b_i/c_i$ and increments proportional to $1+t\,q^{i-N}$, where $t=\lambda N(q-1)q^{N-1}/((1-\lambda)(q^N-1))$; its Newton coefficients are positive, and $\nu_2^2<\nu_1\nu_3$ (Section~\ref{sec:lc}). Exact computation (\path{convexity_probe.py}) gives $g(N,N;N)<0$ for this combination at $(r,N,q,t)=(4/5,10,10,1)$, $(3/5,20,10,2)$, $(1/2,20,10,1)$, $(2/5,60,10,2)$, $(1/3,100,10,2)$, $(3/10,200,2,5)$ and $(2/7,200,10,5)$. In particular, at these parameters no sufficient criterion whose admitted set is convex, such as a system of linear inequalities in the coefficients, can admit both $K_{N,r}$ and $G_{N,q,r}$.
""")
# sharpness paragraph from paper.tex line 1685, minus its heading and first sentences (restated above)
sh = L[1684]
start = sh.index("Log-concavity is not necessary either. ")
sh = sh[start:]
out.append(sh)
out.append(r"""
\section{Open problems}\label{sec:open}

\paragraph{The exact boundary.} Determine the set of profiles for which every constant-ratio array has property (P), or the threshold $V_N$ of Section~\ref{sec:limits}. The examples above suggest that the failures of log-convex profiles are driven by an acceleration of the increments near the terminal index.

\paragraph{Other ratios.} Theorem~\ref{thm:lc} requires $b_i/c_i$ to be constant. The companion paper~\cite{P2} admits ratios $c_i/d_i$ that increase with the index: linearly or as a convex quadratic on every log-concave Newton profile, with Newton coefficients of the ratio that are log-concave in every degree, and for cubic ratios under a single inequality. Criteria for other nonconstant ratios are open.

\paragraph{Monotonicity-type criteria.} Szwarc's Theorems~3.2 and~3.3 in~\cite{szwarc} are open conditions of monotonicity type for infinite systems. By Theorem~\ref{thm:decomp}, any such criterion for nonsymmetric finite systems, valid including the terminal indices, gives one for symmetric finite systems. Inequality conditions of this type for all products except those whose pairwise index sums all exceed $N$ are given in~\cite{P3}; for the remaining, deep products, Theorem~\ref{thm:lc} and its extensions in~\cite{P2} are the only inequality criteria known to us that contain the asymmetric Krawtchouk arrays.
""")
out.append(r"""\section*{AI-use disclosure}

OpenAI Codex and Anthropic Claude were used to develop proof arguments, check source passages, construct exact-arithmetic diagnostics, draft and revise this manuscript, and prepare the Lean formalization. The kernel recurrence and the operator inequality in the proof of Theorem~\ref{thm:lc} arose in research consultations with ChatGPT Pro; the closed form of the recurrence for every degree and the exact checks were completed with Claude, which also developed Sections~\ref{sec:szwarc} and~\ref{sec:limits} and prepared the Lean formalization of all numbered results. The review of Theorem~\ref{thm:lc} was therefore carried out by the same system that proposed its key steps. The results were reviewed in fourteen rounds by ChatGPT Pro, as part of a longer manuscript (an AI review with independent exact checks, not human peer review); the first round failed, the corrections are recorded in \path{REVIEW.md}, and the final confirmation rounds returned PASS. The remark on the sharpness of log-concavity in Section~\ref{sec:limits} passed a further review round with minor fixes. The author set the research objective and retains responsibility for publication decisions and the final mathematical claims. No independent human verification is asserted here. ``Machine-verified'' refers only to the Lean theorems listed in the section on code and formalization, with the axioms stated there; the remarks and computations are supported by exact arithmetic but are not machine-verified.

\section*{Code and formalization}

The companion code~\cite{code} contains exact-arithmetic diagnostics for every result (\path{papers/DIAGNOSTICS.md}) and a Lean~4 development. Run \verb|make lean| to build it and \verb|make axioms| to build and audit the principal statements; the audit invokes \path{lean/CheckAxioms.lean}, which rejects dependencies outside \path{propext}, \path{Classical.choice} and \path{Quot.sound}. All declarations below have compiled proofs without added axioms or admitted goals. Notes on how each Lean statement matches the text are in \path{papers/FORMALIZATION.md}.
\begin{center}
\begin{tabular}{@{}p{0.36\linewidth}p{0.59\linewidth}@{}}
Result & Lean declaration\\[3pt]
Lemma~\ref{lem:finite}: finite realization & \path{Szkraw.finite_realization}, \path{Szkraw.product_triangle_zero}\\[3pt]
Theorem~\ref{thm:lc}: log-concave Newton criterion & \path{Szkraw.logconcave_criterion}\\[3pt]
Remark after Theorem~\ref{thm:lc} & \path{Szkraw.lc_twoParam}, \path{Szkraw.lc_bernstein}, \path{Szkraw.constantRatio_twoParam}\\[3pt]
Corollary~\ref{cor:kraw}: Krawtchouk range & \path{Szkraw.full_krawtchouk_binomial_range}, \path{Szkraw.binomial_normalized_at_zero}, \path{Szkraw.binomial_node_probability_convention}\\[3pt]
Corollary~\ref{cor:additional}: geometric arrays & \path{Szkraw.additional_geometric_class}\\[3pt]
Theorem~\ref{thm:decomp}: quadratic decomposition & \path{Szkraw.decomp_positivity}, \path{Szkraw.decomp_converse}, \path{Szkraw.even_block}, \path{Szkraw.odd_block}, \path{Szkraw.evenComp_admissible}, \path{Szkraw.oddComp_admissible}\\[3pt]
Corollary~\ref{cor:parity}: parity-split criterion & \path{Szkraw.parity_split}, \path{Szkraw.parity_split_sharp}, \path{Szkraw.ps_even_params}, \path{Szkraw.ps_odd_params}\\[3pt]
Theorem~\ref{thm:szwarc}: Szwarc's quadratic system & \path{Szkraw.szwarc_full}, \path{Szkraw.szwarc_sharp}, \path{Szkraw.realization_symmetric}\\[3pt]
Lemma~\ref{lem:corner-value}: corner value & \path{Szkraw.corner_value}\\[3pt]
Proposition~\ref{prop:raise}: raising the top mass & \path{Szkraw.raise_measure}, \path{Szkraw.raise_corner}, \path{Szkraw.raise_sign}, \path{Szkraw.raise_bound}\\[3pt]
Corollary~\ref{cor:radius-exp} and the remark after it & \path{Szkraw.radius_exp}, \path{Szkraw.radius_exp_asymp}, \path{Szkraw.radius_no_uniform}
\end{tabular}
\end{center}
The entry for Theorem~\ref{thm:lc} formalizes Lemmas~\ref{lem:lc-ineq} and~\ref{lem:detours}, the operator induction, and Lemma~\ref{lem:kernel-rec} in converse form: the solution of~\eqref{eq:kernel-rec} yields the linearization coefficients. The Lean proofs of Corollaries~\ref{cor:kraw} and~\ref{cor:parity} obtain positivity of the components from the geometric-increment criterion of~\cite{P3} rather than from Theorem~\ref{thm:lc}; the statements are the ones given here. The Lean proof of Lemma~\ref{lem:corner-value} uses the algebra of~\cite{P3}.

\begin{thebibliography}{9}
""")
bib = {k: l for l in L[1766:1778] for k in [l[len('\\bibitem{'):l.index('}')]] if l.startswith('\\bibitem{')}
for k in ['askey', 'eagleson', 'koelink', 'miclo', 'szwarc', 'szwarc2003']:
    out.append(bib[k])
out.append(r"""\bibitem{P2} L. P. Polzer, \emph{Increasing ratios in finite nonnegative linearization}, companion paper (2026).
\bibitem{P3} L. P. Polzer, \emph{Exact and perturbative criteria for finite nonnegative linearization}, companion paper (2026).""")
out.append(bib['code'].replace('Companion code for Coefficient criteria for finite nonnegative linearization', 'Companion code for finite nonnegative linearization'))
out.append(r"""\end{thebibliography}
\end{document}""")
open(os.path.join(HERE, 'p1.tex'), 'w').write('\n'.join(out) + '\n')
print('wrote p1.tex')
