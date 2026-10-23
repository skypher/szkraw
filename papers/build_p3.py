"""Assemble papers/p3.tex (exact and perturbative criteria; limits at the symmetric endpoint) from paper.tex:
Sections 2-6, Section 7 without the quadratic decomposition and the parity split (now in paper 1), and Sections 9-10
without the results moved to paper 1 (raising the top mass, exponentially small radius) and to paper 2.
Copied verbatim; every change is an exact replacement asserted to match once. Run after p1.tex is compiled."""
import os
HERE = os.path.dirname(os.path.abspath(__file__))
L = open(os.path.join(HERE, '..', 'paper.tex')).read().split('\n')
def lines(a, b):
    return '\n'.join(L[a - 1:b])
def edit(text, *pairs):
    for old, new in pairs:
        assert text.count(old) == 1, ('edit does not match exactly once', old[:90])
        text = text.replace(old, new)
    return text
def cut_between(text, start, end, new):
    i = text.index(start); j = text.index(end, i) + len(end)
    assert text.count(start) == 1 and text.count(end) == 1
    return text[:i] + new + text[j:]
out = [r"""\newcommand{\papertitle}{Exact and perturbative criteria for finite nonnegative linearization}
\newcommand{\papershort}{EXACT AND PERTURBATIVE CRITERIA FOR FINITE LINEARIZATION}
\newcommand{\paperdate}{October 23, 2026}
\input{preamble}
\externaldocument[P1-]{p1}
\begin{document}
\maketitle

\begin{abstract}
We give two sufficient criteria stated directly in the coefficients of a finite stochastic three-term recurrence. The first assumes that the sum of its diagonal and downward coefficients has positive geometric increments with ratio $q\geq1$, and that the ratio of those coefficients is constant and nonnegative. A finite algebra construction gives nonnegative linearization, including products beyond the terminating degree. This includes the full positive Krawtchouk range and the dual $q$-Krawtchouk family with nonconstant increments. The underlying quadratic algebra occurs in Koelink's work on type B Hecke algebras. The second criterion gives explicit perturbation inequalities admitting a relatively open neighborhood of recurrence arrays around every Krawtchouk system in the interior of the positive linearization range. A graded version of the algebra proves positivity of Szwarc's symmetric quadratic system for $p_0\leq1/2$ and gives explicit symmetric neighbourhoods. Szwarc's inequality method survives for all products except those whose pairwise index sums exceed the size, and a reversal identity settles these deep products for palindromic systems. Near the symmetric Krawtchouk endpoint, uniform polynomial and analytic deformation rules that keep nonnegative linearization must satisfy two first-order equalities, and the stability radius of the perturbation criterion has the optimal order in the bias.
\vskip5pt
\noindent\textbf{Keywords.}\enspace Finite orthogonal polynomials; nonnegative linearization; Krawtchouk polynomials; dual $q$-Krawtchouk polynomials; quadratic transformation; polynomial hypergroups.
\vskip5pt
\noindent\textbf{MSC2020 Classification.}\enspace 33C45; 33D45; 42C05.
\end{abstract}

\vskip50pt
\baselineskip=13.5pt
\section{Introduction}\label{sec:introduction}
"""]
out.append(lines(66, 74))
out.append('')
out.append(r"""Section~\ref{sec:criterion} states the geometric criterion. Sections~\ref{sec:algebra} and~\ref{sec:normalization} give its algebraic proof. Section~\ref{sec:perturbation} proves the perturbation inequalities, including explicit nongeometric examples. Section~\ref{sec:applications} fixes the Krawtchouk normalization and compares the geometric recurrence with Koelink's construction. Section~\ref{sec:szwarc} treats Szwarc's quadratic system by a graded algebra and gives explicit symmetric neighbourhoods. Section~\ref{sec:low} adapts Szwarc's inequality method to finite systems, away from the deepest products, and settles the deep products of palindromic systems. Section~\ref{sec:limits} proves that uniformly sampled polynomial deformation rules, and analytic rules whose defining functions extend holomorphically to an open neighborhood of the region $\Omega$ specified there, must satisfy two first-order equalities if they keep property (P) at the symmetric Krawtchouk systems, shows that the stability radius of Theorem~\ref{thm:perturbation} has the optimal order in $1-r$, and records counterexamples to inequality shape conditions at smaller $r$. The final section lists questions left by these results. The companion paper~\cite{P1} proves an inequality criterion that contains the geometric criterion, covers $Q_n$ through a quadratic decomposition, and shows that the stability radius decays exponentially in $N$ for every fixed $r<1$; \cite{P2} admits ratios $c_i/(b_i+c_i)$ that increase with the index.
""")
out.append(lines(78, 389))
out.append('')
sz = lines(391, 522)
sz = edit(sz, ("and then gives an explicit coefficient criterion for symmetric finite systems near \\eqref{eq:szwarc-q}.",
               "and then gives an explicit coefficient criterion for symmetric finite systems near \\eqref{eq:szwarc-q}. A second proof, through a quadratic decomposition of symmetric finite systems and the criterion of~\\cite{P1}, is given in~\\cite[Section~\\ref{P1-sec:szwarc}]{P1}."))
out.append(sz)
tr = L[574]
tr = tr[tr.index("Theorem~\\ref{thm:decomp} also transfers"):]
tr = edit(tr, ("Theorem~\\ref{thm:decomp} also transfers the perturbation criteria:",
               "The quadratic decomposition~\\cite[Theorem~\\ref{P1-thm:decomp}]{P1} also transfers the perturbation criteria:"))
out.append(tr)
out.append('')
out.append(r"\section{Inequality criteria away from the deep products}\label{sec:low}")
low = lines(578, 679)
low = edit(low,
    ("Combined with Theorem~\\ref{thm:decomp}, Corollary~\\ref{cor:palin} gives",
     "Combined with the quadratic decomposition~\\cite[Theorem~\\ref{P1-thm:decomp}]{P1}, Corollary~\\ref{cor:palin} gives"),
    ("(Corollary~\\ref{cor:parity} with $q=r=1$)", "\\cite[Corollary~\\ref{P1-cor:parity}]{P1}"))
out.append(low)
out.append('')
lim = lines(1433, 1606)
lim = edit(lim,
    ("Theorem~\\ref{thm:lc} controls all triples of constant-ratio arrays with log-concave Newton profiles,",
     "the criterion of~\\cite[Theorem~\\ref{P1-thm:lc}]{P1} controls all triples of constant-ratio arrays with log-concave Newton profiles,"))
out.append(lim)
out.append(r"""
For fixed $r$ the radius also decays exponentially in $N$: raising the top mass of the measure of $K_{N,r}$, the reverse of Lemma~\ref{lem:topmass}, gives $\rho_N(r)\leq3(1-r^2)^N$ whenever $(1-r^2)^N\leq\frac12$ and $3(1-r^2)^N\leq(1-r)/N$~\cite[Proposition~\ref{P1-prop:raise} and Corollary~\ref{P1-cor:radius-exp}]{P1}.
""")
fx = L[1653]
fx = edit(fx, ("The deformation of Proposition~\\ref{prop:raise} has the binomial profile $w_n$ and is not a uniform rule.",
               "The deformation that raises the top mass has the binomial profile of the masses and is not a uniform rule."))
out.append(fx)
out.append('')
out.append(lines(1656, 1669))
out.append('')
out.append(r"\section{Open problems}\label{sec:open}")
out.append('')
op = lines(1676, 1689)
op = edit(op, ("and Corollary~\\ref{cor:radius-exp} gives $\\rho_N(r)=O((1-r^2)^N)$ for each fixed $r$;",
               "and~\\cite[Corollary~\\ref{P1-cor:radius-exp}]{P1} gives $\\rho_N(r)=O((1-r^2)^N)$ for each fixed $r$;"),
    ("By Theorem~\\ref{thm:decomp}, any criterion", "By the quadratic decomposition~\\cite[Theorem~\\ref{P1-thm:decomp}]{P1}, any criterion"),
    ("For constant-ratio arrays, Theorem~\\ref{thm:lc} controls the deep triples by inequalities that contain the whole geometric criterion, in particular the Krawtchouk arrays. Theorems~\\ref{thm:lc-vary} and~\\ref{thm:lc-affine} and Proposition~\\ref{prop:lc-quad} extend this to ratios $c_i/(b_i+c_i)$ that increase in the ways described there; other nonconstant ratios remain open.",
     "For constant-ratio arrays, the log-concave Newton criterion~\\cite[Theorem~\\ref{P1-thm:lc}]{P1} controls the deep triples by inequalities that contain the whole geometric criterion, in particular the Krawtchouk arrays, and~\\cite{P2} extends it to ratios $c_i/(b_i+c_i)$ that increase in several ways; other nonconstant ratios remain open."),
    ("First, Corollary~\\ref{cor:radius-exp} gives", "First,~\\cite[Corollary~\\ref{P1-cor:radius-exp}]{P1} gives"))
op = cut_between(op, "For $q\\geq1$ let $G_{N,q,r}$", "can admit both $K_{N,r}$ and $G_{N,q,r}$.",
    "For $q\\geq1$ let $G_{N,q,r}$ be the array \\eqref{eq:parameters}, so that $G_{N,1,r}=K_{N,r}$. The combinations $(1-\\lambda)K_{N,r}+\\lambda G_{N,q,r}$ have $g(N,N;N)<0$ at seven exactly certified parameter choices with $r$ between $2/7$ and $4/5$~\\cite[Section~\\ref{P1-sec:limits}]{P1}, and, in $150$- and $300$-digit arithmetic that is not an exact sign certificate, at $(r,N,q,t)=(1/4,500,3,10)$. At the certified parameters no sufficient criterion whose admitted set is convex, in particular none defined by a system of linear inequalities in the coefficients, can admit both $K_{N,r}$ and $G_{N,q,r}$.")
out.append(op)
out.append(r"""
\section*{AI-use disclosure}

OpenAI Codex was used to develop the proof arguments of Sections~\ref{sec:criterion}--\ref{sec:applications}, search and check source passages, construct exact-arithmetic diagnostics, draft and revise this manuscript, and prepare the Lean translation. Separate AI-assisted reviews checked the algebraic proof, boundary cases, normalizations, and quantitative estimates; these reviews are not human peer review. Anthropic Claude was used to analyse Szwarc's Problem~2 against the survey text, to explore discrete hyperbolic certificates numerically, and to develop and draft Sections~\ref{sec:szwarc}--\ref{sec:limits} together with their exact diagnostics, and it prepared the Lean formalizations of those sections. These sections were reviewed in fourteen rounds by ChatGPT Pro, as part of a longer manuscript (an AI review with independent exact checks, not human peer review); the first round failed, the corrections are recorded in \path{REVIEW.md}, and for each section the final confirmation round on the corrected text returned PASS. The author set the research objective and retains responsibility for publication decisions and the final mathematical claims. No independent human verification is asserted here. ``Machine-verified'' refers only to the Lean theorems listed in the section on code and formalization, with the axioms stated there. Results and prose remarks not covered by those listed Lean theorems are supported by written proofs, AI review and exact numerical checks, but are not machine-verified.

\section*{Code and formalization}

The companion code~\cite{code} contains exact-arithmetic diagnostics for every result (\path{papers/DIAGNOSTICS.md}), among them \path{verify.py}, which compares recurrence-matrix multiplication with multiplication modulo the terminal polynomial, and a Lean~4 development, built and audited by \verb|make lean| and \verb|make axioms|; the audit rejects dependencies outside \path{propext}, \path{Classical.choice} and \path{Quot.sound}. All declarations below have compiled proofs without added axioms or admitted goals. Notes on how each Lean statement matches the text are in \path{papers/FORMALIZATION.md}.
\begin{center}
\begin{tabular}{@{}p{0.36\linewidth}p{0.59\linewidth}@{}}
Result & Lean declaration\\[3pt]
""")
# table rows of paper.tex for the results kept here
keep = ['thm:criterion', 'lem:parameters', 'lem:basis', 'lem:trace', 'lem:three', 'prop:subalgebra', 'lem:normalization',
        'lem:finite', 'lem:margin', 'thm:perturbation', 'cor:nonclassical', 'cor:kraw', 'cor:additional', 'thm:szwarc',
        'lem:edge', 'lem:qthree', 'lem:qmargin', 'lem:stability', 'thm:symmetric', 'cor:symmetric-new', 'thm:low',
        'cor:convex-low', 'thm:all', 'cor:heavy', 'lem:reversal', 'thm:deep', 'thm:palindromic', 'cor:palin',
        'lem:corner-value', 'lem:corner', 'thm:uniform', 'lem:nr', 'cor:analytic-rules', 'prop:families', 'lem:topmass',
        'prop:interior', 'prop:thin', 'cor:radius-order']
rows = []
for l in L[1701:1760]:
    for k in keep:
        if l.startswith(('Theorem~\\ref{%s}' % k, 'Lemma~\\ref{%s}' % k, 'Corollary~\\ref{%s}' % k, 'Proposition~\\ref{%s}' % k)):
            rows.append(l if l.endswith('\\\\[3pt]') else l + '[3pt]')
assert len(rows) == len(keep), (len(rows), len(keep))
rows[-1] = rows[-1][:-len('\\\\[3pt]')]
out.append('\n'.join(rows))
out.append(r"""\end{tabular}
\end{center}

\begin{thebibliography}{9}
""")
bib = {}
for l in L[1766:1778]:
    if l.startswith('\\bibitem{'): bib[l[len('\\bibitem{'):l.index('}')]] = l
for k in ['askey', 'eagleson', 'koelink', 'miclo', 'miclo2015', 'szwarc', 'szwarc2003']:
    out.append(bib[k])
out.append(r"""\bibitem{P1} L. P. Polzer, \emph{A log-concavity criterion for finite nonnegative linearization}, companion paper (2026).
\bibitem{P2} L. P. Polzer, \emph{Increasing ratios in finite nonnegative linearization}, companion paper (2026).""")
out.append(bib['code'].replace('Companion code for Coefficient criteria for finite nonnegative linearization', 'Companion code for finite nonnegative linearization'))
out.append(r"""\end{thebibliography}
\end{document}""")
open(os.path.join(HERE, 'p3.tex'), 'w').write('\n'.join(out) + '\n')
print('wrote p3.tex')
