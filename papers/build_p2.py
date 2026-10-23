"""Assemble papers/p2.tex (increasing ratios) from paper.tex, lines 796-1426 (Section 8 from Theorem 8.6 on).
Copied verbatim; every change is an exact replacement asserted to match (once, or the stated number of times).
Cut: Proposition 8.10 (contained in Theorem 8.11), the diagnostics paragraphs (moved to papers/DIAGNOSTICS.md).
Cross-references into paper 1 use xr-hyper labels P1-*; run after p1.tex has been compiled."""
import sys as _sys, hashlib as _hl
# FROZEN (2026-10-23): papers/p1.tex, p2.tex, p3.tex are now edited directly; this script is kept as a record of how
# they were first generated from paper.tex at commit ad5eb72. It refuses to run unless called with --regenerate and
# paper.tex is byte-identical to that version (line ranges below refer to it). Regenerating discards direct edits.
_SRC = __import__('os').path.join(__import__('os').path.dirname(__import__('os').path.abspath(__file__)), '..', 'paper.tex')
if '--regenerate' not in _sys.argv or _hl.sha256(open(_SRC, 'rb').read()).hexdigest() != '4e82af43d92cc4296d85f6b852776f85aea61a5a686cb921a289f94f734ad567':
    _sys.exit('build script frozen: the papers are edited directly (see the header of this file)')

import os, re
HERE = os.path.dirname(os.path.abspath(__file__))
L = open(os.path.join(HERE, '..', 'paper.tex')).read().split('\n')
def lines(a, b):
    return '\n'.join(L[a - 1:b])
def edit(text, *pairs):
    for p in pairs:
        old, new = p[0], p[1]; n = p[2] if len(p) > 2 else 1
        assert text.count(old) == n, ('edit count mismatch', text.count(old), n, old[:90])
        text = text.replace(old, new)
    return text
def p1refs(text):
    # references to results of paper 1 (lem:lc-ineq is restated locally in Section 2)
    reps = [('Lemma~\\ref{lem:detours}', '\\cite[Lemma~\\ref{P1-lem:detours}]{P1}'),
            ('Lemma~\\ref{lem:kernel-rec}', '\\cite[Lemma~\\ref{P1-lem:kernel-rec}]{P1}'),
            ('Theorem~\\ref{thm:lc}', '\\cite[Theorem~\\ref{P1-thm:lc}]{P1}'),
            ('Section~\\ref{sec:lc}', '\\cite[Section~\\ref{P1-sec:lc}]{P1}')]
    for a, b in reps: text = text.replace(a, b)
    return text
out = [r"""\newcommand{\papertitle}{Increasing ratios in finite nonnegative linearization}
\newcommand{\papershort}{INCREASING RATIOS IN FINITE LINEARIZATION}
\newcommand{\paperdate}{October 23, 2026}
\input{preamble}
\externaldocument[P1-]{p1}
\begin{document}
\maketitle

\begin{abstract}
For finite stochastic three-term recurrences, the companion paper~\cite{P1} proves nonnegative linearization (property (P)) when the ratio of the diagonal to the downward coefficients is constant and the Newton coefficients of the profile $d_i=b_i+c_i$ are log-concave without internal zeros. We admit ratios $\rho(i)=c_i/d_i$ that increase with the index. Property (P) holds when the Newton coefficients of $b$ are those of $c$ times nonincreasing weights. On profiles with log-concave Newton coefficients and nondecreasing $b$ it holds when $\rho$ is linear or a convex quadratic in the index, when the Newton coefficients of $\rho$ are nonnegative and log-concave without internal zeros, in any degree, and for cubic ratios $r+tx+\tau\binom x2+\sigma\binom x3$ under the single inequality $r\sigma\leq\frac74t\tau$. On profiles of Newton degree at most two, ratios of any degree are admitted when the Newton coefficients of $c$ are log-concave. The proofs resum the moves of a kernel recurrence; the key inequalities for log-concave and cubic ratios are proved with exact computer certificates. A self-contained proof that log-concavity of Newton coefficients is preserved under pointwise products (Walkup's theorem) is included. Nondecreasing $b$ alone, or nonnegative Newton coefficients of the ratio alone, do not suffice.
\vskip5pt
\noindent\textbf{Keywords.}\enspace Finite orthogonal polynomials; nonnegative linearization; log-concave sequences; Newton series; computer-assisted proof.
\vskip5pt
\noindent\textbf{MSC2020 Classification.}\enspace 33C45; 42C05; 05A20.
\end{abstract}

\vskip50pt
\baselineskip=13.5pt
\section{Introduction}\label{sec:introduction}

Szwarc~\cite[\S5, Problem~2]{szwarc} asked for criteria, in the recurrence coefficients, for nonnegative linearization (property (P)) of finite systems of orthogonal polynomials. The companion paper~\cite{P1} answers this for arrays whose diagonal and downward coefficients have a constant ratio: property (P) holds whenever the Newton coefficients of the profile are log-concave without internal zeros. This paper treats ratios $\rho(i)=c_i/(b_i+c_i)$ that increase with $i$.

Section~\ref{sec:setting} recalls the setting and the log-concavity inequality on which all proofs rest. Section~\ref{sec:vary} extends the kernel recurrence of~\cite{P1} to arrays with independent diagonal and downward coefficients and proves property (P) when the Newton coefficients of $b$ are those of $c$ times nonincreasing weights (Theorem~\ref{thm:lc-vary} and Corollary~\ref{cor:lc-vary}), and for arrays that are quadratic in the index (Proposition~\ref{prop:lc-quad}). In general some moves of the recurrence have negative weight; Section~\ref{sec:affine} handles them by a resummation, for ratios that increase linearly (Theorem~\ref{thm:lc-affine}) or as a convex quadratic (Theorem~\ref{thm:lc-quadratic}) on every log-concave Newton profile, under the natural condition that $b$ be nondecreasing. Section~\ref{sec:higher} treats ratios of higher degree: on profiles of Newton degree at most two (Theorem~\ref{thm:lc-lowdeg}), and on every log-concave Newton profile when the Newton coefficients of the ratio are log-concave (Theorem~\ref{thm:lc-general}) or, for cubic ratios, when $r\sigma\leq t\tau$ (Theorem~\ref{thm:lc-cubic}). Proposition~\ref{prop:np}, due to Walkup~\cite{walkup}, shows that log-concavity of Newton coefficients is preserved under pointwise products. Section~\ref{sec:open} records counterexamples and open problems.

The key inequalities of Theorems~\ref{thm:lc-general} and~\ref{thm:lc-cubic} are proved with exact computer certificates; the other numbered results have written proofs and are formalized in Lean~4 (see the section on code and formalization).

\section{Setting}\label{sec:setting}

We use the conventions of~\cite{P1}. An array of real coefficients $(a_i,b_i,c_i)_{0\leq i\leq N}$ satisfies
\begin{equation}\label{eq:basic}
\begin{gathered}
a_0=1,\quad b_0=c_0=0,\quad a_N=0,\quad a_i+b_i+c_i=1,\\
a_i>0\ (i<N),\qquad c_i>0\ (i>0),
\end{gathered}
\end{equation}
and $R_{-1}=0$, $R_0=1$ and $xR_i=a_iR_{i+1}+b_iR_i+c_iR_{i-1}$ $(0\leq i<N)$ define its polynomials, with $R_i(1)=1$. By~\cite[Lemma~\ref{P1-lem:finite}]{P1} the array has a positive orthogonality measure on $N+1$ real points, which include $1$, and on this support $R_mR_n=\sum_kg(m,n;k)R_k$ with $g(m,n;k)=[R_m(J)]_{n,k}$, where $J$ is the tridiagonal recurrence matrix; the array has \emph{nonnegative linearization}, or \emph{property (P)}, if all $g(m,n;k)\geq0$. We write $d_i=b_i+c_i$ for the profile and, for $i\geq1$, $\rho(i)=c_i/d_i$ for the ratio.

The Newton coefficients of a sequence $(u_i)_{0\leq i\leq N}$ are $\Delta^ku(0)=\sum_{i\leq k}(-1)^{k-i}\binom kiu_i$, so that $u_n=\sum_k\binom nk\Delta^ku(0)$. A nonnegative, finitely supported sequence $(u_k)_{k\geq0}$ is \emph{log-concave without internal zeros} if its positive entries form an interval and $u_k^2\geq u_{k-1}u_{k+1}$ for all $k\geq1$. For such a sequence put $f_n(\ell)=\sum_{h\geq0}\binom\ell hu_{n+h}$, and, for integers $p,q\geq0$,
\[
W_{p,q}(\ell,a)=\sum_{n\geq p}\binom{n-p+q}q\binom anf_n(\ell),
\]
with $A_j=W_{2j+1,j}$, $B_j=W_{2j+2,j}$ and $C_j=W_{2j+2,j+1}$ when these are formed from the Newton coefficients of the profile.

\begin{lemma}[\cite{P1}]\label{lem:lc-ineq}
Let $(u_k)_{k\geq0}$ be nonnegative, finitely supported and log-concave without internal zeros. Then $(u_k+u_{k+1})_{k\geq0}$ has the same property, hence so does $(f_n(\ell))_{n\geq0}$ for every $\ell\geq0$, and
\[
f_i(\ell)\,f_l(\ell+1)\geq f_0(\ell+1)\,f_{i+l}(\ell)\qquad(i,l\geq1,\ \ell\geq0).
\]
\end{lemma}
\begin{proof}
"""]
# proof of Lemma 3.3 of P1, adapted to a general sequence
pf = lines(752, 754)
pf = edit(pf,
    ("The sequence $(0,\\nu_1,\\nu_2,\\ldots)$ has this property, and $f_i(\\ell)$ is obtained from it by applying $u\\mapsto v$ $\\ell$ times.",
     "The sequence $(f_n(\\ell))_n$ is obtained from $(u_n)_n$ by applying $u\\mapsto v$ $\\ell$ times."),
    ("$g_0+g_1=f_0(\\ell+1)=d_{\\ell+1}$ gives the claim.", "$g_0+g_1=f_0(\\ell+1)$ gives the claim."))
out.append(pf)
out.append(r"""\end{proof}

For the profile, with $u_k=\nu_k$ and $\nu_0=0$, one has $f_0(\ell)=d_\ell$, and the inequality reads $f_i(\ell)f_l(\ell+1)\geq d_{\ell+1}f_{i+l}(\ell)$. The paper~\cite{P1} proves property (P) for constant ratios by expanding the product coefficients in a kernel $\omega_{\ell,a}$ on $\Omega=\{(\ell,a):\ell,a\geq0,\ \ell+a\leq N\}$, which satisfies a recurrence in $\ell$ whose moves have weights formed from the $W_{p,q}$, and by matching each move of odd index with two-step detours through moves of even index~\cite[Lemmas~\ref{P1-lem:kernel-rec} and~\ref{P1-lem:detours}]{P1}. We extend that argument.

\section{Ratios given by weights}\label{sec:vary}
""")
blk = lines(797, 866)
blk = p1refs(blk)
out.append(blk)
out.append('')
out.append(r"\section{Linearly and quadratically increasing ratios}\label{sec:affine}")
out.append(p1refs(edit(lines(869, 933), ('be as in Section~\\ref{sec:lc}', 'be as in Section~\\ref{sec:setting}'))))
out.append('')
q = lines(951, 1051)
q = edit(q, ("This contains Theorem~\\ref{thm:lc-affine} ($\\tau=0$) and Proposition~\\ref{prop:lc-quadprof}. As there, $b$ is nondecreasing exactly when",
             "This contains Theorem~\\ref{thm:lc-affine} ($\\tau=0$). As in the proof of that theorem, $b_{i+1}-b_i=f_1(i)\\bigl(1-\\rho(i+1)-(t+\\tau i)R_i\\bigr)$ with a nonincreasing bracket, so $b$ is nondecreasing exactly when"))
out.append(p1refs(q))
out.append('')
out.append(r"\section{Ratios of higher degree}\label{sec:higher}")
h = lines(1057, 1082)
h = edit(h, (" The diagnostic \\path{runs/varratio/thmQ_check.py} checks in exact arithmetic the formula $\\kappa_k=ke_k$, the log-concavity of $\\kappa$, Lemma~\\ref{lem:lc-ineq} for $\\varphi$ with $i=2$, both detours, $M\\geq0$ and (P) on random members with $3\\leq N\\leq10$, including geometric $(\\rho_k)$.", ""))
out.append(p1refs(h))
out.append('')
out.append(p1refs(lines(1085, 1310)))
out.append('')
c = lines(1321, 1426)
c = edit(c, (" The diagnostics check in exact arithmetic the following.", " Exact diagnostics for this proof are listed in \\path{papers/DIAGNOSTICS.md}."))
out.append(p1refs(c))
out.append('')
# counterexamples and open problems: paper.tex line 1674 (ratio part)
op = L[1673]
op = edit(op,
    ("The geometric criterion imposes exact equalities, whereas the perturbation criterion provides small neighborhoods. Theorem~\\ref{thm:lc} gives inequalities on the profile that retain the full Krawtchouk range with a constant ratio $b_i/c_i$. ",
     "The criterion of~\\cite{P1} retains the full Krawtchouk range with a constant ratio $b_i/c_i$. "),
    ("and the convex kinked ratio below fails at $N=120$.", "and a convex kinked ratio on the linear profile fails at $N=120$~\\cite{P3}."),
    (" and Theorem~\\ref{thm:lc-quadratic} extends this to increasing convex quadratic ratios.", ", Theorem~\\ref{thm:lc-quadratic} extends this to increasing convex quadratic ratios, and Theorems~\\ref{thm:lc-general} and~\\ref{thm:lc-cubic} to ratios of higher degree."))
out.append(r"""\section{Counterexamples and open problems}\label{sec:open}

""" + op)
out.append(r"""
\section*{AI-use disclosure}

OpenAI Codex and Anthropic Claude were used to develop proof arguments, check source passages, construct exact-arithmetic diagnostics, draft and revise this manuscript, and prepare the Lean formalization. The resummation in the proof of Theorem~\ref{thm:lc-affine}, its key inequality under nondecreasing $b$, and the weighted detour and key inequality in the proof of Theorem~\ref{thm:lc-quadratic} arose in research consultations with ChatGPT Pro; the exact checks were completed with Claude, which also prepared the Lean formalizations. Theorem~\ref{thm:lc-lowdeg}, Corollary~\ref{cor:lc-lowdeg}, Theorems~\ref{thm:lc-general} and~\ref{thm:lc-cubic} and Lemma~\ref{lem:abel-weights} were found and proved with Claude, without research consultation; Proposition~\ref{prop:np}, which is due to Walkup, was rederived with Claude together with the self-contained proof given here. Every result was reviewed by ChatGPT Pro, as part of a longer manuscript (an AI review with independent exact checks, not human peer review); the review rounds and their corrections are recorded in \path{REVIEW.md}, and each returned PASS or PASS WITH MINOR FIXES, with the fixes applied. For Theorems~\ref{thm:lc-general} and~\ref{thm:lc-cubic} the reviewer reran transcribed copies of the certificate scripts; the scripts were also run unmodified from a fresh clone of the companion code at the cited revision, and all of them passed (\path{runs/verify/RESULTS.md}). The author set the research objective and retains responsibility for publication decisions and the final mathematical claims. No independent human verification is asserted here. ``Machine-verified'' refers only to the Lean theorems listed in the section on code and formalization; Theorems~\ref{thm:lc-general} and~\ref{thm:lc-cubic} are not machine-verified.

\section*{Code and formalization}

The companion code~\cite{code} contains the certificate scripts cited in the proofs of Theorems~\ref{thm:lc-general} and~\ref{thm:lc-cubic}, exact-arithmetic diagnostics for every result (\path{papers/DIAGNOSTICS.md}), and a Lean~4 development, built and audited by \verb|make lean| and \verb|make axioms|; the audit rejects dependencies outside \path{propext}, \path{Classical.choice} and \path{Quot.sound}. The declarations below have compiled proofs without added axioms or admitted goals. Notes on how each Lean statement matches the text are in \path{papers/FORMALIZATION.md}.
\begin{center}
\begin{tabular}{@{}p{0.36\linewidth}p{0.59\linewidth}@{}}
Result & Lean declaration\\[3pt]
Theorem~\ref{thm:lc-vary}: varying ratio & \path{Szkraw.varyratio_matrix}\\[3pt]
Corollary~\ref{cor:lc-vary}: nonincreasing weights & \path{Szkraw.varyratio_weights}\\[3pt]
Proposition~\ref{prop:lc-quad}: quadratic arrays & \path{Szkraw.quadratic_matrix}\\[3pt]
Theorem~\ref{thm:lc-affine}: linearly increasing ratio & \path{Szkraw.affine_matrix}, \path{Szkraw.affine_bmono_iff}\\[3pt]
Remarks after Theorem~\ref{thm:lc-affine} & \path{Szkraw.affine_range_remarks}, \path{Szkraw.profile_last_le}, \path{Szkraw.affEx_remark}\\[3pt]
Theorem~\ref{thm:lc-quadratic}: convex quadratic ratio & \path{Szkraw.quadratic_ratio_matrix}, \path{Szkraw.quadratic_bmono_iff}\\[3pt]
Remarks on Theorem~\ref{thm:lc-quadratic} & \path{Szkraw.quadExample_remark}, \path{Szkraw.quadB_unit_fails}\\[3pt]
Theorem~\ref{thm:lc-lowdeg}: low-degree profiles & \path{Szkraw.lowdeg_matrix}\\[3pt]
Corollary~\ref{cor:lc-lowdeg} & \path{Szkraw.lowdeg_newton_lc}, \path{Szkraw.lowdeg_ratio_matrix}\\[3pt]
Proposition~\ref{prop:np}: products of Newton sequences & \path{Szkraw.newton_product_LCNZ}\\[3pt]
Lemma~\ref{lem:abel-weights} & \path{Szkraw.abel_weight}\\[3pt]
Section~\ref{sec:open}: the counterexamples with $N=3$ and the cubic counterexample with $N=4$ & \path{Szkraw.openEx1_fails}, \path{Szkraw.openEx2_fails}, \path{Szkraw.cubic_ratio_fails}
\end{tabular}
\end{center}
The Lean proof of Theorem~\ref{thm:lc-general} is in progress: its assembly from the key inequality \eqref{eq:G-key} is formalized, the key inequality is not.

\begin{thebibliography}{9}
""")
bib = {}
for l in L[1766:1778]:
    if l.startswith('\\bibitem{'): bib[l[len('\\bibitem{'):l.index('}')]] = l
out.append(r"""\bibitem{P1} L. P. Polzer, \emph{A log-concavity criterion for finite nonnegative linearization}, companion paper (2026).""")
out.append(r"""\bibitem{P3} L. P. Polzer, \emph{Exact and perturbative criteria for finite nonnegative linearization}, companion paper (2026).""")
for k in ['szwarc', 'walkup', 'wangyeh']:
    out.append(bib[k])
out.append(bib['code'].replace('Companion code for Coefficient criteria for finite nonnegative linearization', 'Companion code for finite nonnegative linearization'))
out.append(r"""\end{thebibliography}
\end{document}""")
open(os.path.join(HERE, 'p2.tex'), 'w').write('\n'.join(out) + '\n')
print('wrote p2.tex')
