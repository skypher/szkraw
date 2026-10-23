# Exact-arithmetic diagnostics for the three papers

These are the diagnostic scripts and checks that the full manuscript `paper.tex` listed after its results; the papers cite this file instead. They are checks on random and structured instances, not proofs; the certificate scripts that are part of the proofs of P2 Theorems 5.5 and 5.6 are cited in those proofs, and their fresh-clone run is recorded in `runs/verify/RESULTS.md`. Text is the LaTeX source of `paper.tex`; numbers refer to `paper.tex` (see the concordance in `FORMALIZATION.md`).

## Paper 1

- P1 Lemmas 3.2-3.4 (paper.tex 8.2-8.4): The diagnostics \path{lc_kernel_check.py} verify Lemmas~\ref{lem:kernel-rec}--\ref{lem:detours} and the matching $\mathcal P^2\geq4\mathcal Q$ in exact arithmetic on random log-concave profiles.
- P1 Corollary 4.2, Theorem 4.3, and paper 3, Section 7: The companion source tree contains \path{probe.py} and \path{verify.py}. The command
\begin{quote}\verb|python3 -u verify.py --max-n 7|\end{quote}
compares recurrence-matrix multiplication with direct multiplication modulo the terminal polynomial on exact rational inputs, checks the perturbation lower bounds, and replays two rejected coefficient-profile tests. It also checks Theorem~\ref{thm:szwarc}, the margin of Lemma~\ref{lem:qmargin} and the negative coefficient for $p_0>1/2$ on exact Szwarc arrays, the identities of Lemma~\ref{lem:qthree} in the graded model, and the lower bound of Theorem~\ref{thm:symmetric} on rational symmetric perturbations. These computations are diagnostics and do not replace the proofs at arbitrary size. For Section~\ref{sec:limits}, \path{rigidity_probe.py} checks Lemma~\ref{lem:corner} exactly for $N\leq20$, the predicted failures of Theorem~\ref{thm:uniform}, the boundary layers of Proposition~\ref{prop:families}, the region of Lemma~\ref{lem:nr} and the fixed-$r$ computations, and \path{smallr_probe.py} replays the small-$r$ counterexamples.

- P1 Section 5 (sharpness remark): `runs/sharp/` with commands and outputs in `runs/sharp/RESULTS.md`; `convexity_probe.py` for the combinations of Krawtchouk and geometric arrays.

## Paper 2

- P2 Proposition 3.3 (8.8): `runs/varratio/quadratic.py` (cited in the text).
- P2 Theorem 4.1 (8.9): The diagnostics \path{runs/varratio/affine_verify.py} and \path{runs/varratio/verify_consultH.py} check in exact arithmetic the steps of this proof, the nonnegativity of $M$, the identity $\omega=G\sum_qM^qG\beta$ and property (P) on random profiles with $3\leq N\leq11$, including $\kappa$ at the largest value for which $b$ is nondecreasing.
- P2 Theorem 4.2 (8.11): The diagnostics \path{runs/varratio/verify_consultI.py}, \path{runs/varratio/verify_consultI_poly.py} and \path{runs/varratio/verify_consultI_local.py} check in exact arithmetic \eqref{eq:quad-B}, the summed $B$-detour, \eqref{eq:quad-key}, the detours of $H$, $V$, $W$ and $C'$, the identities of the key inequality, $M\geq0$ and (P) on random members with $4\leq N\leq13$, the certificate \eqref{eq:quad-cert} symbolically, and \eqref{eq:quad-B} on random log-concave local configurations with $\ell\leq200$.
- P2 Theorem 5.1 / Corollary 5.2 (8.12/8.13): The diagnostic \path{runs/varratio/thmQ_check.py} checks in exact arithmetic the formula $\kappa_k=ke_k$, the log-concavity of $\kappa$, Lemma~\ref{lem:lc-ineq} for $\varphi$ with $i=2$, both detours, $M\geq0$ and (P) on random members with $3\leq N\leq10$, including geometric $(\rho_k)$.
- P2 Theorem 5.5 (8.16):
The diagnostics check in exact arithmetic the following.
\begin{itemize}
\item The closed forms of the central sums: \path{runs/varratio/key_S_high.py} and \path{runs/varratio/key_S_low.py}, symbolically for $a\leq8$.
\item The identities and reductions of steps (iii$'$)--(v) on random log-concave $u$: \path{runs/varratio/key_L1_decomp.py}, \path{runs/varratio/key_L1_quad.py}, \path{runs/varratio/key_S20_proof.py} and \path{runs/varratio/key_L2_chain.py}.
\item The Abel tails of every form: \path{runs/varratio/key_L1_quad.py} ($a\leq70$), \path{runs/varratio/key_S20_quad.py} and \path{runs/varratio/key_S20_proof.py} ($a\leq40$).
\item The $\widehat w$ detour: \path{runs/varratio/what_pointwise.py}.
\item (P) on random members, including steep exponential ratios: \path{runs/varratio/steep_exp_test.py} and \path{runs/varratio/g_farfield.py}.
\end{itemize}
- P2 Theorem 5.6 (8.17):
\begin{itemize}
\item The splitting of $\psi_n$, every detour quotient and the key inequality \eqref{eq:cubic-key} on random members with $N\leq16$: \path{runs/cubic/final_ingredients.py}. The minimal quotients found were $9.1$ for $B$, $11.1$ for $V$, $4.8$ for $E$, $23$ for $H$ and $9.9$ for $C'$, and $2.5$ for the key ratio.
\item (P) on random members at the boundary $r\sigma=t\tau$, in full tables for $4\leq N\leq14$ and in the coefficients $g(m,N;k)$ for $15\leq N\leq60$, and at $r\sigma=\frac74t\tau$ for $4\leq N\leq13$ and $15\leq N\leq40$: \path{runs/cubic/c3_property_P.py}.
\item The polarized coefficients behind \eqref{eq:cubic-B}, \eqref{eq:cubic-E} and \eqref{eq:cubic-key}: \path{runs/cubic/kappa_sym.py}, \path{runs/cubic/edetour_polar.py} and \path{runs/cubic/key_polar.py}. The identities of the local decomposition: \path{runs/cubic/phi_loc.py}.
\end{itemize}
- P2 Section 6: `runs/varratio/frontier_examples.py`, `runs/varratio/cubic_lc_test.py`, `runs/varratio/cubic_diag.py` (cited in the text).

## Paper 3

- P3 Sections 2-7: The companion source tree contains \path{probe.py} and \path{verify.py}. The command
\begin{quote}\verb|python3 -u verify.py --max-n 7|\end{quote}
compares recurrence-matrix multiplication with direct multiplication modulo the terminal polynomial on exact rational inputs, checks the perturbation lower bounds, and replays two rejected coefficient-profile tests. It also checks Theorem~\ref{thm:szwarc}, the margin of Lemma~\ref{lem:qmargin} and the negative coefficient for $p_0>1/2$ on exact Szwarc arrays, the identities of Lemma~\ref{lem:qthree} in the graded model, and the lower bound of Theorem~\ref{thm:symmetric} on rational symmetric perturbations. These computations are diagnostics and do not replace the proofs at arbitrary size. For Section~\ref{sec:limits}, \path{rigidity_probe.py} checks Lemma~\ref{lem:corner} exactly for $N\leq20$, the predicted failures of Theorem~\ref{thm:uniform}, the boundary layers of Proposition~\ref{prop:families}, the region of Lemma~\ref{lem:nr} and the fixed-$r$ computations, and \path{smallr_probe.py} replays the small-$r$ counterexamples.

- P3 Section 9: `rigidity_probe.py`, `smallr_probe.py`, `fixedr_probe.py`, `signpattern_probe.py` (cited in the text). `runs/lean_plan/p3_numeric_witnesses.py` recomputes, in exact arithmetic, the negative coefficient used as witness by each Lean statement for the rule and terminal-row failures (lean/Szkraw/RuleCounterexamples.lean).
