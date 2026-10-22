# Independent review, round 2: do the Lean statements say what the paper says?

You are an independent reviewer for a mathematics paper on nonnegative linearization of finite orthogonal polynomial systems. **Your task is not to check proofs**; Lean has checked them. Check whether each Lean *statement* faithfully expresses the corresponding paper statement, and whether the paper's code-and-formalization section describes the formalized scope accurately.

Round 1 (previous review) passed Theorems 7.1, 7.8, 7.10, 7.12, 7.15, 7.16 and 8.1, Corollaries 7.9, 7.11, 7.13 and 7.17, and Lemma 7.14, with two text fixes, which have been applied. This round covers:
- **(a)** Theorem 2.1 (`geometric_criterion` : `Stmt_geometric`) and Theorem 5.3 (`perturbation_criterion` : `Stmt_perturbation`), which were not supplied in round 1;
- **(b)** the newly formalized Lemma 7.4 (`szwarc_margin`), Lemma 7.5 (`stability`), Theorem 7.6 (`symmetric_criterion`) and Corollary 7.7 (`symmetric_new`);
- **(c)** the updated scope text.

Acceptance rule:
- A Lean statement is acceptable if its hypotheses are equivalent to or weaker than the paper's, and its conclusion is equivalent to or stronger than the paper's, under the stated conventions.
- Report every place where the hypotheses are stronger or the conclusion weaker.
- Report every index range, normalization or convention that differs in a way that matters.
- Report any part of a paper statement that is not covered while the paper does not say so.

Conventions:
- `Coefficients N` holds functions a, b, c : ℕ → ℝ; only the indices 0..N matter.
- `Admissible v` is the paper's (2.1).
- `productMatrix v m = R_m(J)`; its entry (n,k) is g(m,n;k) (Lemma 5.1).
- `MatrixPositivity v` means all g(m,n;k) ≥ 0 for m, n, k ≤ N.
- `FiniteRealization v` packages: the positive measure on N+1 distinct points, the orthogonality, R_m(1) = 1, the terminal relation, the product identities on the support, and Σ_k g(m,n;k) = 1.
- `Triangle m n k` means |m−n| ≤ k ≤ m+n.
- `szwarcCoefficients N p` is the array (7.2) on 0..2N.
- `krawCoefficients N r` has a_i = (N−i)/N, b_i = (1−r)i/N and c_i = ri/N.
- `geometricCoefficients N p q` is the Lean parametrization of (2.3), with p = 1/r.

Answer format:
1. A table: paper result | Lean declaration | MATCH / MATCH, SCOPE NOTED / MISMATCH | reason.
2. The exact fixes.
3. A scope-text check.
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

#### thm:criterion
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
```

#### lem:parameters
```latex
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

#### lem:finite
```latex
\begin{lemma}[Finite recurrence realization and triangle support]\label{lem:finite}
Every recurrence satisfying \eqref{eq:basic} has a positive orthogonality measure on exactly $N+1$ real points. If $J$ is its tridiagonal recurrence matrix, then its finite product coefficients satisfy
\begin{equation}\label{eq:matrix-product}
g(m,n;k)=[R_m(J)]_{n,k}.
\end{equation}
They vanish unless $|m-n|\leq k\leq\min(m+n,N)$, regardless of their signs inside this interval.
\end{lemma}
```

#### Lemma (Krawtchouk margin, Section 5)
```latex
\begin{lemma}[A uniform positive margin in the asymmetric case]\label{lem:margin}
For the Krawtchouk recurrence \eqref{eq:parameters} with $q=1$ and $0<r<1$, put $s=\min(r,1-r)$. Every coefficient in its triangle support obeys
\begin{equation}\label{eq:margin}
g(m,n;k)\geq (s/4)^N\quad\text{if }|m-n|\leq k\leq\min(m+n,N).
\end{equation}
\end{lemma}
```

#### Theorem 5.3 (perturbation)
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
Then the finite system has nonnegative linearization. Throughout its triangle support,
\[
\widetilde g(m,n;k)\geq\tfrac12(s/4)^N.
\]
The product coefficients sum to one.
\end{theorem}
```

#### Szwarc array (7.2)
```latex
Put $M=2N$, $R_{2n}(t)=Q_{2n}(\sqrt Nt)$ and $R_{2n-1}(t)=\sqrt N\,Q_{2n-1}(\sqrt Nt)$. Substitution in \eqref{eq:szwarc-q} shows that the $R_k$ satisfy \eqref{eq:recurrence}, with $N$ replaced by $M$, for the array
\begin{equation}\label{eq:qarray}
b_k=0,\qquad
(a_{2n},c_{2n})=\Big(\frac{N-n}{N},\frac nN\Big),\qquad
(a_{2n-1},c_{2n-1})=(1-p_0,\,p_0).
\end{equation}
It satisfies \eqref{eq:basic} with $M$ in place of $N$ whenever $0<p_0<1$. The two normalizations differ by positive factors and a positive dilation, so they have the same product coefficients up to positive factors.
```

#### thm:szwarc
```latex
\begin{theorem}[Szwarc's quadratic system]\label{thm:szwarc}
Let $N\geq1$ and $0<p_0\leq1/2$. The array \eqref{eq:qarray} has a symmetric positive orthogonality measure on $2N+1$ points, and for all $0\leq m,n\leq 2N$
\[
R_mR_n=\sum_{k=0}^{2N}g(m,n;k)R_k,\qquad g(m,n;k)\geq0,\qquad\sum_k g(m,n;k)=1
\]
on that support. If $1/2<p_0<1$, then $g(2,2;2)<0$.
\end{theorem}
```

#### lem:qmargin
```latex
\begin{lemma}[Margin for the quadratic system]\label{lem:qmargin}
Let $0<p_0<1/2$ and $s=\min(r,1-r)$. For the array \eqref{eq:qarray},
\[
g(m,n;k)\geq(rs/8)^N\qquad\text{whenever }|m-n|\leq k\leq m+n\text{ and }m+n+k\text{ is even}.
\]
All other coefficients vanish.
\end{lemma}
```

#### lem:stability
```latex
\begin{lemma}[Stability of a reference with a margin]\label{lem:stability}
Let $a,b,c$ satisfy \eqref{eq:basic} on the indices $0,\ldots,M$, have nonnegative linearization, and satisfy $a_i\geq\alpha$ for $i<M$, where $0<\alpha\leq1$. Suppose $g(m,n;k)\geq\delta>0$ on a set $\Sigma$ of index triples. Let $\widetilde a,\widetilde b,\widetilde c$ satisfy \eqref{eq:basic}, with $\widetilde b_i\geq0$, and differ from $a,b,c$ by at most $\eta$ in every entry. If $\eta\leq\alpha/2$ and $\eta(8/\alpha)^M\leq\delta/2$, then $|\widetilde g(m,n;k)-g(m,n;k)|\leq\delta/2$ for all $m,n,k$; in particular $\widetilde g\geq\delta/2$ on $\Sigma$.
\end{lemma}
```

#### thm:symmetric
```latex
\begin{theorem}[Symmetric criterion near Szwarc's system]\label{thm:symmetric}
Let $N\geq1$, $0<p_0<1/2$, $r=p_0/(1-p_0)$, $s=\min(r,1-r)$, and
\[
\eta=\frac12\Big(\frac{rs}8\Big)^N(16N)^{-2N}.
\]
Let $c_k$ be the downward coefficients in \eqref{eq:qarray}. Take real numbers $\widetilde c_1,\ldots,\widetilde c_{2N-1}$ with $|\widetilde c_k-c_k|\leq\eta$, and put $\widetilde c_0=0$, $\widetilde c_{2N}=1$, $\widetilde b_k=0$ and $\widetilde a_k=1-\widetilde c_k$. The resulting symmetric finite system has nonnegative linearization with sums one. Moreover $\widetilde g(m,n;k)\geq\frac12(rs/8)^N$ whenever $|m-n|\leq k\leq m+n$ and $m+n+k$ is even, and $\widetilde g(m,n;k)=0$ otherwise.
\end{theorem}
```

#### cor:symmetric-new
```latex
\begin{corollary}[Symmetric systems outside both families]\label{cor:symmetric-new}
For $N\geq2$, $0<p_0<1/2$ and $0<h\leq\eta$, the array obtained from \eqref{eq:qarray} by $c_1\mapsto p_0+h$, $a_1\mapsto1-p_0-h$ has nonnegative linearization. It is neither of the form \eqref{eq:qarray} nor of the form \eqref{eq:parameters}. More generally, Theorem~\ref{thm:symmetric} admits a relatively open set of symmetric stochastic arrays, with $2N-1$ free coefficients, around each array \eqref{eq:qarray} with $0<p_0<1/2$.
\end{corollary}
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
Theorem~\ref{thm:szwarc}: Szwarc's quadratic system & \path{Szkraw.szwarc_system}, \path{Szkraw.szwarc_sharp}\\[3pt]
Lemma~\ref{lem:qmargin}: margin for the quadratic system & \path{Szkraw.szwarc_margin}\\[3pt]
Lemma~\ref{lem:stability}: stability of a reference with a margin & \path{Szkraw.stability}\\[3pt]
Theorem~\ref{thm:symmetric}: symmetric criterion & \path{Szkraw.symmetric_criterion}\\[3pt]
Corollary~\ref{cor:symmetric-new}: symmetric systems outside both families & \path{Szkraw.symmetric_new}\\[3pt]
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
The first includes a positive finite orthogonality measure, distinct support points, the terminal relation, and all finite product identities. The second includes the explicit radius, positive triangle margin, and exact zeros outside the triangle. The entries for Section~\ref{sec:szwarc} state nonnegativity of the coefficients $g(m,n;k)$: for Theorem~\ref{thm:low} and Corollary~\ref{cor:convex-low} on all triples with two indices of sum at most $N$, and for Theorems~\ref{thm:all}, \ref{thm:deep} and~\ref{thm:palindromic} and Corollaries~\ref{cor:heavy} and~\ref{cor:palin} on all triples. Lemma~\ref{lem:reversal} and the identities of Theorem~\ref{thm:deep} are stated for the matrices $R_m(J)$ and $R'_t(J)=\Pi R'_t(\Pi J\Pi)\Pi$. Theorem~\ref{thm:szwarc} is proved in Lean through Corollary~\ref{cor:parity} with $q=1$, and Lemma~\ref{lem:qmargin} through the decomposition, whose components are Krawtchouk arrays; the symmetry of the measure in Theorem~\ref{thm:szwarc} is not formalized. In Corollary~\ref{cor:symmetric-new}, ``not of the form \eqref{eq:parameters}'' is formalized as the failure of the hypotheses of Theorem~\ref{thm:criterion} and as disagreement with every array \eqref{eq:parameters} in the Lean parametrization; its last sentence is Theorem~\ref{thm:symmetric}. For Corollary~\ref{cor:parity}, when $N\geq2$, Lean proves that both normalized components satisfy the hypotheses of Theorem~\ref{thm:criterion}; \path{Szkraw.parity_split} also covers $N=1$, where the odd component is the constant polynomial alone. The identification of the parameters through Lemma~\ref{lem:parameters} is not formalized. In Theorem~\ref{thm:decomp} the identity for $g(2a,2b+1;2c+1)$ is stated with the unnormalized odd component, which has the same product coefficients (\path{Szkraw.product_normalize}). The finite realization holds for every array satisfying \eqref{eq:basic} (\path{Szkraw.finite_realization}). The proofs formalize the cone argument and the identity $g(m,n;k)\int R_k^2\,d\mu=g(m,k;n)\int R_n^2\,d\mu$ in matrix form. The entry for Theorem~\ref{thm:lc} includes the same finite realization as the first and the nonnegativity of every coefficient $g(m,n;k)$; its proof formalizes Lemmas~\ref{lem:lc-ineq} and~\ref{lem:detours}, the operator induction, and Lemma~\ref{lem:kernel-rec} in converse form: the solution of~\eqref{eq:kernel-rec} yields the linearization coefficients. The remark after the proof of Theorem~\ref{thm:lc} (nonnegative coefficients of the two-parameter system and nonnegative Bernstein coefficients in $r$) is not formalized. All of them have compiled proofs without added axioms or admitted goals; the axiom audit reports only \path{propext}, \path{Classical.choice} and \path{Quot.sound}. The other results of Section~\ref{sec:szwarc} have not yet been formalized; formalizing them is planned.

```

#### AI-use disclosure
```latex
\section*{AI-use disclosure}

OpenAI Codex was used to develop the proof arguments, search and check source passages, construct exact-arithmetic diagnostics, draft and revise this manuscript, and prepare the Lean translation. Separate AI-assisted reviews checked the algebraic proof, boundary cases, normalizations, and quantitative estimates; these reviews are not human peer review. Anthropic Claude was used to analyse Szwarc's Problem~2 against the survey text, to explore discrete hyperbolic certificates numerically, and to develop and draft Sections~\ref{sec:szwarc}, \ref{sec:lc} and~\ref{sec:limits} together with their exact diagnostics. The kernel recurrence and the operator inequality of Section~\ref{sec:lc} arose in research consultations with ChatGPT Pro; the closed form of the recurrence for every degree and the exact checks were completed with Claude, which also prepared the Lean formalizations of Theorem~\ref{thm:lc} and of the results of Section~\ref{sec:szwarc} listed in the section on code and formalization. The review of Section~\ref{sec:lc} was therefore carried out by the same system that proposed its key steps. These sections were then reviewed in fourteen rounds by ChatGPT Pro (an AI review with independent exact checks, not human peer review); the first round failed, the corrections are recorded in \path{REVIEW.md}, and for each section the final confirmation round on the corrected text returned PASS. The author set the research objective and retains responsibility for publication decisions and the final mathematical claims. No independent human verification is asserted here. ``Machine-verified'' refers only to the Lean theorems listed in the section on code and formalization, with the axioms stated there. Other results, including Lemmas~\ref{lem:edge} and~\ref{lem:qthree} of Section~\ref{sec:szwarc}, the symmetry of the measure in Theorem~\ref{thm:szwarc}, the parameter identification in Corollary~\ref{cor:parity}, and the remark after the proof of Theorem~\ref{thm:lc}, are supported by written proofs, AI review and exact numerical checks, but are not machine-verified.
```

## Part B. Lean statements (types only)

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


noncomputable def perturbationRadius (N : ℕ) (r : ℝ) : ℝ :=
  (1 / 2 : ℝ) * (min r (1-r) / (32 * N)) ^ N


def CloseToKrawtchouk {N : ℕ} (v : Coefficients N) (r : ℝ) : Prop :=
  (∀ i, i ≤ N → 0 ≤ v.b i) ∧
  ∀ i, i ≤ N →
    |v.a i - ((N : ℝ) - i) / N| ≤ perturbationRadius N r ∧
    |v.b i - ((1-r) * i) / N| ≤ perturbationRadius N r ∧
    |v.c i - (r * i) / N| ≤ perturbationRadius N r


/-- Full geometric criterion: discrete realization and positivity, with no
realization or positivity hypotheses moved to the caller. -/
def Stmt_geometric : Prop :=
  ∀ (N : ℕ) (v : Coefficients N), Admissible v → Geometric v →
    FiniteRealization v ∧ MatrixPositivity v


def Triangle (m n k : ℕ) : Prop := m ≤ n+k ∧ n ≤ m+k ∧ k ≤ m+n


def PerturbationMargin {N : ℕ} (v : Coefficients N) (r : ℝ) : Prop :=
  ∀ (m : ℕ) (n k : Fin (N+1)), m ≤ N →
    (Triangle m n.val k.val →
      (1/2 : ℝ)*(min r (1-r)/4)^N ≤ productMatrix v m n k) ∧
    (¬ Triangle m n.val k.val → productMatrix v m n k = 0)


/-- Full perturbation criterion at the stated coefficient radius. -/
def Stmt_perturbation : Prop :=
  ∀ (N : ℕ) (v : Coefficients N) (r : ℝ),
    Admissible v → 0 < r → r < 1 → CloseToKrawtchouk v r →
    FiniteRealization v ∧ MatrixPositivity v ∧ PerturbationMargin v r


```
### lean/Szkraw/GeometricCriterion.lean
```lean
/-- The full geometric recurrence criterion, including its finite spectral realization. -/
theorem geometric_criterion : Stmt_geometric := …

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
### lean/Szkraw/AllProducts.lean
```lean
/-- The product coefficients `g(m,n;k)` for fixed `k`, extended by zero off the square. -/
noncomputable def Gk (v : Coefficients N) (k : Fin (N + 1)) (m n : ℕ) : ℝ :=
  if h : m ≤ N ∧ n ≤ N then productMatrix v m ⟨n, by omega⟩ k else 0


```
### lean/Szkraw/ParitySplit.lean
```lean
/-- Szwarc's array (7.2): `b ≡ 0`, `(a_{2n}, c_{2n}) = ((N-n)/N, n/N)`, `(a_{2n-1}, c_{2n-1}) = (1-p_0, p_0)`. -/
noncomputable def szwarcCoefficients (N : ℕ) (p : ℝ) : Coefficients (2 * N) :=
  ⟨fun k => if k % 2 = 0 then ((N : ℝ) - ((k / 2 : ℕ) : ℝ)) / N else 1 - p,
   fun _ => 0,
   fun k => if k % 2 = 0 then ((k / 2 : ℕ) : ℝ) / N else p⟩


```
### lean/Szkraw/Stability.lean
```lean
/-- **Lemma 7.5** (Stability of a reference with a margin). -/
def Stmt_stability : Prop :=
  ∀ (M : ℕ) (v w : Coefficients M) (α δ η : ℝ) (Sig : ℕ → ℕ → ℕ → Prop),
    Admissible v → MatrixPositivity v → 0 < α → α ≤ 1 → (∀ i, i < M → α ≤ v.a i) →
    0 < δ → (∀ m, m ≤ M → ∀ n k : Fin (M + 1), Sig m n k → δ ≤ productMatrix v m n k) →
    Admissible w → (∀ i, i ≤ M → 0 ≤ w.b i) →
    (∀ i, i ≤ M → |w.a i - v.a i| ≤ η ∧ |w.b i - v.b i| ≤ η ∧ |w.c i - v.c i| ≤ η) →
    η ≤ α / 2 → η * (8 / α) ^ M ≤ δ / 2 →
    (∀ m, m ≤ M → ∀ n k : Fin (M + 1), |productMatrix w m n k - productMatrix v m n k| ≤ δ / 2) ∧
    (∀ m, m ≤ M → ∀ n k : Fin (M + 1), Sig m n k → δ / 2 ≤ productMatrix w m n k)


theorem stability : Stmt_stability := …

```
### lean/Szkraw/SzwarcMargin.lean
```lean
/-- **Lemma 7.4** (Margin for the quadratic system). -/
def Stmt_szwarc_margin : Prop :=
  ∀ (N : ℕ), 1 ≤ N → ∀ p : ℝ, 0 < p → p < 1 / 2 →
    ∀ m, m ≤ 2 * N → ∀ n k : Fin (2 * N + 1),
      ((Triangle m n.val k.val ∧ (m + n.val + k.val) % 2 = 0) →
        (p / (1 - p) * min (p / (1 - p)) (1 - p / (1 - p)) / 8) ^ N ≤
          productMatrix (szwarcCoefficients N p) m n k) ∧
      (¬(Triangle m n.val k.val ∧ (m + n.val + k.val) % 2 = 0) →
        productMatrix (szwarcCoefficients N p) m n k = 0)


theorem szwarc_margin : Stmt_szwarc_margin := …

/-- The radius `η = ½ (rs/8)^N (16N)^{-2N}` of Theorem 7.6. -/
noncomputable def symEta (N : ℕ) (p : ℝ) : ℝ :=
  (1 / 2) * (p / (1 - p) * min (p / (1 - p)) (1 - p / (1 - p)) / 8) ^ N / (16 * (N : ℝ)) ^ (2 * N)


/-- **Theorem 7.6** (Symmetric criterion near Szwarc's system). -/
def Stmt_symmetric : Prop :=
  ∀ (N : ℕ), 1 ≤ N → ∀ p : ℝ, 0 < p → p < 1 / 2 → ∀ w : Coefficients (2 * N),
    (∀ k, k ≤ 2 * N → w.b k = 0) → (∀ k, k ≤ 2 * N → w.a k = 1 - w.c k) → w.c 0 = 0 →
    w.c (2 * N) = 1 →
    (∀ k, 1 ≤ k → k + 1 ≤ 2 * N → |w.c k - (szwarcCoefficients N p).c k| ≤ symEta N p) →
    Admissible w ∧ FiniteRealization w ∧ MatrixPositivity w ∧
    (∀ m, m ≤ 2 * N → ∀ n k : Fin (2 * N + 1), Triangle m n.val k.val ∧ (m + n.val + k.val) % 2 = 0 →
      (1 / 2) * (p / (1 - p) * min (p / (1 - p)) (1 - p / (1 - p)) / 8) ^ N ≤ productMatrix w m n k) ∧
    (∀ m, m ≤ 2 * N → ∀ n k : Fin (2 * N + 1), ¬(Triangle m n.val k.val ∧ (m + n.val + k.val) % 2 = 0) →
      productMatrix w m n k = 0)


theorem symmetric_criterion : Stmt_symmetric := …

/-- The array of Corollary 7.7: (7.2) with `c_1 ↦ p_0 + h`, `a_1 ↦ 1 - p_0 - h`. -/
noncomputable def perturbedSzwarc (N : ℕ) (p h : ℝ) : Coefficients (2 * N) :=
  ⟨fun k => if k = 1 then 1 - p - h else (szwarcCoefficients N p).a k,
   fun k => (szwarcCoefficients N p).b k,
   fun k => if k = 1 then p + h else (szwarcCoefficients N p).c k⟩


/-- **Corollary 7.7** (Symmetric systems outside both families). -/
theorem symmetric_new (N : ℕ) (hN : 2 ≤ N) (p : ℝ) (hp : 0 < p) (hp2 : p < 1 / 2) (h : ℝ)
    (hh : 0 < h) (hhη : h ≤ symEta N p) :
    MatrixPositivity (perturbedSzwarc N p h) ∧
    (∀ p' : ℝ, ¬ ∀ k, k ≤ 2 * N → (perturbedSzwarc N p h).c k = (szwarcCoefficients N p').c k) ∧
    ¬ Geometric (perturbedSzwarc N p h) ∧
    (∀ p' q' : ℝ, 1 ≤ p' → 1 ≤ q' → ¬ ∀ k, k ≤ 2 * N →
      (perturbedSzwarc N p h).b k = (geometricCoefficients (2 * N) p' q').b k ∧
      (perturbedSzwarc N p h).c k = (geometricCoefficients (2 * N) p' q').c k) := …

```
### lean/Szkraw/KrawtchoukMargin.lean
```lean
/-- The full quantitative perturbation theorem, including realization and exact support. -/
theorem perturbation_criterion : Stmt_perturbation :=
```