# Independent review, round 3: do the Lean statements say what the paper says?

As in rounds 1 and 2 (both PASS WITH MINOR FIXES, fixes applied), **do not check proofs**. Check only whether each Lean statement faithfully expresses the paper statement, under the acceptance rule: Lean hypotheses equivalent to or weaker than the paper's, and Lean conclusion equivalent to or stronger.

This round covers declarations added after round 2:
- **Theorem 7.1 in full**: `szwarc_full : Stmt_szwarc_full`. It adds the symmetry of the measure through `realization_symmetric`, which holds for every finite realization (`IsRealization`, the body of `FiniteRealization`) of an admissible array with b ≡ 0. The sharpness part is `szwarc_sharp`, reviewed in round 1.
- **Corollary 7.9, parameter identification**: `ps_even_params`, `ps_odd_params` (and `ps_d_formula`). Note that `geometricCoefficients N p q` is the Lean parametrization of (2.3) with p = 1/r: a_i = q^i[N−i]_q/[N]_q, b_i = (p−1)[i]_q/(p[N]_q), c_i = [i]_q/(p[N]_q).
- Also check the updated scope sentences of the code-and-formalization section for Theorem 7.1 and Corollary 7.9.

Conventions as before:
- `Admissible v` is (2.1).
- `productMatrix v m` has entry (n,k) = g(m,n;k).
- `MatrixPositivity v` means g ≥ 0 on all triples.
- `szwarcCoefficients N p` is (7.2) on 0..2N.
- `ParitySplit v p₀ q` is hypotheses (i)–(ii) of Corollary 7.9, with q ≥ 1.
- `normalize` is the affine normalization of Theorem 7.8.

Answer format: a table (paper claim | Lean declaration | MATCH / MATCH, SCOPE NOTED / MISMATCH | reason), exact fixes, and an overall verdict (PASS / PASS WITH MINOR FIXES / FAIL). Be terse.

## Part A. Paper statements

#### Conventions
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

#### Lemma 2.2 and Theorem 2.1
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

#### Theorem 7.1
```latex
\begin{theorem}[Szwarc's quadratic system]\label{thm:szwarc}
Let $N\geq1$ and $0<p_0\leq1/2$. The array \eqref{eq:qarray} has a symmetric positive orthogonality measure on $2N+1$ points, and for all $0\leq m,n\leq 2N$
\[
R_mR_n=\sum_{k=0}^{2N}g(m,n;k)R_k,\qquad g(m,n;k)\geq0,\qquad\sum_k g(m,n;k)=1
\]
on that support. If $1/2<p_0<1$, then $g(2,2;2)<0$.
\end{theorem}
```

#### Theorem 7.8 (for the normalization)
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

#### Corollary 7.9
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
Theorem~\ref{thm:lc}: log-concave Newton criterion & \path{Szkraw.logconcave_criterion}
\end{tabular}
\end{center}
The first includes a positive finite orthogonality measure, distinct support points, the terminal relation, and all finite product identities. The second includes the explicit radius, positive triangle margin, and exact zeros outside the triangle. The entries for Section~\ref{sec:szwarc} state nonnegativity of the coefficients $g(m,n;k)$: for Theorem~\ref{thm:low} and Corollary~\ref{cor:convex-low} on all triples with two indices of sum at most $N$, and for Theorems~\ref{thm:all}, \ref{thm:deep} and~\ref{thm:palindromic} and Corollaries~\ref{cor:heavy} and~\ref{cor:palin} on all triples. Lemma~\ref{lem:reversal} and the identities of Theorem~\ref{thm:deep} are stated for the matrices $R_m(J)$ and $R'_t(J)=\Pi R'_t(\Pi J\Pi)\Pi$. Theorem~\ref{thm:szwarc} is proved in Lean through Corollary~\ref{cor:parity} with $q=1$, and Lemma~\ref{lem:qmargin} through the decomposition, whose components are Krawtchouk arrays; the symmetry of its measure holds for every finite realization of an array with $b\equiv0$ (\path{Szkraw.realization_symmetric}). In Corollary~\ref{cor:symmetric-new}, ``not of the form \eqref{eq:parameters}'' is formalized as the failure of the hypotheses of Theorem~\ref{thm:criterion} and as disagreement with every array \eqref{eq:parameters} in the Lean parametrization; its last sentence follows from the explicit coefficient box of positive radius in \path{Szkraw.symmetric_criterion}; openness and dimension are not stated separately in Lean. For Corollary~\ref{cor:parity}, when $N\geq2$, Lean proves that both normalized components satisfy the hypotheses of Theorem~\ref{thm:criterion} and are the arrays \eqref{eq:parameters} with parameters $(N,q,r)$ and $(N-1,q,r/q)$ (\path{Szkraw.ps_even_params}, \path{Szkraw.ps_odd_params}); \path{Szkraw.parity_split} also covers $N=1$, where the odd component is the constant polynomial alone. In Theorem~\ref{thm:decomp} the identity for $g(2a,2b+1;2c+1)$ is stated with the unnormalized odd component, which has the same product coefficients (\path{Szkraw.product_normalize}). The finite realization holds for every array satisfying \eqref{eq:basic} (\path{Szkraw.finite_realization}). The proofs formalize the cone argument and the identity $g(m,n;k)\int R_k^2\,d\mu=g(m,k;n)\int R_n^2\,d\mu$ in matrix form. The entry for Theorem~\ref{thm:lc} includes the same finite realization as the first and the nonnegativity of every coefficient $g(m,n;k)$; its proof formalizes Lemmas~\ref{lem:lc-ineq} and~\ref{lem:detours}, the operator induction, and Lemma~\ref{lem:kernel-rec} in converse form: the solution of~\eqref{eq:kernel-rec} yields the linearization coefficients. The remark after the proof of Theorem~\ref{thm:lc} (nonnegative coefficients of the two-parameter system and nonnegative Bernstein coefficients in $r$) is not formalized. All of them have compiled proofs without added axioms or admitted goals; the axiom audit reports only \path{propext}, \path{Classical.choice} and \path{Quot.sound}. The other results of Section~\ref{sec:szwarc} have not yet been formalized; formalizing them is planned.

```

## Part B. Lean statements

### lean/Szkraw/SymmetricMeasure.lean
```lean
/-- The data of a finite realization (the body of `FiniteRealization`). -/
def IsRealization (v : Coefficients N) (x w : Fin (N + 1) → ℝ) : Prop :=
  Function.Injective x ∧
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


theorem finiteRealization_iff (v : Coefficients N) :
    FiniteRealization v ↔ ∃ x w, IsRealization v x w := Iff.rfl

/-- **Theorem 7.1**, symmetry of the measure: every finite realization of an array with `b ≡ 0` is
symmetric: the support is invariant under `x ↦ -x`, with equal weights at `x` and `-x`. -/
theorem realization_symmetric (v : Coefficients N) (hv : Admissible v) (hb : ∀ i, i ≤ N → v.b i = 0)
    (x w : Fin (N + 1) → ℝ) (hr : IsRealization v x w) :
    ∀ t, ∃ t', x t' = -x t ∧ w t' = w t := …

/-- **Theorem 7.1** in full: for `0 < p_0 ≤ 1/2`, the array (7.2) has a finite realization (a
positive measure on `2N + 1` points with the product identities and coefficient sums one),
nonnegative linearization, and every such measure is symmetric. Sharpness is `szwarc_sharp`. -/
def Stmt_szwarc_full : Prop :=
  ∀ (N : ℕ), 1 ≤ N → ∀ p : ℝ, 0 < p → p ≤ 1 / 2 →
    FiniteRealization (szwarcCoefficients N p) ∧ MatrixPositivity (szwarcCoefficients N p) ∧
    ∀ x w, IsRealization (szwarcCoefficients N p) x w → ∀ t, ∃ t', x t' = -x t ∧ w t' = w t


theorem szwarc_full : Stmt_szwarc_full := …

```
### lean/Szkraw/ParitySplit.lean
```lean
/-- Hypotheses (i)–(ii) of Corollary 7.9 with parameters `p_0` and `q`. -/
def ParitySplit (v : Coefficients (2 * N)) (p₀ q : ℝ) : Prop :=
  1 ≤ q ∧ (∀ n, 2 * n + 1 ≤ 2 * N → v.c (2 * n + 1) = p₀) ∧
    (∀ n, 1 ≤ n → n ≤ N → 0 < v.c (2 * n) - v.c (2 * (n - 1))) ∧
    (∀ n, 1 ≤ n → n < N → v.c (2 * (n + 1)) - v.c (2 * n) = q * (v.c (2 * n) - v.c (2 * (n - 1))))


/-- Szwarc's array (7.2): `b ≡ 0`, `(a_{2n}, c_{2n}) = ((N-n)/N, n/N)`, `(a_{2n-1}, c_{2n-1}) = (1-p_0, p_0)`. -/
noncomputable def szwarcCoefficients (N : ℕ) (p : ℝ) : Coefficients (2 * N) :=
  ⟨fun k => if k % 2 = 0 then ((N : ℝ) - ((k / 2 : ℕ) : ℝ)) / N else 1 - p,
   fun _ => 0,
   fun k => if k % 2 = 0 then ((k / 2 : ℕ) : ℝ) / N else p⟩


```
### lean/Szkraw/QuadDecomp.lean
```lean
/-- The affine normalization `(a, b, c) ↦ (a, b - b_0, c)/a_0`. -/
noncomputable def normalize {K : ℕ} (w : Coefficients K) : Coefficients K :=
  ⟨fun n => w.a n / w.a 0, fun n => (w.b n - w.b 0) / w.a 0, fun n => w.c n / w.a 0⟩


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


/-- The normalized even component. -/
noncomputable def evenComp : Coefficients N := normalize (evenRaw v)


/-- The normalized odd component. -/
noncomputable def oddComp : Coefficients (N - 1) := normalize (oddRaw v)


```
### lean/Szkraw/Parameters.lean
```lean
noncomputable def geometricCoefficients (N : ℕ) (p q : ℝ) : Coefficients N where
  a i := q^i*qInteger q (N-i)/qInteger q N
  b i := (p-1)*qInteger q i/(p*qInteger q N)
  c i := qInteger q i/(p*qInteger q N)


```
### lean/Szkraw/Elementary.lean
```lean
def qInteger (q : ℝ) : ℕ → ℝ
  | 0 => 0
  | n+1 => qInteger q n + q^n


```
### lean/Szkraw/ParityParams.lean (section variables, then theorems)
```lean
variable {N : ℕ} (v : Coefficients (2 * N)) (hv : Admissible v) (hb : ∀ i, i ≤ 2 * N → v.b i = 0)
  {p₀ q : ℝ} (hp : ParitySplit v p₀ q)
include hv hb hp
/-- `d_n = [n]_q / [N]_q`. -/
theorem ps_d_formula : ∀ n, n ≤ N → v.c (2 * n) = qInteger q n / qInteger q N := …

/-- The normalized even component is (2.3) with parameters `(N, q, r)`. -/
theorem ps_even_params :
    ∀ i, i ≤ N → (evenComp v).a i = (geometricCoefficients N ((1 - p₀) / p₀) q).a i ∧
      (evenComp v).b i = (geometricCoefficients N ((1 - p₀) / p₀) q).b i ∧
      (evenComp v).c i = (geometricCoefficients N ((1 - p₀) / p₀) q).c i := …

/-- The normalized odd component (`N ≥ 2`) is (2.3) with parameters `(N - 1, q, r/q)`. -/
theorem ps_odd_params (hN2 : 2 ≤ N) :
    ∀ i, i ≤ N - 1 → (oddComp v).a i = (geometricCoefficients (N - 1) (q * (1 - p₀) / p₀) q).a i ∧
      (oddComp v).b i = (geometricCoefficients (N - 1) (q * (1 - p₀) / p₀) q).b i ∧
      (oddComp v).c i = (geometricCoefficients (N - 1) (q * (1 - p₀) / p₀) q).c i := …

```