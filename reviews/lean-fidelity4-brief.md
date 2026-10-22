# Independent review, round 4: do the Lean statements say what the paper says?

As in rounds 1–3 (all PASS WITH MINOR FIXES, fixes applied), **do not check proofs**. Check only whether each Lean statement faithfully expresses the paper statement, under the acceptance rule: Lean hypotheses equivalent to or weaker than the paper's, and Lean conclusion equivalent to or stronger. Where the Lean statement covers less than the paper claims, say exactly what is missing.

This round covers declarations added after round 3:
- **Remark after the proof of Theorem 8.1**:
  - `lc_twoParam : Stmt_lc_twoParam` (two-parameter form). `twoParam N d x y` is the array a_i = 1 − d_i, b_i = x d_i, c_i = y d_i; the paper's (u, v) are Lean's (x, y), and the paper's yp_i = … is the three-term recurrence of this array. Lean states the polynomial form as an identity for all real x and y, with h independent of (x, y).
  - `lc_bernstein : Stmt_lc_bernstein` (Bernstein form, as an identity for all real r). Its B_s equal C(D,s) times the paper's Bernstein coefficients.
  - `constantRatio_twoParam`, which identifies every array satisfying the hypotheses of Theorem 8.1 (`Admissible v`, `c_i = r d_i`, the Newton condition) with `twoParam N d (1 − r) r` and its profile with an `LCProfile`.
  - `LCProfile` is the profile hypothesis: d_0 = 0, d_N = 1, d_i > 0 for 1 ≤ i ≤ N, d_i < 1 for i < N, with the Newton condition. It is weaker than the paper's strict monotonicity.
- **Lemma 9.1** (corner value): `corner_value`. `krawCoefficients N r` is K_{N,r}: a_i = (N − i)/N, b_i = (1 − r)i/N, c_i = ri/N.
- Also check the updated scope sentences of the code-and-formalization section for the remark and for Lemma 9.1.

Conventions as before:
- `Admissible v` is (2.1).
- `productMatrix v m` has entry (n,k) = g(m,n;k). It is R_m(J) for the tridiagonal recurrence matrix J, with R_m built by the recurrence; row 0 of R_m(J) holds the coefficients of R_m in the basis R_0, …, R_N on the support. This makes g(m,n;k) a well-defined real number for any real coefficient array with a_i ≠ 0 (i < N).
- `Fin (N + 1)` indices range over 0..N.
- `Finset.range n` is {0, …, n − 1}; natural-number subtraction truncates at 0.

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

#### Parameters (2.3)
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

#### Section 8 opening and Theorem 8.1
```latex
Theorem~\ref{thm:criterion} requires the increments of the profile $d_i=b_i+c_i$ to be geometric. This section replaces that equality by inequalities on the Newton coefficients of the profile, for arrays with constant ratio $b_i/c_i$. Write
\[
\nu_k=\sum_{i=0}^k(-1)^{k-i}\binom ki d_i\quad(1\leq k\leq N),\qquad d_n=\sum_{k=1}^n\binom nk\nu_k\quad(0\leq n\leq N);
\]
below we put $\nu_0=0$ and $\nu_k=0$ for $k>N$.
We say that $(\nu_k)_{1\leq k\leq N}$ is \emph{log-concave without internal zeros} if all $\nu_k\geq0$, the indices with $\nu_k>0$ form an interval $\{1,\ldots,K\}$, and $\nu_k^2\geq\nu_{k-1}\nu_{k+1}$ for $2\leq k\leq N-1$. Note $\nu_1=d_1>0$.

\begin{theorem}[Log-concave Newton criterion]\label{thm:lc}
Let $0=d_0<d_1<\cdots<d_N=1$ have Newton coefficients that are log-concave without internal zeros, let $0<r\leq1$, and put $a_i=1-d_i$, $b_i=(1-r)d_i$, $c_i=rd_i$. Then the system has nonnegative linearization.
\end{theorem}
```

#### Rescaled system (first paragraph of the proof of Theorem 8.1)
```latex
\paragraph{A rescaled system and a kernel.}
Fix $r$ and put $t=(1-r)/\sqrt r\geq0$. If $p_i$ is defined by $p_0=1$ and $yp_i=a_ip_{i+1}+td_ip_i+d_ip_{i-1}$ $(0\leq i<N)$, then $R_i(x)=r^{i/2}p_i(x/\sqrt r)$, so the coefficients $H_{mn}^k$ in $p_mp_n=\sum_kH_{mn}^kp_k$ on the support satisfy $g(m,n;k)=r^{(m+n-k)/2}H_{mn}^k$. It suffices to show $H_{mn}^k\geq0$. Put
\[
```

#### Remark after the proof of Theorem 8.1
```latex
\begin{remark}
The argument is valid coefficientwise in $t$. With independent parameters in $yp_i=a_ip_{i+1}+ud_ip_i+vd_ip_{i-1}$, weighted homogeneity ($\deg y=\deg u=1$, $\deg v=2$) then shows that each linearization coefficient is a polynomial in $(u,v)$ with nonnegative coefficients: for $D=m+n-k\geq0$ it has the form $\sum_{0\leq j\leq\lfloor D/2\rfloor}h_ju^{D-2j}v^j$ with $h_j\geq0$, and it vanishes for $D<0$. Consequently every $g(m,n;k)$ of the array of Theorem~\ref{thm:lc}, as a function of $r$, equals $\sum_jh_jr^j(1-r)^{D-2j}$; multiplying the $j$-th term by $(r+(1-r))^j=1$ shows that its coefficients in the Bernstein basis of degree $D$ are $\binom Ds^{-1}\sum_{j\leq s\leq2j}h_j\binom j{s-j}\geq0$. The diagnostics \path{lc_kernel_check.py} verify Lemmas~\ref{lem:kernel-rec}--\ref{lem:detours} and the matching $\mathcal P^2\geq4\mathcal Q$ in exact arithmetic on random log-concave profiles.
\end{remark}
```

#### Section 9 notation and Lemma 9.1
```latex
Theorems~\ref{thm:low} and~\ref{thm:palindromic} control every triple except the deep ones by inequalities, Theorem~\ref{thm:lc} controls all triples of constant-ratio arrays with log-concave Newton profiles, and Section~\ref{sec:open} records shape conditions that fail on deep triples. This section shows that part of the failure is structural near the symmetric endpoint. For uniformly sampled polynomial deformation directions, and for the analytic and boundary-layer extensions specified below, admission at every sufficiently large symmetric Krawtchouk system imposes two first-order boundary equalities. This does not exclude arbitrary uniform inequality criteria, nor families of admissible arrays that are not of these forms. Write $K_{N,r}$ for the Krawtchouk array \eqref{eq:parameters} with $q=1$, and use the coordinates $b_1,\ldots,b_{N-1},c_1,\ldots,c_N$ of a stochastic array with $b_0=0$, $a_0=1$, $a_N=0$, $b_N=1-c_N$ and $a_n=1-b_n-c_n$ otherwise. An affine change of $x$, together with the positive normalization $R_n(x_0)=1$ at the largest support point $x_0$, reduces every finite system to this form. A direction $v=(\delta b_1,\ldots,\delta b_{N-1},\delta c_1,\ldots,\delta c_N)$ changes these coordinates; we put $\delta b_0=\delta c_0=0$ and $\delta b_N=-\delta c_N$.

\begin{lemma}[Corner value]\label{lem:corner-value}
For $0<r\leq1$, the array $K_{N,r}$ has $g(N,N;N)=(1-r)^N$.
\end{lemma}
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
Theorem~\ref{thm:lc}: log-concave Newton criterion & \path{Szkraw.logconcave_criterion}\\[3pt]
Remark after Theorem~\ref{thm:lc}: two-parameter and Bernstein coefficients & \path{Szkraw.lc_twoParam}, \path{Szkraw.lc_bernstein}, \path{Szkraw.constantRatio_twoParam}\\[3pt]
Lemma~\ref{lem:corner-value}: corner value & \path{Szkraw.corner_value}
\end{tabular}
\end{center}
The first includes a positive finite orthogonality measure, distinct support points, the terminal relation, and all finite product identities. The second includes the explicit radius, positive triangle margin, and exact zeros outside the triangle. The entries for Section~\ref{sec:szwarc} state nonnegativity of the coefficients $g(m,n;k)$: for Theorem~\ref{thm:low} and Corollary~\ref{cor:convex-low} on all triples with two indices of sum at most $N$, and for Theorems~\ref{thm:all}, \ref{thm:deep} and~\ref{thm:palindromic} and Corollaries~\ref{cor:heavy} and~\ref{cor:palin} on all triples. Lemma~\ref{lem:reversal} and the identities of Theorem~\ref{thm:deep} are stated for the matrices $R_m(J)$ and $R'_t(J)=\Pi R'_t(\Pi J\Pi)\Pi$. Theorem~\ref{thm:szwarc} is proved in Lean through Corollary~\ref{cor:parity} with $q=1$, and Lemma~\ref{lem:qmargin} through the decomposition, whose components are Krawtchouk arrays; the symmetry of its measure holds for every finite realization of an array satisfying \eqref{eq:basic} with $b\equiv0$ (\path{Szkraw.realization_symmetric}). In Corollary~\ref{cor:symmetric-new}, ``not of the form \eqref{eq:parameters}'' is formalized as the failure of the hypotheses of Theorem~\ref{thm:criterion} and as disagreement with every array \eqref{eq:parameters} in the Lean parametrization; its last sentence follows from the explicit coefficient box of positive radius in \path{Szkraw.symmetric_criterion}; openness and dimension are not stated separately in Lean. For Corollary~\ref{cor:parity}, when $N\geq2$, Lean proves that both normalized components satisfy the hypotheses of Theorem~\ref{thm:criterion} and are the arrays \eqref{eq:parameters} with parameters $(N,q,r)$ and $(N-1,q,r/q)$ (\path{Szkraw.ps_even_params}, \path{Szkraw.ps_odd_params}); \path{Szkraw.parity_split} also covers $N=1$, where the odd component is the constant polynomial alone. In Theorem~\ref{thm:decomp} the identity for $g(2a,2b+1;2c+1)$ is stated with the unnormalized odd component, which has the same product coefficients (\path{Szkraw.product_normalize}). The finite realization holds for every array satisfying \eqref{eq:basic} (\path{Szkraw.finite_realization}). The proofs formalize the cone argument and the identity $g(m,n;k)\int R_k^2\,d\mu=g(m,k;n)\int R_n^2\,d\mu$ in matrix form. The entry for Theorem~\ref{thm:lc} includes the same finite realization as the first and the nonnegativity of every coefficient $g(m,n;k)$; its proof formalizes Lemmas~\ref{lem:lc-ineq} and~\ref{lem:detours}, the operator induction, and Lemma~\ref{lem:kernel-rec} in converse form: the solution of~\eqref{eq:kernel-rec} yields the linearization coefficients. The remark after the proof of Theorem~\ref{thm:lc} is formalized as identities for all real $u$ and $v$ (two-parameter form, \path{Szkraw.lc_twoParam}) and for all real $r$ (Bernstein form, \path{Szkraw.lc_bernstein}, whose coefficients $B_s$ are $\binom Ds$ times the Bernstein coefficients); \path{Szkraw.constantRatio_twoParam} identifies the arrays of Theorem~\ref{thm:lc} with this family, and the proof formalizes the operator induction coefficientwise in $t$. All of them have compiled proofs without added axioms or admitted goals; the axiom audit reports only \path{propext}, \path{Classical.choice} and \path{Quot.sound}. Lemmas~\ref{lem:edge} and~\ref{lem:qthree}, which serve only the paper's own proof of Theorem~\ref{thm:szwarc}, and the results of Section~\ref{sec:limits} other than Lemma~\ref{lem:corner-value} have not yet been formalized; formalizing them is planned.

```

## Part B. Lean statements

### lean/Szkraw/Statements.lean
```lean
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

/-- Theorem 8.1 in the form of the geometric criterion: finite realization (orthogonality
measure, terminal relation, product identities) together with matrix positivity. -/
def Stmt_logconcave : Prop :=
  ∀ (N : ℕ) (v : Coefficients N), Admissible v → ConstantRatioLogConcave v →
    FiniteRealization v ∧ MatrixPositivity v

```
### lean/Szkraw/LCRemark.lean
```lean
/-- Hypotheses on the profile in Theorem 8.1. -/
structure LCProfile (N : ℕ) (d : ℕ → ℝ) : Prop where
  hN : 1 ≤ N
  d0 : d 0 = 0
  dN : d N = 1
  pos : ∀ i, 1 ≤ i → i ≤ N → 0 < d i
  lt1 : ∀ i, i < N → d i < 1
  lc : LogConcaveNoInternalZeros N (newtonCoeff d)

/-- The array `y p_i = a_i p_{i+1} + x d_i p_i + y d_i p_{i-1}` with `a_i = 1 - d_i`. -/
def twoParam (N : ℕ) (d : ℕ → ℝ) (x y : ℝ) : Coefficients N :=
  ⟨fun i => 1 - d i, fun i => x * d i, fun i => y * d i⟩

/-- The remark after Theorem 8.1, two-parameter form. -/
def Stmt_lc_twoParam : Prop :=
  ∀ (N : ℕ) (d : ℕ → ℝ), LCProfile N d → ∀ m, m ≤ N → ∀ n k : Fin (N + 1),
    ∃ h : ℕ → ℝ, (∀ j, 0 ≤ h j) ∧ (m + n.val < k.val → ∀ j, h j = 0) ∧
      ∀ x y : ℝ, productMatrix (twoParam N d x y) m n k =
        ∑ j ∈ range ((m + n.val - k.val) / 2 + 1), h j * x ^ (m + n.val - k.val - 2 * j) * y ^ j

theorem lc_twoParam : Stmt_lc_twoParam := …

/-- The remark after Theorem 8.1, Bernstein form. -/
def Stmt_lc_bernstein : Prop :=
  ∀ (N : ℕ) (d : ℕ → ℝ), LCProfile N d → ∀ m, m ≤ N → ∀ n k : Fin (N + 1),
    ∃ B : ℕ → ℝ, (∀ s, 0 ≤ B s) ∧ ∀ r : ℝ,
      productMatrix (twoParam N d (1 - r) r) m n k =
        ∑ s ∈ range (m + n.val - k.val + 1), B s * r ^ s * (1 - r) ^ (m + n.val - k.val - s)

theorem lc_bernstein : Stmt_lc_bernstein := …

/-- The arrays of Theorem 8.1 are `twoParam N d (1 - r) r` with a profile satisfying `LCProfile`. -/
theorem constantRatio_twoParam {N : ℕ} (v : Coefficients N) (hv : Admissible v) {r : ℝ} (hr0 : 0 < r)
    (hc : ∀ i, i ≤ N → v.c i = r * profile v i)
    (hlc : LogConcaveNoInternalZeros N (newtonCoeff (profile v))) :
    LCProfile N (profile v) ∧ ∀ m, m ≤ N → productMatrix v m = productMatrix (twoParam N (profile v) (1 - r) r) m := …

```
### lean/Szkraw/Krawtchouk.lean
```lean
noncomputable def krawCoefficients (N : ℕ) (r : ℝ) : Coefficients N where
  a i := ((N : ℝ)-i)/N
  b i := (1-r)*i/N
  c i := r*i/N

```
### lean/Szkraw/CornerValue.lean
```lean
/-- **Lemma 9.1** (Corner value). -/
theorem corner_value (N : ℕ) (hN : 1 ≤ N) (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1) :
    productMatrix (krawCoefficients N r) N ⟨N, by omega⟩ ⟨N, by omega⟩ = (1 - r) ^ N := …

```