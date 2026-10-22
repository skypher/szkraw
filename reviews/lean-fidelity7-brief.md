# Independent review, round 7: Proposition 9.8 in Lean

As in rounds 1–6 (round 6: PASS), **do not check proofs**. Check only whether each Lean statement faithfully expresses the paper statement, under the acceptance rule: Lean hypotheses equivalent to or weaker than the paper's, and Lean conclusion equivalent to or stronger. Where the Lean statement covers less than the paper claims, say exactly what is missing.

This round covers **Proposition 9.8** (interior points near the symmetric endpoint):
- `interior_measure`: for N ≥ 2, Λ > `lamN N` and all small ε > 0, with r = 1 − Λε, three things hold.
  - The masses `kw N r t − ε[t = 0]` of K_{N,r}, with its top mass lowered by ε, are positive.
  - The polynomials of `epsRaw (kv N r) (kx N r) (kw N r) (−ε)` (coefficients in the fixed coordinate x) are orthogonal for these masses at the nodes `kx N r t`, and equal 1 at the top node x₀ = 1. This identifies them as the polynomials of the lowered measure.
  - Every triangle coefficient g(m,n;k), |m−n| ≤ k ≤ min(m+n,N), is positive.
- `interior_open`: after the affine normalization (`epsNorm … (−ε)`, the substitution y = (1−ε)x + ε), the array satisfies (2.1), and some η > 0 makes every array satisfying (2.1) within η coefficientwise have property (P). This is the paper's relatively open neighborhood.
- `lamN N` is Λ_N: an explicit finite sum of ratios |∂_ε g| / |∂_r g| of first-order rates at K_{N,1}, defined through the smooth family `lowK` (equal to the lowered system for r ≤ 1). The paper's Λ_N is a maximum. Any finite constant meets the existential claim; the paper's numerical values of Λ_N are not part of the statement.
- Supporting statements, included for context:
  - `kraw_g_formula` is the explicit formula for g of K_{N,r}, the combinatorial form of the paper's H-formula;
  - `kraw1_zero` and `kraw1_pos` give the zero pattern at r = 1;
  - `kraw_deriv_neg` gives the r-derivative on odd triples.
- Also check the scope sentence for Proposition 9.8 in the code-and-formalization section.

Conventions:
- `Admissible v` is (2.1), and `productMatrix v m` has entry (n,k) = g(m,n;k).
- `Triangle m n k` means m ≤ n+k ∧ n ≤ m+k ∧ k ≤ m+n.
- `kv N r = geometricCoefficients N (1/r) 1` agrees with `krawCoefficients N r` on indices 0..N.
- `kx N r t = 1 − (1+r)t/N` and `kw N r t = C(N,t) r^{N−t}/(1+r)^N` are the nodes and masses of K_{N,r}.

Answer format: a table (paper claim | Lean declaration | MATCH / MATCH, SCOPE NOTED / MISMATCH | reason), exact fixes, and an overall verdict (PASS / PASS WITH MINOR FIXES / FAIL). Be terse.

## Part A. Paper statements

#### Section 9 setting
```latex
Theorems~\ref{thm:low} and~\ref{thm:palindromic} control every triple except the deep ones by inequalities, Theorem~\ref{thm:lc} controls all triples of constant-ratio arrays with log-concave Newton profiles, and Section~\ref{sec:open} records shape conditions that fail on deep triples. This section shows that part of the failure is structural near the symmetric endpoint. For uniformly sampled polynomial deformation directions, and for the analytic and boundary-layer extensions specified below, admission at every sufficiently large symmetric Krawtchouk system imposes two first-order boundary equalities. This does not exclude arbitrary uniform inequality criteria, nor families of admissible arrays that are not of these forms. Write $K_{N,r}$ for the Krawtchouk array \eqref{eq:parameters} with $q=1$, and use the coordinates $b_1,\ldots,b_{N-1},c_1,\ldots,c_N$ of a stochastic array with $b_0=0$, $a_0=1$, $a_N=0$, $b_N=1-c_N$ and $a_n=1-b_n-c_n$ otherwise. An affine change of $x$, together with the positive normalization $R_n(x_0)=1$ at the largest support point $x_0$, reduces every finite system to this form. A direction $v=(\delta b_1,\ldots,\delta b_{N-1},\delta c_1,\ldots,\delta c_N)$ changes these coordinates; we put $\delta b_0=\delta c_0=0$ and $\delta b_N=-\delta c_N$.
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
\begin{proposition}[Interior points near the symmetric endpoint]\label{prop:interior}
For every $N\geq2$ there is $\Lambda_N<\infty$ such that, for $\Lambda>\Lambda_N$ and all sufficiently small $\varepsilon>0$, the measure of $K_{N,1-\Lambda\varepsilon}$ with its top mass lowered by $\varepsilon$ has $g(m,n;k)>0$ for all $|m-n|\leq k\leq\min(m+n,N)$. Consequently, after the affine normalization of Section~\ref{sec:criterion}, a relatively open set of arrays near it has property (P).
\end{proposition}
```

#### The proof of Proposition 9.8 (for the formula of g of K_{N,r} it quotes)
```latex
By the model of Lemma~\ref{lem:margin}, $K_{N,r}$ has
\begin{gather*}
g(m,n;k)=\sum_jH(m,n;j)\binom js r^{j-s}(1-r)^s,\\
H(m,n;j)=\frac{\binom mj\binom{N-m}{n-j}}{\binom Nn},\qquad s=k-m-n+2j,
\end{gather*}
where the sum is over $\max(0,m+n-N)\leq j\leq\min(m,n)$ with $0\leq s\leq j$.
At $r=1$ only $s=0$ survives, so a triangle coefficient of $K_{N,1}$ vanishes exactly when $m+n+k$ is odd or $m+n+k>2N$. Both deformations are smooth in $(r,\varepsilon)$, so only these zeros need first-order positivity.
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
Proposition~\ref{prop:interior}: interior points near the symmetric endpoint & \path{Szkraw.interior_measure}, \path{Szkraw.interior_open}\\[3pt]
Proposition~\ref{prop:thin}: thinness near the symmetric endpoint & \path{Szkraw.thinness}\\[3pt]
Corollary~\ref{cor:radius-order}: optimal order of the stability radius & \path{Szkraw.radius_order}\\[3pt]
Proposition~\ref{prop:raise}: raising the top mass & \path{Szkraw.raise_measure}, \path{Szkraw.raise_corner}, \path{Szkraw.raise_sign}, \path{Szkraw.raise_bound}\\[3pt]
Corollary~\ref{cor:radius-exp}: exponentially small stability radius & \path{Szkraw.radius_exp}, \path{Szkraw.radius_exp_asymp}
\end{tabular}
\end{center}
The first includes a positive finite orthogonality measure, distinct support points, the terminal relation, and all finite product identities. The second includes the explicit radius, positive triangle margin, and exact zeros outside the triangle. The entries for Section~\ref{sec:szwarc} state nonnegativity of the coefficients $g(m,n;k)$: for Theorem~\ref{thm:low} and Corollary~\ref{cor:convex-low} on all triples with two indices of sum at most $N$, and for Theorems~\ref{thm:all}, \ref{thm:deep} and~\ref{thm:palindromic} and Corollaries~\ref{cor:heavy} and~\ref{cor:palin} on all triples. Lemma~\ref{lem:reversal} and the identities of Theorem~\ref{thm:deep} are stated for the matrices $R_m(J)$ and $R'_t(J)=\Pi R'_t(\Pi J\Pi)\Pi$. Theorem~\ref{thm:szwarc} is proved in Lean through Corollary~\ref{cor:parity} with $q=1$, and Lemma~\ref{lem:qmargin} through the decomposition, whose components are Krawtchouk arrays; the symmetry of its measure holds for every finite realization of an array satisfying \eqref{eq:basic} with $b\equiv0$ (\path{Szkraw.realization_symmetric}). In Corollary~\ref{cor:symmetric-new}, ``not of the form \eqref{eq:parameters}'' is formalized as the failure of the hypotheses of Theorem~\ref{thm:criterion} and as disagreement with every array \eqref{eq:parameters} in the Lean parametrization; its last sentence follows from the explicit coefficient box of positive radius in \path{Szkraw.symmetric_criterion}; openness and dimension are not stated separately in Lean. For Corollary~\ref{cor:parity}, when $N\geq2$, Lean proves that both normalized components satisfy the hypotheses of Theorem~\ref{thm:criterion} and are the arrays \eqref{eq:parameters} with parameters $(N,q,r)$ and $(N-1,q,r/q)$ (\path{Szkraw.ps_even_params}, \path{Szkraw.ps_odd_params}); \path{Szkraw.parity_split} also covers $N=1$, where the odd component is the constant polynomial alone. In Theorem~\ref{thm:decomp} the identity for $g(2a,2b+1;2c+1)$ is stated with the unnormalized odd component, which has the same product coefficients (\path{Szkraw.product_normalize}). The finite realization holds for every array satisfying \eqref{eq:basic} (\path{Szkraw.finite_realization}). The proofs formalize the cone argument and the identity $g(m,n;k)\int R_k^2\,d\mu=g(m,k;n)\int R_n^2\,d\mu$ in matrix form. The entry for Theorem~\ref{thm:lc} includes the same finite realization as the first and the nonnegativity of every coefficient $g(m,n;k)$; its proof formalizes Lemmas~\ref{lem:lc-ineq} and~\ref{lem:detours}, the operator induction, and Lemma~\ref{lem:kernel-rec} in converse form: the solution of~\eqref{eq:kernel-rec} yields the linearization coefficients. The remark after the proof of Theorem~\ref{thm:lc} is formalized as identities for all real $u$ and $v$ (two-parameter form, \path{Szkraw.lc_twoParam}) and for all real $r$ (Bernstein form, \path{Szkraw.lc_bernstein}, whose coefficients $B_s$ are $\binom Ds$ times the Bernstein coefficients); \path{Szkraw.constantRatio_twoParam} identifies the arrays of Theorem~\ref{thm:lc} with this family, and the proof formalizes the operator induction coefficientwise in $t$. All of them have compiled proofs without added axioms or admitted goals; the axiom audit reports only \path{propext}, \path{Classical.choice} and \path{Quot.sound}. Lemma~\ref{lem:edge} is stated for every commutative real algebra with elements $y_1,\ldots,y_N$ satisfying $y_j^2=(1-r)y_j+r$ whose squarefree monomials form a basis, which determines $A$ up to isomorphism, and for $r\neq-1$; \path{Szkraw.cube_model} shows that the real functions on $\{1,-r\}^N$ form such an algebra. Its basis assertion is stated as linear independence of the $f_ly_S$ together with equality of their span and the ideal $f_lA$. Lemma~\ref{lem:qthree} is stated for $N\geq1$, $p_0<1$ and $r=p_0/(1-p_0)$, in every commutative real algebra satisfying these relations, without a basis hypothesis; its recurrence is an equality in $A\times A^N$, which restricts to $V$, and \path{Szkraw.Uvec_top} states $U_{2N+1}=0$ separately. Lemma~\ref{lem:corner} is stated for $N\geq2$ as the derivative at $\varepsilon=0$ of $g(N,N;N)$ along $K_{N,1}+\varepsilon v$. Its Lean proof replaces the beta integrals by an explicit matrix: the derivative $X$ of $R_N^\varepsilon(J_\varepsilon)$ satisfies $[J,X]=[\Pi,E]$ and $e_0^\mathsf TX=0$, and $Z_{mn}=\binom Nn(-1)^{n+s}/(2\binom{N-1}s)$ for $m+n=2s+1$, $Z_{mn}=0$ for $m+n$ even, satisfies $ZJ-JZ=e_Ne_N^\mathsf T$ on the columns $n\geq1$; hence the derivative equals $\operatorname{tr}((Z\Pi-\Pi Z)E)$, which is evaluated entry by entry. In Theorem~\ref{thm:uniform} the set of arrays is a family of sets indexed by $N$ whose members satisfy $g(m,n;k)\geq0$, admission is Definition~\ref{def:rule}, and the second statement is the vanishing of the derivative for every $N\geq1$ above the degrees. In Proposition~\ref{prop:thin} the direction is given in the coordinates $b_1,\ldots,b_{N-1},c_1,\ldots,c_N$ of Section~\ref{sec:limits}, the hypothesis is that the derivative of $g(N,N;N)$ at $\varepsilon=0$ is negative, and the conclusion is that $K_{N,r}+\varepsilon v$ satisfies \eqref{eq:basic} and has $g(N,N;N)<0$; \path{Szkraw.productMatrix_contDiffAt} gives the smoothness used in its proof. In Corollary~\ref{cor:radius-order}, $\rho_N(r)$ is the supremum of the radii with the stated property, and exact order means $c_1(1-r)^N\leq\rho_N(r)\leq c_2(1-r)^N$ for all $r$ in an interval $(r_0,1)$. Lemma~\ref{lem:topmass} is stated for the spectral measure of every array satisfying \eqref{eq:basic}, whose node $x_0=1$ exists by \path{Szkraw.spectral_top_node}; the polynomials of $\mu_\varepsilon$ are identified by orthogonality and their value $1$ at $x_0$ (\path{Szkraw.lower_measure}), and both parts are derivatives at $\varepsilon=0$. In Proposition~\ref{prop:interior}, $\Lambda_N$ is an explicit finite sum bounding the ratios of the two first-order rates (\path{Szkraw.lamN}), the lowered measure is identified by orthogonality and normalization, and the neighborhood is an explicit coefficient box around the normalized array; the proof uses an explicit formula for the coefficients of $K_{N,r}$ (\path{Szkraw.kraw_g_formula}). In Proposition~\ref{prop:raise}, Lean states that the normalized array satisfies \eqref{eq:basic}, that its polynomials are orthogonal for the raised measure transported to $y=(1+\varepsilon)x-\varepsilon$ and equal $1$ at the top node, and then the corner formula, its sign and the coefficient bound; the proof uses the polynomials $(1+\varepsilon S_n)R_n-\varepsilon\sum_{j<n}\pi_jR_j$ for any finite system (\path{TopMass.lean}). The results of Section~\ref{sec:limits} other than Lemmas~\ref{lem:corner-value} and~\ref{lem:corner}, Theorem~\ref{thm:uniform}, Proposition~\ref{prop:thin}, Corollaries~\ref{cor:radius-order} and~\ref{cor:radius-exp}, Lemma~\ref{lem:topmass}, Propositions~\ref{prop:interior} and~\ref{prop:raise} and the first statement and part (1) of Proposition~\ref{prop:families} have not yet been formalized; formalizing them is planned.

```

## Part B. Lean statements

### lean/Szkraw/Statements.lean
```lean
def Admissible {N : ℕ} (v : Coefficients N) : Prop :=
  1 ≤ N ∧ v.a 0 = 1 ∧ v.b 0 = 0 ∧ v.c 0 = 0 ∧ v.a N = 0 ∧
  (∀ i, i ≤ N → v.a i + v.b i + v.c i = 1) ∧
  (∀ i, i < N → 0 < v.a i) ∧
  (∀ i, 0 < i → i ≤ N → 0 < v.c i)

noncomputable def productMatrix {N : ℕ} (v : Coefficients N) (m : ℕ) :
    Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ := (matrixPair v m).2

def MatrixPositivity {N : ℕ} (v : Coefficients N) : Prop :=
  ∀ m, m ≤ N → ∀ i j, 0 ≤ productMatrix v m i j

def Triangle (m n k : ℕ) : Prop := m ≤ n+k ∧ n ≤ m+k ∧ k ≤ m+n

```
### lean/Szkraw/Krawtchouk.lean
```lean
noncomputable def krawCoefficients (N : ℕ) (r : ℝ) : Coefficients N where
  a i := ((N : ℝ)-i)/N
  b i := (1-r)*i/N
  c i := r*i/N

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

```
### lean/Szkraw/KrawCube.lean
```lean
/-- The count `Σ_{|S|=m, |T|=n, J ⊆ S ∩ T, (S Δ T) ∪ J = U} (1-r)^{|J|} r^{|S∩T| - |J|}`. -/
noncomputable def countP (N m n : ℕ) (U : Finset (Fin N)) (r : ℝ) : ℝ :=
  ∑ S ∈ univ.filter (fun S : Finset (Fin N) => S.card = m), ∑ T ∈ univ.filter (fun T : Finset (Fin N) => T.card = n),
    ∑ J ∈ (S ∩ T).powerset, if symmDiff S T ∪ J = U then (1 - r) ^ J.card * r ^ ((S ∩ T).card - J.card) else 0

/-- **Explicit coefficients of `K_{N,r}`** (`r ≠ -1`):
`g(m,n;k) = C(N,k) / (C(N,m) C(N,n)) · countP N m n U r` for any `U` with `|U| = k`. -/
theorem kraw_g_formula {N : ℕ} {r : ℝ} (hN : 1 ≤ N) (hr : 1 + r ≠ 0) (m : ℕ) (hm : m ≤ N) (n k : Fin (N + 1))
    (U : Finset (Fin N)) (hU : U.card = k) :
    productMatrix (krawCoefficients N r) m n k =
      ((N.choose k : ℕ) : ℝ) / (((N.choose m : ℕ) : ℝ) * ((N.choose n : ℕ) : ℝ)) * countP N m n U r := …

```
### lean/Szkraw/KrawOne.lean
```lean
/-- At `K_{N,1}`: `g(m,n;k) = 0` when `m + n + k` is odd or exceeds `2N`. -/
theorem kraw1_zero (hN : 1 ≤ N) (m : ℕ) (hm : m ≤ N) (n k : Fin (N + 1))
    (h : (m + n.val + k.val) % 2 = 1 ∨ 2 * N < m + n.val + k.val) :
    productMatrix (krawCoefficients N 1) m n k = 0 := …

/-- At `K_{N,1}`: `g(m,n;k) > 0` on the triangle when `m + n + k` is even and at most `2N`. -/
theorem kraw1_pos (hN : 1 ≤ N) (m : ℕ) (hm : m ≤ N) (n k : Fin (N + 1)) (h1 : m ≤ n.val + k.val)
    (h2 : n.val ≤ m + k.val) (h3 : k.val ≤ m + n.val) (heven : (m + n.val + k.val) % 2 = 0)
    (hle : m + n.val + k.val ≤ 2 * N) :
    0 < productMatrix (krawCoefficients N 1) m n k := …

/-- For `m + n + k` odd on the triangle, `g(m,n;k)` of `K_{N,r}` has negative `r`-derivative at
`r = 1`. -/
theorem kraw_deriv_neg (hN : 1 ≤ N) (m : ℕ) (hm : m ≤ N) (n k : Fin (N + 1)) (h1 : m ≤ n.val + k.val)
    (h2 : n.val ≤ m + k.val) (h3 : k.val ≤ m + n.val) (hodd : (m + n.val + k.val) % 2 = 1)
    (hle : m + n.val + k.val ≤ 2 * N + 1) :
    ∃ D < 0, HasDerivAt (fun r => productMatrix (krawCoefficients N r) m n k) D 1 := …

```
### lean/Szkraw/Interior.lean
```lean
/-- `A_n = 1 - ε Σ_{j<n} C(N,j) r^{-j}`. -/
noncomputable def lowA (N : ℕ) (r ε : ℝ) (n : ℕ) : ℝ := 1 - ε * ∑ j ∈ range n, (N.choose j : ℝ) / r ^ j

/-- `K_{N,r}` with the top mass lowered by `ε`, in the fixed coordinate `x`. -/
noncomputable def lowK (N : ℕ) (r ε : ℝ) : Coefficients N where
  a n := ((N : ℝ) - n) / N * lowA N r ε n / lowA N r ε (n + 1)
  b n := 1 - ((N : ℝ) - n) / N * lowA N r ε n / lowA N r ε (n + 1) - r * n / N * lowA N r ε (n + 1) / lowA N r ε n
  c n := r * n / N * lowA N r ε (n + 1) / lowA N r ε n

/-- `G(r, ε) = g(m,n;k)` of `lowK N r ε`. -/
noncomputable def lowG (N m : ℕ) (n k : Fin (N + 1)) (p : ℝ × ℝ) : ℝ := productMatrix (lowK N p.1 p.2) m n k

/-- The constant `Λ_N`: a bound for `∂_ε G / (-∂_r G)` over the triangle. -/
noncomputable def lamN (N : ℕ) : ℝ :=
  ∑ z : Fin (N + 1) × Fin (N + 1) × Fin (N + 1),
    |fderiv ℝ (lowG N z.1 z.2.1 z.2.2) (1, 0) (0, 1)| / |fderiv ℝ (lowG N z.1 z.2.1 z.2.2) (1, 0) (1, 0)|

/-- **Proposition 9.8** (Interior points near the symmetric endpoint): for `Λ > Λ_N` and all
sufficiently small `ε > 0`, the measure of `K_{N,1-Λε}` with its top mass lowered by `ε` (in the
fixed coordinate `x`, `epsRaw … (-ε)`) has `g(m,n;k) > 0` on the whole triangle. -/
theorem interior_points (hN : 2 ≤ N) {Λ : ℝ} (hΛ : lamN N < Λ) :
    ∃ ε₀ > 0, ∀ ε, 0 < ε → ε < ε₀ →
      0 < 1 - Λ * ε ∧ 1 - Λ * ε < 1 ∧ ε < kw N (1 - Λ * ε) 0 ∧
        ∀ m, m ≤ N → ∀ n k : Fin (N + 1), Triangle m n.val k.val →
          0 < productMatrix (epsRaw (kv N (1 - Λ * ε)) (kx N (1 - Λ * ε)) (kw N (1 - Λ * ε)) (-ε)) m n k := …

/-- **Proposition 9.8**, the lowered measure: for `Λ > Λ_N` and small `ε > 0`, with `r = 1 - Λ ε`,
the masses `w_t - ε [t = 0]` of `K_{N,r}` stay positive, the polynomials of `epsRaw … (-ε)` are
orthogonal for them and equal `1` at `x_0 = 1`, and every triangle coefficient is positive. -/
theorem interior_measure (hN : 2 ≤ N) {Λ : ℝ} (hΛ : lamN N < Λ) :
    ∃ ε₀ > 0, ∀ ε, 0 < ε → ε < ε₀ →
      (∀ t, 0 < kw N (1 - Λ * ε) t - if t = 0 then ε else 0) ∧
      (∀ n, n ≤ N → (recurrencePolynomial (epsRaw (kv N (1 - Λ * ε)) (kx N (1 - Λ * ε)) (kw N (1 - Λ * ε)) (-ε))
        n).eval 1 = 1) ∧
      (∀ m n, m ≤ N → n ≤ N → m ≠ n →
        ∑ t, (kw N (1 - Λ * ε) t - if t = 0 then ε else 0) *
          (recurrencePolynomial (epsRaw (kv N (1 - Λ * ε)) (kx N (1 - Λ * ε)) (kw N (1 - Λ * ε)) (-ε)) m).eval
            (kx N (1 - Λ * ε) t) *
          (recurrencePolynomial (epsRaw (kv N (1 - Λ * ε)) (kx N (1 - Λ * ε)) (kw N (1 - Λ * ε)) (-ε)) n).eval
            (kx N (1 - Λ * ε) t) = 0) ∧
      ∀ m, m ≤ N → ∀ n k : Fin (N + 1), Triangle m n.val k.val →
        0 < productMatrix (epsRaw (kv N (1 - Λ * ε)) (kx N (1 - Λ * ε)) (kw N (1 - Λ * ε)) (-ε)) m n k := …

/-- **Proposition 9.8**, consequence: after the affine normalization of Section 2 the lowered system
satisfies (2.1), and every array satisfying (2.1) within some `η > 0` of it has property (P). -/
theorem interior_open (hN : 2 ≤ N) {Λ : ℝ} (hΛ : lamN N < Λ) :
    ∃ ε₀ > 0, ∀ ε, 0 < ε → ε < ε₀ →
      Admissible (epsNorm (kv N (1 - Λ * ε)) (kx N (1 - Λ * ε)) (kw N (1 - Λ * ε)) (-ε)) ∧
      ∃ η > 0, ∀ w : Coefficients N, Admissible w →
        (∀ i, i ≤ N → |w.a i - (epsNorm (kv N (1 - Λ * ε)) (kx N (1 - Λ * ε)) (kw N (1 - Λ * ε)) (-ε)).a i| ≤ η ∧
          |w.b i - (epsNorm (kv N (1 - Λ * ε)) (kx N (1 - Λ * ε)) (kw N (1 - Λ * ε)) (-ε)).b i| ≤ η ∧
          |w.c i - (epsNorm (kv N (1 - Λ * ε)) (kx N (1 - Λ * ε)) (kw N (1 - Λ * ε)) (-ε)).c i| ≤ η) →
        MatrixPositivity w := …

```