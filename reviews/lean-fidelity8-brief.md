# Independent review, round 8: Lemma 9.5, Corollary 9.6 and Proposition 9.9 (2) in Lean

As in rounds 1–7 (round 7: PASS WITH MINOR FIXES), **do not check proofs**. Check only whether each Lean statement faithfully expresses the paper statement, under the acceptance rule: Lean hypotheses equivalent to or weaker than the paper's, and Lean conclusion equivalent to or stronger. Where the Lean statement covers less than the paper claims, say exactly what is missing.

This round covers the last three results of Section 9:
- **Lemma 9.5** (`norlund_rice`): `Ulog x = ∫_0^1 log‖x − t‖ dt` is the paper's U; Ω = `{x | Ulog x ≤ -1}`. "f analytic on an open set containing Ω" is `DifferentiableOn ℂ f D` for an open `D ⊇ Ω` (complex differentiability on an open set is analyticity). "O(√N e^{−ηN}) for some η > 0" is: ∃ η > 0, ∃ C, ∀ N ≥ 1, ‖Σ_{n=0}^N (−1)^n C(N,n) f(n/N)‖ ≤ C √N e^{−ηN} (`altBinom N f` is the sum).
- **Corollary 9.6**: β, γ are rules on [0,1] (functions ℝ → ℝ, used only at n/N). `AnalyticOnOmega β` means β agrees on [0,1] with a function complex differentiable on an open set containing Ω.
  - first statement: `analytic_forced_equalities`;
  - second statement: `analytic_rule_small` (a derivative d exists and |d| ≤ |s_N| C √N e^{−ηN} for every N ≥ 2);
  - the example: `expRule_analytic`, `expRule_L`, `expRule_deriv` (γ = 0, every N ≥ 2).
  - `analytic_rule_deriv` gives the general derivative, for context.
- **Proposition 9.9 (2)** (`families_boundary_layers`): finitely supported layers are sequences vanishing beyond a fixed K. The formulas for the direction are hypotheses for all large N, on the indices the coordinates use (δb_n for 1 ≤ n ≤ N−1, δc_n for 1 ≤ n ≤ N; the convention δb_0 = δc_0 = 0, δb_N = −δc_N is built into `stochDir`/`stochArray`). The family hypothesis is that of the first statement (`ContainsFamily`, with every member of `S N` having property (P)). Corollary 9.6's first statement is derived from it with zero layers.
- Also check the new table rows and scope sentences in the code-and-formalization section.

Conventions:
- `Coefficients N` has fields a, b, c : ℕ → ℝ.
- `Admissible v` is (2.1), and `productMatrix v m` has entry (n,k) = g(m,n;k).
- `MatrixPositivity v` is property (P).
- `krawDir N δb δc 1 ε` is K_{N,1} + εv in the Section 9 coordinates.
- `ruleArray β γ N ε = krawDir N (n ↦ β(n/N)) (n ↦ γ(n/N)) 1 ε`.
- `altSum vb vc N` is A_N for the direction v_N = (vb N, vc N).

Answer format: a table (paper claim | Lean declaration | MATCH / MATCH, SCOPE NOTED / MISMATCH | reason), exact fixes, and an overall verdict (PASS / PASS WITH MINOR FIXES / FAIL). Be terse.

## Part A. Paper statements

#### Section 9 setting
```latex
Theorems~\ref{thm:low} and~\ref{thm:palindromic} control every triple except the deep ones by inequalities, Theorem~\ref{thm:lc} controls all triples of constant-ratio arrays with log-concave Newton profiles, and Section~\ref{sec:open} records shape conditions that fail on deep triples. This section shows that part of the failure is structural near the symmetric endpoint. For uniformly sampled polynomial deformation directions, and for the analytic and boundary-layer extensions specified below, admission at every sufficiently large symmetric Krawtchouk system imposes two first-order boundary equalities. This does not exclude arbitrary uniform inequality criteria, nor families of admissible arrays that are not of these forms. Write $K_{N,r}$ for the Krawtchouk array \eqref{eq:parameters} with $q=1$, and use the coordinates $b_1,\ldots,b_{N-1},c_1,\ldots,c_N$ of a stochastic array with $b_0=0$, $a_0=1$, $a_N=0$, $b_N=1-c_N$ and $a_n=1-b_n-c_n$ otherwise. An affine change of $x$, together with the positive normalization $R_n(x_0)=1$ at the largest support point $x_0$, reduces every finite system to this form. A direction $v=(\delta b_1,\ldots,\delta b_{N-1},\delta c_1,\ldots,\delta c_N)$ changes these coordinates; we put $\delta b_0=\delta c_0=0$ and $\delta b_N=-\delta c_N$.
```

#### Lemma 9.2 (corner identity; defines A_N and s_N)
```latex
\begin{lemma}[Corner identity]\label{lem:corner}
Let $N\geq2$ and $s_N=(-1)^{\lfloor N/2\rfloor+1}\binom{N-1}{\lfloor(N-1)/2\rfloor}^{-1}$. Put $F=\delta b+2\delta c$ if $N$ is even and $F=\delta b$ if $N$ is odd. Then
\[
\frac{d}{d\varepsilon}\,g(N,N;N)\Big|_{K_{N,1}+\varepsilon v,\ \varepsilon=0}=s_N\sum_{n=0}^N(-1)^n\binom NnF(n).
\]
\end{lemma}
```

#### Definition 9.3
```latex
\begin{definition}\label{def:rule}
A \emph{uniform rule} is a pair of real functions $\beta,\gamma$ on $[0,1]$. It defines, for each $N$, the direction $v_N$ with $\delta b_n=\beta(n/N)$ for $1\leq n<N$ and $\delta c_n=\gamma(n/N)$ for $1\leq n\leq N$. A set of arrays \emph{admits} the rule at the symmetric endpoint if there is $N_0$ such that for every $N\geq N_0$ there is $\varepsilon_N>0$ with $K_{N,1}+\varepsilon v_N$ in the set for all $0<\varepsilon<\varepsilon_N$. Put
\[
L_{\mathrm{even}}=\beta(0)+2\gamma(0)+\beta(1)+\gamma(1),\qquad L_{\mathrm{odd}}=\beta(0)-\beta(1)-\gamma(1).
\]
\end{definition}
```

#### Theorem 9.4 (context)
```latex
\begin{theorem}[Forced equalities for uniform criteria]\label{thm:uniform}
Let $\beta,\gamma$ be polynomials. If a set of arrays with property (P) admits the rule $(\beta,\gamma)$ at the symmetric endpoint, then $L_{\mathrm{even}}=L_{\mathrm{odd}}=0$. If $L_{\mathrm{even}}=L_{\mathrm{odd}}=0$, the first-order change of $g(N,N;N)$ along $v_N$ vanishes for every $N$ above the degrees of $\beta$ and $\gamma$.
\end{theorem}
```

#### Paragraph before Lemma 9.5 (defines U and Ω)
```latex
The polynomial hypothesis can be replaced by analyticity on a fixed region. Let $U(x)=\int_0^1\log|x-t|\,dt$ and $\Omega=\{x\in\mathbb C:U(x)\leq-1\}$, the region of convergence of equispaced interpolation. It contains $[0,1]$, has nonanalytic boundary points (with vertical tangents) at $0$ and $1$, and meets the line $\operatorname{Re}x=\tfrac12$ at $\operatorname{Im}x=\pm0.2628\ldots$.
```

#### Lemma 9.5
```latex
\begin{lemma}[N\"orlund--Rice bound]\label{lem:nr}
If $f$ is analytic on an open set containing $\Omega$, then $\sum_{n=0}^N(-1)^n\binom Nnf(n/N)=O(\sqrt N\,e^{-\eta N})$ for some $\eta>0$.
\end{lemma}
```

#### Proof of Lemma 9.5 (context only)
```latex
\begin{proof}
The residues of $1/\prod_{k=0}^N(x-k/N)$ give
\[
\sum_{n=0}^N(-1)^n\binom Nnf(n/N)=(-1)^N\frac{N!}{N^N}\,\frac1{2\pi i}\oint_\Gamma\frac{f(x)\,dx}{\prod_{k=0}^N(x-k/N)}
\]
for any cycle $\Gamma$ in the domain of $f$ that winds once around $[0,1]$. Since $U$ is continuous and tends to $\infty$, the compact sets $\{U\leq-1+t\}$ shrink to $\Omega$ as $t\downarrow0$. Choose $\eta>0$ with $\{U\leq-1+3\eta\}$ inside the domain of $f$, and a bounded polygonal open set $V$ with $\{U\leq-1+\eta\}\subset V$ and $\overline V\subset\{U<-1+3\eta\}$. The oriented boundary $\Gamma$ of $V$, possibly with several components, is a cycle outside $\{U\leq-1+\eta\}$ that winds once around every node $k/N$ and bounds a region inside the domain of $f$. With $d=\operatorname{dist}(\Gamma,[0,1])>0$, the derivative of $t\mapsto\log|x-t|$ on $[0,1]$ is bounded by $1/d$ for $x\in\Gamma$, so a Riemann-sum estimate gives $\sum_{k=0}^N\log|x-k/N|\geq NU(x)-C_\Gamma\geq N(-1+\eta)-C_\Gamma$ with $C_\Gamma$ independent of $N$. Stirling's bound $N!/N^N\leq e\sqrt Ne^{-N}$ completes the proof.
\end{proof}
```

#### Corollary 9.6
```latex
\begin{corollary}\label{cor:analytic-rules}
Let $\beta,\gamma$ be analytic on an open set containing $\Omega$. If a set of arrays with property (P) admits the rule $(\beta,\gamma)$ at the symmetric endpoint, then $L_{\mathrm{even}}=L_{\mathrm{odd}}=0$. When these equalities hold, the first-order change of $g(N,N;N)$ along $v_N$ is $O(|s_N|\sqrt N\,e^{-\eta N})$; it need not vanish.
\end{corollary}
```

#### Proof of Corollary 9.6 (context only)
```latex
\begin{proof}
By Lemma~\ref{lem:nr}, the alternating sum of $\beta+2\gamma$ or $\beta$ is $O(\sqrt Ne^{-\eta N})$. The derivative in Lemma~\ref{lem:corner} is therefore $s_N(-L_{\mathrm{even}}+o(1))$ for even $N$ and $s_N(-L_{\mathrm{odd}}+o(1))$ for odd $N$, and the argument of Theorem~\ref{thm:uniform} gives the equalities. The rule $\beta(x)=e^x-1-(e-1)x$, $\gamma=0$ has $L_{\mathrm{even}}=L_{\mathrm{odd}}=0$ and derivative $s_N(1-e^{1/N})^N\neq0$.
\end{proof}
```

#### Proposition 9.9
```latex
\begin{proposition}[Families depending on $N$]\label{prop:families}
Let $v_N$ be directions such that a set with property (P) contains $K_{N,1}+\varepsilon v_N$ for all large $N$ and small $\varepsilon>0$, and let $A_N$ be the alternating sum in Lemma~\ref{lem:corner} for $v_N$. Then $s_NA_N\geq0$ for all large $N$.
\begin{enumerate}
\item Along either parity class, $A_N$ is not eventually strictly positive and not eventually strictly negative. If $A_N$ has an eventual weak sign along a parity class, it vanishes for all large $N$ of the residue class modulo $4$ on which that sign conflicts with the sign of $s_N$.
\item Suppose $\delta b_n=\beta(n/N)+p_n+q_{N-n}$ and $\delta c_n=\gamma(n/N)+p'_n+q'_{N-n}$, with $\beta,\gamma$ as in Corollary~\ref{cor:analytic-rules} and finitely supported boundary layers $p,q,p',q'$ independent of $N$. Then $q'_0=L_{\mathrm{even}}=L_{\mathrm{odd}}$, $p_k=q_k$ and $p'_k+q'_k=-p_k$ for $k\geq1$.
\end{enumerate}
\end{proposition}
```

#### Proof of Proposition 9.9 (context only)
```latex
\begin{proof}
A negative first-order change of $g(N,N;N)$ excludes $K_{N,1}+\varepsilon v_N$ for small $\varepsilon$, so $s_NA_N\geq0$. Part (1) follows because the sign of $s_N$ alternates along each parity class. In (2), write $D_Nf=\sum_{n=0}^N(-1)^n\binom Nnf(n/N)$. For large $N$, $A_N=D_N(\beta+2\gamma)+P_e(N)$ for even $N$ and $A_N=D_N\beta+P_o(N)$ for odd $N$, where
\begin{gather*}
P_e(N)=q'_0-L_{\mathrm{even}}+\sum_{k\geq1}(-1)^k\binom Nk\bigl[p_k+q_k+2(p'_k+q'_k)\bigr],\\
P_o(N)=q'_0-L_{\mathrm{odd}}+\sum_{k\geq1}(-1)^k\binom Nk(p_k-q_k).
\end{gather*}
These are polynomials in $N$. A nonzero polynomial has an eventual strict sign, which the remainder $O(\sqrt Ne^{-\eta N})$ of Lemma~\ref{lem:nr} cannot change, so part (1) forces $P_e\equiv P_o\equiv0$. The polynomials $1,\binom N1,\binom N2,\ldots$ are linearly independent, which gives the stated conditions.
\end{proof}
```

#### Code-and-formalization section: new table rows and scope sentences
```latex
Lemma~\ref{lem:nr}: N\"orlund--Rice bound & \path{Szkraw.norlund_rice}\\[3pt]
Corollary~\ref{cor:analytic-rules}: analytic rules & \path{Szkraw.analytic_forced_equalities}, \path{Szkraw.analytic_rule_small}, \path{Szkraw.expRule_analytic}, \path{Szkraw.expRule_L}, \path{Szkraw.expRule_deriv}\\[3pt]
Proposition~\ref{prop:families}: families depending on $N$ & \path{Szkraw.families_sign}, \path{Szkraw.families_weak_sign}, \path{Szkraw.families_no_strict_sign}, \path{Szkraw.families_boundary_layers}\\[3pt]

Lemma~\ref{lem:nr} is stated with $U(x)=\int_0^1\log|x-t|\,dt$ (\path{Szkraw.Ulog}) for $f$ complex differentiable on an open set containing $\Omega$, as a bound $C\sqrt N\,e^{-\eta N}$ for every $N\geq1$; the cycle of its proof is the boundary of a finite union of squares of a grid whose origin has irrational coordinates, so that no node $k/N$ lies on a grid line (\path{Szkraw.residue_identity}), and the Riemann-sum and Stirling estimates are \path{Szkraw.riemann_lower} and \path{Szkraw.factorial_le_stirling}. In Corollary~\ref{cor:analytic-rules} and Proposition~\ref{prop:families}~(2), a rule on $[0,1]$ is analytic on an open set containing $\Omega$ if it is the restriction of a function complex differentiable there (\path{Szkraw.AnalyticOnOmega}); the second statement of Corollary~\ref{cor:analytic-rules} is the bound $|s_N|\,C\sqrt N\,e^{-\eta N}$ on the derivative for every $N\geq2$, and the example is stated for every $N\geq2$. In Proposition~\ref{prop:families}~(2) the boundary layers vanish beyond a fixed index $K$, the formulas for $\delta b_n$ and $\delta c_n$ are assumed for $1\leq n\leq N-1$ and $1\leq n\leq N$ and all large $N$, and the hypothesis is that of the first statement; Corollary~\ref{cor:analytic-rules} is derived from it with zero boundary layers.

Every numbered result of Section~\ref{sec:limits} is formalized; its prose remarks, including the description of $\Omega$ and the computations away from $r=1$, are not.
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

/-- **Proposition 9.9 (1)**: along either parity class, `A_N` is neither eventually strictly
positive nor eventually strictly negative. -/
theorem families_no_strict_sign (S : (N : ℕ) → Set (Coefficients N))
    (hS : ∀ N, ∀ v ∈ S N, MatrixPositivity v) {vb vc : ℕ → ℕ → ℝ} (hfam : ContainsFamily S vb vc)
    (p : ℕ) (hp : p < 2) :
    ¬(∃ M, ∀ N, M ≤ N → N % 2 = p → 0 < altSum vb vc N) ∧
      ¬(∃ M, ∀ N, M ≤ N → N % 2 = p → altSum vb vc N < 0) := …
```

### lean/Szkraw/NorlundU.lean
```lean
/-- The logarithmic potential `U(x) = ∫_0^1 log|x - t| dt`. -/
noncomputable def Ulog (x : ℂ) : ℝ := ∫ t : ℝ in (0 : ℝ)..1, Real.log ‖x - t‖
```

### lean/Szkraw/NorlundResidue.lean
```lean
/-- The alternating binomial sum `Σ_{n=0}^N (-1)^n C(N,n) f(n/N)`. -/
noncomputable def altBinom (N : ℕ) (f : ℂ → ℂ) : ℂ :=
  ∑ n ∈ range (N + 1), (-1 : ℂ) ^ n * (N.choose n : ℂ) * f ((n : ℂ) / N)
```

### lean/Szkraw/Norlund.lean
```lean
/-- **Lemma 9.5 (Nörlund–Rice bound).** If `f` is holomorphic on an open set `D` containing
`Ω = {U ≤ -1}`, then `Σ_{n=0}^N (-1)^n C(N,n) f(n/N) = O(√N e^{-ηN})` for some `η > 0`. -/
theorem norlund_rice (f : ℂ → ℂ) (D : Set ℂ) (hD : IsOpen D) (hf : DifferentiableOn ℂ f D)
    (hΩ : {x : ℂ | Ulog x ≤ -1} ⊆ D) :
    ∃ η > 0, ∃ C : ℝ, ∀ N : ℕ, 1 ≤ N → ‖altBinom N f‖ ≤ C * Real.sqrt N * Real.exp (-(η * N)) := …
```

### lean/Szkraw/AnalyticRules.lean
```lean
/-- A rule `β` on `[0,1]` that extends to a function holomorphic on an open set containing
`Ω = {U ≤ -1}`. -/
def AnalyticOnOmega (β : ℝ → ℝ) : Prop :=
  ∃ (F : ℂ → ℂ) (D : Set ℂ), IsOpen D ∧ {x : ℂ | Ulog x ≤ -1} ⊆ D ∧ DifferentiableOn ℂ F D ∧
    ∀ t ∈ Set.Icc (0 : ℝ) 1, F t = β t

/-- `D_N φ = Σ_{n=0}^N (-1)^n C(N,n) φ(n/N)`. -/
noncomputable def DN (N : ℕ) (φ : ℝ → ℝ) : ℝ :=
  ∑ n ∈ range (N + 1), (-1 : ℝ) ^ n * (N.choose n : ℝ) * φ (n / N)

/-- The first-order change of `g(N,N;N)` along a general uniform rule. -/
theorem analytic_rule_deriv (β γ : ℝ → ℝ) {N : ℕ} (hN : 2 ≤ N) :
    HasDerivAt (fun ε => productMatrix (ruleArray β γ N ε) N (Fin.last N) (Fin.last N))
      (sN N * (if N % 2 = 0 then DN N (fun x => β x + 2 * γ x) - Leven β γ else DN N β - Lodd β γ)) 0 := …

/-- **Corollary 9.6**, first statement: if a set of arrays with property (P) admits an analytic
rule `(β, γ)` at the symmetric endpoint, then `L_even = L_odd = 0`. -/
theorem analytic_forced_equalities (S : (N : ℕ) → Set (Coefficients N))
    (hS : ∀ N, ∀ v ∈ S N, MatrixPositivity v) {β γ : ℝ → ℝ} (hβ : AnalyticOnOmega β)
    (hγ : AnalyticOnOmega γ) (hadm : AdmitsRule S β γ) : Leven β γ = 0 ∧ Lodd β γ = 0 := …

/-- **Corollary 9.6**, second statement: when `L_even = L_odd = 0`, the first-order change of
`g(N,N;N)` along `v_N` is `O(|s_N| √N e^{-ηN})`. -/
theorem analytic_rule_small {β γ : ℝ → ℝ} (hβ : AnalyticOnOmega β) (hγ : AnalyticOnOmega γ)
    (hL : Leven β γ = 0 ∧ Lodd β γ = 0) :
    ∃ η > 0, ∃ C, ∀ N : ℕ, 2 ≤ N → ∃ d,
      HasDerivAt (fun ε => productMatrix (ruleArray β γ N ε) N (Fin.last N) (Fin.last N)) d 0 ∧
        |d| ≤ |sN N| * (C * Real.sqrt N * Real.exp (-(η * N))) := …

/-- The rule `β(x) = e^x - 1 - (e - 1)x` of Corollary 9.6. -/
noncomputable def expRule (x : ℝ) : ℝ := Real.exp x - 1 - (Real.exp 1 - 1) * x

theorem expRule_analytic : AnalyticOnOmega expRule := …

theorem expRule_L : Leven expRule (fun _ => 0) = 0 ∧ Lodd expRule (fun _ => 0) = 0 := …

/-- **Corollary 9.6**, third statement: the rule `β(x) = e^x - 1 - (e - 1)x`, `γ = 0` is analytic
(entire), has `L_even = L_odd = 0`, and the first-order change of `g(N,N;N)` along it is
`s_N (1 - e^{1/N})^N ≠ 0`. -/
theorem expRule_deriv {N : ℕ} (hN : 2 ≤ N) :
    HasDerivAt (fun ε => productMatrix (ruleArray expRule (fun _ => 0) N ε) N (Fin.last N) (Fin.last N))
      (sN N * (1 - Real.exp (1 / N)) ^ N) 0 ∧ sN N * (1 - Real.exp (1 / N)) ^ N ≠ 0 := …

/-- **Proposition 9.9 (2)** (boundary layers): let `δb_n = β(n/N) + p_n + q_{N-n}` for
`1 ≤ n ≤ N - 1` and `δc_n = γ(n/N) + p'_n + q'_{N-n}` for `1 ≤ n ≤ N`, for all large `N`, with `β, γ` analytic on an
open set containing `Ω` and finitely supported boundary layers `p, q, p', q'` independent of `N`.
If a set with property (P) contains `K_{N,1} + ε v_N` for all large `N` and small `ε > 0`, then
`q'_0 = L_even = L_odd`, `p_k = q_k` and `p'_k + q'_k = -p_k` for `k ≥ 1`. -/
theorem families_boundary_layers (S : (N : ℕ) → Set (Coefficients N))
    (hS : ∀ N, ∀ v ∈ S N, MatrixPositivity v) {β γ : ℝ → ℝ} (hβ : AnalyticOnOmega β)
    (hγ : AnalyticOnOmega γ) {p q p' q' : ℕ → ℝ} {K : ℕ} (hp : ∀ k, K < k → p k = 0)
    (hq : ∀ k, K < k → q k = 0) (hp' : ∀ k, K < k → p' k = 0) (hq' : ∀ k, K < k → q' k = 0)
    {vb vc : ℕ → ℕ → ℝ} (hvb : ∃ N₁, ∀ N, N₁ ≤ N → ∀ n, 1 ≤ n → n < N → vb N n = β (n / N) + p n + q (N - n))
    (hvc : ∃ N₁, ∀ N, N₁ ≤ N → ∀ n, 1 ≤ n → n ≤ N → vc N n = γ (n / N) + p' n + q' (N - n))
    (hfam : ContainsFamily S vb vc) :
    q' 0 = Leven β γ ∧ q' 0 = Lodd β γ ∧ (∀ k, 1 ≤ k → p k = q k) ∧ ∀ k, 1 ≤ k → p' k + q' k = -p k := …
```
