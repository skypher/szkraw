# Independent review, round 9: three consequences stated in the text of Section 9

As in rounds 1–8 (round 8: PASS WITH MINOR FIXES, documentation only), **do not check proofs**. Check only whether each Lean statement faithfully expresses the paper's claim, under the acceptance rule: Lean hypotheses equivalent to or weaker than the paper's, and Lean conclusion equivalent to or stronger. Where the Lean statement covers less than the paper claims, say exactly what is missing.

This round covers three prose consequences, not numbered results:
- After Theorem 9.4 (`no_open_rule_set`): "for every d ≥ 0, no set of arrays with property (P) admits all rules of an open subset of the polynomial rules of degree at most d". Rules of degree ≤ d are given by coefficient vectors in (Fin (d+1) → ℝ)², with the product topology; `coeffPoly c = Σ_i c_i X^i`. The conclusion is that some rule in any nonempty open set is not admitted. Admission is Definition 9.3 (`AdmitsRule`), as in Theorem 9.4.
- After Proposition 9.9 (`boundary_layers_palindromic`), under the hypotheses of Proposition 9.9 (2):
  - the single equality γ(0) + β(1) + γ(1) = 0, the necessary part of "reduces the two bulk equalities to the single equality";
  - for k ≥ 1 and all N ≥ k + K + 1, the palindromic relations δb_k = δb_{N−k} and δa_k = δc_{N−k} for the boundary-layer contributions, with δa = −δb − δc inside.

  "the separate terminal adjustment need not itself be palindromic" is not formalized; it is a remark, not a claim to prove.
- After Corollary 9.13 (`radius_no_uniform`): "for every fixed r, no set of arrays with property (P) contains coefficient balls of a radius independent of N around all K_{N,r}". The balls are those of ρ_N(r) (Corollary 9.11): arrays satisfying (2.1), with b ≥ 0, within ρ coefficientwise of K_{N,r}. `stableRadii N r` is the set of such good radii. Lean states that for fixed 0 < r < 1 and every ρ > 0, ρ fails to be a good radius for all large N.
- Also check the new scope sentence.

Answer format: a table (paper claim | Lean declaration | MATCH / MATCH, SCOPE NOTED / MISMATCH | reason), exact fixes, and an overall verdict (PASS / PASS WITH MINOR FIXES / FAIL). Be terse.

## Part A. Paper text

#### After Theorem 9.4
```latex
The two functionals are independent already on constant rules, where $L_{\mathrm{even}}=2\beta+3\gamma$ and $L_{\mathrm{odd}}=-\gamma$. Consequently, for every $d\geq0$, no set of arrays with property (P) admits all rules of an open subset of the polynomial rules of degree at most $d$.
```

#### Proposition 9.9 (for context)
```latex
\begin{proposition}[Families depending on $N$]\label{prop:families}
Let $v_N$ be directions such that a set with property (P) contains $K_{N,1}+\varepsilon v_N$ for all large $N$ and small $\varepsilon>0$, and let $A_N$ be the alternating sum in Lemma~\ref{lem:corner} for $v_N$. Then $s_NA_N\geq0$ for all large $N$.
\begin{enumerate}
\item Along either parity class, $A_N$ is not eventually strictly positive and not eventually strictly negative. If $A_N$ has an eventual weak sign along a parity class, it vanishes for all large $N$ of the residue class modulo $4$ on which that sign conflicts with the sign of $s_N$.
\item Suppose $\delta b_n=\beta(n/N)+p_n+q_{N-n}$ and $\delta c_n=\gamma(n/N)+p'_n+q'_{N-n}$, with $\beta,\gamma$ as in Corollary~\ref{cor:analytic-rules} and finitely supported boundary layers $p,q,p',q'$ independent of $N$. Then $q'_0=L_{\mathrm{even}}=L_{\mathrm{odd}}$, $p_k=q_k$ and $p'_k+q'_k=-p_k$ for $k\geq1$.
\end{enumerate}
\end{proposition}
```

#### After Proposition 9.9
```latex
Thus a separate adjustment of the top coefficient $c_N$ reduces the two bulk equalities to the single equality $\gamma(0)+\beta(1)+\gamma(1)=0$. For $k\geq1$, the boundary-layer contributions satisfy the palindromic first-order relations $\delta b_k=\delta b_{N-k}$ and $\delta a_k=\delta c_{N-k}$; the separate terminal adjustment need not itself be palindromic.
```

#### Corollary 9.11 (defines rho_N(r))
```latex
\begin{corollary}[Optimal order of the stability radius]\label{cor:radius-order}
For $N\geq2$ let $\rho_N(r)$ be the largest $\rho$ such that every array satisfying \eqref{eq:basic} with $\widetilde b_i\geq0$ and with left side of \eqref{eq:closeness} at most $\rho$ has property (P). Then $\rho_N(r)$ is of exact order $(1-r)^N$ as $r\to1$.
\end{corollary}
```

#### Corollary 9.13 (for context)
```latex
\begin{corollary}[Exponentially small stability radius]\label{cor:radius-exp}
Let $0<r<1$, and let $\rho_N(r)$ be as in Corollary~\ref{cor:radius-order}. If $(1-r^2)^N\leq\tfrac12$ and $3(1-r^2)^N\leq(1-r)/N$, then
\[
\rho_N(r)\leq3\tau_N^*\max_nw_n\leq3(1-r^2)^N.
\]
In particular $\rho_N(r)=O\bigl((1-r^2)^N\bigr)$ as $N\to\infty$, for every fixed $r\in(0,1)$.
\end{corollary}
```

#### After Corollary 9.13
```latex
Thus, for every fixed $r$, no set of arrays with property (P) contains coefficient balls of a radius independent of $N$ around all $K_{N,r}$;
```

#### Code-and-formalization section: new scope sentence
```latex
Every numbered result of Section~\ref{sec:limits} is formalized, and so are three consequences stated in its text: no set with property (P) admits all rules of an open set of polynomial rules of degree at most $d$, with rules given by coefficient vectors (\path{Szkraw.no_open_rule_set}); the single equality $\gamma(0)+\beta(1)+\gamma(1)=0$ and the palindromic relations for the boundary layers after Proposition~\ref{prop:families} (\path{Szkraw.boundary_layers_palindromic}); and the absence of coefficient balls of a radius independent of $N$ around all $K_{N,r}$, in the sense of $\rho_N(r)$, after Corollary~\ref{cor:radius-exp} (\path{Szkraw.radius_no_uniform}). The other prose remarks of Section~\ref{sec:limits}, including the description of $\Omega$ and the computations away from $r=1$, are not formalized.
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


### lean/Szkraw/RadiusOrder.lean
```lean
/-- `v` is within `ρ` of `K_{N,r}` in the norm (5.2). -/
def WithinKraw {N : ℕ} (v : Coefficients N) (r ρ : ℝ) : Prop :=
  ∀ i, i ≤ N → |v.a i - ((N : ℝ) - i) / N| ≤ ρ ∧ |v.b i - ((1 - r) * i) / N| ≤ ρ ∧ |v.c i - (r * i) / N| ≤ ρ

/-- The radii `ρ ≥ 0` for which every array satisfying (2.1) with `b_i ≥ 0` within `ρ` of
`K_{N,r}` has property (P). -/
def stableRadii (N : ℕ) (r : ℝ) : Set ℝ :=
  {ρ | 0 ≤ ρ ∧ ∀ v : Coefficients N, Admissible v → (∀ i, i ≤ N → 0 ≤ v.b i) → WithinKraw v r ρ →
    MatrixPositivity v}

/-- `ρ_N(r)`, the stability radius of Corollary 9.11. -/
noncomputable def stabilityRadius (N : ℕ) (r : ℝ) : ℝ := sSup (stableRadii N r)
```

### lean/Szkraw/AnalyticRules.lean
```lean
/-- A rule `β` on `[0,1]` that extends to a function holomorphic on an open set containing
`Ω = {U ≤ -1}`. -/
def AnalyticOnOmega (β : ℝ → ℝ) : Prop :=
  ∃ (F : ℂ → ℂ) (D : Set ℂ), IsOpen D ∧ {x : ℂ | Ulog x ≤ -1} ⊆ D ∧ DifferentiableOn ℂ F D ∧
    ∀ t ∈ Set.Icc (0 : ℝ) 1, F t = β t

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

### lean/Szkraw/RadiusExp.lean
```lean
/-- Consequence of Corollary 9.13: for fixed `0 < r < 1`, no radius `ρ > 0` is stable for all
large `N`. Thus no set of arrays with property (P) contains coefficient balls of a radius
independent of `N` around all `K_{N,r}`. -/
theorem radius_no_uniform (hr : 0 < r) (hr1 : r < 1) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ N₀, ∀ N, N₀ ≤ N → ρ ∉ stableRadii N r := …
```

### lean/Szkraw/LimitsRemarks.lean
```lean
/-- The polynomial `Σ_{i ≤ d} c_i X^i` with coefficient vector `c`. -/
noncomputable def coeffPoly {d : ℕ} (c : Fin (d + 1) → ℝ) : ℝ[X] :=
  ∑ i, Polynomial.C (c i) * Polynomial.X ^ (i : ℕ)

/-- Consequence of Theorem 9.4: for every `d`, no set of arrays with property (P) admits all
rules of a nonempty open set of polynomial rules `(β, γ)` of degree at most `d` (rules given by
their coefficient vectors). -/
theorem no_open_rule_set (S : (N : ℕ) → Set (Coefficients N)) (hS : ∀ N, ∀ v ∈ S N, MatrixPositivity v)
    (d : ℕ) (U : Set ((Fin (d + 1) → ℝ) × (Fin (d + 1) → ℝ))) (hU : IsOpen U) (hne : U.Nonempty) :
    ∃ u ∈ U, ¬AdmitsRule S (coeffPoly u.1).eval (coeffPoly u.2).eval := …

/-- Consequences of Proposition 9.9 (2): `γ(0) + β(1) + γ(1) = 0`, and for `k ≥ 1` and all large
`N` the boundary-layer contributions `δb^L_n = p_n + q_{N-n}`, `δc^L_n = p'_n + q'_{N-n}`,
`δa^L_n = -δb^L_n - δc^L_n` satisfy `δb^L_k = δb^L_{N-k}` and `δa^L_k = δc^L_{N-k}`. -/
theorem boundary_layers_palindromic (S : (N : ℕ) → Set (Coefficients N))
    (hS : ∀ N, ∀ v ∈ S N, MatrixPositivity v) {β γ : ℝ → ℝ} (hβ : AnalyticOnOmega β)
    (hγ : AnalyticOnOmega γ) {p q p' q' : ℕ → ℝ} {K : ℕ} (hp : ∀ k, K < k → p k = 0)
    (hq : ∀ k, K < k → q k = 0) (hp' : ∀ k, K < k → p' k = 0) (hq' : ∀ k, K < k → q' k = 0)
    {vb vc : ℕ → ℕ → ℝ} (hvb : ∃ N₁, ∀ N, N₁ ≤ N → ∀ n, 1 ≤ n → n < N → vb N n = β (n / N) + p n + q (N - n))
    (hvc : ∃ N₁, ∀ N, N₁ ≤ N → ∀ n, 1 ≤ n → n ≤ N → vc N n = γ (n / N) + p' n + q' (N - n))
    (hfam : ContainsFamily S vb vc) :
    γ 0 + β 1 + γ 1 = 0 ∧ ∀ k, 1 ≤ k → ∀ N, k + K + 1 ≤ N →
      p k + q (N - k) = p (N - k) + q (N - (N - k)) ∧
        -(p k + q (N - k)) - (p' k + q' (N - k)) = p' (N - k) + q' (N - (N - k)) := …
```
