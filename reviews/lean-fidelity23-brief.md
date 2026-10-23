# Lean statement fidelity, round 23: exact computational counterexamples in P1, P2 and P3

Repository: github.com/skypher/szkraw, commit 81eddf3, files lean/Szkraw/{RatioCounterexamples,ProfileCounterexamples,RuleCounterexamples,ComboCounterexamples,ColumnCheck}.lean. Axiom audit: lean/axioms.log (only propext, Classical.choice, Quot.sound for every theorem below).

As in earlier rounds, **do not check proofs**. Check whether each Lean statement says what the cited passage says (Lean hypotheses equivalent or weaker, conclusions equivalent or stronger), and whether the proposed text changes are accurate. Conventions as in rounds 1–22 (`Coefficients`, `Admissible` = (2.1), `MatrixPositivity`, `productMatrix v m n k = g(m,n;k)`, `profile v i = b_i + c_i`, `newtonCoeff d k = Δ^k d(0)`). Statements of the form "∃ v admissible with profile d and c = ρ d, and every admissible v with profile d and c = ρ d has …" fix a, b, c on 0 ≤ i ≤ N, as accepted in round 22. The negative coefficients are decided by exact integer columns of the product table evaluated in the Lean kernel (`decide +kernel`, no `native_decide`); this is proof method, not to be checked.

## Paper passages

P1, paragraph "How sharp is log-concavity?" (first part):

In Theorem~\ref{thm:lc} the Krawtchouk arrays lie on the edge of the hypothesis on the profile, and the arrays $G_{N,q,r}$ lie on its boundary, with equality in every log-concavity inequality. Positivity of the Newton coefficients of the profile does not suffice. For $q>1$ and $0<\lambda<1$ the combination $(1-\lambda)K_{N,r}+\lambda G_{N,q,r}$ is a stochastic array with constant ratio $b_i/c_i$ and increments proportional to $1+t\,q^{i-N}$, where $t=\lambda N(q-1)q^{N-1}/((1-\lambda)(q^N-1))$; its Newton coefficients are positive, and for $N\geq3$ one has $\nu_2^2<\nu_1\nu_3$ (Section~\ref{sec:lc}). Exact computation (\path{convexity_probe.py}) gives $g(N,N;N)<0$ for this combination at $(r,N,q,t)=(4/5,10,10,1)$, $(3/5,20,10,2)$, $(1/2,20,10,1)$, $(2/5,60,10,2)$, $(1/3,100,10,2)$, $(3/10,200,2,5)$ and $(2/7,200,10,5)$. In particular, at these parameters no sufficient criterion whose admitted set is convex, such as a system of linear inequalities in the coefficients, can admit both $K_{N,r}$ and $G_{N,q,r}$.

P2, Section 6 (counterexamples and open problems):

Increasing ratios with nondecreasing $b$ can fail as well: for the linear profile $d_i=i/3$ and the concave ratio $\rho=(1/2,3/4,5/6)$, for which $b_i=1/6$ for $i\geq1$, one has $g(3,3;3)=-1/24$, and a convex kinked ratio on the linear profile fails at $N=120$~\cite{P3}.

Even the bound $r\leq\frac9{10}$ does not restore (P) for cubic ratios: on linear profiles with $\kappa=1/80$, which keeps $b$ nondecreasing, $\rho_i=\frac9{10}+\kappa\binom i3/\binom N3$ gives $g(48,48;48)<0$ for $N=48$, and $\rho_i=\frac9{10}+\kappa(i/N)^3$ gives $g(64,64;63)<0$ for $N=64$. Steeper ratios fail at smaller $r$, again with nondecreasing $b$ and nonnegative Newton coefficients of $\rho$: $\rho_i=\frac12+10^{i-N}/100$ gives $g(40,40;40)<0$ for $N=40$, and raising only the last ratio, $\rho_i=r$ for $i<N$ and $\rho_N=r+(1-r)/N$, gives $g(40,40;38)<0$ for $r=\frac12$, $N=40$ and $g(120,120;119)<0$ for $r=\frac25$, $N=120$ (\path{runs/varratio/frontier_examples.py}). Write a cubic ratio as $\rho(x)=r+tx+\tau\binom x2+\sigma\binom x3$. The cubic examples above violate $r\sigma\leq t\tau$, a consequence of log-concavity without internal zeros of $(r,t,\tau,\sigma)$: in the first two $t=\tau=0$, and for $\kappa(i/N)^3$ one has $t\tau=6\kappa^2/N^6<r\sigma=6r\kappa/N^3$.

P3, Section 9 (limits), fixed r:

Exact computations (\path{fixedr_probe.py}) confirm failures of property (P) along the terminal row at sizes down to $10^{-15}$ for $r=4/5$, $N=40$. The comparison at $r=\tfrac12$ concerns only the first-order term. Along the terminal row, $g(N,N;N)$ is a polynomial in the perturbation, since the recurrence for the linearization coefficients divides only by $a_0,\ldots,a_{N-1}$.  Exact terminal-row failures also occur for $r\leq\tfrac12$: at size $6.3\cdot10^{-6}$ for $r=\tfrac12$, $N=120$; at size $3.2\cdot10^{-3}$ for $r=\tfrac25$, $N=100$; and at size $1.6\cdot10^{-2}$ for $r=\tfrac13$, $N=120$.

P3, Section 9, computations away from r = 1:

\paragraph{Computations away from $r=1$.}
The explicit fixed-size, one-kink, and log-concave-increment examples below are reproduced by \path{rigidity_probe.py} and \path{smallr_probe.py}. Exact rational computations certify the stated finite examples; the separately labelled high-precision calculations provide numerical evidence. No asymptotic conclusion is asserted. Here $g(N,N;N)$ is computed from column $N$ of the product table, an $O(N^2)$-operation recurrence, so sizes in the hundreds are cheap.
\begin{itemize}
\item For the rule $\beta=1$, $\gamma=0$, exact computation shows that property (P) fails at $r=4/5$, with perturbation size $1/100$, for every $N=6,\ldots,14$, and at $r=19/20$, with perturbation size $1/1000$, for every $N=4,\ldots,14$. The period-four sign pattern at $r=1$ does not persist in general for $r<1$: at $r=4/5$ the first-order derivatives are $512/1875$ for $N=4$ and $-71936/5859375$ for $N=8$.
\item Below $r=\tfrac12$, the counterexamples we found to shape conditions occur at sizes that grow as $r$ decreases; we did not determine minimal sizes or prove a scaling. For constant-ratio arrays with convex profile, one-kink counterexamples ($m$ unit increments, then $1+\delta$) have $g(N,N;N)<0$ in exact arithmetic at
\begin{center}
\begin{tabular}{@{}lccccccc@{}}
$r$&$2/5$&$1/3$&$3/10$&$1/4$&$2/7$&$1/5$&$1/10$\\
$N$&$20$&$40$&$40$&$60$&$80$&$100$&$500$
\end{tabular}
\end{center}
\item Convex profiles with log-concave increments (step ratios nonincreasing and at least $1$) contain Krawtchouk, every geometric profile and the normalized quadratic profiles $d_\kappa(x)=(x+\kappa x^2)/(1+\kappa)$, $\kappa\geq0$, and they exclude the one-kink counterexamples. Yet $k$ steps of ratio $1+1/(2N)$ followed by flat increments give $g(N,N;N)<0$ at $(r,N,k)=(\tfrac12,80,40)$, $(\tfrac25,32,22)$ and $(\tfrac13,90,62)$ in exact arithmetic. In $80$- and $150$-digit floating-point arithmetic, which agree but are not exact sign certificates, the same happens at $(\tfrac14,250,175)$ and $(\tfrac15,500,400)$.
\end{itemize}

P3, open problems:

Convexity of the profile does not suffice even with a constant ratio and $r$ bounded away from $1$: for $d$ with increments $1$ at the first seven steps and $6/5$ at the remaining seven ($N=14$), exact arithmetic gives $g(14,14;14)<0$ at $r=1/2$, and the analogous profile with $N=20$, twelve unit increments and $21/20$ afterwards gives $g(20,20;20)<0$ at $r=2/5$. Log-convex increments fail as well: fourteen unit increments followed by $(21/20)^t$, $t=1,\ldots,4$, give $g(18,18;18)<0$ at $r=1/2$.

## Lean declarations

```lean
-- Thinness.lean (existing)
/-- The stochastic array with coordinates `b_1, …, b_{N-1}, c_1, …, c_N`. -/
def stochArray (N : ℕ) (b c : ℕ → ℝ) : Coefficients N where
  a i := if i = 0 then 1 else if i = N then 0 else 1 - b i - c i
  b i := if i = 0 then 0 else if i = N then 1 - c N else b i
  c i := if i = 0 then 0 else c i

/-- `K_{N,r} + ε v` for the direction `v = (δb, δc)` in the coordinates of `stochArray`. -/
noncomputable def krawDir (N : ℕ) (δb δc : ℕ → ℝ) (r ε : ℝ) : Coefficients N :=
  stochArray N (fun n => (1 - r) * n / N + ε * δb n) (fun n => r * n / N + ε * δc n)

-- Parameters.lean (existing; p = 1/r)
noncomputable def geometricCoefficients (N : ℕ) (p q : ℝ) : Coefficients N where
  a i := q^i*qInteger q (N-i)/qInteger q N
  b i := (p-1)*qInteger q i/(p*qInteger q N)
  c i := qInteger q i/(p*qInteger q N)

-- RatioCounterexamples.lean
/-- **P2, Section 6, cubic ratio with `t = τ = 0`.** For `N = 48`, the linear profile and
`ρ_i = 9/10 + κ C(i,3)/C(N,3)` with `κ = 1/80`: `b` is nondecreasing and `g(48,48;48) < 0`. -/
theorem cubicBinom48_fails :
    let d : ℕ → ℝ := fun i => i / 48
    let ρ : ℕ → ℝ := fun i => 9 / 10 + 1 / 80 * (i.choose 3 : ℝ) / (Nat.choose 48 3 : ℝ)
    (∃ v : Coefficients 48, Admissible v ∧ (∀ i, i ≤ 48 → profile v i = d i) ∧
      ∀ i, i ≤ 48 → v.c i = ρ i * profile v i) ∧
    ∀ v : Coefficients 48, Admissible v → (∀ i, i ≤ 48 → profile v i = d i) →
      (∀ i, i ≤ 48 → v.c i = ρ i * profile v i) →
      (∀ i, i < 48 → v.b i ≤ v.b (i + 1)) ∧ productMatrix v 48 48 48 < 0 := …

/-- **P2, Section 6, cubic ratio `9/10 + κ (i/N)³`.** For `N = 64`, the linear profile and
`ρ_i = 9/10 + κ (i/N)³` with `κ = 1/80`: `b` is nondecreasing and `g(64,64;63) < 0`. In the binomial basis
`ρ(x) = r + t x + τ C(x,2) + σ C(x,3)` with `r = 9/10`, `t = κ/N³`, `τ = σ = 6κ/N³`, and `t τ < r σ`. -/
theorem cubicPow64_fails :
    let d : ℕ → ℝ := fun i => i / 64
    let ρ : ℕ → ℝ := fun i => 9 / 10 + 1 / 80 * ((i : ℝ) / 64) ^ 3
    ((∃ v : Coefficients 64, Admissible v ∧ (∀ i, i ≤ 64 → profile v i = d i) ∧
      ∀ i, i ≤ 64 → v.c i = ρ i * profile v i) ∧
    ∀ v : Coefficients 64, Admissible v → (∀ i, i ≤ 64 → profile v i = d i) →
      (∀ i, i ≤ 64 → v.c i = ρ i * profile v i) →
      (∀ i, i < 64 → v.b i ≤ v.b (i + 1)) ∧ productMatrix v 64 64 63 < 0) ∧
    (∀ i : ℕ, ρ i = 9 / 10 + 1 / 80 / 64 ^ 3 * i + 6 / 80 / 64 ^ 3 * (i.choose 2 : ℝ) +
      6 / 80 / 64 ^ 3 * (i.choose 3 : ℝ)) ∧
    (1 / 80 / 64 ^ 3 : ℝ) * (6 / 80 / 64 ^ 3) < 9 / 10 * (6 / 80 / 64 ^ 3) := …

/-- **P2, Section 6, steep ratio.** For `N = 40`, the linear profile and `ρ_i = 1/2 + 10^(i-N)/100`: the Newton
coefficients of `ρ` are nonnegative, `b` is nondecreasing and `g(40,40;40) < 0`. -/
theorem steepRatio40_fails :
    let d : ℕ → ℝ := fun i => i / 40
    let ρ : ℕ → ℝ := fun i => 1 / 2 + (10 : ℝ) ^ ((i : ℤ) - 40) / 100
    (∀ k, 0 ≤ newtonCoeff ρ k) ∧
    (∃ v : Coefficients 40, Admissible v ∧ (∀ i, i ≤ 40 → profile v i = d i) ∧
      ∀ i, i ≤ 40 → v.c i = ρ i * profile v i) ∧
    ∀ v : Coefficients 40, Admissible v → (∀ i, i ≤ 40 → profile v i = d i) →
      (∀ i, i ≤ 40 → v.c i = ρ i * profile v i) →
      (∀ i, i < 40 → v.b i ≤ v.b (i + 1)) ∧ productMatrix v 40 40 40 < 0 := …

/-- **P2, Section 6, raising only the last ratio, `N = 40`.** For the linear profile, `r = 1/2`, `ρ_i = r` for
`i < N` and `ρ_N = r + (1-r)/N`: the Newton coefficients of `ρ` on `0 ≤ k ≤ N` are nonnegative, `b` is
nondecreasing and `g(40,40;38) < 0`. -/
theorem topRatio40_fails :
    let d : ℕ → ℝ := fun i => i / 40
    let ρ : ℕ → ℝ := fun i => 1 / 2 + (1 - 1 / 2) / 40 * if i = 40 then 1 else 0
    (∀ k, k ≤ 40 → 0 ≤ newtonCoeff ρ k) ∧
    (∃ v : Coefficients 40, Admissible v ∧ (∀ i, i ≤ 40 → profile v i = d i) ∧
      ∀ i, i ≤ 40 → v.c i = ρ i * profile v i) ∧
    ∀ v : Coefficients 40, Admissible v → (∀ i, i ≤ 40 → profile v i = d i) →
      (∀ i, i ≤ 40 → v.c i = ρ i * profile v i) →
      (∀ i, i < 40 → v.b i ≤ v.b (i + 1)) ∧ productMatrix v 40 40 38 < 0 := …

/-- **P2, Section 6, raising only the last ratio, `N = 120`** (the convex kinked ratio at `N = 120`). For the
linear profile, `r = 2/5`, `ρ_i = r` for `i < N` and `ρ_N = r + (1-r)/N`: the Newton coefficients of `ρ` on
`0 ≤ k ≤ N` are nonnegative, `b` is nondecreasing and `g(120,120;119) < 0`. -/
theorem topRatio120_fails :
    let d : ℕ → ℝ := fun i => i / 120
    let ρ : ℕ → ℝ := fun i => 2 / 5 + (1 - 2 / 5) / 120 * if i = 120 then 1 else 0
    (∀ k, k ≤ 120 → 0 ≤ newtonCoeff ρ k) ∧
    (∃ v : Coefficients 120, Admissible v ∧ (∀ i, i ≤ 120 → profile v i = d i) ∧
      ∀ i, i ≤ 120 → v.c i = ρ i * profile v i) ∧
    ∀ v : Coefficients 120, Admissible v → (∀ i, i ≤ 120 → profile v i = d i) →
      (∀ i, i ≤ 120 → v.c i = ρ i * profile v i) →
      (∀ i, i < 120 → v.b i ≤ v.b (i + 1)) ∧ productMatrix v 120 120 119 < 0 := …

-- ProfileCounterexamples.lean
/-- The normalized profile with increments `e`: `d_i = (Σ_{j<i} e_j) / (Σ_{j<N} e_j)`. -/
noncomputable def incProfile (e : ℕ → ℝ) (N i : ℕ) : ℝ := (∑ j ∈ range i, e j) / ∑ j ∈ range N, e j

/-- One-kink increments: `1` for the first `m` steps, then `1 + δ`. -/
noncomputable def kinkInc (m : ℕ) (δ : ℝ) (j : ℕ) : ℝ := if j < m then 1 else 1 + δ

/-- Log-concave increments: `k` steps of ratio `q`, then flat (`e_j = q^min(j,k)`). -/
noncomputable def stepInc (q : ℝ) (k j : ℕ) : ℝ := q ^ min j k

/-- Shape of the one-kink statements: constant ratio `r`, profile with increments `kinkInc m δ`. -/
def KinkFails (r δ : ℝ) (N m : ℕ) : Prop :=
  (∃ v : Coefficients N, Admissible v ∧ (∀ i, i ≤ N → profile v i = incProfile (kinkInc m δ) N i) ∧
    ∀ i, i ≤ N → v.c i = r * profile v i) ∧
  ∀ v : Coefficients N, Admissible v → (∀ i, i ≤ N → profile v i = incProfile (kinkInc m δ) N i) →
    (∀ i, i ≤ N → v.c i = r * profile v i) → productMatrix v N (Fin.last N) (Fin.last N) < 0

/-- Shape of the statements with increments `e`: constant ratio `r`, profile `incProfile e N`. -/
def IncFails (r : ℝ) (e : ℕ → ℝ) (N : ℕ) : Prop :=
  (∃ v : Coefficients N, Admissible v ∧ (∀ i, i ≤ N → profile v i = incProfile e N i) ∧
    ∀ i, i ≤ N → v.c i = r * profile v i) ∧
  ∀ v : Coefficients N, Admissible v → (∀ i, i ≤ N → profile v i = incProfile e N i) →
    (∀ i, i ≤ N → v.c i = r * profile v i) → productMatrix v N (Fin.last N) (Fin.last N) < 0

/-- Log-convex increments: fourteen unit increments, then `(21/20)^t`, `t = 1, …, 4`, i.e. `e_j = (21/20)^(j-13)`
for `j < 18` (truncated subtraction). -/
noncomputable def cvxInc (j : ℕ) : ℝ := (21 / 20 : ℝ) ^ (j - 13)

/-- `r = 1/2`, `N = 14`: seven unit increments, then `6/5` (P3, open problems). -/
theorem kink14_fails : KinkFails (1 / 2) (1 / 5) 14 7 := …

/-- `r = 2/5`, `N = 20`: twelve unit increments, then `21/20` (P3, Section 9 table and open problems). -/
theorem kink20_2_5_fails : KinkFails (2 / 5) (1 / 20) 20 12 := …

/-- `r = 1/3`, `N = 40`, `m = 28`, `δ = 1/5` (P3, Section 9 table). -/
theorem kink40_1_3_fails : KinkFails (1 / 3) (1 / 5) 40 28 := …

/-- `r = 3/10`, `N = 40`, `m = 28`, `δ = 1/10` (P3, Section 9 table). -/
theorem kink40_3_10_fails : KinkFails (3 / 10) (1 / 10) 40 28 := …

/-- `r = 1/4`, `N = 60`, `m = 45`, `δ = 1/10` (P3, Section 9 table). -/
theorem kink60_1_4_fails : KinkFails (1 / 4) (1 / 10) 60 45 := …

/-- `r = 2/7`, `N = 80`, `m = 60`, `δ = 1/5` (P3, Section 9 table). -/
theorem kink80_2_7_fails : KinkFails (2 / 7) (1 / 5) 80 60 := …

/-- `r = 1/5`, `N = 100`, `m = 80`, `δ = 1/10` (P3, Section 9 table). -/
theorem kink100_1_5_fails : KinkFails (1 / 5) (1 / 10) 100 80 := …

/-- The increments `stepInc q k` with `q ≥ 1` are log-concave: step ratios at least `1` and nonincreasing. -/
theorem stepInc_logconcave (q : ℝ) (hq : 1 ≤ q) (k : ℕ) :
    (∀ j, 1 ≤ stepInc q k (j + 1) / stepInc q k j) ∧
    ∀ j, stepInc q k (j + 2) / stepInc q k (j + 1) ≤ stepInc q k (j + 1) / stepInc q k j := …

/-- `k` steps of ratio `1 + 1/(2N)`, then flat increments: `r = 2/5`, `N = 32`, `k = 22` (P3, Section 9). -/
theorem logconcave32_fails : IncFails (2 / 5) (stepInc (1 + 1 / (2 * 32)) 22) 32 := …

/-- `r = 1/2`, `N = 80`, `k = 40` steps of ratio `1 + 1/(2N)`, then flat increments (P3, Section 9). -/
theorem logconcave80_fails : IncFails (1 / 2) (stepInc (1 + 1 / (2 * 80)) 40) 80 := …

/-- `r = 1/3`, `N = 90`, `k = 62` steps of ratio `1 + 1/(2N)`, then flat increments (P3, Section 9). -/
theorem logconcave90_fails : IncFails (1 / 3) (stepInc (1 + 1 / (2 * 90)) 62) 90 := …

/-- The increments `cvxInc` are log-convex: step ratios at least `1` and nondecreasing. -/
theorem cvxInc_logconvex :
    (∀ j, 1 ≤ cvxInc (j + 1) / cvxInc j) ∧ ∀ j, cvxInc (j + 1) / cvxInc j ≤ cvxInc (j + 2) / cvxInc (j + 1) := …

/-- `r = 1/2`, `N = 18`, log-convex increments `cvxInc` (P3, open problems). -/
theorem logconvex18_fails : IncFails (1 / 2) cvxInc 18 := …

-- RuleCounterexamples.lean
/-- **P3, Section 9**: for the rule `β = 1`, `γ = 0`, property (P) fails at `r = 4/5` with perturbation size
`1/100` for every `N = 6, …, 14`; the perturbed arrays are admissible with `b ≥ 0`. -/
theorem rule_fails_4_5 (N : ℕ) (h6 : 6 ≤ N) (h14 : N ≤ 14) :
    let v := krawDir N (fun _ => 1) (fun _ => 0) (4 / 5) (1 / 100)
    Admissible v ∧ (∀ i, i ≤ N → 0 ≤ v.b i) ∧ ¬ MatrixPositivity v := …

/-- **P3, Section 9**: for the rule `β = 1`, `γ = 0`, property (P) fails at `r = 19/20` with perturbation size
`1/1000` for every `N = 4, …, 14`; the perturbed arrays are admissible with `b ≥ 0`. -/
theorem rule_fails_19_20 (N : ℕ) (h4 : 4 ≤ N) (h14 : N ≤ 14) :
    let v := krawDir N (fun _ => 1) (fun _ => 0) (19 / 20) (1 / 1000)
    Admissible v ∧ (∀ i, i ≤ N → 0 ≤ v.b i) ∧ ¬ MatrixPositivity v := …

/-- `K_{N,r}` with `c_N → c_N + e`, `b_N → b_N - e`. -/
noncomputable def termArray (N : ℕ) (r e : ℝ) : Coefficients N :=
  krawDir N (fun _ => 0) (fun n => if n = N then 1 else 0) r e

/-- **P3, Section 9**: along the terminal direction, property (P) fails at size `10⁻¹⁵` for `r = 4/5`, `N = 40`
(`e = 10⁻¹⁵`), at size `6.3 · 10⁻⁶` for `r = 1/2`, `N = 120`, at size `3.2 · 10⁻³` for `r = 2/5`, `N = 100`, and at
size `1.6 · 10⁻²` for `r = 1/3`, `N = 120` (`e < 0` in the last three); the arrays are admissible with `b ≥ 0`
and `g(N,N;N) < 0`. -/
theorem terminal_fails :
    (Admissible (termArray 40 (4 / 5) (1 / 10 ^ 15)) ∧ (∀ i, i ≤ 40 → 0 ≤ (termArray 40 (4 / 5) (1 / 10 ^ 15)).b i) ∧
      productMatrix (termArray 40 (4 / 5) (1 / 10 ^ 15)) 40 (Fin.last 40) (Fin.last 40) < 0) ∧
    (Admissible (termArray 120 (1 / 2) (-63 / 10 ^ 7)) ∧
      (∀ i, i ≤ 120 → 0 ≤ (termArray 120 (1 / 2) (-63 / 10 ^ 7)).b i) ∧
      productMatrix (termArray 120 (1 / 2) (-63 / 10 ^ 7)) 120 (Fin.last 120) (Fin.last 120) < 0) ∧
    (Admissible (termArray 100 (2 / 5) (-32 / 10 ^ 4)) ∧
      (∀ i, i ≤ 100 → 0 ≤ (termArray 100 (2 / 5) (-32 / 10 ^ 4)).b i) ∧
      productMatrix (termArray 100 (2 / 5) (-32 / 10 ^ 4)) 100 (Fin.last 100) (Fin.last 100) < 0) ∧
    (Admissible (termArray 120 (1 / 3) (-16 / 10 ^ 3)) ∧
      (∀ i, i ≤ 120 → 0 ≤ (termArray 120 (1 / 3) (-16 / 10 ^ 3)).b i) ∧
      productMatrix (termArray 120 (1 / 3) (-16 / 10 ^ 3)) 120 (Fin.last 120) (Fin.last 120) < 0) := …

-- ComboCounterexamples.lean
/-- The convex combination `(1 - lam) v + lam w` of two arrays. -/
noncomputable def combo {N : ℕ} (lam : ℝ) (v w : Coefficients N) : Coefficients N where
  a i := (1 - lam) * v.a i + lam * w.a i
  b i := (1 - lam) * v.b i + lam * w.b i
  c i := (1 - lam) * v.c i + lam * w.c i

/-- The weight `lam` of `G` that gives the parameter `t`. -/
noncomputable def comboLam (N : ℕ) (q t : ℝ) : ℝ :=
  let u := t * (q ^ N - 1) / (N * (q - 1) * q ^ (N - 1))
  u / (1 + u)

/-- **P1, "How sharp is log-concavity?"**, the combination: for `N ≥ 1`, `p = 1/r ≥ 1`, `q > 1` and `0 < λ < 1`,
`(1-λ) K_{N,r} + λ G_{N,q,r}` is admissible with `c_i = r d_i`, its increments are `(1-λ)/N (1 + t q^(i-N))` with
`t = λ N (q-1) q^(N-1) / ((1-λ)(q^N - 1))`, its Newton coefficients `ν_1, …, ν_N` are positive, and
`ν₂² < ν₁ ν₃` if `N ≥ 3`. -/
theorem combo_shape (N : ℕ) (hN : 1 ≤ N) (p q lam : ℝ) (hp : 1 ≤ p) (hq : 1 < q) (h0 : 0 < lam) (h1 : lam < 1) :
    let v := combo lam (geometricCoefficients N p 1) (geometricCoefficients N p q)
    let t := lam * N * (q - 1) * q ^ (N - 1) / ((1 - lam) * (q ^ N - 1))
    Admissible v ∧ (∀ i, i ≤ N → v.c i = p⁻¹ * profile v i) ∧
    (∀ i, 1 ≤ i → i ≤ N → profile v i - profile v (i - 1) = (1 - lam) / N * (1 + t * q ^ ((i : ℤ) - N))) ∧
    (∀ k, 1 ≤ k → k ≤ N → 0 < newtonCoeff (profile v) k) ∧
    (3 ≤ N → newtonCoeff (profile v) 2 ^ 2 < newtonCoeff (profile v) 1 * newtonCoeff (profile v) 3) := …

/-- `(r, N, q, t) = (4/5, 10, 10, 1)`: `K` and `G` have (P), the combination is admissible and
`g(10,10;10) < 0`. -/
theorem combo_fails_4_5_10 :
    let r : ℝ := ((4 : ℤ) : ℝ) / ((5 : ℤ) : ℝ)
    let lam := comboLam 10 ((10 : ℤ) : ℝ) ((1 : ℤ) : ℝ)
    0 < lam ∧ lam < 1 ∧
    lam * 10 * (((10 : ℤ) : ℝ) - 1) * ((10 : ℤ) : ℝ) ^ (10 - 1) / ((1 - lam) * (((10 : ℤ) : ℝ) ^ 10 - 1)) = ((1 : ℤ) : ℝ) ∧
    MatrixPositivity (geometricCoefficients 10 r⁻¹ 1) ∧ MatrixPositivity (geometricCoefficients 10 r⁻¹ ((10 : ℤ) : ℝ)) ∧
    Admissible (combo lam (geometricCoefficients 10 r⁻¹ 1) (geometricCoefficients 10 r⁻¹ ((10 : ℤ) : ℝ))) ∧
    productMatrix (combo lam (geometricCoefficients 10 r⁻¹ 1) (geometricCoefficients 10 r⁻¹ ((10 : ℤ) : ℝ)))
      10 (Fin.last 10) (Fin.last 10) < 0 := …

/-- `(r, N, q, t) = (3/5, 20, 10, 2)`: `K` and `G` have (P), the combination is admissible and
`g(20,20;20) < 0`. -/
theorem combo_fails_3_5_20 :
    let r : ℝ := ((3 : ℤ) : ℝ) / ((5 : ℤ) : ℝ)
    let lam := comboLam 20 ((10 : ℤ) : ℝ) ((2 : ℤ) : ℝ)
    0 < lam ∧ lam < 1 ∧
    lam * 20 * (((10 : ℤ) : ℝ) - 1) * ((10 : ℤ) : ℝ) ^ (20 - 1) / ((1 - lam) * (((10 : ℤ) : ℝ) ^ 20 - 1)) = ((2 : ℤ) : ℝ) ∧
    MatrixPositivity (geometricCoefficients 20 r⁻¹ 1) ∧ MatrixPositivity (geometricCoefficients 20 r⁻¹ ((10 : ℤ) : ℝ)) ∧
    Admissible (combo lam (geometricCoefficients 20 r⁻¹ 1) (geometricCoefficients 20 r⁻¹ ((10 : ℤ) : ℝ))) ∧
    productMatrix (combo lam (geometricCoefficients 20 r⁻¹ 1) (geometricCoefficients 20 r⁻¹ ((10 : ℤ) : ℝ)))
      20 (Fin.last 20) (Fin.last 20) < 0 := …

/-- `(r, N, q, t) = (1/2, 20, 10, 1)`: `K` and `G` have (P), the combination is admissible and
`g(20,20;20) < 0`. -/
theorem combo_fails_1_2_20 :
    let r : ℝ := ((1 : ℤ) : ℝ) / ((2 : ℤ) : ℝ)
    let lam := comboLam 20 ((10 : ℤ) : ℝ) ((1 : ℤ) : ℝ)
    0 < lam ∧ lam < 1 ∧
    lam * 20 * (((10 : ℤ) : ℝ) - 1) * ((10 : ℤ) : ℝ) ^ (20 - 1) / ((1 - lam) * (((10 : ℤ) : ℝ) ^ 20 - 1)) = ((1 : ℤ) : ℝ) ∧
    MatrixPositivity (geometricCoefficients 20 r⁻¹ 1) ∧ MatrixPositivity (geometricCoefficients 20 r⁻¹ ((10 : ℤ) : ℝ)) ∧
    Admissible (combo lam (geometricCoefficients 20 r⁻¹ 1) (geometricCoefficients 20 r⁻¹ ((10 : ℤ) : ℝ))) ∧
    productMatrix (combo lam (geometricCoefficients 20 r⁻¹ 1) (geometricCoefficients 20 r⁻¹ ((10 : ℤ) : ℝ)))
      20 (Fin.last 20) (Fin.last 20) < 0 := …

/-- `(r, N, q, t) = (2/5, 60, 10, 2)`: `K` and `G` have (P), the combination is admissible and
`g(60,60;60) < 0`. -/
theorem combo_fails_2_5_60 :
    let r : ℝ := ((2 : ℤ) : ℝ) / ((5 : ℤ) : ℝ)
    let lam := comboLam 60 ((10 : ℤ) : ℝ) ((2 : ℤ) : ℝ)
    0 < lam ∧ lam < 1 ∧
    lam * 60 * (((10 : ℤ) : ℝ) - 1) * ((10 : ℤ) : ℝ) ^ (60 - 1) / ((1 - lam) * (((10 : ℤ) : ℝ) ^ 60 - 1)) = ((2 : ℤ) : ℝ) ∧
    MatrixPositivity (geometricCoefficients 60 r⁻¹ 1) ∧ MatrixPositivity (geometricCoefficients 60 r⁻¹ ((10 : ℤ) : ℝ)) ∧
    Admissible (combo lam (geometricCoefficients 60 r⁻¹ 1) (geometricCoefficients 60 r⁻¹ ((10 : ℤ) : ℝ))) ∧
    productMatrix (combo lam (geometricCoefficients 60 r⁻¹ 1) (geometricCoefficients 60 r⁻¹ ((10 : ℤ) : ℝ)))
      60 (Fin.last 60) (Fin.last 60) < 0 := …

/-- `(r, N, q, t) = (1/3, 100, 10, 2)`: `K` and `G` have (P), the combination is admissible and
`g(100,100;100) < 0`. -/
theorem combo_fails_1_3_100 :
    let r : ℝ := ((1 : ℤ) : ℝ) / ((3 : ℤ) : ℝ)
    let lam := comboLam 100 ((10 : ℤ) : ℝ) ((2 : ℤ) : ℝ)
    0 < lam ∧ lam < 1 ∧
    lam * 100 * (((10 : ℤ) : ℝ) - 1) * ((10 : ℤ) : ℝ) ^ (100 - 1) / ((1 - lam) * (((10 : ℤ) : ℝ) ^ 100 - 1)) = ((2 : ℤ) : ℝ) ∧
    MatrixPositivity (geometricCoefficients 100 r⁻¹ 1) ∧ MatrixPositivity (geometricCoefficients 100 r⁻¹ ((10 : ℤ) : ℝ)) ∧
    Admissible (combo lam (geometricCoefficients 100 r⁻¹ 1) (geometricCoefficients 100 r⁻¹ ((10 : ℤ) : ℝ))) ∧
    productMatrix (combo lam (geometricCoefficients 100 r⁻¹ 1) (geometricCoefficients 100 r⁻¹ ((10 : ℤ) : ℝ)))
      100 (Fin.last 100) (Fin.last 100) < 0 := …

/-- `(r, N, q, t) = (3/10, 200, 2, 5)`: `K` and `G` have (P), the combination is admissible and
`g(200,200;200) < 0`. -/
theorem combo_fails_3_10_200 :
    let r : ℝ := ((3 : ℤ) : ℝ) / ((10 : ℤ) : ℝ)
    let lam := comboLam 200 ((2 : ℤ) : ℝ) ((5 : ℤ) : ℝ)
    0 < lam ∧ lam < 1 ∧
    lam * 200 * (((2 : ℤ) : ℝ) - 1) * ((2 : ℤ) : ℝ) ^ (200 - 1) / ((1 - lam) * (((2 : ℤ) : ℝ) ^ 200 - 1)) = ((5 : ℤ) : ℝ) ∧
    MatrixPositivity (geometricCoefficients 200 r⁻¹ 1) ∧ MatrixPositivity (geometricCoefficients 200 r⁻¹ ((2 : ℤ) : ℝ)) ∧
    Admissible (combo lam (geometricCoefficients 200 r⁻¹ 1) (geometricCoefficients 200 r⁻¹ ((2 : ℤ) : ℝ))) ∧
    productMatrix (combo lam (geometricCoefficients 200 r⁻¹ 1) (geometricCoefficients 200 r⁻¹ ((2 : ℤ) : ℝ)))
      200 (Fin.last 200) (Fin.last 200) < 0 := …

/-- `(r, N, q, t) = (2/7, 200, 10, 5)`: `K` and `G` have (P), the combination is admissible and
`g(200,200;200) < 0`. -/
theorem combo_fails_2_7_200 :
    let r : ℝ := ((2 : ℤ) : ℝ) / ((7 : ℤ) : ℝ)
    let lam := comboLam 200 ((10 : ℤ) : ℝ) ((5 : ℤ) : ℝ)
    0 < lam ∧ lam < 1 ∧
    lam * 200 * (((10 : ℤ) : ℝ) - 1) * ((10 : ℤ) : ℝ) ^ (200 - 1) / ((1 - lam) * (((10 : ℤ) : ℝ) ^ 200 - 1)) = ((5 : ℤ) : ℝ) ∧
    MatrixPositivity (geometricCoefficients 200 r⁻¹ 1) ∧ MatrixPositivity (geometricCoefficients 200 r⁻¹ ((10 : ℤ) : ℝ)) ∧
    Admissible (combo lam (geometricCoefficients 200 r⁻¹ 1) (geometricCoefficients 200 r⁻¹ ((10 : ℤ) : ℝ))) ∧
    productMatrix (combo lam (geometricCoefficients 200 r⁻¹ 1) (geometricCoefficients 200 r⁻¹ ((10 : ℤ) : ℝ)))
      200 (Fin.last 200) (Fin.last 200) < 0 := …
```

Not formalized (and not claimed): the one-kink example with N = 500 (r = 1/10; its kernel evaluation did not finish within 50 minutes), the two first-order derivatives 512/1875 and −71936/5859375 at r = 4/5, the 80- and 150-digit examples, the sampled tests of P2, the negative entry of the operator M of P2, and P1's float/high-precision searches. The one-kink parameters m and δ, which the P3 table omits, are those of `smallr_probe.py`; the N = 20 example of the table is the N = 20 example of the open problems.

## Proposed changes (applied only after this round passes)

1. P1 Lean table: new last row `The combinations $(1-\lambda)K_{N,r}+\lambda G_{N,q,r}$ in the paragraph ``How sharp is log-concavity?'' and the seven listed failures & \path{Szkraw.combo_shape}, \path{Szkraw.combo_fails_4_5_10}, \path{Szkraw.combo_fails_3_5_20}, \path{Szkraw.combo_fails_1_2_20}, \path{Szkraw.combo_fails_2_5_60}, \path{Szkraw.combo_fails_1_3_100}, \path{Szkraw.combo_fails_3_10_200}, \path{Szkraw.combo_fails_2_7_200}`.
2. P2: (a) the Lean-table row `Section~\ref{sec:open}: the counterexamples with $N=3$ and the cubic counterexample with $N=4$ & …` gets a following row `Section~\ref{sec:open}: the counterexamples with $N=48$, $64$, $40$, $40$ and $120$ & \path{Szkraw.cubicBinom48_fails}, \path{Szkraw.cubicPow64_fails}, \path{Szkraw.steepRatio40_fails}, \path{Szkraw.topRatio40_fails}, \path{Szkraw.topRatio120_fails}`; (b) cross-reference fix: "and a convex kinked ratio on the linear profile fails at $N=120$~\cite{P3}" becomes "and a convex kinked ratio on the linear profile fails at $N=120$ (the last example of this section)" (that example is the top-raised ratio ρ_N = r + (1−r)/N, r = 2/5, of the same paragraph; paper.tex had "below"; P3 contains no such example).
3. P3 Lean table: new rows `Section~\ref{sec:limits}: terminal-row failures at fixed $r$ & \path{Szkraw.terminal_fails}`; `Section~\ref{sec:limits}: the rule $\beta=1$, $\gamma=0$ at $r=4/5$ and $r=19/20$ & \path{Szkraw.rule_fails_4_5}, \path{Szkraw.rule_fails_19_20}`; `Section~\ref{sec:limits}: the one-kink counterexamples with $N\leq100$ and the exact log-concave-increment counterexamples & \path{Szkraw.kink20_2_5_fails}, \path{Szkraw.kink40_1_3_fails}, \path{Szkraw.kink40_3_10_fails}, \path{Szkraw.kink60_1_4_fails}, \path{Szkraw.kink80_2_7_fails}, \path{Szkraw.kink100_1_5_fails}, \path{Szkraw.stepInc_logconcave}, \path{Szkraw.logconcave32_fails}, \path{Szkraw.logconcave80_fails}, \path{Szkraw.logconcave90_fails}`; `Section~\ref{sec:open}: the convex-profile and log-convex-increment counterexamples & \path{Szkraw.kink14_fails}, \path{Szkraw.kink20_2_5_fails}, \path{Szkraw.cvxInc_logconvex}, \path{Szkraw.logconvex18_fails}`.
4. papers/FORMALIZATION.md: (a) "In Section~10 only the two counterexamples with $N=3$ and the cubic counterexample with $N=4$ are formalized; they are stated with all properties claimed for them, and the remaining computational statements there are not formalized." becomes "In Section~10 the two counterexamples with $N=3$, the cubic counterexample with $N=4$ and the five ratio counterexamples on linear profiles with $N=48,64,40,40,120$ (\path{Szkraw.cubicBinom48_fails}, \path{Szkraw.cubicPow64_fails}, \path{Szkraw.steepRatio40_fails}, \path{Szkraw.topRatio40_fails}, \path{Szkraw.topRatio120_fails}) are formalized, each with the properties claimed for it; the sampled tests and the negative entry of the operator $M$ are not formalized. The combinations of $K_{N,r}$ and $G_{N,q,r}$ in the paragraph of P1 on how sharp log-concavity is are formalized as \path{Szkraw.combo_shape} (the general claims) and \path{Szkraw.combo_fails_4_5_10}, …, \path{Szkraw.combo_fails_2_7_200} (the seven listed failures, each with $K$ and $G$ having (P))."; (b) "The remaining prose of Section~9, the computations and heuristics away from $r=1$, is not formalized." becomes "Of the computations in Section~9 (P3 Section~9 and open problems), the exact ones are formalized: the terminal-row failures (\path{Szkraw.terminal_fails}), the rule $\beta=1$, $\gamma=0$ (\path{Szkraw.rule_fails_4_5}, \path{Szkraw.rule_fails_19_20}), the one-kink, log-concave-increment and log-convex-increment counterexamples (\path{Szkraw.kink14_fails}, …, \path{Szkraw.logconvex18_fails}), except the one-kink example with $N=500$ and the two first-order derivatives $512/1875$ and $-71936/5859375$. The high-precision examples and the heuristics are not formalized. These finite computations are decided by exact integer columns of the product table, evaluated in the Lean kernel (\path{Szkraw.ColCheck.productMatrix_eq_col}, \verb|decide +kernel|)."

Please answer per item (each Lean statement or group, then each proposed change): MATCH / MISMATCH with reasons, then an overall verdict (PASS / PASS WITH MINOR FIXES / FAIL), with exact replacement text for any fix.
