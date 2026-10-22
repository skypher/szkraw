# Independent review, round 11: Theorem 8.6, Corollary 8.7 and Proposition 8.8 in Lean

As in rounds 1–10, **do not check proofs**. Check only whether each Lean statement faithfully expresses the paper statement, under the acceptance rule: Lean hypotheses equivalent to or weaker than the paper's, and Lean conclusion equivalent to or stronger. Where the Lean statement covers less than the paper claims, say exactly what is missing.

Conventions:
- `Coefficients N` has fields a, b, c : ℕ → ℝ.
- `Admissible v` is the paper's (2.1): stochastic, a_0 = 1, b_0 = c_0 = 0, a_N = 0, a_i > 0 for i < N, c_i > 0 for 1 ≤ i ≤ N.
- `MatrixPositivity v` is nonnegative linearization: `productMatrix v m n k = g(m,n;k)`.
- `newtonCoeff x k = Σ_i (−1)^(k−i) C(k,i) x_i` is the k-th Newton coefficient Δ^k x(0).
- `padNewton N ν` is (0, ν_1, …, ν_N, 0, …).
- `iterShift u ℓ n = Σ_{h ≤ ℓ} C(ℓ,h) u(n+h)` (`iterShift_eq`), so `iterShift (padNewton N κ) ℓ n` is the paper's φ_n(ℓ), and the same for ψ.

The paper's scalars κ_k, β_k are the Newton coefficients of c and b. In Proposition 8.8, b_n = β_1 n + β_2 C(n,2) and c_n = κ_1 n + κ_2 C(n,2) are hypotheses for n ≤ N.

Answer format: a table (paper claim | Lean declaration | MATCH / MATCH, SCOPE NOTED / MISMATCH | reason), exact fixes, and an overall verdict (PASS / PASS WITH MINOR FIXES / FAIL). Be terse.

## Part A. Paper statements

#### Section 8 notation (Newton coefficients, log-concave without internal zeros)
```latex
This section replaces that equality by inequalities on the Newton coefficients of the profile, for arrays with constant ratio $b_i/c_i$. Write
\[
\nu_k=\sum_{i=0}^k(-1)^{k-i}\binom ki d_i\quad(1\leq k\leq N),\qquad d_n=\sum_{k=1}^n\binom nk\nu_k\quad(0\leq n\leq N);
\]
below we put $\nu_0=0$ and $\nu_k=0$ for $k>N$.
We say that $(\nu_k)_{1\leq k\leq N}$ is \emph{log-concave without internal zeros} if all $\nu_k\geq0$, the indices with $\nu_k>0$ form an interval $\{1,\ldots,K\}$, and $\nu_k^2\geq\nu_{k-1}\nu_{k+1}$ for $2\leq k\leq N-1$. Note $\nu_1=d_1>0$.
```

#### Varying ratio: setting
```latex
The kernel argument also works in the stochastic normalization itself, with independent diagonal and downward coefficients. Let $a_i+b_i+c_i=1$ for $0\leq i\leq N$, with $b_0=c_0=0$, $a_N=0$, $a_i>0$ for $i<N$ and $c_i>0$ for $i\geq1$. Write
\[
\kappa_k=\sum_{i=0}^k(-1)^{k-i}\binom kic_i,\qquad\beta_k=\sum_{i=0}^k(-1)^{k-i}\binom kib_i\qquad(1\leq k\leq N),
\]
with $\kappa_k=\beta_k=0$ for $k=0$ and $k>N$, and put $\varphi_n(\ell)=\sum_{h\geq0}\binom\ell h\kappa_{n+h}$ and $\psi_n(\ell)=\sum_{h\geq0}\binom\ell h\beta_{n+h}$, so that $\varphi_0(\ell)=c_\ell$ and $\psi_0(\ell)=b_\ell$ for $\ell\leq N$.
```

#### Theorem 8.6
```latex
\begin{theorem}[Varying ratio]\label{thm:lc-vary}
Let $(\kappa_k)$ be log-concave without internal zeros and $\beta_k\geq0$ for all $k$. Suppose that for $0\leq\ell\leq N-1$
\[
\psi_1(\ell)\,\varphi_n(\ell+1)\geq c_{\ell+1}\,\psi_{n+1}(\ell)\quad(n\geq2),\qquad\varphi_2(\ell)\,\psi_n(\ell+1)\geq c_{\ell+1}\,\psi_{n+2}(\ell)\quad(n\geq1).
\]
Then the system has nonnegative linearization.
\end{theorem}
```

#### Corollary 8.7
```latex
\begin{corollary}\label{cor:lc-vary}
If $(\kappa_k)$ is log-concave without internal zeros and $\beta_k=w_k\kappa_k$ for $k\geq1$ with $w_1\geq w_2\geq\cdots\geq0$, then the system has nonnegative linearization. The ratio $c_i/(b_i+c_i)$ is nondecreasing in $i\geq1$, and it is constant when $w$ is constant on the support of $\kappa$; these are the arrays of Theorem~\ref{thm:lc}.
\end{corollary}
```

#### Proposition 8.8
```latex
\begin{proposition}[Quadratic arrays]\label{prop:lc-quad}
Let $b_n=\beta_1n+\beta_2\binom n2$ and $c_n=\kappa_1n+\kappa_2\binom n2$ $(0\leq n\leq N)$ define an array as above. If $\kappa_2\geq0$, $\kappa_2+\beta_2\geq0$ and $b_0\leq b_1\leq\cdots\leq b_N$, then the system has nonnegative linearization.
\end{proposition}
```

#### Code-and-formalization: new table rows and scope sentences
```latex
Theorem~\ref{thm:lc-vary}: varying ratio & \path{Szkraw.varyratio_matrix}\\[3pt]
Corollary~\ref{cor:lc-vary}: nonincreasing weights & \path{Szkraw.varyratio_weights}\\[3pt]
Proposition~\ref{prop:lc-quad}: quadratic arrays & \path{Szkraw.quadratic_matrix}\\[3pt]

Theorem~\ref{thm:lc-vary} is stated for arrays satisfying \eqref{eq:basic}, with the two mixed inequalities written through iterated shift sums $\varphi_n(\ell)=\sum_h\binom\ell h\kappa_{n+h}$ of the padded Newton sequences (\path{Szkraw.MixedIneq}); its proof formalizes the kernel identity for the generator $z^{-1}c(\theta)+b(\theta)+z(1-b(\theta)-c(\theta))$ for every array (\path{Szkraw.kernel_starV}), an operator induction with abstract move weights that need to be nonnegative and dominated only on $\Omega$ (\path{Szkraw.gkernel_nonneg}), and the mixed detour inequalities (\path{Szkraw.lemma_8_4_AV}, \path{Szkraw.lemma_8_4_CV}). In Corollary~\ref{cor:lc-vary} the weights need to be nonincreasing on $1\leq k\leq N$; its proof uses that the order $\psi_k\varphi_i\leq\psi_i\varphi_k$ $(i\leq k)$ is preserved by the shift sums (\path{Szkraw.mixedIneq_of_crossOrder}), and the statement includes the monotone ratio and, for weights constant on the support of $\kappa$, $b=w_0c$. Proposition~\ref{prop:lc-quad} is stated in the form given there.
```

## Part B. Lean statements

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

def MatrixPositivity {N : ℕ} (v : Coefficients N) : Prop :=
  ∀ m, m ≤ N → ∀ i j, 0 ≤ productMatrix v m i j
```

### lean/Szkraw/LogConcaveStatement.lean
```lean
/-- Newton coefficients `ν k = Σ_{i ≤ k} (-1)^(k-i) C(k,i) d i`, i.e. `Δ^k d (0)`. -/
noncomputable def newtonCoeff (d : ℕ → ℝ) (k : ℕ) : ℝ :=
  ∑ i ∈ range (k + 1), (-1 : ℝ) ^ (k - i) * (k.choose i : ℝ) * d i

/-- `(ν k)_{1 ≤ k ≤ N}` is nonnegative and log-concave without internal zeros, with `ν 1 > 0`. -/
def LogConcaveNoInternalZeros (N : ℕ) (ν : ℕ → ℝ) : Prop :=
  0 < ν 1 ∧
  (∀ k, 1 ≤ k → k ≤ N → 0 ≤ ν k) ∧
  (∀ k, 2 ≤ k → k + 1 ≤ N → ν (k - 1) * ν (k + 1) ≤ ν k ^ 2) ∧
  (∀ k, 1 ≤ k → k < N → ν k = 0 → ν (k + 1) = 0)

/-- The padded Newton sequence `(0, ν 1, …, ν N, 0, …)`. -/
noncomputable def padNewton (N : ℕ) (ν : ℕ → ℝ) (i : ℕ) : ℝ := if 1 ≤ i ∧ i ≤ N then ν i else 0
```

### lean/Szkraw/LCSequences.lean
```lean
/-- The shifted sum `v i = u i + u (i+1)`. -/
def shiftSum (u : ℕ → ℝ) (i : ℕ) : ℝ := u i + u (i + 1)

/-- Iterated shift sums. -/
def iterShift (u : ℕ → ℝ) : ℕ → ℕ → ℝ
  | 0 => u
  | n + 1 => Szkraw.shiftSum (iterShift u n)

/-- `iterShift u ℓ i = Σ_{h ≤ ℓ} C(ℓ,h) u (i+h)`. -/
theorem iterShift_eq (u : ℕ → ℝ) : ∀ ℓ i,
    Szkraw.iterShift u ℓ i = ∑ h ∈ range (ℓ + 1), (ℓ.choose h : ℝ) * u (i + h)
  | 0, i => by simp [Szkraw.iterShift]
  | ℓ + 1, i => by
    show Szkraw.iterShift u ℓ i + Szkraw.iterShift u ℓ (i + 1) = _
    rw [iterShift_eq u ℓ i, iterShift_eq u ℓ (i + 1)]
    have hA : ∑ h ∈ range (ℓ + 1), (ℓ.choose h : ℝ) * u (i + h) =
        ∑ h ∈ range (ℓ + 2), (ℓ.choose h : ℝ) * u (i + h) := …
```

### lean/Szkraw/VRDetours.lean
```lean
/-- The two mixed inequalities of Theorem 8.6, for `0 ≤ ℓ ≤ N - 1`. -/
def MixedIneq (u v : ℕ → ℝ) (N : ℕ) : Prop :=
  (∀ ℓ n, ℓ < N → 2 ≤ n →
    Szkraw.iterShift u (ℓ + 1) 0 * Szkraw.iterShift v ℓ (n + 1) ≤
      Szkraw.iterShift v ℓ 1 * Szkraw.iterShift u (ℓ + 1) n) ∧
  (∀ ℓ n, ℓ < N → 1 ≤ n →
    Szkraw.iterShift u (ℓ + 1) 0 * Szkraw.iterShift v ℓ (n + 2) ≤
      Szkraw.iterShift u ℓ 2 * Szkraw.iterShift v (ℓ + 1) n)
```

### lean/Szkraw/VRAssembly.lean
```lean
/-- Hypotheses of Theorem 8.6: the Newton coefficients `κ` of `c` are log-concave without internal
zeros, those `β` of `b` are nonnegative, and the two mixed inequalities hold for `0 ≤ ℓ ≤ N-1`,
with `φ_n(ℓ) = Σ_h C(ℓ,h) κ_{n+h}` and `ψ_n(ℓ) = Σ_h C(ℓ,h) β_{n+h}` (`κ_0 = β_0 = 0`, zero
beyond `N`); here `iterShift (padNewton N κ) ℓ n = φ_n(ℓ)` (`iterShift_eq`). -/
def VaryRatioHyp {N : ℕ} (vv : Coefficients N) : Prop :=
  LogConcaveNoInternalZeros N (newtonCoeff vv.c) ∧
  (∀ k, 1 ≤ k → k ≤ N → 0 ≤ newtonCoeff vv.b k) ∧
  MixedIneq (padNewton N (newtonCoeff vv.c)) (padNewton N (newtonCoeff vv.b)) N

/-- Theorem 8.6 (varying ratio), matrix-positivity conclusion. -/
def Stmt_varyratio : Prop :=
  ∀ (N : ℕ) (vv : Coefficients N), Admissible vv → VaryRatioHyp vv → MatrixPositivity vv

/-- **Theorem 8.6** (varying ratio). -/
theorem varyratio_matrix : Stmt_varyratio := …
```

### lean/Szkraw/VRCorollaries.lean
```lean
/-- Hypotheses of Corollary 8.7. -/
def WeightHyp {N : ℕ} (vv : Coefficients N) (w : ℕ → ℝ) : Prop :=
  LogConcaveNoInternalZeros N (newtonCoeff vv.c) ∧
  (∀ k, 1 ≤ k → k ≤ N → 0 ≤ w k) ∧
  (∀ i k, 1 ≤ i → i ≤ k → k ≤ N → w k ≤ w i) ∧
  (∀ k, 1 ≤ k → k ≤ N → newtonCoeff vv.b k = w k * newtonCoeff vv.c k)

/-- Corollary 8.7: property (P), the nondecreasing ratio `c_i/(b_i + c_i)`, and the constant-weight
case `b = w₀ c`. -/
def Stmt_varyratio_weights : Prop :=
  ∀ (N : ℕ) (vv : Coefficients N) (w : ℕ → ℝ), Admissible vv → WeightHyp vv w →
    MatrixPositivity vv ∧
    (∀ i, 1 ≤ i → i < N → vv.c i / (vv.b i + vv.c i) ≤ vv.c (i + 1) / (vv.b (i + 1) + vv.c (i + 1))) ∧
    (∀ w₀ : ℝ, (∀ k, 1 ≤ k → k ≤ N → newtonCoeff vv.c k ≠ 0 → w k = w₀) → ∀ i, i ≤ N → vv.b i = w₀ * vv.c i)

theorem varyratio_weights : Stmt_varyratio_weights := …

/-- Hypotheses of Proposition 8.8 (quadratic arrays). -/
def QuadHyp {N : ℕ} (vv : Coefficients N) : Prop :=
  ∃ β₁ β₂ κ₁ κ₂ : ℝ,
    (∀ n, n ≤ N → vv.b n = β₁ * n + β₂ * (n.choose 2 : ℝ) ∧ vv.c n = κ₁ * n + κ₂ * (n.choose 2 : ℝ)) ∧
    0 ≤ κ₂ ∧ 0 ≤ κ₂ + β₂ ∧ (∀ n, n < N → vv.b n ≤ vv.b (n + 1))

/-- Proposition 8.8 (quadratic arrays). -/
def Stmt_quadratic : Prop :=
  ∀ (N : ℕ) (vv : Coefficients N), Admissible vv → QuadHyp vv → MatrixPositivity vv

/-- **Proposition 8.8** (quadratic arrays). -/
theorem quadratic_matrix : Stmt_quadratic := …
```
