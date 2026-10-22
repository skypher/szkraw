# Independent review, Lean fidelity round 12: Theorem 8.9 in Lean

As in rounds 1–11, **do not check proofs**. Check only whether the Lean statement faithfully expresses the paper statement, under the acceptance rule: Lean hypotheses equivalent to or weaker than the paper's, and Lean conclusion equivalent to or stronger. Where the Lean statement covers less than the paper claims, say exactly what is missing. Also check the new table row and the scope sentence against the Lean statement.

Conventions (unchanged from rounds 1–11):
- `Coefficients N` has fields a, b, c : ℕ → ℝ.
- `Admissible v` is the paper's (2.1): stochastic, a_0 = 1, b_0 = c_0 = 0, a_N = 0, a_i > 0 for i < N, c_i > 0 for 1 ≤ i ≤ N.
- `MatrixPositivity v` is nonnegative linearization: `productMatrix v m n k = g(m,n;k)` for all m ≤ N and all n, k.
- `profile v i = v.b i + v.c i` is the profile d.
- `newtonCoeff x k = Σ_i (−1)^(k−i) C(k,i) x_i` is Δ^k x(0).
- Theorem 8.1 was accepted in earlier rounds with the same encoding (`ConstantRatioLogConcave`: Admissible, `c_i = r·profile_i` for i ≤ N, `LogConcaveNoInternalZeros N (newtonCoeff (profile v))`).

Answer format: a table (paper claim | Lean declaration | MATCH / MATCH, SCOPE NOTED / MISMATCH | reason), exact fixes, and an overall verdict (PASS / PASS WITH MINOR FIXES / FAIL). Be terse.

## Part A. Paper statements

#### Section 8 notation
```latex
This section replaces that equality by inequalities on the Newton coefficients of the profile, for arrays with constant ratio $b_i/c_i$. Write
\[
\nu_k=\sum_{i=0}^k(-1)^{k-i}\binom ki d_i\quad(1\leq k\leq N),\qquad d_n=\sum_{k=1}^n\binom nk\nu_k\quad(0\leq n\leq N);
\]
below we put $\nu_0=0$ and $\nu_k=0$ for $k>N$.
We say that $(\nu_k)_{1\leq k\leq N}$ is \emph{log-concave without internal zeros} if all $\nu_k\geq0$, the indices with $\nu_k>0$ form an interval $\{1,\ldots,K\}$, and $\nu_k^2\geq\nu_{k-1}\nu_{k+1}$ for $2\leq k\leq N-1$. Note $\nu_1=d_1>0$.
```

#### Theorem 8.1 (for comparison; accepted in earlier rounds)
```latex
\begin{theorem}[Log-concave Newton criterion]\label{thm:lc}
Let $0=d_0<d_1<\cdots<d_N=1$ have Newton coefficients that are log-concave without internal zeros, let $0<r\leq1$, and put $a_i=1-d_i$, $b_i=(1-r)d_i$, $c_i=rd_i$. Then the system has nonnegative linearization.
\end{theorem}
```

#### Theorem 8.9
```latex
\begin{theorem}[Linearly increasing ratio]\label{thm:lc-affine}
Let $0=d_0<d_1<\cdots<d_N=1$ have Newton coefficients that are log-concave without internal zeros, let $0<r\leq1$ and $0\leq\kappa\leq\frac{N}{2N-1}(1-r)$, and put $\rho_i=r+\kappa i/N$, $a_i=1-d_i$, $b_i=(1-\rho_i)d_i$ and $c_i=\rho_id_i$. Then the system has nonnegative linearization.
\end{theorem}
```
The sentence after it:
```latex
For the linear profile $d_i=i/N$ these are arrays of Proposition~\ref{prop:lc-quad}, and the bound on $\kappa$ is exactly the condition that $b$ be nondecreasing there.
```

#### Code-and-formalization: new table row and scope sentence
```latex
Theorem~\ref{thm:lc-affine}: linearly increasing ratio & \path{Szkraw.affine_matrix}\\[3pt]

Theorem~\ref{thm:lc-affine} is stated for arrays satisfying \eqref{eq:basic} with $c_i=(r+\kappa i/N)(b_i+c_i)$ for $i\leq N$, $0<r\leq1$, $\kappa\geq0$ and $(2N-1)\kappa\leq N(1-r)$, as in Theorem~\ref{thm:lc}; its proof formalizes the Leibniz formulas, the log-concavity of the Newton coefficients of $c$ through $\widehat\kappa$ (\path{Szkraw.affU_lcnz}), the key inequality (\path{Szkraw.AffSetting.key}) and the resummation as an identity of matrices indexed by $\{0,\ldots,N\}^2$ (\path{Szkraw.resum_nonneg}, \path{Szkraw.gkernel_resum}). The Lean proof uses the detour constant $4$ for all four families and, in the key inequality, only the products with $(i,j)\in\{(1,n-1),(n-1,1)\}$ for $n\geq3$ and $(2,n-2)$ for $n\geq4$, which give the coefficient $2n$ for $n=3$ and $2n+\binom n2$ for $n\geq4$ in place of $\gamma_n$ and suffice for the coefficient comparison.
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
def profile {N : ℕ} (v : Coefficients N) (i : ℕ) : ℝ := v.b i + v.c i

noncomputable def newtonCoeff (d : ℕ → ℝ) (k : ℕ) : ℝ :=
  ∑ i ∈ range (k + 1), (-1 : ℝ) ^ (k - i) * (k.choose i : ℝ) * d i

def LogConcaveNoInternalZeros (N : ℕ) (ν : ℕ → ℝ) : Prop :=
  0 < ν 1 ∧
  (∀ k, 1 ≤ k → k ≤ N → 0 ≤ ν k) ∧
  (∀ k, 2 ≤ k → k + 1 ≤ N → ν (k - 1) * ν (k + 1) ≤ ν k ^ 2) ∧
  (∀ k, 1 ≤ k → k < N → ν k = 0 → ν (k + 1) = 0)
```

### lean/Szkraw/VRAffineMain.lean
```lean
/-- Hypotheses of Theorem 8.9: `c_i = (r + κ i / N) d_i` with `0 < r ≤ 1` and
`0 ≤ κ ≤ N(1-r)/(2N-1)` (written `(2N-1)κ ≤ N(1-r)`), and a profile `d = b + c` whose Newton
coefficients are log-concave without internal zeros. -/
def AffineRatioHyp {N : ℕ} (vv : Coefficients N) : Prop :=
  ∃ r κ : ℝ, 0 < r ∧ r ≤ 1 ∧ 0 ≤ κ ∧ (2 * (N : ℝ) - 1) * κ ≤ N * (1 - r) ∧
    (∀ i, i ≤ N → vv.c i = (r + κ * i / N) * profile vv i) ∧
    LogConcaveNoInternalZeros N (newtonCoeff (profile vv))

/-- Theorem 8.9 (linearly increasing ratio), matrix-positivity conclusion. -/
def Stmt_affine : Prop :=
  ∀ (N : ℕ) (vv : Coefficients N), Admissible vv → AffineRatioHyp vv → MatrixPositivity vv


/-- **Theorem 8.9** (linearly increasing ratio). -/
theorem affine_matrix : Stmt_affine
```
Axiom audit: `affine_matrix` depends only on propext, Classical.choice, Quot.sound.
