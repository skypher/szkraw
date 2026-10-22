# Independent review, Lean fidelity round 13: Theorem 8.9 (strengthened) and Proposition 8.10

As in rounds 1–12, **do not check proofs**. Check only whether each Lean statement faithfully expresses the paper statement, under the acceptance rule: Lean hypotheses equivalent to or weaker than the paper's, Lean conclusion equivalent to or stronger. Where a Lean statement covers less than the paper claims, say exactly what is missing. Also check the table rows and the scope sentences against the Lean statements.

Since round 12, Theorem 8.9 has a weaker hypothesis: b nondecreasing in place of (2N−1)κ ≤ N(1−r). The theorem also states that this condition is equivalent to κ(N + d_{N−1}/(1−d_{N−1})) ≤ N(1−r). Proposition 8.10 is new.

Conventions (unchanged):
- `Coefficients N` has fields a, b, c : ℕ → ℝ.
- `Admissible v` is the paper's (2.1): stochastic, a_0 = 1, b_0 = c_0 = 0, a_N = 0, a_i > 0 for i < N, c_i > 0 for 1 ≤ i ≤ N.
- `MatrixPositivity v` is nonnegative linearization: `productMatrix v m n k = g(m,n;k)` for all m ≤ N and all n, k.
- `profile v i = v.b i + v.c i`.
- `newtonCoeff x k = Σ_i (−1)^(k−i) C(k,i) x_i`.
- Theorem 8.1 was accepted earlier with the same array-based encoding: Admissible, the ratio relation for i ≤ N, and `LogConcaveNoInternalZeros N (newtonCoeff (profile v))`.

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

#### Theorem 8.9
```latex
\begin{theorem}[Linearly increasing ratio]\label{thm:lc-affine}
Let $0=d_0<d_1<\cdots<d_N=1$ have Newton coefficients that are log-concave without internal zeros, let $0<r\leq1$ and $\kappa\geq0$, and put $\rho_i=r+\kappa i/N$, $a_i=1-d_i$, $b_i=(1-\rho_i)d_i$ and $c_i=\rho_id_i$. If $b$ is nondecreasing, then the system has nonnegative linearization. The condition that $b$ be nondecreasing is equivalent to $\kappa\bigl(N+d_{N-1}/(1-d_{N-1})\bigr)\leq N(1-r)$.
\end{theorem}
```
Text after it:
```latex
For the linear profile $d_i=i/N$ the condition reads $\kappa\leq\frac N{2N-1}(1-r)$, and these are arrays of Proposition~\ref{prop:lc-quad}. For a convex profile $d_{N-1}\leq(N-1)/N$, so the admitted range of $\kappa$ contains $[0,\frac N{2N-1}(1-r)]$. When $r<1$, this containment is strict for a nonlinear profile. For example, $N=4$, $d_i=(2^i-1)/15$, $r=1/2$ and $\kappa=2/5$ are admitted, with $b=(0,2/75,3/50,7/75,1/10)$, although $(2N-1)\kappa/N=7/10>1-r$.
```

#### Proposition 8.10
```latex
\begin{proposition}[Quadratic profiles]\label{prop:lc-quadprof}
Let $d_i=\nu_1i+\nu_2\binom i2$ with $\nu_1>0$, $\nu_2\geq0$ and $d_N=1$, let $\rho(x)=r+tx+\tau\binom x2$ with $r>0$ and $t,\tau\geq0$, and put $a_i=1-d_i$, $b_i=(1-\rho(i))d_i$ and $c_i=\rho(i)d_i$. If $b$ is nondecreasing, then the system has nonnegative linearization.
\end{proposition}
```
Text after it (prose; scope says it is not formalized):
```latex
As in the proof of Theorem~\ref{thm:lc-affine}, $b_{i+1}-b_i=f_1(i)\bigl(1-\rho(i+1)-(t+\tau i)R_i\bigr)$ with a nonincreasing bracket, so $b$ is nondecreasing exactly when $t(N+R)+\tau\bigl(\binom N2+(N-1)R\bigr)\leq1-r$, where $R=d_{N-1}/(1-d_{N-1})$.
```

#### Code-and-formalization: table rows and scope sentences
```latex
Theorem~\ref{thm:lc-affine}: linearly increasing ratio & \path{Szkraw.affine_matrix}\\[3pt]
Proposition~\ref{prop:lc-quadprof}: quadratic profiles & \path{Szkraw.quadprofile_matrix}\\[3pt]

Theorem~\ref{thm:lc-affine} is stated for arrays satisfying \eqref{eq:basic} whose profile $d_i=b_i+c_i$ has Newton coefficients log-concave without internal zeros, with $c_i=(r+\kappa i/N)(b_i+c_i)$ for $i\leq N$, $0<r\leq1$, $\kappa\geq0$ and $b_0\leq b_1\leq\cdots\leq b_N$, using the same array-based encoding as in Theorem~\ref{thm:lc}; the equivalence of the last condition with $\kappa\bigl(N+d_{N-1}/(1-d_{N-1})\bigr)\leq N(1-r)$ is \path{Szkraw.affine_bmono_iff}. Its proof formalizes the Leibniz formulas, the log-concavity of the Newton coefficients of $c$ through $\widehat\kappa$ (\path{Szkraw.affU_lcnz}), the key inequality through \eqref{eq:affine-red}, the bound $\alpha u_1\geq tu_0$ and the interpolation of $F$ (\path{Szkraw.AffSetting.key}, \path{Szkraw.Fz_nonneg}), and the resummation as an identity of matrices indexed by $\{0,\ldots,N\}^2$ (\path{Szkraw.resum_nonneg}, \path{Szkraw.gkernel_resum}). The Lean proof uses the detour constant $4$ for all four families, and for $K\geq0$ the products with $(i,j)\in\{(1,n-1),(n-1,1)\}$ for $n\geq3$ and $(2,n-2)$ for $n\geq4$. Proposition~\ref{prop:lc-quadprof} is stated for arrays satisfying \eqref{eq:basic} with $b_i+c_i=\nu_1i+\nu_2\binom i2$ and $c_i=\bigl(r+ti+\tau\binom i2\bigr)(b_i+c_i)$ for $i\leq N$, $\nu_1>0$, $\nu_2\geq0$, $r>0$, $t,\tau\geq0$ and $b_0\leq\cdots\leq b_N$; its proof identifies the iterated shift sums of the Newton coefficients with finite differences on $\Omega$ (\path{Szkraw.iterShift_padNewton}), uses the Leibniz rule for a quadratic factor (\path{Szkraw.fwdDiff_quad_mul}) and the inequality $\varphi_2(\ell)\varphi_2(\ell+1)\geq c_{\ell+1}\varphi_4(\ell)$ (\path{Szkraw.phi2_phi2}), and applies the resummation with $H_j=0$ and $V_1=-A^\psi_1$. The equivalent form of the monotonicity of $b$ stated after Proposition~\ref{prop:lc-quadprof} is not formalized.
```

## Part B. Lean statements

### lean/Szkraw/Statements.lean, LogConcaveStatement.lean (unchanged)
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
/-- Hypotheses of Theorem 8.9: `c_i = (r + κ i / N) d_i` with `0 < r ≤ 1` and `κ ≥ 0`, the diagonal
coefficients `b_0 ≤ b_1 ≤ ⋯ ≤ b_N` nondecreasing, and a profile `d = b + c` whose Newton coefficients
are log-concave without internal zeros. -/
def AffineRatioHyp {N : ℕ} (vv : Coefficients N) : Prop :=
  ∃ r κ : ℝ, 0 < r ∧ r ≤ 1 ∧ 0 ≤ κ ∧ (∀ i, i < N → vv.b i ≤ vv.b (i + 1)) ∧
    (∀ i, i ≤ N → vv.c i = (r + κ * i / N) * profile vv i) ∧
    LogConcaveNoInternalZeros N (newtonCoeff (profile vv))

/-- Theorem 8.9 (linearly increasing ratio), matrix-positivity conclusion. -/
def Stmt_affine : Prop :=
  ∀ (N : ℕ) (vv : Coefficients N), Admissible vv → AffineRatioHyp vv → MatrixPositivity vv


/-- **Theorem 8.9** (linearly increasing ratio). -/
theorem affine_matrix : Stmt_affine

/-- **Theorem 8.9, the condition on `κ`**: `b` is nondecreasing exactly when
`κ (N + d_{N-1}/(1 - d_{N-1})) ≤ N(1-r)`. -/
theorem affine_bmono_iff {N : ℕ} (vv : Coefficients N) (hv : Admissible vv) {r κ : ℝ} (hr : 0 < r)
    (hκ : 0 ≤ κ) (hc : ∀ i, i ≤ N → vv.c i = (r + κ * i / N) * profile vv i)
    (hlc : LogConcaveNoInternalZeros N (newtonCoeff (profile vv))) :
    (∀ i, i < N → vv.b i ≤ vv.b (i + 1)) ↔
      κ * (N + profile vv (N - 1) / (1 - profile vv (N - 1))) ≤ N * (1 - r) 
```

### lean/Szkraw/VRQuadProfile.lean
```lean
/-- Hypotheses of Proposition 8.10. -/
def QuadProfileHyp {N : ℕ} (vv : Coefficients N) : Prop :=
  ∃ ν1 ν2 r t τ : ℝ, 0 < ν1 ∧ 0 ≤ ν2 ∧ 0 < r ∧ 0 ≤ t ∧ 0 ≤ τ ∧
    (∀ i, i ≤ N → profile vv i = ν1 * i + ν2 * (i.choose 2 : ℝ)) ∧
    (∀ i, i ≤ N → vv.c i = (r + t * i + τ * (i.choose 2 : ℝ)) * profile vv i) ∧
    (∀ i, i < N → vv.b i ≤ vv.b (i + 1))

/-- Proposition 8.10 (quadratic profiles), matrix-positivity conclusion. -/
def Stmt_quadprofile : Prop :=
  ∀ (N : ℕ) (vv : Coefficients N), Admissible vv → QuadProfileHyp vv → MatrixPositivity vv

section QPproof

variable (ν1 ν2 r t τ : ℝ)

/-- The ratio `ρ(i) = r + t i + τ C(i,2)`. -/
noncomputable def gQ (i : ℕ) : ℝ := r + t * i + τ * (i.choose 2 : ℝ)

/-- `c = ρ d` as a function on `ℕ`. -/
noncomputable def cQ (i : ℕ) : ℝ := gQ r t τ i * dQ ν1 ν2 i

theorem dQ_diff1' (i : ℕ) : (fwdDiff 1)^[1] (dQ ν1 ν2) i = ν1 + ν2 * i := by rw [dQ_diff1]
theorem dQ_diff2' (i : ℕ) : (fwdDiff 1)^[2] (dQ ν1 ν2) i = ν2 := by rw [dQ_diff2]
theorem dQ_diff_high' (k i : ℕ) : (fwdDiff 1)^[k + 3] (dQ ν1 ν2) i = 0 := by rw [dQ_diff_high]

theorem dQ_succ (i : ℕ) : dQ ν1 ν2 (i + 1) = dQ ν1 ν2 i + (ν1 + ν2 * i) := by
  have := dQ_diff1' ν1 ν2 i
  simp only [Function.iterate_one] at this
  have e : fwdDiff 1 (dQ ν1 ν2) i = dQ ν1 ν2 (i + 1) - dQ ν1 ν2 i := rfl
  linarith

/-- `φ₂(x) = ρ(x+2) ν₂ + 2(t + τ(x+1))(ν₁ + ν₂ x) + τ d(x)`. -/
theorem cQ_diff2 (x : ℕ) : (fwdDiff 1)^[2] (cQ ν1 ν2 r t τ) x =
    gQ r t τ (x + 2) * ν2 + 2 * (t + τ * ((x : ℝ) + 1)) * (ν1 + ν2 * x) + τ * dQ ν1 ν2 x := by
  have h := fwdDiff_quad_mul r t τ (dQ ν1 ν2) 0 x
  have e : cQ ν1 ν2 r t τ = fun i : ℕ => (r + t * i + τ * (i.choose 2 : ℝ)) * dQ ν1 ν2 i := rfl
  rw [e, h, dQ_diff2', dQ_diff1']
  simp only [Function.iterate_zero, id]
  unfold gQ; push_cast; ring

/-- `φ₃(x) = 3(t + τ(x+2)) ν₂ + 3τ(ν₁ + ν₂ x)`. -/
theorem cQ_diff3 (x : ℕ) : (fwdDiff 1)^[3] (cQ ν1 ν2 r t τ) x =
    3 * (t + τ * ((x : ℝ) + 2)) * ν2 + 3 * τ * (ν1 + ν2 * x) := by
  have h := fwdDiff_quad_mul r t τ (dQ ν1 ν2) 1 x
  have e : cQ ν1 ν2 r t τ = fun i : ℕ => (r + t * i + τ * (i.choose 2 : ℝ)) * dQ ν1 ν2 i := rfl
  rw [e, show (3 : ℕ) = 1 + 2 from rfl, h, show 1 + 2 = 0 + 3 from rfl, dQ_diff_high', show 1 + 1 = 2 from rfl,
    dQ_diff2', dQ_diff1']
  push_cast; ring

/-- `φ₄ = 6 τ ν₂`. -/
theorem cQ_diff4 (x : ℕ) : (fwdDiff 1)^[4] (cQ ν1 ν2 r t τ) x = 6 * τ * ν2 := by
  have h := fwdDiff_quad_mul r t τ (dQ ν1 ν2) 2 x
  have e : cQ ν1 ν2 r t τ = fun i : ℕ => (r + t * i + τ * (i.choose 2 : ℝ)) * dQ ν1 ν2 i := rfl
  have z4 : (fwdDiff 1)^[2 + 2] (dQ ν1 ν2) x = 0 := dQ_diff_high' ν1 ν2 1 x
  have z3 : (fwdDiff 1)^[2 + 1] (dQ ν1 ν2) x = 0 := dQ_diff_high' ν1 ν2 0 x
  rw [e]
  refine h.trans ?_
  rw [z4, z3, dQ_diff2']
  push_cast; ring

/-- `φ_n = 0` for `n ≥ 5`. -/
theorem cQ_diff_high (k x : ℕ) : (fwdDiff 1)^[k + 5] (cQ ν1 ν2 r t τ) x = 0 := by
  have h := fwdDiff_quad_mul r t τ (dQ ν1 ν2) (k + 3) x
  have e : cQ ν1 ν2 r t τ = fun i : ℕ => (r + t * i + τ * (i.choose 2 : ℝ)) * dQ ν1 ν2 i := rfl
  rw [e, show k + 5 = k + 3 + 2 by ring, h, show k + 3 + 2 = (k + 2) + 3 by ring, dQ_diff_high',
    show k + 3 + 1 = (k + 1) + 3 by ring, dQ_diff_high', dQ_diff_high']
  ring

variable {ν1 ν2 r t τ}

theorem gQ_mono (ht : 0 ≤ t) (hτ : 0 ≤ τ) {i j : ℕ} (hij : i ≤ j) : gQ r t τ i ≤ gQ r t τ j := by
  unfold gQ
  have h1 : (i : ℝ) ≤ j := by exact_mod_cast hij
  have h2 : (i.choose 2 : ℝ) ≤ (j.choose 2 : ℝ) := by exact_mod_cast Nat.choose_le_choose 2 hij
  nlinarith

theorem gQ_pos (hr : 0 < r) (ht : 0 ≤ t) (hτ : 0 ≤ τ) (i : ℕ) : 0 < gQ r t τ i := by
  unfold gQ; positivity

theorem dQ_nonneg (h1 : 0 < ν1) (h2 : 0 ≤ ν2) (i : ℕ) : 0 ≤ dQ ν1 ν2 i := by unfold dQ; positivity

theorem cQ_diff_nonneg (h1 : 0 < ν1) (h2 : 0 ≤ ν2) (hr : 0 < r) (ht : 0 ≤ t) (hτ : 0 ≤ τ) (x n : ℕ) (hn : 2 ≤ n) :
    0 ≤ (fwdDiff 1)^[n] (cQ ν1 ν2 r t τ) x := by
  have hd := dQ_nonneg h1 h2 x
  have hg := (gQ_pos hr ht hτ (x + 2)).le
  rcases Nat.lt_or_ge n 5 with h | h
  · interval_cases n
    · rw [cQ_diff2]; positivity
    · rw [cQ_diff3]; positivity
    · rw [cQ_diff4]; positivity
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 5 := ⟨n - 5, by omega⟩
    rw [cQ_diff_high]

/-- The detour of the `B₁`-move: `φ₂(x) φ₂(x+1) ≥ c_{x+1} φ₄(x)`. -/
theorem phi2_phi2 (h1 : 0 < ν1) (h2 : 0 ≤ ν2) (hr : 0 < r) (ht : 0 ≤ t) (hτ : 0 ≤ τ) (x : ℕ) :
    gQ r t τ (x + 1) * dQ ν1 ν2 (x + 1) * (fwdDiff 1)^[4] (cQ ν1 ν2 r t τ) x ≤
      (fwdDiff 1)^[2] (cQ ν1 ν2 r t τ) x * (fwdDiff 1)^[2] (cQ ν1 ν2 r t τ) (x + 1) := by
  rw [cQ_diff4, cQ_diff2, cQ_diff2, dQ_succ]
  set p1 := gQ r t τ (x + 1)
  have hp2 : p1 ≤ gQ r t τ (x + 2) := gQ_mono ht hτ (by omega)
  have hp3 : p1 ≤ gQ r t τ (x + 1 + 2) := gQ_mono ht hτ (by omega)
  have hp1 : 0 < p1 := gQ_pos hr ht hτ _
  set u0 := dQ ν1 ν2 x
  set v := ν1 + ν2 * (x : ℝ)
  have hu0 : 0 ≤ u0 := dQ_nonneg h1 h2 x
  have hx0 : (0 : ℝ) ≤ x := Nat.cast_nonneg x
  have hv : 0 ≤ v := by positivity
  -- convexity: `u₀ ≤ x v`
  have hconv : u0 ≤ x * v := by
    have hc2 : (x.choose 2 : ℝ) * 2 = (x : ℝ) * ((x : ℝ) - 1) := by
      rcases Nat.eq_zero_or_pos x with hx | hx
      · subst hx; simp
      · have := choose_two_mul x
        have h' : ((x.choose 2 * 2 : ℕ) : ℝ) = ((x * (x - 1) : ℕ) : ℝ) := by rw [this]
        push_cast [Nat.cast_sub (show 1 ≤ x by omega)] at h'; linarith
    simp only [u0, v, dQ]
    nlinarith
  push_cast
  set X := u0 + 2 * ((x : ℝ) + 1) * v
  set Y := u0 + v + 2 * ((x : ℝ) + 2) * (v + ν2)
  have hA : p1 * ν2 + τ * X ≤ gQ r t τ (x + 2) * ν2 + 2 * (t + τ * ((x : ℝ) + 1)) * v + τ * u0 := by
    simp only [X]; nlinarith [mul_le_mul_of_nonneg_right hp2 h2, mul_nonneg ht hv]
  have hB : p1 * ν2 + τ * Y ≤ gQ r t τ (x + 1 + 2) * ν2 + 2 * (t + τ * ((x : ℝ) + 1 + 1)) * (ν1 + ν2 * ((x : ℝ) + 1)) +
      τ * (u0 + v) := by
    simp only [Y, v]; nlinarith [mul_le_mul_of_nonneg_right hp3 h2, mul_nonneg ht (by positivity : (0 : ℝ) ≤ ν1 + ν2 * ((x : ℝ) + 1))]
  have hX : 0 ≤ X := by positivity
  have hY : 0 ≤ Y := by positivity
  have hXY : 6 * (u0 + v) ≤ X + Y := by simp only [X, Y]; nlinarith
  have hAn : 0 ≤ p1 * ν2 + τ * X := by positivity
  have hBn : 0 ≤ p1 * ν2 + τ * Y := by positivity
  have k1 := mul_le_mul hA hB hBn (le_trans hAn hA)
  have k2 : p1 * τ * ν2 * (6 * (u0 + v)) ≤ (p1 * ν2 + τ * X) * (p1 * ν2 + τ * Y) := by
    have := mul_le_mul_of_nonneg_left hXY (by positivity : 0 ≤ p1 * τ * ν2)
    nlinarith [mul_nonneg (mul_nonneg hτ hτ) (mul_nonneg hX hY), sq_nonneg (p1 * ν2)]
  have e : (x : ℝ) + 1 + 1 = (x : ℝ) + 2 := by ring
  rw [e] at k1
  nlinarith [k1, k2]

end QPproof


theorem WtF_zero_of {F : ℕ → ℕ → ℝ} {p q ℓ a : ℕ} (h : ∀ n, p ≤ n → n ≤ a → F ℓ n = 0) : WtF F p q ℓ a = 0 := by
  unfold WtF
  refine sum_eq_zero fun n hn => ?_
  rw [mem_range] at hn
  by_cases hp : p ≤ n
  · rw [h n hp (by omega), mul_zero]
  · rw [if_neg hp]; ring

theorem WtF_nonpos_of {F : ℕ → ℕ → ℝ} {p q ℓ a : ℕ} (h : ∀ n, p ≤ n → n ≤ a → F ℓ n ≤ 0) : WtF F p q ℓ a ≤ 0 := by
  unfold WtF
  refine sum_nonpos fun n hn => ?_
  rw [mem_range] at hn
  by_cases hp : p ≤ n
  · rw [if_pos hp]; exact mul_nonpos_of_nonneg_of_nonpos (by positivity) (h n hp (by omega))
  · rw [if_neg hp]; simp

theorem WtF_ge_single {F : ℕ → ℕ → ℝ} {p q ℓ a : ℕ} (h : ∀ n, p ≤ n → n ≤ a → 0 ≤ F ℓ n) {n0 : ℕ}
    (hp : p ≤ n0) (ha : n0 ≤ a) :
    ((n0 - p + q).choose q : ℝ) * (a.choose n0 : ℝ) * F ℓ n0 ≤ WtF F p q ℓ a := by
  unfold WtF
  have hmem : n0 ∈ range (a + 1) := mem_range.mpr (by omega)
  have := single_le_sum (f := fun n => (if p ≤ n then ((n - p + q).choose q : ℝ) else 0) * (a.choose n : ℝ) * F ℓ n)
    (fun n hn => by
      rw [mem_range] at hn
      by_cases hpn : p ≤ n
      · rw [if_pos hpn]; exact mul_nonneg (by positivity) (h n hpn (by omega))
      · rw [if_neg hpn]; simp) hmem
  simpa [hp] using this

/-- **Proposition 8.10** (quadratic profiles). -/
theorem quadprofile_matrix : Stmt_quadprofile := by
  intro N vv hv hyp
  obtain ⟨ν1, ν2, r, t, τ, h1, h2, hr, ht, hτ, hd, hc, hbmono⟩ := hyp
  have hv' := hv
  obtain ⟨hN, _, hb0, hc0, haN, hsum, hapos, hcpos⟩ := hv'
  set u := padNewton N (newtonCoeff vv.c) with hu_def
  set w := padNewton N (newtonCoeff vv.b) with hw_def
  set ν := padNewton N (newtonCoeff (profile vv)) with hν_def
  set PH : ℕ → ℕ → ℝ := fun ℓ n => (fwdDiff 1)^[n] (cQ ν1 ν2 r t τ) ℓ with hPH
  set FD : ℕ → ℕ → ℝ := fun ℓ n => (fwdDiff 1)^[n] (dQ ν1 ν2) ℓ with hFD
  have hd0 : profile vv 0 = 0 := by simp [profile, hb0, hc0]
  have hcQ : ∀ i, i ≤ N → vv.c i = cQ ν1 ν2 r t τ i := fun i hi => by
    rw [hc i hi, hd i hi]; rfl
  have hdQ : ∀ i, i ≤ N → profile vv i = dQ ν1 ν2 i := hd
  have phi : ∀ ℓ n, ℓ + n ≤ N → Szkraw.iterShift u ℓ n = PH ℓ n := fun ℓ n h => by
    rw [hu_def, iterShift_padNewton vv.c hc0 N ℓ n h]
    exact fwdDiff_iter_congr n ℓ fun i _ hi => hcQ i (by omega)
  have fdef : ∀ ℓ n, ℓ + n ≤ N → Szkraw.iterShift ν ℓ n = FD ℓ n := fun ℓ n h => by
    rw [hν_def, iterShift_padNewton (profile vv) hd0 N ℓ n h]
    exact fwdDiff_iter_congr n ℓ fun i _ hi => hdQ i (by omega)
  have hw_eq : w = fun i => ν i - u i := by
    funext i
    rw [hw_def, hν_def, hu_def]
    unfold padNewton
    split_ifs
    · rw [← newtonCoeff_sub]
      exact newtonCoeff_congr fun j _ => by simp [profile]
    · ring
  have psi : ∀ ℓ n, ℓ + n ≤ N → Szkraw.iterShift w ℓ n = FD ℓ n - PH ℓ n := fun ℓ n h => by
    rw [hw_eq, iterShift_sub, fdef ℓ n h, phi ℓ n h]
  -- values of the differences
  have PH_nn : ∀ ℓ n, 2 ≤ n → 0 ≤ PH ℓ n := fun ℓ n hn => cQ_diff_nonneg h1 h2 hr ht hτ ℓ n hn
  have PH_z : ∀ ℓ n, 5 ≤ n → PH ℓ n = 0 := fun ℓ n hn => by
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 5 := ⟨n - 5, by omega⟩
    exact cQ_diff_high ν1 ν2 r t τ k ℓ
  have FD_z : ∀ ℓ n, 3 ≤ n → FD ℓ n = 0 := fun ℓ n hn => by
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
    exact dQ_diff_high' ν1 ν2 k ℓ
  have FD_nn : ∀ ℓ n, 0 ≤ FD ℓ n := fun ℓ n => by
    rcases Nat.lt_or_ge n 3 with h | h
    · interval_cases n
      · exact dQ_nonneg h1 h2 ℓ
      · simp only [hFD]; rw [dQ_diff1']; positivity
      · simp only [hFD]; rw [dQ_diff2']; exact h2
    · rw [FD_z ℓ n h]
  -- the weights on `Ω` as `WtF`
  have WU : ∀ p q ℓ a, ℓ + a ≤ N → Wt u p q ℓ a = WtF PH p q ℓ a := fun p q ℓ a h => by
    rw [Wt_eq_WtF]; exact WtF_congr fun n hn => phi ℓ n (by omega)
  have WW : ∀ p q ℓ a, ℓ + a ≤ N → Wt w p q ℓ a = WtF (fun ℓ n => FD ℓ n - PH ℓ n) p q ℓ a := fun p q ℓ a h => by
    rw [Wt_eq_WtF]; exact WtF_congr fun n hn => psi ℓ n (by omega)
  have WN : ∀ p q ℓ a, ℓ + a ≤ N → Wt ν p q ℓ a = WtF FD p q ℓ a := fun p q ℓ a h => by
    rw [Wt_eq_WtF]; exact WtF_congr fun n hn => fdef ℓ n (by omega)
  have hwC : ∀ j ℓ a, wC u w j ℓ a = Wt ν (2 * j + 2) (j + 1) ℓ a := fun j ℓ a => by
    unfold wC; rw [Wt_add]; congr 1; funext i; rw [hw_eq]; ring
  -- `u ≥ 0`, `u 1 > 0`
  have hu_nn : ∀ i, 0 ≤ u i := by
    intro i
    rw [hu_def]; unfold padNewton
    split_ifs with hi
    · have e : newtonCoeff vv.c i = PH 0 i := by
        rw [newtonCoeff_eq_iter]; exact fwdDiff_iter_congr i 0 fun j _ hj => hcQ j (by omega)
      rw [e]
      rcases Nat.lt_or_ge i 2 with h | h
      · have : i = 1 := by omega
        subst this
        simp only [hPH, Function.iterate_one]
        show 0 ≤ cQ ν1 ν2 r t τ (0 + 1) - cQ ν1 ν2 r t τ 0
        have : cQ ν1 ν2 r t τ 0 = 0 := by simp [cQ, dQ]
        rw [this, sub_zero]
        exact mul_nonneg (gQ_pos hr ht hτ _).le (dQ_nonneg h1 h2 _)
      · exact PH_nn 0 i h
    · exact le_rfl
  have hu1 : 0 < u 1 := by
    rw [hu_def]; unfold padNewton; rw [if_pos ⟨le_rfl, hN⟩]
    have : newtonCoeff vv.c 1 = vv.c 1 - vv.c 0 := by simp [newtonCoeff, Finset.sum_range_succ]; ring
    rw [this, hc0, sub_zero]; exact hcpos 1 (by norm_num) hN
  have hu0 : u 0 = 0 := padNewton_zero _ _
  have hddc : ∀ i, i ≤ N → dd u i = vv.c i := fun i hi => dd_padNewton vv.c hc0 N i hi
  have hddb : ∀ i, i ≤ N → dd w i = vv.b i := fun i hi => dd_padNewton vv.b hb0 N i hi
  refine matrixPositivity_of_kernel vv hv hu_nn hu1 hu0 hddc hddb (fun k' hk' => ?_)
  have hT : dd w N + dd u N = 1 := by
    rw [hddb N le_rfl, hddc N le_rfl]; have := hsum N le_rfl; rw [haN] at this; linarith
  -- the moves
  have bchain : ∀ ℓ k, ℓ + k ≤ N → vv.b ℓ ≤ vv.b (ℓ + k) := by
    intro ℓ k hk
    induction k with
    | zero => simp
    | succ k ih => exact le_trans (ih (by omega)) (hbmono (ℓ + k) (by omega))
  have hA0 : ∀ ℓ a, ℓ + a ≤ N → 0 ≤ wA w 0 ℓ a := fun ℓ a h => by
    unfold wA; rw [show 2 * 0 + 1 = 1 by ring, Wt_one_zero, hddb _ h, hddb _ (by omega)]
    linarith [bchain ℓ a h]
  have hA1 : ∀ ℓ a, ℓ + a ≤ N → wA w 1 ℓ a ≤ 0 := fun ℓ a h => by
    unfold wA; rw [WW _ _ _ _ h]
    refine WtF_nonpos_of fun n hn _ => ?_
    rw [FD_z ℓ n (by omega)]; linarith [PH_nn ℓ n (by omega)]
  have hAz : ∀ j ℓ a, 2 ≤ j → ℓ + a ≤ N → wA w j ℓ a = 0 := fun j ℓ a hj h => by
    unfold wA; rw [WW _ _ _ _ h]
    refine WtF_zero_of fun n hn _ => ?_
    rw [FD_z ℓ n (by omega), PH_z ℓ n (by omega)]; ring
  have hBnn : ∀ j ℓ a, ℓ + a ≤ N → 0 ≤ wB u j ℓ a := fun j ℓ a h => by
    unfold wB; rw [WU _ _ _ _ h]; exact WtF_nonneg fun n hn _ => PH_nn ℓ n (by omega)
  have hBz : ∀ j ℓ a, 2 ≤ j → ℓ + a ≤ N → wB u j ℓ a = 0 := fun j ℓ a hj h => by
    unfold wB; rw [WU _ _ _ _ h]; exact WtF_zero_of fun n hn _ => PH_z ℓ n (by omega)
  have hB0z : ∀ ℓ a, a < 2 → wB u 0 ℓ a = 0 := fun ℓ a ha => by
    unfold wB; exact Wt_eq_zero _ _ _ _ (by omega)
  have hCnn : ∀ j ℓ a, ℓ + a ≤ N → 0 ≤ wC u w j ℓ a := fun j ℓ a h => by
    rw [hwC, WN _ _ _ _ h]; exact WtF_nonneg fun n _ _ => FD_nn ℓ n
  have hCz : ∀ j ℓ a, 1 ≤ j → ℓ + a ≤ N → wC u w j ℓ a = 0 := fun j ℓ a hj h => by
    rw [hwC, WN _ _ _ _ h]; exact WtF_zero_of fun n hn _ => FD_z ℓ n (by omega)
  set V0 : ℕ → ℕ → ℕ → ℝ := fun j ℓ a => if j = 1 then -wA w 1 ℓ a else 0 with hV0
  have hV0nn : ∀ j ℓ a, ℓ + a ≤ N → 0 ≤ V0 j ℓ a := fun j ℓ a h => by
    simp only [hV0]; split_ifs
    · linarith [hA1 ℓ a h]
    · exact le_rfl
  have hcc : ∀ n, 1 ≤ n → 0 < dd u n := fun n hn => dd_pos_of hu_nn hu1 hn
  have hw : ResumWeights (dd u) (wA w) (wB u) (wC u w) (fun _ _ _ => 0) V0 (wSV u w) N := by
    refine ⟨hcc, fun j ℓ a hj h => ?_, hA0, hBnn, hCnn, fun _ _ _ _ => le_rfl, hV0nn, fun ℓ a h => ?_,
      fun j ℓ a hj h => ?_, fun j ℓ a hj h => ?_, fun j ℓ a hj h => ?_, fun j ℓ a hj h => ?_, fun ℓ a h ha => ?_⟩
    · -- split
      simp only [hV0]
      split_ifs with hj1
      · subst hj1; ring
      · rw [hAz j ℓ a (by omega) h]; ring
    · -- straight weights
      unfold wSV
      rcases Nat.lt_or_ge (ℓ + a) N with hl | hl
      · rw [hddb _ hl.le, hddc _ hl.le]; have := hsum (ℓ + a) hl.le; linarith [hapos (ℓ + a) hl]
      · rw [show ℓ + a = N by omega]; linarith
    · -- domB
      rcases Nat.lt_or_ge a 2 with ha | ha
      · rw [hB0z ℓ a ha, zero_mul]
        unfold wB; rw [Wt_eq_zero _ _ _ _ (by omega), mul_zero]
      rcases Nat.lt_or_ge j 2 with hj2 | hj2
      · have hj1 : j = 1 := by omega
        subst hj1
        rcases Nat.lt_or_ge a 4 with ha4 | ha4
        · unfold wB; rw [Wt_eq_zero _ _ _ _ (by omega), mul_zero]
          exact mul_nonneg (hBnn 0 ℓ a h) (hBnn _ _ _ (by omega))
        -- `B₁ = C(a,4) φ₄`, `B₀ ≥ C(a,2) φ₂`, `B₀' ≥ C(a-2,2) φ₂'`
        have hB1 : wB u 1 ℓ a = (a.choose 4 : ℝ) * PH ℓ 4 := by
          unfold wB; rw [WU _ _ _ _ h]; unfold WtF
          rw [sum_eq_single 4]
          · simp
          · intro n hn hn4
            rw [mem_range] at hn
            by_cases h4 : 4 ≤ n
            · rw [PH_z ℓ n (by omega), mul_zero]
            · rw [if_neg (by omega)]; ring
          · intro hn; exact absurd (mem_range.mpr (by omega)) hn
        have hB0 : (a.choose 2 : ℝ) * PH ℓ 2 ≤ wB u 0 ℓ a := by
          unfold wB; rw [WU _ _ _ _ h]
          have := WtF_ge_single (F := PH) (p := 2) (q := 0) (ℓ := ℓ) (a := a)
            (fun n hn _ => PH_nn ℓ n hn) (n0 := 2) le_rfl ha
          simpa using this
        have hB0' : ((a - 2).choose 2 : ℝ) * PH (ℓ + 1) 2 ≤ wB u 0 (ℓ + 1) (a - 2) := by
          unfold wB; rw [WU _ _ _ _ (by omega)]
          have := WtF_ge_single (F := PH) (p := 2) (q := 0) (ℓ := ℓ + 1) (a := a - 2)
            (fun n hn _ => PH_nn (ℓ + 1) n hn) (n0 := 2) le_rfl (by omega)
          simpa using this
        have hccv : dd u (ℓ + 1) = gQ r t τ (ℓ + 1) * dQ ν1 ν2 (ℓ + 1) := by
          rw [hddc _ (by omega), hcQ _ (by omega)]; rfl
        have hpp := phi2_phi2 h1 h2 hr ht hτ ℓ
        have hch : (a.choose 4 : ℝ) * 6 = (a.choose 2 : ℝ) * ((a - 2).choose 2 : ℝ) := by
          have := Nat.choose_mul (n := a) (k := 4) (s := 2) (by norm_num)
          have h42 : (4 : ℕ).choose 2 = 6 := by decide
          rw [h42, show 4 - 2 = 2 from rfl] at this
          exact_mod_cast this
        have hφ2 := PH_nn ℓ 2 le_rfl
        have hφ2' := PH_nn (ℓ + 1) 2 le_rfl
        have hφ4 := PH_nn ℓ 4 (by norm_num)
        have hC2 : (0 : ℝ) ≤ (a.choose 2 : ℝ) := Nat.cast_nonneg _
        have hC2' : (0 : ℝ) ≤ ((a - 2).choose 2 : ℝ) := Nat.cast_nonneg _
        have hC4 : (0 : ℝ) ≤ (a.choose 4 : ℝ) := Nat.cast_nonneg _
        have hc0' : 0 ≤ dd u (ℓ + 1) := (hcc (ℓ + 1) (by omega)).le
        rw [hB1, show 1 - 1 = 0 from rfl]
        have k1 : (a.choose 2 : ℝ) * PH ℓ 2 * (((a - 2).choose 2 : ℝ) * PH (ℓ + 1) 2) ≤
            wB u 0 ℓ a * wB u 0 (ℓ + 1) (a - 2) :=
          mul_le_mul hB0 hB0' (mul_nonneg hC2' hφ2') (hBnn 0 ℓ a h)
        have k2 : dd u (ℓ + 1) * PH ℓ 4 ≤ PH ℓ 2 * PH (ℓ + 1) 2 := by rw [hccv]; exact hpp
        have k3 : 6 * (a.choose 4 : ℝ) * (dd u (ℓ + 1) * PH ℓ 4) ≤ 6 * (a.choose 4 : ℝ) * (PH ℓ 2 * PH (ℓ + 1) 2) :=
          mul_le_mul_of_nonneg_left k2 (by positivity)
        have k4 : 0 ≤ 2 * (a.choose 4 : ℝ) * (dd u (ℓ + 1) * PH ℓ 4) := by positivity
        have k5 : 6 * (a.choose 4 : ℝ) * (PH ℓ 2 * PH (ℓ + 1) 2) =
            (a.choose 2 : ℝ) * PH ℓ 2 * (((a - 2).choose 2 : ℝ) * PH (ℓ + 1) 2) := by
          linear_combination (PH ℓ 2 * PH (ℓ + 1) 2) * hch
        linarith [k1, k3, k4, k5]
      · rw [hBz j ℓ a hj2 h, mul_zero]
        exact mul_nonneg (hBnn 0 ℓ a h) (hBnn _ _ _ (by omega))
    · -- domC
      rw [hCz j ℓ a hj h, mul_zero]
      rcases Nat.lt_or_ge a 2 with ha | ha
      · rw [hB0z ℓ a ha, zero_mul]
      · exact mul_nonneg (hBnn 0 ℓ a h) (hCnn _ _ _ (by omega))
    · -- domH
      simp
    · -- domV
      have : V0 j ℓ a = 0 := by simp only [hV0]; rw [if_neg (by omega)]
      rw [this, mul_zero]
      rcases Nat.lt_or_ge a 2 with ha | ha
      · rw [hB0z ℓ a ha, zero_mul]
      · exact mul_nonneg (hBnn 0 ℓ a h) (hV0nn _ _ _ (by omega))
    · -- key: `H = 0`
      simp only [mul_zero]
      have := hcc (ℓ + 1) (by omega)
      have hv1 := hV0nn 1 ℓ a h
      refine add_nonneg (add_nonneg (mul_nonneg (hA0 ℓ a h) (hBnn _ _ _ (by omega)))
        (mul_nonneg (hBnn 0 ℓ a h) (hA0 _ _ (by omega)))) (by positivity)
  exact gkernel_resum hN hw (genRec_of hu_nn hu1)
    (fun a => by rw [kerFnV_zero]; split_ifs <;> norm_num) (kerFnV_supp hu_nn hu1 N hk' hT)


/-- **Proposition 8.10** (quadratic profiles). -/
theorem quadprofile_matrix : Stmt_quadprofile
```
Axiom audit: `affine_matrix`, `affine_bmono_iff`, `quadprofile_matrix` depend only on propext, Classical.choice, Quot.sound.
