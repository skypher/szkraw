# Independent review, Lean fidelity round 14: Theorem 8.11 (convex quadratic ratio) and the remarks after Proposition 8.10 and Theorem 8.11

As in rounds 1–13, **do not check proofs**. Check only whether each Lean statement faithfully expresses the paper statement, under the acceptance rule: Lean hypotheses equivalent to or weaker than the paper's, Lean conclusion equivalent to or stronger. Where a Lean statement covers less than the paper claim, say so and check that the paper's scope sentences disclose it. Also check that the code-and-formalization text (table rows, scope sentences, disclosure) describes the Lean declarations accurately.

New since round 13: Theorem 8.11 is machine-verified (`quadratic_ratio_matrix`), with the equivalence stated after it (`quadratic_bmono_iff`). The equivalence after Proposition 8.10 (`quadprofile_bmono_iff`) was added after the round-13 brief and has not been reviewed yet.

Conventions (unchanged):
- `Coefficients N` has fields a, b, c : ℕ → ℝ.
- `Admissible v` is the paper's (2.1): stochastic, a_0 = 1, b_0 = c_0 = 0, a_N = 0, a_i > 0 for i < N, c_i > 0 for 1 ≤ i ≤ N.
- `MatrixPositivity v` is nonnegative linearization: `productMatrix v m n k = g(m,n;k)` for all m ≤ N and all n, k.
- `profile v i = v.b i + v.c i`.
- `newtonCoeff x k = Σ_i (−1)^(k−i) C(k,i) x_i`.
- Theorems 8.1 and 8.9 and Proposition 8.10 were accepted earlier with the same array-based encoding: Admissible, the ratio relation for i ≤ N, and `LogConcaveNoInternalZeros N (newtonCoeff (profile v))` where applicable.
- `Szkraw.iterShift ν ℓ n = Σ_h C(ℓ,h) ν(n+h)` (iterated shift sums) and `dd ν ℓ = iterShift ν ℓ 0`. For ν the zero-padded Newton sequence of d, `dd ν ℓ = d_ℓ` and `iterShift ν ℓ n = Δ^n d(ℓ)` for ℓ + n ≤ N. `Wt u p q ℓ a = Σ_{p ≤ n ≤ a} C(n−p+q, q) C(a,n) iterShift u ℓ n`; `WtF F p q ℓ a` is the same with `F ℓ n` in place of `iterShift u ℓ n`. `LCNZ` is log-concavity without internal zeros for an infinite nonnegative sequence. `sH`, `sT` are the sums H_*, T of the proof of Theorem 8.9.

Answer format: a table (paper claim | Lean declaration | MATCH / MATCH, SCOPE NOTED / MISMATCH | reason), exact fixes, and an overall verdict (PASS / PASS WITH MINOR FIXES / FAIL). Be terse.

## Part A. Paper statements

#### Section 8 notation
```latex
Write
\[
\nu_k=\sum_{i=0}^k(-1)^{k-i}\binom ki d_i\quad(1\leq k\leq N),\qquad d_n=\sum_{k=1}^n\binom nk\nu_k\quad(0\leq n\leq N);
\]
below we put $\nu_0=0$ and $\nu_k=0$ for $k>N$.
We say that $(\nu_k)_{1\leq k\leq N}$ is \emph{log-concave without internal zeros} if all $\nu_k\geq0$, the indices with $\nu_k>0$ form an interval $\{1,\ldots,K\}$, and $\nu_k^2\geq\nu_{k-1}\nu_{k+1}$ for $2\leq k\leq N-1$. Note $\nu_1=d_1>0$.
```

#### Proposition 8.10 and the text after it
```latex
\begin{proposition}[Quadratic profiles]\label{prop:lc-quadprof}
Let $d_i=\nu_1i+\nu_2\binom i2$ with $\nu_1>0$, $\nu_2\geq0$ and $d_N=1$, let $\rho(x)=r+tx+\tau\binom x2$ with $r>0$ and $t,\tau\geq0$, and put $a_i=1-d_i$, $b_i=(1-\rho(i))d_i$ and $c_i=\rho(i)d_i$. If $b$ is nondecreasing, then the system has nonnegative linearization.
\end{proposition}

As in the proof of Theorem~\ref{thm:lc-affine}, $b_{i+1}-b_i=f_1(i)\bigl(1-\rho(i+1)-(t+\tau i)R_i\bigr)$ with a nonincreasing bracket, so $b$ is nondecreasing exactly when $t(N+R)+\tau\bigl(\binom N2+(N-1)R\bigr)\leq1-r$, where $R=d_{N-1}/(1-d_{N-1})$.
```

#### Theorem 8.11 and the text after it
```latex
\begin{theorem}[Convex quadratic ratio]\label{thm:lc-quadratic}
Let $0=d_0<d_1<\cdots<d_N=1$ have Newton coefficients that are log-concave without internal zeros, let $\rho(x)=r+tx+\tau\binom x2$ with $r>0$ and $t,\tau\geq0$, and put $a_i=1-d_i$, $b_i=(1-\rho(i))d_i$ and $c_i=\rho(i)d_i$. If $b$ is nondecreasing, then the system has nonnegative linearization.
\end{theorem}

This contains Theorem~\ref{thm:lc-affine} ($\tau=0$) and Proposition~\ref{prop:lc-quadprof}. As there, $b$ is nondecreasing exactly when $t(N+R)+\tau\bigl(\binom N2+(N-1)R\bigr)\leq1-r$ with $R=d_{N-1}/(1-d_{N-1})$. The Newton coefficients of $c$ need not be log-concave: for $d_i=i/4$ and $\rho(x)=\frac12+\binom x2/40$ they are $(1/8,1/80,3/160,0)$. The proof below replaces their log-concavity by a weighted detour inequality.
```

#### Equations cited in the scope sentence (from the proof of Theorem 8.11)
```latex
\begin{equation}\label{eq:quad-B}
(n+1)(n+2)\,\varphi_2(\ell)\varphi_n(\ell+1)\geq8(n-1)\,c_{\ell+1}\varphi_{n+2}(\ell).
\end{equation}
\begin{equation}\label{eq:quad-cert}
K_nAB-L_npC\geq0.
\end{equation}
\begin{equation}\label{eq:quad-key}
A^\psi_0(\ell,a)B_0(\ell+1,a-1)+B_0(\ell,a)A^\psi_0(\ell+1,a-2)\geq c_{\ell+1}\bigl(4H_1-2V_1-W_1\bigr)(\ell,a).
\end{equation}
```
Here $\varphi_n(\ell)=\Delta^nc(\ell)$, $f_n(\ell)=\Delta^nd(\ell)$, $c_{\ell+1}=\rho(\ell+1)d_{\ell+1}$, $\Delta\rho(x)=t+\tau x$; in eq. quad-key, $A^\psi_0(\ell,a)=b_{\ell+a}-b_\ell$, $B_0(\ell,a)=\sum_{n\geq2}\binom an\varphi_n(\ell)$, and $H_1,V_1,W_1$ are $W_{3,1}$ formed from $h_n=(1-\rho(\ell+n))f_n$, $v_n=n\Delta\rho(\ell+n-1)f_{n-1}$, $w_n=\binom n2\tau f_{n-2}$, where $W_{p,q}(\ell,a)=\sum_{n\geq p}\binom{n-p+q}q\binom an(\cdot)_n$; in eq. quad-cert, $K_n=(n+1)(n+2)$, $L_n=8(n-1)$, $A=p+(2h-1)s+h^2\tau$, $B=p+nh(s+\tau)+\binom n2h^2\tau$, $C=p+((n+2)h-1)s+\binom{n+2}2h^2\tau$, for an integer $n\geq2$ and reals $h\geq1$, $p,\tau\geq0$, $s\geq(h-1)\tau$.

#### Code-and-formalization: table rows, scope sentences, disclosure
```latex
Proposition~\ref{prop:lc-quadprof}: quadratic profiles & \path{Szkraw.quadprofile_matrix}\\[3pt]
Theorem~\ref{thm:lc-quadratic}: convex quadratic ratio & \path{Szkraw.quadratic_ratio_matrix}, \path{Szkraw.quadratic_bmono_iff}\\[3pt]

Proposition~\ref{prop:lc-quadprof} is stated for arrays satisfying \eqref{eq:basic} with $b_i+c_i=\nu_1i+\nu_2\binom i2$ and $c_i=\bigl(r+ti+\tau\binom i2\bigr)(b_i+c_i)$ for $i\leq N$, $\nu_1>0$, $\nu_2\geq0$, $r>0$, $t,\tau\geq0$ and $b_0\leq\cdots\leq b_N$; its proof identifies the iterated shift sums of the Newton coefficients with finite differences on $\Omega$ (\path{Szkraw.iterShift_padNewton}), uses the Leibniz rule for a quadratic factor (\path{Szkraw.fwdDiff_quad_mul}) and the inequality $\varphi_2(\ell)\varphi_2(\ell+1)\geq c_{\ell+1}\varphi_4(\ell)$ (\path{Szkraw.phi2_phi2}), and applies the resummation with $H_j=0$ and $V_1=-A^\psi_1$. The equivalent form of the monotonicity of $b$ stated after Proposition~\ref{prop:lc-quadprof} is \path{Szkraw.quadprofile_bmono_iff}, stated for the same arrays without the monotonicity hypothesis. Theorem~\ref{thm:lc-quadratic} is stated for arrays satisfying \eqref{eq:basic} whose profile has Newton coefficients log-concave without internal zeros, with $c_i=\bigl(r+ti+\tau\binom i2\bigr)(b_i+c_i)$ for $i\leq N$, $r>0$, $t,\tau\geq0$ and $b_0\leq b_1\leq\cdots\leq b_N$, using the array-based encoding of Theorem~\ref{thm:lc}; the equivalent form of the monotonicity of $b$ stated after it is \path{Szkraw.quadratic_bmono_iff}, stated for the same arrays without the monotonicity hypothesis. Its proof formalizes the Leibniz rule for a quadratic factor in every order (\path{Szkraw.leibniz_quad}), the weighted detour \eqref{eq:quad-B} through the reduction to the configuration $u_k=q^{k-1}$ and the certificate \eqref{eq:quad-cert} (\path{Szkraw.quadB_seq}, \path{Szkraw.cert_nonneg}), the key inequality \eqref{eq:quad-key} (\path{Szkraw.QuadSetting.key}, \path{Szkraw.quad_key_red}), and the resummation with the third family $W_j$ (\path{Szkraw.resum_nonneg2}, \path{Szkraw.gkernel_resum2}). The Lean proof uses the detour constant $4$ for $B$, $C'$, $H$ and $V$ and the constant $3$ for $W$.

Theorem~\ref{thm:lc-quadratic} was added last; its written proof passed a further review round with minor fixes, and it is machine-verified.

``Machine-verified'' refers only to the Lean theorems listed in the section on code and formalization, with the axioms stated there. Other results and the prose remarks are supported by written proofs, AI review and exact numerical checks, but are not machine-verified.
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

### lean/Szkraw/VRQuadMain.lean
```lean
/-- Hypotheses of Theorem 8.11: `c_i = (r + t i + τ C(i,2)) d_i` with `r > 0` and `t, τ ≥ 0`, the
diagonal coefficients `b_0 ≤ b_1 ≤ ⋯ ≤ b_N` nondecreasing, and a profile `d = b + c` whose Newton
coefficients are log-concave without internal zeros. -/
def QuadRatioHyp {N : ℕ} (vv : Coefficients N) : Prop :=
  ∃ r t τ : ℝ, 0 < r ∧ 0 ≤ t ∧ 0 ≤ τ ∧ (∀ i, i < N → vv.b i ≤ vv.b (i + 1)) ∧
    (∀ i, i ≤ N → vv.c i = (r + t * i + τ * (i.choose 2 : ℝ)) * profile vv i) ∧
    LogConcaveNoInternalZeros N (newtonCoeff (profile vv))

/-- Theorem 8.11 (convex quadratic ratio), matrix-positivity conclusion. -/
def Stmt_quadratic_ratio : Prop :=
  ∀ (N : ℕ) (vv : Coefficients N), Admissible vv → QuadRatioHyp vv → MatrixPositivity vv

/-- **Theorem 8.11** (convex quadratic ratio). -/
theorem quadratic_ratio_matrix : Stmt_quadratic_ratio

/-- **After Theorem 8.11**: for the arrays of Theorem 8.11 without the monotonicity hypothesis, `b` is
nondecreasing exactly when `t(N+R) + τ(C(N,2) + (N-1)R) ≤ 1 - r`, where `R = d_{N-1}/(1 - d_{N-1})`. -/
theorem quadratic_bmono_iff {N : ℕ} (vv : Coefficients N) (hv : Admissible vv) {r t τ : ℝ}
    (ht : 0 ≤ t) (hτ : 0 ≤ τ)
    (hc : ∀ i, i ≤ N → vv.c i = (r + t * i + τ * (i.choose 2 : ℝ)) * profile vv i)
    (hlc : LogConcaveNoInternalZeros N (newtonCoeff (profile vv))) :
    (∀ i, i < N → vv.b i ≤ vv.b (i + 1)) ↔
      t * (N + profile vv (N - 1) / (1 - profile vv (N - 1))) +
        τ * ((N.choose 2 : ℝ) + ((N : ℝ) - 1) * (profile vv (N - 1) / (1 - profile vv (N - 1)))) ≤ 1 - r

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

/-- **Proposition 8.10** (quadratic profiles). -/
theorem quadprofile_matrix : Stmt_quadprofile

/-- **After Proposition 8.10**: for the arrays of Proposition 8.10 without the monotonicity
hypothesis, `b` is nondecreasing exactly when `t(N+R) + τ(C(N,2) + (N-1)R) ≤ 1 - r`, where
`R = d_{N-1}/(1 - d_{N-1})`. -/
theorem quadprofile_bmono_iff {N : ℕ} (vv : Coefficients N) (hv : Admissible vv) {ν1 ν2 r t τ : ℝ}
    (h1 : 0 < ν1) (h2 : 0 ≤ ν2) (ht : 0 ≤ t) (hτ : 0 ≤ τ)
    (hd : ∀ i, i ≤ N → profile vv i = ν1 * i + ν2 * (i.choose 2 : ℝ))
    (hc : ∀ i, i ≤ N → vv.c i = (r + t * i + τ * (i.choose 2 : ℝ)) * profile vv i) :
    (∀ i, i < N → vv.b i ≤ vv.b (i + 1)) ↔
      t * (N + profile vv (N - 1) / (1 - profile vv (N - 1))) +
        τ * ((N.choose 2 : ℝ) + ((N : ℝ) - 1) * (profile vv (N - 1) / (1 - profile vv (N - 1)))) ≤ 1 - r

```

### lean/Szkraw/VRQuadLeib.lean
```lean
/-- The ratio as a function on `ℕ`. -/
noncomputable def rhoN (r t τ : ℝ) (i : ℕ) : ℝ := r + t * i + τ * (i.choose 2 : ℝ)

```

### lean/Szkraw/VRQuadB.lean
```lean
/-- `ρ(x) = r + t x + τ C(x,2)` for real `x`. -/
noncomputable def rhoQ (r t τ x : ℝ) : ℝ := r + t * x + τ * (x * (x - 1) / 2)

/-- `Δρ(x) = t + τ x`. -/
noncomputable def drhoQ (t τ x : ℝ) : ℝ := t + τ * x

```

### lean/Szkraw/VRQuadB2.lean
```lean
/-- The Leibniz expression `Φ_k(base, v)`. -/
noncomputable def PhiQ (r t τ base : ℝ) (k : ℕ) (v : ℕ → ℝ) : ℝ :=
  rhoQ r t τ (base + k) * v k + k * drhoQ t τ (base + k - 1) * v (k - 1) +
    (k : ℝ) * (k - 1) / 2 * τ * v (k - 2)

```

### lean/Szkraw/VRQuadLeib.lean
```lean
/-- The quadratic Leibniz rule for every order. -/
theorem leibniz_quad (r t τ : ℝ) (ν : ℕ → ℝ) (n ℓ : ℕ) :
    (fwdDiff 1)^[n] (fun i => rhoN r t τ i * dd ν i) ℓ = PhiQ r t τ ℓ n (Szkraw.iterShift ν ℓ)

```

### lean/Szkraw/VRQuadB2.lean
```lean
/-- **The weighted `B`-detour** (paper, eq. `quad-B`) for a log-concave sequence with `v₀ ≤ ℓ v₁`. -/
theorem quadB_seq {v : ℕ → ℝ} (hv : LCNZ v) (hv1 : 0 < v 1) {n : ℕ} (hn : 2 ≤ n) {r t τ ℓ : ℝ}
    (hr : 0 < r) (ht : 0 ≤ t) (hτ : 0 ≤ τ) (hℓ : 0 ≤ ℓ) (hz : v 0 ≤ ℓ * v 1) :
    8 * ((n : ℝ) - 1) * rhoQ r t τ (ℓ + 1) * (v 0 + v 1) * PhiQ r t τ ℓ (n + 2) v ≤
      ((n : ℝ) + 1) * (n + 2) * PhiQ r t τ ℓ 2 v * PhiQ r t τ (ℓ + 1) n (fun k => v k + v (k + 1))

```

### lean/Szkraw/VRQuadCert.lean
```lean
/-- `K_n A B - L_n p C` of the certificate, with `n` real. -/
noncomputable def certE (n h p τ s : ℝ) : ℝ :=
  (n + 1) * (n + 2) * (p + (2 * h - 1) * s + h ^ 2 * τ) *
      (p + n * h * (s + τ) + n * (n - 1) / 2 * h ^ 2 * τ) -
    8 * (n - 1) * p * (p + ((n + 2) * h - 1) * s + (n + 2) * (n + 1) / 2 * h ^ 2 * τ)

/-- **The certificate** (paper, eq. `quad-cert`). -/
theorem cert_nonneg {n : ℕ} (hn : 2 ≤ n) {h p τ s : ℝ} (hh : 1 ≤ h) (hp : 0 ≤ p) (hτ : 0 ≤ τ)
    (hs : (h - 1) * τ ≤ s) : 0 ≤ certE n h p τ s

```

### lean/Szkraw/VRQuadDetours.lean
```lean
/-- The Newton sequence of `b`. -/
noncomputable def quadW (ν u : ℕ → ℝ) (i : ℕ) : ℝ := ν i - u i

/-- The setting of Theorem 8.11: `ν` is log-concave without internal zeros with `ν 0 = 0 < ν 1`,
`u ≥ 0` satisfies the Leibniz rule on `Ω`, and `b`, with values `dd (quadW ν u) m`, is nondecreasing. -/
structure QuadSetting (N : ℕ) (r t τ : ℝ) (ν u : ℕ → ℝ) : Prop where
  hN : 1 ≤ N
  hr : 0 < r
  ht : 0 ≤ t
  hτ : 0 ≤ τ
  hν : LCNZ ν
  hν0 : ν 0 = 0
  hν1 : 0 < ν 1
  hu_nn : ∀ i, 0 ≤ u i
  hφ : ∀ ℓ n, ℓ + n ≤ N → Szkraw.iterShift u ℓ n = PhiQ r t τ ℓ n (Szkraw.iterShift ν ℓ)
  hb : ∀ m, m < N → dd (quadW ν u) m ≤ dd (quadW ν u) (m + 1)

/-- `h_n(ℓ) = (1 - ρ(ℓ+n)) f_n(ℓ)`. -/
noncomputable def hQ (r t τ : ℝ) (ν : ℕ → ℝ) (ℓ n : ℕ) : ℝ :=
  (1 - rhoN r t τ (ℓ + n)) * Szkraw.iterShift ν ℓ n

/-- `v_n(ℓ) = n Δρ(ℓ+n-1) f_{n-1}(ℓ)`. -/
noncomputable def vQ (t τ : ℝ) (ν : ℕ → ℝ) (ℓ n : ℕ) : ℝ :=
  (n : ℝ) * drhoQ t τ ((ℓ : ℝ) + n - 1) * Szkraw.iterShift ν ℓ (n - 1)

/-- `w_n(ℓ) = C(n,2) τ f_{n-2}(ℓ)`. -/
noncomputable def wQ (τ : ℝ) (ν : ℕ → ℝ) (ℓ n : ℕ) : ℝ :=
  (n : ℝ) * ((n : ℝ) - 1) / 2 * τ * Szkraw.iterShift ν ℓ (n - 2)

/-- `H_j = W^h_{2j+1,j}`. -/
noncomputable def quadH (r t τ : ℝ) (ν : ℕ → ℝ) (j ℓ a : ℕ) : ℝ := WtF (hQ r t τ ν) (2 * j + 1) j ℓ a

/-- `V_j = W^v_{2j+1,j}`. -/
noncomputable def quadV (t τ : ℝ) (ν : ℕ → ℝ) (j ℓ a : ℕ) : ℝ := WtF (vQ t τ ν) (2 * j + 1) j ℓ a

/-- `W_j = W^w_{2j+1,j}`. -/
noncomputable def quadWw (τ : ℝ) (ν : ℕ → ℝ) (j ℓ a : ℕ) : ℝ := WtF (wQ τ ν) (2 * j + 1) j ℓ a

```

### lean/Szkraw/VRQuadMain.lean
```lean
/-- **The key inequality** (paper, eq. `quad-key`), on `Ω` with `a ≥ 3`. -/
theorem QuadSetting.key {ℓ a : ℕ} (h : ℓ + a ≤ N) (ha : 3 ≤ a) :
    4 * dd u (ℓ + 1) * quadH r t τ ν 1 ℓ a ≤
      Wt (quadW ν u) 1 0 ℓ a * Wt u 2 0 (ℓ + 1) (a - 1) + Wt u 2 0 ℓ a * Wt (quadW ν u) 1 0 (ℓ + 1) (a - 2) +
      2 * dd u (ℓ + 1) * quadV t τ ν 1 ℓ a + dd u (ℓ + 1) * quadWw τ ν 1 ℓ a

```

### lean/Szkraw/VRQuadKey.lean
```lean
/-- `Z = Σ_{n ≥ 2} C(a-n,2) C(a,n) u_n`. -/
noncomputable def sZ (u : ℕ → ℝ) (a : ℕ) : ℝ :=
  ∑ n ∈ range (a + 1), (if 2 ≤ n then ((a - n).choose 2 : ℝ) * (a.choose n : ℝ) else 0) * u n

/-- `W_* = Σ_n n C(a-n,2) C(a,n) u_n`, so that `W₁ = τ W_*`. -/
noncomputable def sWs (u : ℕ → ℝ) (a : ℕ) : ℝ :=
  ∑ n ∈ range (a + 1), ((n : ℝ) * ((a - n).choose 2 : ℝ) * (a.choose n : ℝ)) * u n

/-- **The reduced key inequality for quadratic ratios**: for `α u₁ ≥ s u₀`, `s ≥ τ(a-1)`. -/
theorem quad_key_red {ν : ℕ → ℝ} (hν : LCNZ ν) (hν1 : 0 < ν 1) (ℓ a : ℕ) (ha : 3 ≤ a) {α s τ : ℝ}
    (hs : 0 ≤ s) (hτ : 0 ≤ τ) (hα : s * dd ν ℓ ≤ α * Szkraw.iterShift ν ℓ 1)
    (hsτ : τ * ((a : ℝ) - 1) ≤ s) :
    0 ≤ (α * Wt ν 1 0 ℓ a - s * a * dd ν ℓ + τ * (a.choose 2 : ℝ) * dd ν ℓ) * Wt ν 2 0 (ℓ + 1) (a - 1) +
      Wt ν 2 0 ℓ a * ((α + s) * Wt ν 1 0 (ℓ + 1) (a - 2) - s * ((a : ℝ) - 2) * dd ν (ℓ + 1) +
        τ * ((a - 1).choose 2 : ℝ) * dd ν (ℓ + 1)) -
      dd ν (ℓ + 1) * (4 * α * sH (Szkraw.iterShift ν ℓ) a + 2 * s * sT (Szkraw.iterShift ν ℓ) a +
        4 * τ * sZ (Szkraw.iterShift ν ℓ) a - τ * sWs (Szkraw.iterShift ν ℓ) a)

```

### lean/Szkraw/VRMoves2.lean
```lean
/-- Hypotheses of the resummation, on `Ω = {ℓ + a ≤ N}`: the `A`-weights of positive index split
as `H - V - W`; the weights `A₀, B, C, H, V, W` and the straight weight `s` are nonnegative; the
`B`, `C`, `H`, `V` (constant `4`) and `W` (constant `3`) moves are dominated by detours through `B₀`;
and the key inequality controls `H₁`. -/
structure ResumWeights2 (cc : ℕ → ℝ) (A B C H V W : ℕ → ℕ → ℕ → ℝ) (s : ℕ → ℕ → ℝ) (N : ℕ) : Prop where
  cc_pos : ∀ n, 1 ≤ n → 0 < cc n
  split : ∀ j ℓ a, 1 ≤ j → ℓ + a ≤ N → A j ℓ a = H j ℓ a - V j ℓ a - W j ℓ a
  A0_nn : ∀ ℓ a, ℓ + a ≤ N → 0 ≤ A 0 ℓ a
  B_nn : ∀ j ℓ a, ℓ + a ≤ N → 0 ≤ B j ℓ a
  C_nn : ∀ j ℓ a, ℓ + a ≤ N → 0 ≤ C j ℓ a
  H_nn : ∀ j ℓ a, ℓ + a ≤ N → 0 ≤ H j ℓ a
  V_nn : ∀ j ℓ a, ℓ + a ≤ N → 0 ≤ V j ℓ a
  W_nn : ∀ j ℓ a, ℓ + a ≤ N → 0 ≤ W j ℓ a
  s_nn : ∀ ℓ a, ℓ + a ≤ N → 0 ≤ s ℓ a
  domB : ∀ j ℓ a, 1 ≤ j → ℓ + a ≤ N → 4 * cc (ℓ + 1) * B j ℓ a ≤ B 0 ℓ a * B (j - 1) (ℓ + 1) (a - 2)
  domC : ∀ j ℓ a, 1 ≤ j → ℓ + a ≤ N → 4 * cc (ℓ + 1) * C j ℓ a ≤ B 0 ℓ a * C (j - 1) (ℓ + 1) (a - 2)
  domH : ∀ j ℓ a, 2 ≤ j → ℓ + a ≤ N → 4 * cc (ℓ + 1) * H j ℓ a ≤ B 0 ℓ a * H (j - 1) (ℓ + 1) (a - 2)
  domV : ∀ j ℓ a, 2 ≤ j → ℓ + a ≤ N → 4 * cc (ℓ + 1) * V j ℓ a ≤ B 0 ℓ a * V (j - 1) (ℓ + 1) (a - 2)
  domW : ∀ j ℓ a, 2 ≤ j → ℓ + a ≤ N → 3 * cc (ℓ + 1) * W j ℓ a ≤ B 0 ℓ a * W (j - 1) (ℓ + 1) (a - 2)
  key : ∀ ℓ a, ℓ + a ≤ N → 3 ≤ a → 4 * cc (ℓ + 1) * H 1 ℓ a ≤
    A 0 ℓ a * B 0 (ℓ + 1) (a - 1) + B 0 ℓ a * A 0 (ℓ + 1) (a - 2) + 2 * cc (ℓ + 1) * V 1 ℓ a +
      cc (ℓ + 1) * W 1 ℓ a

/-- **Resummation induction.** Every solution of the generic kernel recurrence with nonnegative
initial values and the support property is nonnegative under `ResumWeights2`. -/
theorem gkernel_resum2 {H V W : ℕ → ℕ → ℕ → ℝ} {ω : ℕ → ℕ → ℝ} (hN : 1 ≤ N)
    (hw : ResumWeights2 cc A B C H V W s N) (hrec : GenRec cc A B C s ω)
    (h0 : ∀ a, 0 ≤ ω 0 a) (hsupp : ∀ ℓ a, N < ℓ + a → ω ℓ a = 0) : ∀ ℓ a, 0 ≤ ω ℓ a

```

### lean/Szkraw/VRResum2.lean
```lean
theorem resum_nonneg2 (K : ℕ) (hK : ∀ i, lev i ≤ K)
    {U P Q Cp Cm A0 Hp Hm H1 Vp Vm V1 Wp Wm W1 : Matrix ι ι ℝ}
    (hU : MNN U) (hP : MNN P) (hCp : MNN Cp) (hA0 : MNN A0) (hHp : MNN Hp) (hVp : MNN Vp) (hWp : MNN Wp)
    (rU : Raise lev 1 U) (rP : Raise lev 1 P) (rQ : Raise lev 1 Q) (rCp : Raise lev 1 Cp)
    (rCm : Raise lev 1 Cm) (rA0 : Raise lev 1 A0) (rHp : Raise lev 1 Hp) (rHm : Raise lev 1 Hm)
    (rH1 : Raise lev 1 H1) (rVp : Raise lev 1 Vp) (rVm : Raise lev 1 Vm)
    (rWp : Raise lev 1 Wp) (rWm : Raise lev 1 Wm)
    (dQ : ∀ i j, 4 * Q i j ≤ (P * P) i j)
    (dH : ∀ i j, 4 * Hm i j ≤ (Hp * P) i j)
    (dV : ∀ i j, 4 * Vm i j ≤ (Vp * P) i j)
    (dC : ∀ i j, 4 * Cm i j ≤ (Cp * P) i j)
    (dW : ∀ i j, 3 * Wm i j ≤ (Wp * P) i j)
    (dV1 : ∀ i j, V1 i j ≤ Vp i j) (dW1 : ∀ i j, W1 i j ≤ Wp i j)
    (dkey : ∀ i j, 4 * H1 i j ≤ (A0 * P) i j + (P * A0) i j + 2 * V1 i j + W1 i j)
    {β ω : ι → ℝ} (hβ : ∀ i, 0 ≤ β i)
    (hrec : ω = β + (U + P - Q + Cp - Cm + A0 + Hp - Hm - H1 + Vp - Vm + Wp - Wm) *ᵥ ω) :
    ∀ i, 0 ≤ ω i

```
