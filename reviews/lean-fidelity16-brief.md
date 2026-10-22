# Independent review, Lean fidelity round 16: the remarks after Theorems 8.9 and 8.11 and the counterexamples in the open problems

As in rounds 1–15, **do not check proofs**. Check only whether each Lean statement faithfully expresses the paper claim, under the acceptance rule: Lean hypotheses equivalent to or weaker than the paper's, Lean conclusion equivalent to or stronger. Where a Lean statement covers less than the paper claim, say so and check that the scope sentences disclose it. Also check that the new table rows and scope sentences describe the Lean declarations accurately.

New since round 15: prose remarks and examples are now formalized: the remarks after Theorem 8.9 (linear-profile threshold, range of κ, strictness for nonlinear profiles, the N = 4 example), the example after Theorem 8.11, the failure of eq. quad-B with constant 1 (from the proof of Theorem 8.11), and the two N = 3 counterexamples in the open problems.

Conventions (unchanged): `Coefficients N` has fields a, b, c : ℕ → ℝ; `Admissible v` is the paper's (2.1); `MatrixPositivity v` is nonnegative linearization with `productMatrix v m n k = g(m,n;k)`; `profile v i = v.b i + v.c i`; `newtonCoeff x k = Σ_i (−1)^(k−i) C(k,i) x_i`; `fwdDiff 1 f x = f (x+1) − f x`, so `(fwdDiff 1)^[n] c ℓ = Δ^n c(ℓ) = φ_n(ℓ)`. `AffineRatioHyp`, `affine_bmono_iff` and `QuadRatioHyp` were accepted in rounds 13–14 as the hypotheses of Theorems 8.9 and 8.11 and the equivalence after Theorem 8.9.

Answer format: a table (paper claim | Lean declaration | MATCH / MATCH, SCOPE NOTED / MISMATCH | reason), exact fixes, and an overall verdict (PASS / PASS WITH MINOR FIXES / FAIL). Be terse.

## Part A. Paper text

#### Theorem 8.9 and the remarks after it
```latex
\begin{theorem}[Linearly increasing ratio]\label{thm:lc-affine}
Let $0=d_0<d_1<\cdots<d_N=1$ have Newton coefficients that are log-concave without internal zeros, let $0<r\leq1$ and $\kappa\geq0$, and put $\rho_i=r+\kappa i/N$, $a_i=1-d_i$, $b_i=(1-\rho_i)d_i$ and $c_i=\rho_id_i$. If $b$ is nondecreasing, then the system has nonnegative linearization. The condition that $b$ be nondecreasing is equivalent to $\kappa\bigl(N+d_{N-1}/(1-d_{N-1})\bigr)\leq N(1-r)$.
\end{theorem}

For the linear profile $d_i=i/N$ the condition reads $\kappa\leq\frac N{2N-1}(1-r)$, and these are arrays of Proposition~\ref{prop:lc-quad}. For a convex profile $d_{N-1}\leq(N-1)/N$, so the admitted range of $\kappa$ contains $[0,\frac N{2N-1}(1-r)]$. When $r<1$, this containment is strict for a nonlinear profile. For example, $N=4$, $d_i=(2^i-1)/15$, $r=1/2$ and $\kappa=2/5$ are admitted, with $b=(0,2/75,3/50,7/75,1/10)$, although $(2N-1)\kappa/N=7/10>1-r$.
```

#### Proposition 8.8 (cited in the remark)
```latex
\begin{proposition}[Quadratic arrays]\label{prop:lc-quad}
Let $b_n=\beta_1n+\beta_2\binom n2$ and $c_n=\kappa_1n+\kappa_2\binom n2$ $(0\leq n\leq N)$ define an array as above. If $\kappa_2\geq0$, $\kappa_2+\beta_2\geq0$ and $b_0\leq b_1\leq\cdots\leq b_N$, then the system has nonnegative linearization.
\end{proposition}
```

#### Theorem 8.11, the remark after it, and the parenthetical remark in its proof
```latex
\begin{theorem}[Convex quadratic ratio]\label{thm:lc-quadratic}
Let $0=d_0<d_1<\cdots<d_N=1$ have Newton coefficients that are log-concave without internal zeros, let $\rho(x)=r+tx+\tau\binom x2$ with $r>0$ and $t,\tau\geq0$, and put $a_i=1-d_i$, $b_i=(1-\rho(i))d_i$ and $c_i=\rho(i)d_i$. If $b$ is nondecreasing, then the system has nonnegative linearization.
\end{theorem}

This contains Theorem~\ref{thm:lc-affine} ($\tau=0$) and Proposition~\ref{prop:lc-quadprof}. As there, $b$ is nondecreasing exactly when $t(N+R)+\tau\bigl(\binom N2+(N-1)R\bigr)\leq1-r$ with $R=d_{N-1}/(1-d_{N-1})$. The Newton coefficients of $c$ need not be log-concave: for $d_i=i/4$ and $\rho(x)=\frac12+\binom x2/40$ they are $(1/8,1/80,3/160,0)$. The proof below replaces their log-concavity by a weighted detour inequality.

(With constant $1$ in place of $\frac{(n+1)(n+2)}{8(n-1)}$, \eqref{eq:quad-B} can fail: for $N=20$, $d_i=(2^i-1)/(2^{20}-1)$, $r=\frac12$, $t=0$, $\tau=10^{-3}$ one gets $\varphi_2(16)\varphi_2(17)<c_{17}\varphi_4(16)$.)
```
(In the parenthetical remark, $\varphi_n(\ell)=\Delta^nc(\ell)$ and $c_{\ell+1}=\rho(\ell+1)d_{\ell+1}$; eq. quad-B reads $(n+1)(n+2)\varphi_2(\ell)\varphi_n(\ell+1)\geq8(n-1)c_{\ell+1}\varphi_{n+2}(\ell)$, whose constant-1 version at $n=2$ is $\varphi_2(\ell)\varphi_2(\ell+1)\geq c_{\ell+1}\varphi_4(\ell)$.)

#### Open problems (excerpt)
```latex
Log-concavity of the Newton coefficients of both $d$ and $c$ together with monotone $b$ does not suffice: $d=(0,25,55,91)/91$, $c=(0,24,54,90)/91$ gives $g(3,3;3)=-3/2002$. Increasing ratios with nondecreasing $b$ can fail as well: for the linear profile $d_i=i/3$ and the concave ratio $\rho=(1/2,3/4,5/6)$, for which $b_i=1/6$ for $i\geq1$, one has $g(3,3;3)=-1/24$, and the convex kinked ratio below fails at $N=120$. Convex ratios of higher degree are not covered: for the cubic ratio $\rho_i=r+\kappa(i/N)^3$ on a linear profile, (P) held in our exact searches up to $N=150$ (coefficients $g(m,N;k)$) but the operator $M$ of the proof of Theorem~\ref{thm:lc-affine} has negative entries, and the steep ratio $\rho_i=r+\kappa2^{i-N}$ fails (P) on linear profiles from $N=8$ (\path{runs/varratio/nonlinear_probe.py}, \path{runs/varratio/resum_test.py}).
```

#### Code-and-formalization: new table rows and scope sentences
```latex
Remarks after Theorem~\ref{thm:lc-affine}: range of $\kappa$ and example & \path{Szkraw.affine_range_remarks}, \path{Szkraw.profile_last_le}, \path{Szkraw.affEx_remark}\\[3pt]
Remarks on Theorem~\ref{thm:lc-quadratic}: example, and \eqref{eq:quad-B} with constant $1$ & \path{Szkraw.quadExample_remark}, \path{Szkraw.quadB_unit_fails}\\[3pt]
Section~\ref{sec:open}: the two counterexamples with $N=3$ & \path{Szkraw.openEx1_fails}, \path{Szkraw.openEx2_fails}\\[3pt]

For the remarks after Theorem~\ref{thm:lc-affine}, \path{Szkraw.profile_last_le} gives $d_{N-1}\leq(N-1)/N$, with equality only for the linear profile, for arrays satisfying \eqref{eq:basic} whose profile has Newton coefficients log-concave without internal zeros (such profiles are convex), and \path{Szkraw.affine_range_remarks} states the claims on the range of $\kappa$ for the condition $\kappa\bigl(N+d_{N-1}/(1-d_{N-1})\bigr)\leq N(1-r)$, which is equivalent to nondecreasing $b$ by \path{Szkraw.affine_bmono_iff}; that the linear-profile arrays are arrays of Proposition~\ref{prop:lc-quad} is not stated separately. \path{Szkraw.affEx_remark}, \path{Szkraw.quadExample_remark} and \path{Szkraw.quadB_unit_fails} also show that the examples satisfy the hypotheses of Theorem~\ref{thm:lc-affine}, respectively Theorem~\ref{thm:lc-quadratic}. In Section~\ref{sec:open} only the two counterexamples with $N=3$ are formalized; they are stated with all properties claimed for them, and the remaining computational statements there are not formalized.
```

## Part B. Lean statements

### Accepted earlier (unchanged)
```lean
-- Szkraw/LogConcaveStatement.lean
/-- `(ν k)_{1 ≤ k ≤ N}` is nonnegative and log-concave without internal zeros, with `ν 1 > 0`. -/
def LogConcaveNoInternalZeros (N : ℕ) (ν : ℕ → ℝ) : Prop :=
  0 < ν 1 ∧
  (∀ k, 1 ≤ k → k ≤ N → 0 ≤ ν k) ∧
  (∀ k, 2 ≤ k → k + 1 ≤ N → ν (k - 1) * ν (k + 1) ≤ ν k ^ 2) ∧
  (∀ k, 1 ≤ k → k < N → ν k = 0 → ν (k + 1) = 0)

-- Szkraw/VRAffineMain.lean
/-- Hypotheses of Theorem 8.9: `c_i = (r + κ i / N) d_i` with `0 < r ≤ 1` and `κ ≥ 0`, the diagonal
coefficients `b_0 ≤ b_1 ≤ ⋯ ≤ b_N` nondecreasing, and a profile `d = b + c` whose Newton coefficients
are log-concave without internal zeros. -/
def AffineRatioHyp {N : ℕ} (vv : Coefficients N) : Prop :=
  ∃ r κ : ℝ, 0 < r ∧ r ≤ 1 ∧ 0 ≤ κ ∧ (∀ i, i < N → vv.b i ≤ vv.b (i + 1)) ∧
    (∀ i, i ≤ N → vv.c i = (r + κ * i / N) * profile vv i) ∧
    LogConcaveNoInternalZeros N (newtonCoeff (profile vv))

-- Szkraw/VRAffineMain.lean
/-- **Theorem 8.9, the condition on `κ`**: `b` is nondecreasing exactly when
`κ (N + d_{N-1}/(1 - d_{N-1})) ≤ N(1-r)`. -/
theorem affine_bmono_iff {N : ℕ} (vv : Coefficients N) (hv : Admissible vv) {r κ : ℝ} (hr : 0 < r)
    (hκ : 0 ≤ κ) (hc : ∀ i, i ≤ N → vv.c i = (r + κ * i / N) * profile vv i)
    (hlc : LogConcaveNoInternalZeros N (newtonCoeff (profile vv))) :
    (∀ i, i < N → vv.b i ≤ vv.b (i + 1)) ↔
      κ * (N + profile vv (N - 1) / (1 - profile vv (N - 1))) ≤ N * (1 - r)

-- Szkraw/VRQuadMain.lean
/-- Hypotheses of Theorem 8.11: `c_i = (r + t i + τ C(i,2)) d_i` with `r > 0` and `t, τ ≥ 0`, the
diagonal coefficients `b_0 ≤ b_1 ≤ ⋯ ≤ b_N` nondecreasing, and a profile `d = b + c` whose Newton
coefficients are log-concave without internal zeros. -/
def QuadRatioHyp {N : ℕ} (vv : Coefficients N) : Prop :=
  ∃ r t τ : ℝ, 0 < r ∧ 0 ≤ t ∧ 0 ≤ τ ∧ (∀ i, i < N → vv.b i ≤ vv.b (i + 1)) ∧
    (∀ i, i ≤ N → vv.c i = (r + t * i + τ * (i.choose 2 : ℝ)) * profile vv i) ∧
    LogConcaveNoInternalZeros N (newtonCoeff (profile vv))

```

### Remarks after Theorem 8.9
```lean
-- Szkraw/VRAffineRemarks.lean
/-- The profile data of an admissible array with log-concave Newton coefficients: `d_{N-1} ≤ (N-1)/N`,
with equality only for the linear profile. -/
theorem profile_last_le {N : ℕ} (vv : Coefficients N) (hv : Admissible vv)
    (hlc : LogConcaveNoInternalZeros N (newtonCoeff (profile vv))) :
    profile vv (N - 1) ≤ ((N : ℝ) - 1) / N ∧
      (profile vv (N - 1) = ((N : ℝ) - 1) / N → ∀ i, i ≤ N → profile vv i = (i : ℝ) / N)

-- Szkraw/VRAffineRemarks.lean
/-- **The remarks after Theorem 8.9.** For an admissible array whose profile has Newton coefficients
log-concave without internal zeros, with `R = d_{N-1}/(1 - d_{N-1})`:
for the linear profile the condition `κ(N+R) ≤ N(1-r)` reads `κ ≤ N(1-r)/(2N-1)`; for every profile,
every `κ ∈ [0, N(1-r)/(2N-1)]` satisfies it (for `r ≤ 1`); and for `r < 1` and a nonlinear profile,
`κ = N(1-r)/(N+R)` satisfies it although `κ > N(1-r)/(2N-1)`. -/
theorem affine_range_remarks {N : ℕ} (vv : Coefficients N) (hv : Admissible vv)
    (hlc : LogConcaveNoInternalZeros N (newtonCoeff (profile vv))) (r : ℝ) :
    ((∀ i, i ≤ N → profile vv i = (i : ℝ) / N) → ∀ κ : ℝ,
        (κ * (N + profile vv (N - 1) / (1 - profile vv (N - 1))) ≤ N * (1 - r) ↔
          κ ≤ N * (1 - r) / (2 * N - 1))) ∧
      (r ≤ 1 → ∀ κ : ℝ, 0 ≤ κ → κ ≤ N * (1 - r) / (2 * N - 1) →
        κ * (N + profile vv (N - 1) / (1 - profile vv (N - 1))) ≤ N * (1 - r)) ∧
      (r < 1 → (∃ i, i ≤ N ∧ profile vv i ≠ (i : ℝ) / N) →
        N * (1 - r) / (2 * N - 1) < N * (1 - r) / (N + profile vv (N - 1) / (1 - profile vv (N - 1))) ∧
        N * (1 - r) / (N + profile vv (N - 1) / (1 - profile vv (N - 1))) *
          (N + profile vv (N - 1) / (1 - profile vv (N - 1))) ≤ N * (1 - r))

-- Szkraw/VRAffineRemarks.lean
/-- The example after Theorem 8.9: `N = 4`, `d_i = (2^i-1)/15`, `r = 1/2`, `κ = 2/5`. -/
noncomputable def affEx : Coefficients 4 where
  a i := 1 - ((2 : ℝ) ^ i - 1) / 15
  b i := (1 - (1 / 2 + 2 / 5 * i / 4)) * (((2 : ℝ) ^ i - 1) / 15)
  c i := (1 / 2 + 2 / 5 * i / 4) * (((2 : ℝ) ^ i - 1) / 15)

-- Szkraw/VRAffineRemarks.lean
/-- **The example after Theorem 8.9**: the array is admitted by Theorem 8.9 (so it has nonnegative
linearization), `b = (0, 2/75, 3/50, 7/75, 1/10)`, and `(2N-1)κ/N = 7/10 > 1 - r`. -/
theorem affEx_remark :
    Admissible affEx ∧ AffineRatioHyp affEx ∧ MatrixPositivity affEx ∧
      affEx.b 0 = 0 ∧ affEx.b 1 = 2 / 75 ∧ affEx.b 2 = 3 / 50 ∧ affEx.b 3 = 7 / 75 ∧ affEx.b 4 = 1 / 10 ∧
      (2 * 4 - 1) * (2 / 5 : ℝ) / 4 = 7 / 10 ∧ (1 - 1 / 2 : ℝ) < 7 / 10

```

### Remarks on Theorem 8.11
```lean
-- Szkraw/VRQuadExample.lean
/-- The array of the remark after Theorem 8.11: `d_i = i/4`, `ρ(x) = 1/2 + C(x,2)/40`. -/
noncomputable def quadExample : Coefficients 4 where
  a i := 1 - (i : ℝ) / 4
  b i := (1 - (1 / 2 + (i.choose 2 : ℝ) / 40)) * ((i : ℝ) / 4)
  c i := (1 / 2 + (i.choose 2 : ℝ) / 40) * ((i : ℝ) / 4)

-- Szkraw/VRQuadExample.lean
/-- **The example after Theorem 8.11**: the array satisfies Theorem 8.11 and has nonnegative
linearization, while the Newton coefficients of `c` are `(1/8, 1/80, 3/160, 0)`, not log-concave. -/
theorem quadExample_remark :
    Admissible quadExample ∧ QuadRatioHyp quadExample ∧ MatrixPositivity quadExample ∧
      newtonCoeff quadExample.c 1 = 1 / 8 ∧ newtonCoeff quadExample.c 2 = 1 / 80 ∧
      newtonCoeff quadExample.c 3 = 3 / 160 ∧ newtonCoeff quadExample.c 4 = 0 ∧
      ¬ LogConcaveNoInternalZeros 4 (newtonCoeff quadExample.c)

-- Szkraw/QuadBUnitFails.lean
/-- The profile `d_i = (2^i - 1)/(2^20 - 1)`. -/
noncomputable def dPow (i : ℕ) : ℝ := ((2 : ℝ) ^ i - 1) / (2 ^ 20 - 1)

-- Szkraw/QuadBUnitFails.lean
/-- The ratio `ρ(i) = 1/2 + C(i,2)/1000`. -/
noncomputable def rhoPow (i : ℕ) : ℝ := 1 / 2 + (i.choose 2 : ℝ) / 1000

-- Szkraw/QuadBUnitFails.lean
noncomputable def quadBEx : Coefficients 20 where
  a i := 1 - dPow i
  b i := (1 - rhoPow i) * dPow i
  c i := rhoPow i * dPow i

-- Szkraw/QuadBUnitFails.lean
/-- **The unit-constant form of eq. `quad-B` fails** for an array satisfying Theorem 8.11:
`φ₂(16) φ₂(17) < c₁₇ φ₄(16)`. -/
theorem quadB_unit_fails :
    Admissible quadBEx ∧ QuadRatioHyp quadBEx ∧
      (fwdDiff 1)^[2] quadBEx.c 16 * (fwdDiff 1)^[2] quadBEx.c 17 < quadBEx.c 17 * (fwdDiff 1)^[4] quadBEx.c 16

```

### Open problems
```lean
-- Szkraw/OpenExamples.lean
/-- `d = (0,25,55,91)/91`, `c = (0,24,54,90)/91`, `b = (0,1,1,1)/91`. -/
noncomputable def openEx1 : Coefficients 3 where
  a i := if i = 0 then 1 else if i = 1 then 66 / 91 else if i = 2 then 36 / 91 else 0
  b i := if i = 0 then 0 else 1 / 91
  c i := if i = 0 then 0 else if i = 1 then 24 / 91 else if i = 2 then 54 / 91 else 90 / 91

-- Szkraw/OpenExamples.lean
/-- `d_i = i/3`, `c_i = ρ_i d_i` with `ρ = (1/2, 3/4, 5/6)`, `b_i = 1/6` for `i ≥ 1`. -/
noncomputable def openEx2 : Coefficients 3 where
  a i := 1 - (i : ℝ) / 3
  b i := if i = 0 then 0 else 1 / 6
  c i := if i = 0 then 0 else if i = 1 then 1 / 6 else if i = 2 then 1 / 2 else 5 / 6

-- Szkraw/OpenExamples.lean
/-- **First counterexample in the open problems**: log-concave Newton coefficients of `d` and of `c`
and nondecreasing `b` do not imply nonnegative linearization. -/
theorem openEx1_fails :
    Admissible openEx1 ∧ LogConcaveNoInternalZeros 3 (newtonCoeff (profile openEx1)) ∧
      LogConcaveNoInternalZeros 3 (newtonCoeff openEx1.c) ∧ (∀ i, i < 3 → openEx1.b i ≤ openEx1.b (i + 1)) ∧
      productMatrix openEx1 3 3 3 = -3 / 2002 ∧ ¬ MatrixPositivity openEx1

-- Szkraw/OpenExamples.lean
/-- **Second counterexample in the open problems**: the linear profile `d_i = i/3` with the concave
increasing ratio `ρ = (1/2, 3/4, 5/6)` has `b_i = 1/6` for `i ≥ 1` and `g(3,3;3) = -1/24`. -/
theorem openEx2_fails :
    Admissible openEx2 ∧ (∀ i, i ≤ 3 → profile openEx2 i = (i : ℝ) / 3) ∧
      openEx2.c 1 = 1 / 2 * profile openEx2 1 ∧ openEx2.c 2 = 3 / 4 * profile openEx2 2 ∧
      openEx2.c 3 = 5 / 6 * profile openEx2 3 ∧ (∀ i, 1 ≤ i → i ≤ 3 → openEx2.b i = 1 / 6) ∧
      productMatrix openEx2 3 3 3 = -1 / 24 ∧ ¬ MatrixPositivity openEx2

```

