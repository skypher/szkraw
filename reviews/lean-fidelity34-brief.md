# Lean statement fidelity, round 34: the raising deformation at fixed r is not a uniform rule (P3, remark after Corollary 9.11), and the strengthened `direction_not_uniform`

Repository: github.com/skypher/szkraw, commit ee6b5a6: lean/Szkraw/RaiseDirection.lean (new), lean/Szkraw/LambdaN.lean (`direction_not_uniform` restated), lean/Szkraw/RaiseTopMass.lean and lean/Szkraw/TopMass.lean (definitions accepted for P1 Proposition `prop:raise` in earlier rounds). Axiom audit lean/axioms.log (389 lines, only propext, Classical.choice, Quot.sound).

As in earlier rounds, **do not check proofs**. Check whether each Lean statement says what the passage says, and whether the P3 table row and the shortened not-formalized paragraph are accurate. Report MATCH / MISMATCH per item with exact replacement text for any fix.

Background: round 33 (reviews/lean-fidelity33-answer.md) accepted `direction_not_uniform` for the symmetric endpoint but found that the raising remark at fixed 0<r<1 was not covered, and that the relative parameter τ (additive mass τw₀) is an N-dependent reparametrization. A later internal check noted that the round-33 statement excluded only rules that fit at **every N ≥ 1**, while Definition 9.3 admission and Theorem 9.4 use only N ≥ N₀. Both statements are now quantified over every N₀ and every nonzero rescaling s_N of the direction.

## Paper passages

P3, Definition 9.3 and Theorem 9.4:

\begin{definition}\label{def:rule}
A \emph{uniform rule} is a pair of real functions $\beta,\gamma$ on $[0,1]$. It defines, for each $N$, the direction $v_N$ with $\delta b_n=\beta(n/N)$ for $1\leq n<N$ and $\delta c_n=\gamma(n/N)$ for $1\leq n\leq N$. A set of arrays \emph{admits} the rule at the symmetric endpoint if there is $N_0$ such that for every $N\geq N_0$ there is $\varepsilon_N>0$ with $K_{N,1}+\varepsilon v_N$ in the set for all $0<\varepsilon<\varepsilon_N$. Put
\[
L_{\mathrm{even}}=\beta(0)+2\gamma(0)+\beta(1)+\gamma(1),\qquad L_{\mathrm{odd}}=\beta(0)-\beta(1)-\gamma(1).
\]
\end{definition}

\begin{theorem}[Forced equalities for uniform criteria]\label{thm:uniform}
Let $\beta,\gamma$ be polynomials. If a set of arrays with property (P) admits the rule $(\beta,\gamma)$ at the symmetric endpoint, then $L_{\mathrm{even}}=L_{\mathrm{odd}}=0$. If $L_{\mathrm{even}}=L_{\mathrm{odd}}=0$, the first-order change of $g(N,N;N)$ along $v_N$ vanishes for every $N$ above the degrees of $\beta$ and $\gamma$.
\end{theorem}
\begin{proof}
For a polynomial $p$ of degree less than $N$, $\sum_{n=0}^N(-1)^n\binom Nnp(n/N)=0$. Only boundary terms survive in Lemma~\ref{lem:corner}: the derivative equals $-s_NL_{\mathrm{even}}$ for even $N$ and $-s_NL_{\mathrm{odd}}$ for odd $N$. The sign of $s_N$ changes from $N$ to $N+2$. If, for instance, $L_{\mathrm{even}}\neq0$, then the derivative is negative for every large even $N$ in one residue class modulo $4$. For such $N$, $g(N,N;N)<0$ at $K_{N,1}+\varepsilon v_N$ for all small $\varepsilon>0$, since the coefficient vanishes at $\varepsilon=0$.
\end{proof}

P3, after Proposition 9.8 (the top-mass direction at r=1):

\dot c_n=-\frac nN\binom Nn,\qquad\dot b_n=\Bigl(\frac{2n}{N}-1\Bigr)\binom Nn.
\]
After the affine normalization restoring $R_1=x$, the top-mass direction is
\[
\delta a_n=\frac{N-n}{N}\Bigl(\binom Nn-1\Bigr),\qquad
\delta b_n=1+\Bigl(\frac{2n}{N}-1\Bigr)\binom Nn,\qquad
\delta c_n=-\frac nN\Bigl(1+\binom Nn\Bigr).
\]
Its binomial dependence on $N$ is not a uniform rule of Definition~\ref{def:rule}, consistently with Theorem~\ref{thm:uniform}.

P3, remark after Corollary `cor:radius-order` (the sentence in question is "The deformation that raises the top mass has the binomial profile of the masses and is not a uniform rule."):

For fixed $r$ the radius also decays exponentially in $N$: raising the top mass of the measure of $K_{N,r}$, the reverse of Lemma~\ref{lem:topmass}, gives $\rho_N(r)\leq3(1-r^2)^N$ whenever $(1-r^2)^N\leq\frac12$ and $3(1-r^2)^N\leq(1-r)/N$~\cite[Proposition~\ref{P1-prop:raise} and Corollary~\ref{P1-cor:radius-exp}]{P1}.

Thus, for every fixed $r\in(0,1)$, no set of arrays with property (P) contains coefficient balls of a positive radius independent of $N$ around all $K_{N,r}$; Theorem~\ref{thm:perturbation} gives the lower bound $\rho_N(r)\geq\tfrac12(\min(r,1-r)/(32N))^N$. The deformation that raises the top mass has the binomial profile of the masses and is not a uniform rule.

P1, Proposition `prop:raise` (the raising deformation; relative parameter τ, additive mass ε = τw₀):

\begin{proposition}[Raising the top mass]\label{prop:raise}
Let $N\geq1$ and $0<r<1$. The measure of $K_{N,r}$ has nodes $x_n=1-(1+r)n/N$ and masses $w_n=\binom Nnr^{N-n}/(1+r)^N$. For $\tau>0$ let $\mu^\tau$ be this measure with the mass at $x_0=1$ raised to $(1+\tau)w_0$. Then $\mu^\tau$ has
\[
g(N,N;N)=\frac{(1+\tau)^2(I-w_0)+w_0}{(1+\tau)(h-w_0)+w_0},\qquad I=\bigl(r(1-r)\bigr)^N,\quad h=r^N,
\]
which is negative exactly when $\tau>\tau_N^*=\bigl(1-(1-r^2)^N\bigr)^{-1/2}-1$. After the affine normalization $R_n(1)=1$, $R_1=x$, its recurrence coefficients differ from those of $K_{N,r}$ by at most $3\tau\max_nw_n$.
\end{proposition}
\begin{proof}
Write $\pi_n$ and $S_n=\sum_{j<n}\pi_j$ for $K_{N,r}$, and put $\varepsilon=\tau w_0$. The polynomial $(1+\varepsilon S_n)R_n-\varepsilon\sum_{j<n}\pi_jR_j$ has degree $n$ and equals $1$ at $x_0$. For $\deg p<n$, its integral against $p$ with respect to $\mu^\tau=\mu+\varepsilon\delta_{x_0}$ is $-\varepsilon p(x_0)+\varepsilon p(x_0)=0$, because $\sum_{j<n}\pi_jR_j$ reproduces $p(x_0)$. Hence it is the polynomial $R_n^\tau$ of $\mu^\tau$.

On the support, dual orthogonality gives $\sum_{j\leq N}\pi_jR_j(x)=\boldsymbol1_{x=x_0}/w_0$, and in particular $S_N+\pi_N=1/w_0$. Therefore $R_N^\tau=(1+\tau)R_N-\tau\boldsymbol1_{x_0}$ on the support. By Lemma~\ref{lem:corner-value} and $\pi_N=r^{-N}$ (Lemma~\ref{lem:finite}), $\int R_N^3\,d\mu=I$; also $\int R_N^2\,d\mu=h$. Hence

## Lean definitions (accepted earlier)

```lean
/-- The array of `K_{N,r}` in the parametrization (2.3), `p = 1/r`. -/
noncomputable abbrev kv (N : ℕ) (r : ℝ) : Coefficients N := geometricCoefficients N (1 / r) 1

/-- The nodes `x_n = 1 - (1 + r) n / N`. -/
noncomputable def kx (N : ℕ) (r : ℝ) (j : Fin (N + 1)) : ℝ := binomialNode (1 / r) N j.val

/-- The masses `w_n = C(N,n) r^{N-n} / (1+r)^N`. -/
noncomputable def kw (N : ℕ) (r : ℝ) (j : Fin (N + 1)) : ℝ := binomialMass (1 / r) N j.val

/-- The normalized array of `K_{N,r}` with the top mass raised to `(1 + τ) w_0`. -/
noncomputable def raisedKraw (N : ℕ) (r τ : ℝ) : Coefficients N :=
  epsNorm (kv N r) (kx N r) (kw N r) (τ * kw N r 0)

-- TopMass.lean (variables v : Coefficients N, x w : Fin (N+1) → ℝ)
/-- `π_n = 1/‖R_n‖²`. -/
noncomputable def piw (n : ℕ) : ℝ := (nrm v x w n)⁻¹

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

`piw (kv N r) (kx N r) (kw N r) n = C(N,n)/r^n` for n ≤ N and `kw N r 0 = (r/(1+r))^N` are proved (`k_piw`, `k_w0`); `kv N r` has `a_n = (N-n)/N`, `c_n = r n/N` (`kv_a`, `kv_c`).

## New and restated Lean statements

```lean
/-- The binomial masses `w_n = C(N,n) r^{N-n} / (1+r)^N` of `K_{N,r}`. -/
noncomputable def raiseMass (N : ℕ) (r : ℝ) (n : ℕ) : ℝ := (N.choose n : ℝ) * r ^ (N - n) / (1 + r) ^ N

/-- First-order change of the affine-normalized array `epsNorm` when the top mass changes by `τ w0`. -/
theorem epsNorm_scaled_hasDerivAt (n : ℕ) :
    HasDerivAt (fun τ => (epsNorm v x w (τ * w0)).b n)
      (w0 * (-(v.a n + v.c n) + (v.a n - v.c n) * piw v x w n)) 0 ∧
    HasDerivAt (fun τ => (epsNorm v x w (τ * w0)).c n) (w0 * v.c n * (1 + piw v x w n)) 0 := …

/-- **P3, Section 9 (raising at fixed `r`)**: for `0 < r ≤ 1` and `n ≤ N`, raising the top mass of `K_{N,r}` to
`(1 + τ) w_0` (`raisedKraw`, P1 Proposition 5.2) moves the coefficients at `τ = 0` in the direction
`δb_n = ((N-n)/N - r n/N) w_n - ((N-n)/N + r n/N) w_0`, `δc_n = (r n/N)(w_0 + w_n)`, where
`w_n = C(N,n) r^{N-n} / (1+r)^N` are the binomial masses. -/
theorem raise_direction (hN : 1 ≤ N) (hr : 0 < r) (hr1 : r ≤ 1) (n : ℕ) (hn : n ≤ N) :
    HasDerivAt (fun τ => (raisedKraw N r τ).b n)
      ((((N : ℝ) - n) / N - r * n / N) * raiseMass N r n - (((N : ℝ) - n) / N + r * n / N) * raiseMass N r 0) 0 ∧
    HasDerivAt (fun τ => (raisedKraw N r τ).c n) (r * n / N * (raiseMass N r 0 + raiseMass N r n)) 0 := …

/-- **P3, Section 9**: at every fixed `0 < r ≤ 1`, the deformation raising the top mass of `K_{N,r}` is not a
uniform rule, from any starting size `N₀` on and in any parametrization: for every `s_N ≠ 0` (`N ≥ N₀`), the
velocity of `t ↦ raisedKraw N r (s_N t)` at `t = 0` is not of the form `δb_n = β(n/N)` (`1 ≤ n < N`),
`δc_n = γ(n/N)` (`1 ≤ n ≤ N`) for all `N ≥ N₀`. This covers the relative `τ` (`s_N = 1`), the additive mass
`ε = τ w_0` (`s_N = 1/w_0`), and lowering (`s_N < 0`). The ratio `δb_n/δc_n` at `n/N = 1/N` differs between the
sizes `N` and `2N` for every `N ≥ 2`. -/
theorem raise_not_uniform (hr : 0 < r) (hr1 : r ≤ 1) (N₀ : ℕ) (s : ℕ → ℝ) (hs : ∀ N, N₀ ≤ N → s N ≠ 0) :
    ¬ ∃ β γ : ℝ → ℝ, ∀ N : ℕ, N₀ ≤ N →
      (∀ n, 1 ≤ n → n < N → HasDerivAt (fun t => (raisedKraw N r (s N * t)).b n) (β (n / N)) 0) ∧
      (∀ n, 1 ≤ n → n ≤ N → HasDerivAt (fun t => (raisedKraw N r (s N * t)).c n) (γ (n / N)) 0) := …

/-- **P3, Section 9**: the affine-normalized top-mass direction is not a uniform rule `δb_n = β(n/N)`,
`δc_n = γ(n/N)`, from any starting size `N₀` on and after any rescaling `s_N ≠ 0` (`s_N = 1` lowers the top mass,
`s_N = -1` raises it): its dependence on `N` is binomial. The ratio `δb_n/δc_n` at `n/N = 1/N` differs between the
sizes `N` and `2N` for every `N ≥ 2`. -/
theorem direction_not_uniform (N₀ : ℕ) (s : ℕ → ℝ) (hs : ∀ N, N₀ ≤ N → s N ≠ 0) :
    ¬ ∃ β γ : ℝ → ℝ, ∀ N : ℕ, N₀ ≤ N →
      (∀ n, 1 ≤ n → n < N → s N * (1 + (2 * (n : ℝ) / N - 1) * N.choose n) = β (n / N)) ∧
      (∀ n, 1 ≤ n → n ≤ N → s N * -((n : ℝ) / N * (1 + N.choose n)) = γ (n / N)) := …
```

Notes. (a) `raisedKraw N r τ` is defined for all real τ; `HasDerivAt` at τ = 0 is the two-sided derivative, which equals the one-sided velocity of the raising deformation τ > 0. (b) The statements cover 0 < r ≤ 1; the paper's remark concerns 0 < r < 1. (c) The `HasDerivAt` hypotheses in `raise_not_uniform` say that the velocity of t ↦ raisedKraw N r (s_N t) at t = 0 is the rule's v_N for every N ≥ N₀; s_N = 1 is the paper's τ, s_N = 1/w₀ the additive mass, s_N < 0 lowering.

## P3 changes at ee6b5a6

New table row:

Remark after Corollary~\ref{cor:radius-order}: the direction of the raising deformation at fixed $r$, its binomial profile, not a uniform rule & \path{Szkraw.raise_direction}, \path{Szkraw.raise_not_uniform}

Removed from the not-formalized paragraph (the round-33 sentence): "The non-uniformity assertion for the raising deformation at fixed $0<r<1$ also remains unformalized; \path{Szkraw.direction_not_uniform} establishes non-uniformity of the additive-mass lowering and raising directions at $r=1$."

Questions: (1) Does `raise_direction` state the first-order direction of the raising deformation of P1 `prop:raise` (relative τ, affine normalization R_n(1)=1, R_1=x), and is it "the binomial profile of the masses"? (2) Does `raise_not_uniform` formalize "is not a uniform rule" (Definition 9.3) for the raising deformation at fixed r, in a form strong enough for the consistency remark with Theorem 9.4 (admission only for N ≥ N₀)? (3) Does the restated `direction_not_uniform` still formalize the sentence after Proposition 9.8, now for every N₀ and every rescaling? (4) Are the table row and the shortened not-formalized paragraph accurate?

Answer per item, then an overall verdict (PASS / PASS WITH MINOR FIXES / FAIL).
