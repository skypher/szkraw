# Lean statement fidelity, round 21: the extension of Theorem 8.17 to rσ ≤ (7/4) tτ

Repository: github.com/skypher/szkraw, commit 7086f41, file lean/Szkraw/CubicMain.lean. Axiom audit: lean/axioms.log (only propext, Classical.choice, Quot.sound; `Szkraw.cubic_ratio74_matrix` is its last line).

As in earlier rounds, **do not check proofs**. Check whether the Lean statement says what the paper says (Lean hypotheses equivalent or weaker, conclusions equivalent or stronger), and whether the proposed text changes are accurate. Conventions as in rounds 1–20 (`Coefficients`, `Admissible` = (2.1), `MatrixPositivity`, `profile vv i = b_i + c_i`, `newtonCoeff`, `LogConcaveNoInternalZeros`). Round 19 accepted `Szkraw.cubic_ratio_matrix : Stmt_cubic_ratio` for Theorem 8.17 with rσ ≤ tτ (P2 Theorem 5.6).

## Paper statements

P2 Theorem 5.6 (= paper.tex Theorem 8.17):

\begin{theorem}[Cubic ratio]\label{thm:lc-cubic}
Let $0=d_0<d_1<\cdots<d_N=1$ have Newton coefficients that are log-concave without internal zeros, and let $\rho(x)=r+tx+\tau\binom x2+\sigma\binom x3$ with $r>0$, $t,\tau,\sigma\geq0$ and $r\sigma\leq t\tau$. Put $a_i=1-d_i$, $b_i=(1-\rho(i))d_i$ and $c_i=\rho(i)d_i$. If $b$ is nondecreasing, then the system has nonnegative linearization.
\end{theorem}

P2, remark after the proof of Theorem 5.6 (its last sentences give the extension):

The condition $r\sigma\leq t\tau$ enters only through \eqref{eq:cubic-B} and \eqref{eq:cubic-E}, each time through $\kappa_{t\tau}+\kappa_{r\sigma}\geq0$. On geometric profiles at $(\ell,n)=(0,3)$ one has $\kappa_{r\sigma}=-20q(4q^3+11q^2+9q+1)$ and $\kappa_{t\tau}=20(q+1)(8q^3+33q^2+30q+6)$ in \eqref{eq:cubic-B}, so $\kappa_{t\tau}/|\kappa_{r\sigma}|\to2$ as $q\to\infty$. This geometric family therefore obstructs the coefficientwise test for $r\sigma\leq u\,t\tau$ with $u>2$; it does not establish a cutoff at $u=1$. In fact \eqref{eq:cubic-B} and \eqref{eq:cubic-E} also hold with $\kappa_{t\tau}+\frac74\kappa_{r\sigma}\geq0$ in place of $\kappa_{t\tau}+\kappa_{r\sigma}\geq0$; the other coefficients and the key inequality do not involve the condition. For \eqref{eq:cubic-E}, and for \eqref{eq:cubic-B} with $n\geq6$, the tail sums above stay nonnegative. For \eqref{eq:cubic-B} with $n\leq5$ the transfers alone do not suffice. There the modified coefficient $\kappa_{t\tau}+\frac74\kappa_{r\sigma}$ is certified after the substitution $u_0=zu_1$, $0\leq z\leq\min(\ell,1/q)$ with $q=u_2/u_1$, in the regimes $z=0$, $z=\ell$ and $z=1/q$ (\path{runs/cubic/bdetour_u.py}, \path{runs/cubic/edetour_u.py}). The relevant expressions are affine in $z$, so these boundary regimes cover the admissible interval for $q>0$. When $q=0$, all $u_k$ with $k\geq2$ vanish, and the inequality follows directly. For \eqref{eq:cubic-corner}, with $u_0=0$, the modified tail sums are also nonnegative. Here \path{runs/cubic/bdetour_u.py} supplies the small-$n$ $B$ certificate; \path{runs/cubic/edetour_u.py} separately certifies $E$. Hence Theorem~\ref{thm:lc-cubic} holds with $r\sigma\leq\frac74t\tau$ in place of $r\sigma\leq t\tau$. With $\frac95$ the certificate of \path{runs/cubic/bdetour_u.py} fails. Exact diagnostics for this proof are listed in \path{papers/DIAGNOSTICS.md}.

The claim to check: Theorem 5.6 holds with rσ ≤ (7/4) tτ in place of rσ ≤ tτ.

## Lean declarations

```lean
/-- Hypotheses of Theorem 8.17: `c_i = (r + t i + τ C(i,2) + σ C(i,3)) d_i` with `r > 0`,
`t, τ, σ ≥ 0` and `r σ ≤ t τ`, the diagonal coefficients `b_0 ≤ b_1 ≤ ⋯ ≤ b_N` nondecreasing, and a
profile `d = b + c` whose Newton coefficients are log-concave without internal zeros. -/
def CubicRatioHyp {N : ℕ} (vv : Coefficients N) : Prop :=
  ∃ r t τ σ : ℝ, 0 < r ∧ 0 ≤ t ∧ 0 ≤ τ ∧ 0 ≤ σ ∧ r * σ ≤ t * τ ∧
    (∀ i, i < N → vv.b i ≤ vv.b (i + 1)) ∧
    (∀ i, i ≤ N → vv.c i = (r + t * i + τ * (i.choose 2 : ℝ) + σ * (i.choose 3 : ℝ)) * profile vv i) ∧
    LogConcaveNoInternalZeros N (newtonCoeff (profile vv))

/-- Theorem 8.17 (cubic ratio), matrix-positivity conclusion. -/
def Stmt_cubic_ratio : Prop :=
  ∀ (N : ℕ) (vv : Coefficients N), Admissible vv → CubicRatioHyp vv → MatrixPositivity vv

/-- Theorem 8.17 with the extension `r σ ≤ (7/4) t τ` (remark after its proof). -/
def CubicRatioHyp74 {N : ℕ} (vv : Coefficients N) : Prop :=
  ∃ r t τ σ : ℝ, 0 < r ∧ 0 ≤ t ∧ 0 ≤ τ ∧ 0 ≤ σ ∧ r * σ ≤ 7 / 4 * (t * τ) ∧
    (∀ i, i < N → vv.b i ≤ vv.b (i + 1)) ∧
    (∀ i, i ≤ N → vv.c i = (r + t * i + τ * (i.choose 2 : ℝ) + σ * (i.choose 3 : ℝ)) * profile vv i) ∧
    LogConcaveNoInternalZeros N (newtonCoeff (profile vv))

/-- Theorem 8.17, extended form (`r σ ≤ (7/4) t τ`), matrix-positivity conclusion. -/
def Stmt_cubic_ratio74 : Prop :=
  ∀ (N : ℕ) (vv : Coefficients N), Admissible vv → CubicRatioHyp74 vv → MatrixPositivity vv

/-- **Theorem 8.17, extended** to `r σ ≤ (7/4) t τ` (remark after the proof). -/
theorem cubic_ratio74_matrix : Stmt_cubic_ratio74 := …

/-- **Theorem 8.17** (cubic ratio, `r σ ≤ t τ`), from the extended form. -/
theorem cubic_ratio_matrix : Stmt_cubic_ratio := by
  intro N vv hv hyp
  obtain ⟨r, t, τ, σ, hr, ht, hτ, hσ, hrs, hb, hc, hlc⟩ := hyp
  exact cubic_ratio74_matrix N vv hv ⟨r, t, τ, σ, hr, ht, hτ, hσ, by nlinarith [mul_nonneg ht hτ], hb, hc, hlc⟩
```

`cubic_ratio_matrix` (Theorem 5.6 itself, accepted in round 19) is now derived from `cubic_ratio74_matrix`, since rσ ≤ tτ implies rσ ≤ (7/4) tτ for t, τ ≥ 0.

## Proposed changes (applied only after this round passes)

1. P2 Lean table: after the row `Theorem~\ref{thm:lc-cubic}: cubic ratio & \path{Szkraw.cubic_ratio_matrix}` add the row `Remark after the proof of Theorem~\ref{thm:lc-cubic}: extension to $r\sigma\leq\frac74t\tau$ & \path{Szkraw.cubic_ratio74_matrix}`.
2. P2 introduction: "The key inequalities of Theorems 5.5 and 5.6 are proved with exact computer certificates, and both theorems are also machine-verified" becomes "…, and both theorems, together with the extension of Theorem 5.6 to $r\sigma\leq\frac74t\tau$, are also machine-verified".
3. P2 disclosure: "Theorems 5.5 and 5.6 are machine-verified; the extension to $r\sigma\leq\frac74t\tau$ in the remark after the proof of Theorem 5.6 is not." becomes "Theorems 5.5 and 5.6 and the extension to $r\sigma\leq\frac74t\tau$ in the remark after the proof of Theorem 5.6 are machine-verified."
4. P2 remark after the proof of Theorem 5.6: after "Hence Theorem 5.6 holds with $r\sigma\leq\frac74t\tau$ in place of $r\sigma\leq t\tau$." insert: "This extension is machine-verified (\path{Szkraw.cubic_ratio74_matrix}). For \eqref{eq:cubic-B} with $n\leq5$ the Lean proof does not substitute $u_0=zu_1$: it writes the modified coefficient, times a positive polynomial in $\ell$, as a combination of transfers, products $u_au_b$ and the terms $u_j(\ell u_1-u_0)\geq0$ with multipliers that are polynomials in $\ell$ with nonnegative coefficients after a shift of $\ell$, plus exact rational certificates at the few smaller values of $\ell$ (\path{runs/lean_plan/cert74.py}, \path{runs/lean_plan/gen_cubicB.py})."
5. papers/FORMALIZATION.md: new table row `| Theorem 8.17, remark after the proof: extension to $r\sigma\leq\frac74t\tau$ | \`Szkraw.cubic_ratio74_matrix\` | P2 5.6 |` after the Theorem 8.17 row; the notes sentence "The extension to $r\sigma\leq\frac74t\tau$ in the remark after the proof is not formalized." becomes "The extension to $r\sigma\leq\frac74t\tau$ in the remark after the proof is \path{Szkraw.cubic_ratio74_matrix}, with the same hypotheses except $r\sigma\leq\frac74t\tau$; \path{Szkraw.cubic_ratio_matrix} is derived from it. For \eqref{eq:cubic-B} with $n\leq5$ its certificates also use the terms $u_j(\ell u_1-u_0)\geq0$, with multipliers polynomial in $\ell$ (\path{runs/lean_plan/cert74.py})."

Please answer per item: MATCH / MISMATCH with reasons, then an overall verdict (PASS / PASS WITH MINOR FIXES / FAIL), with exact replacement text for any fix.
