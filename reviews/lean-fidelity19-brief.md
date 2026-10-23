# Lean statement fidelity, round 19: Theorem 8.17 (cubic ratio)

Repository: github.com/skypher/szkraw, commit f8a0e44. Statement and assembly: lean/Szkraw/CubicMain.lean (`CubicRatioHyp`, `Stmt_cubic_ratio`, `cubic_ratio_matrix`). Axiom audit: lean/axioms.log (`cubic_ratio_matrix` depends only on propext, Classical.choice, Quot.sound).

As in rounds 1–18, **do not check proofs**; Lean checks them. Check only whether the Lean statement says what the paper's Theorem 8.17 (= Theorem 5.6 of P2) says, under the acceptance rule: Lean hypotheses equivalent to or weaker than the paper's, Lean conclusion equivalent to or stronger. Also check the proposed text changes at the end. They will be applied only after this round passes.

Conventions are unchanged from round 14 (Theorem 8.11, `QuadRatioHyp`, accepted): `Coefficients`, `Admissible` (= (2.1)), `MatrixPositivity` (= nonnegative linearization), `profile v i = b_i + c_i`, `newtonCoeff`, `LogConcaveNoInternalZeros`.

Points to check:
1. Is the ratio encoded correctly? Lean writes c_i = (r + t i + τ C(i,2) + σ C(i,3)) (b_i + c_i) for i ≤ N, with 0 < r, 0 ≤ t, τ, σ and r σ ≤ t τ.
2. Are the data and monotonicity hypotheses encoded as for Theorem 8.11 (array encoding, b nondecreasing via adjacent inequalities, Newton log-concavity of the profile)? Is anything narrowed?
3. Is the conclusion `MatrixPositivity vv` correct?
4. The remark after the proof of Theorem 8.17 extends the theorem to r σ ≤ (7/4) t τ. The Lean statement covers only r σ ≤ t τ, the theorem as stated. Is the proposed disclosure of this accurate?
5. Are the proposed table rows, notes sentence and disclosure changes accurate?

Answer format: MATCH / MISMATCH per item with reason, exact fixes, overall verdict (PASS / PASS WITH MINOR FIXES / FAIL). Terse.

## Paper statement (paper.tex, Theorem 8.17; P2 Theorem 5.6)

```latex
\begin{theorem}[Cubic ratio]\label{thm:lc-cubic}
Let $0=d_0<d_1<\cdots<d_N=1$ have Newton coefficients that are log-concave without internal zeros, and let $\rho(x)=r+tx+\tau\binom x2+\sigma\binom x3$ with $r>0$, $t,\tau,\sigma\geq0$ and $r\sigma\leq t\tau$. Put $a_i=1-d_i$, $b_i=(1-\rho(i))d_i$ and $c_i=\rho(i)d_i$. If $b$ is nondecreasing, then the system has nonnegative linearization.
\end{theorem}
```
Remark after the proof (excerpt): "Hence Theorem~\ref{thm:lc-cubic} holds with $r\sigma\leq\frac74t\tau$ in place of $r\sigma\leq t\tau$."

## Lean statement

```lean
/-- Theorem 8.17 hypotheses (matrix form). -/
def CubicRatioHyp {N : ℕ} (vv : Coefficients N) : Prop :=
  ∃ r t τ σ : ℝ, 0 < r ∧ 0 ≤ t ∧ 0 ≤ τ ∧ 0 ≤ σ ∧ r * σ ≤ t * τ ∧
    (∀ i, i < N → vv.b i ≤ vv.b (i + 1)) ∧
    (∀ i, i ≤ N → vv.c i = (r + t * i + τ * (i.choose 2 : ℝ) + σ * (i.choose 3 : ℝ)) * profile vv i) ∧
    LogConcaveNoInternalZeros N (newtonCoeff (profile vv))

/-- Theorem 8.17 (cubic ratio), matrix-positivity conclusion. -/
def Stmt_cubic_ratio : Prop :=
  ∀ (N : ℕ) (vv : Coefficients N), Admissible vv → CubicRatioHyp vv → MatrixPositivity vv

theorem cubic_ratio_matrix : Stmt_cubic_ratio
```
For comparison, the accepted Theorem 8.11 hypothesis:
```lean
def QuadRatioHyp {N : ℕ} (vv : Coefficients N) : Prop :=
  ∃ r t τ : ℝ, 0 < r ∧ 0 ≤ t ∧ 0 ≤ τ ∧ (∀ i, i < N → vv.b i ≤ vv.b (i + 1)) ∧
    (∀ i, i ≤ N → vv.c i = (r + t * i + τ * (i.choose 2 : ℝ)) * profile vv i) ∧
    LogConcaveNoInternalZeros N (newtonCoeff (profile vv))
```

## Proposed changes (applied only after this round passes)

In papers/p2.tex:
1. New row in the Lean table, after the row for Theorem~\ref{thm:lc-general}:
   `Theorem~\ref{thm:lc-cubic}: cubic ratio & \path{Szkraw.cubic_ratio_matrix}\\[3pt]`
2. Introduction: "..., and Theorem~\ref{thm:lc-general} is also machine-verified; the other results have written proofs." becomes "..., and both theorems are also machine-verified; the other results have written proofs."
3. AI-use disclosure: "Theorem~\ref{thm:lc-general} is machine-verified; Theorem~\ref{thm:lc-cubic} is not." becomes "Theorems~\ref{thm:lc-general} and~\ref{thm:lc-cubic} are machine-verified; the extension to $r\sigma\leq\frac74t\tau$ in the remark after the proof of Theorem~\ref{thm:lc-cubic} is not."

In papers/FORMALIZATION.md (numbering of paper.tex):
4. New row: `| Theorem 8.17: cubic ratio | Szkraw.cubic_ratio_matrix | P2 5.6 |`
5. New notes sentence after the one on Theorem 8.16: "Theorem~8.17 is stated for arrays satisfying \eqref{eq:basic} whose profile has Newton coefficients log-concave without internal zeros, with $c_i=\bigl(r+ti+\tau\binom i2+\sigma\binom i3\bigr)(b_i+c_i)$ for $i\leq N$, $r>0$, $t,\tau,\sigma\geq0$, $r\sigma\leq t\tau$ and $b_0\leq\cdots\leq b_N$, using the array-based encoding of Theorem~8.1. Its proof follows the moves and the resummation of the written proof, with $E$ in place of $W$ in the resummation of Theorem~8.11. It certifies the detour inequalities \eqref{eq:cubic-B}, \eqref{eq:cubic-corner} and \eqref{eq:cubic-E} differently. Each coefficient form in $(r,t,\tau,\sigma)$ is written as a nonnegative combination of the log-concavity transfers $u_{a+1}u_{b-1}-u_au_b$ and of monomials, and the tail sums of coefficients are polynomials in $(\ell,n)$ with nonnegative coefficients (\path{runs/lean_plan/gen_cubicB.py}, \path{runs/lean_plan/gen_cubicE.py}). The key inequality reduces, as in Theorem~8.11, to the reduced inequality of that proof for the $\sigma$-free part and to $\Phi_3^{\mathrm{loc}}\geq0$; the latter is proved with the edge bounds used for Theorem~8.16. The extension to $r\sigma\leq\frac74t\tau$ in the remark after the proof is not formalized."
