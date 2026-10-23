# Lean statement fidelity, round 18: Theorem 8.16 (log-concave ratio)

Repository: github.com/skypher/szkraw, commit 148cca3. Statement and assembly: lean/Szkraw/GenMain.lean; final theorem `Szkraw.lc_general` in lean/Szkraw/GenMM1S20.lean. Axiom audit: lean/axioms.log (every listed declaration, including `lc_general`, depends only on propext, Classical.choice, Quot.sound).

As in rounds 1–17, **do not check proofs**; Lean checks them. Check only whether the Lean statement says what the paper's Theorem 8.16 (= Theorem 5.5 of the split paper P2) says, under the acceptance rule: Lean hypotheses equivalent to or weaker than the paper's, Lean conclusion equivalent to or stronger. Also check the proposed table row, notes sentence and disclosure changes at the end. They will be applied only after this round passes.

Conventions (unchanged, accepted in earlier rounds for Theorems 8.1, 8.9 and 8.11 and Proposition 8.14):
- `Coefficients N` has fields a, b, c : ℕ → ℝ.
- `Admissible v` is the paper's (2.1): stochastic for i ≤ N, a_0 = 1, b_0 = c_0 = 0, a_N = 0, a_i > 0 for i < N, c_i > 0 for 1 ≤ i ≤ N.
- `MatrixPositivity v` is nonnegative linearization.
- `profile v i = v.b i + v.c i`.
- `newtonCoeff x k = Σ_i (−1)^(k−i) C(k,i) x_i`.
- `LogConcaveNoInternalZeros N ν` is the paper's "(ν_k)_{1≤k≤N} log-concave without internal zeros" (round 1).
- `LCNZ u`: nonnegative, u_i u_{i+2} ≤ u_{i+1}², positive entries form an interval (round 17).

Points to check:
1. The ratio. Lean encodes c_i = ρ(i) d_i for i ≤ N as `vv.c i = dd ρc i * profile vv i`, where `dd ρc i = Σ_{k≤i} C(i,k) ρc_k` (`dd_eq_nval`). Does this match ρ(x) = Σ_k ρ_k C(x,k) at x = i?
2. "(ρ_k)_{k≥0} nonnegative and log-concave without internal zeros, ρ_0 > 0" is encoded as `LCNZ ρc ∧ 0 < ρc 0`. Is this a match?
3. The data. The paper takes 0 = d_0 < d_1 < … < d_N = 1 and puts a_i = 1 − d_i, b_i = (1 − ρ(i)) d_i, c_i = ρ(i) d_i. Lean takes any array satisfying (2.1) whose profile d = b + c has Newton coefficients log-concave without internal zeros, with the ratio relation and b nondecreasing (`∀ i < N, b i ≤ b (i+1)`). This is the encoding accepted for Theorems 8.9 and 8.11.
   - Every paper instance satisfies (2.1): a_i > 0 for i < N, a_N = 0, and c_i = ρ(i) d_i > 0 for i ≥ 1, since ρ(i) ≥ ρ_0 > 0.
   - Lean does not assume that d is strictly increasing. That only weakens the hypothesis.
   Is anything narrowed?
4. Conclusion: `MatrixPositivity vv`. Is this a match?
5. Are the proposed table row, notes sentence and disclosure changes below accurate?

Answer format: MATCH / MISMATCH per item with reason, exact fixes, overall verdict (PASS / PASS WITH MINOR FIXES / FAIL). Terse.

## Paper statement (paper.tex, Theorem 8.16; P2 Theorem 5.5)

Section 8 notation: ν_k = Σ_{i≤k} (−1)^{k−i} C(k,i) d_i (1 ≤ k ≤ N), d_n = Σ_{k=1}^n C(n,k) ν_k; ν_0 = 0 and ν_k = 0 for k > N. "(ν_k)_{1≤k≤N} log-concave without internal zeros": all ν_k ≥ 0, the indices with ν_k > 0 form an interval {1,…,K}, and ν_k² ≥ ν_{k−1} ν_{k+1} for 2 ≤ k ≤ N−1.

```latex
\begin{theorem}[Log-concave ratio]\label{thm:lc-general}
Let $0=d_0<d_1<\cdots<d_N=1$ have Newton coefficients that are log-concave without internal zeros. Let $\rho(x)=\sum_k\rho_k\binom xk$, where $(\rho_k)_{k\geq0}$ is nonnegative and log-concave without internal zeros and $\rho_0>0$. Put $a_i=1-d_i$, $b_i=(1-\rho(i))d_i$ and $c_i=\rho(i)d_i$. If $b$ is nondecreasing, then the system has nonnegative linearization.
\end{theorem}
```

## Lean statement

```lean
def LCNZ (u : ℕ → ℝ) : Prop :=
  (∀ i, 0 ≤ u i) ∧ (∀ i, u i * u (i + 2) ≤ u (i + 1) ^ 2) ∧
  (∀ i j k, i ≤ j → j ≤ k → 0 < u i → 0 < u k → 0 < u j)

-- iterated shift sums: iterShift u 0 = u, iterShift u (n+1) = shiftSum (iterShift u n), shiftSum v i = v i + v (i+1)
noncomputable def dd (u : ℕ → ℝ) (ℓ : ℕ) : ℝ := Szkraw.iterShift u ℓ 0
def nval (ρ : ℕ → ℝ) (x : ℕ) : ℝ := ∑ i ∈ range (x + 1), (x.choose i : ℝ) * ρ i
theorem dd_eq_nval (u : ℕ → ℝ) (n : ℕ) : dd u n = nval u n

/-- The hypotheses of Theorem 8.16 (matrix form): `c_i = ρ(i) d_i`, `ρ(x) = Σ_k ρ_k C(x,k)`, with
`(ρ_k)` nonnegative, log-concave without internal zeros and `ρ_0 > 0`; `d` has log-concave Newton
coefficients; `b` is nondecreasing on `0..N`. -/
def GenRatioHyp {N : ℕ} (vv : Coefficients N) : Prop :=
  ∃ ρc : ℕ → ℝ, LCNZ ρc ∧ 0 < ρc 0 ∧ (∀ i, i < N → vv.b i ≤ vv.b (i + 1)) ∧
    (∀ i, i ≤ N → vv.c i = dd ρc i * profile vv i) ∧
    LogConcaveNoInternalZeros N (newtonCoeff (profile vv))

/-- Theorem 8.16 (log-concave ratio), matrix-positivity conclusion. -/
def Stmt_lc_general : Prop :=
  ∀ (N : ℕ) (vv : Coefficients N), Admissible vv → GenRatioHyp vv → MatrixPositivity vv

/-- **Theorem 8.16**, unconditional. -/
theorem lc_general : Stmt_lc_general
```

## Proposed changes (applied only after this round passes)

In papers/p2.tex (the split paper; its Lean table uses its own numbering via \ref):
1. New row in the Lean table, after the row for Lemma~\ref{lem:abel-weights}:
   `Theorem~\ref{thm:lc-general}: log-concave ratio & \path{Szkraw.lc_general}\\[3pt]`
2. Delete the sentence after the table: "The Lean proof of Theorem~\ref{thm:lc-general} is in progress: its assembly from the key inequality \eqref{eq:G-key} is formalized, the key inequality is not."
3. Introduction: "The key inequalities of Theorems~\ref{thm:lc-general} and~\ref{thm:lc-cubic} are proved with exact computer certificates; the other results have written proofs." becomes "The key inequalities of Theorems~\ref{thm:lc-general} and~\ref{thm:lc-cubic} are proved with exact computer certificates, and Theorem~\ref{thm:lc-general} is also machine-verified; the other results have written proofs."
4. AI-use disclosure: "Theorems~\ref{thm:lc-general} and~\ref{thm:lc-cubic} are not machine-verified." becomes "Theorem~\ref{thm:lc-general} is machine-verified; Theorem~\ref{thm:lc-cubic} is not."

In papers/FORMALIZATION.md (numbering of paper.tex):
5. New row in the Lean declaration table: `| Theorem 8.16: log-concave ratio | Szkraw.lc_general | P2 5.5 |`
6. New notes sentence after the one on Proposition 8.14: "Theorem~8.16 is stated for arrays satisfying \eqref{eq:basic} whose profile $d_i=b_i+c_i$ has Newton coefficients log-concave without internal zeros, with $c_i=\rho(i)(b_i+c_i)$ for $i\leq N$, where $\rho(i)=\sum_{k\leq i}\binom ik\rho_k$ with $(\rho_k)_{k\geq0}$ satisfying \path{Szkraw.LCNZ} and $\rho_0>0$, and with $b_0\leq b_1\leq\cdots\leq b_N$; the array-based encoding is that of Theorem~8.1. Its proof formalizes steps (i)--(v) of the written proof: the reduction to the matrix $M_{k,m}$, the coefficients $l_k$, and the central sums. For step (vi) it does not use the weight sums of Lemma~8.15. Instead it bounds each quadratic form below by $u_1\sum_ne_nu_n$ with explicit $e_n\geq0$, using $u_iu_j\geq u_1u_{i+j-1}$ for $i,j\geq1$ and $u_0u_{n+1}\leq u_1u_n$; the generic coefficients are certified in closed form for all $n\geq4$. For step (vii), the sums $M_{1,m}+M_{m,1}$ ($3\leq a\leq5$) and $S_{2,0}$ ($a\in\{3,4\}$) are exact rational combinations of $u_k(u_{i+1}u_{j-1}-u_iu_j)$ and monomials (\path{runs/lean_plan/window_cert.py})."
