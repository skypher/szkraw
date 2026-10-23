# Lean statement fidelity, round 24: first-order derivatives along the rule β = 1, γ = 0 at r = 4/5 (P3, Section 9)

Repository: github.com/skypher/szkraw, commit e479a4e, file lean/Szkraw/PolyColumn.lean. Axiom audit: lean/axioms.log (last line `Szkraw.PolyCol.rule_deriv_4_5`, only propext, Classical.choice, Quot.sound).

As in earlier rounds, **do not check proofs**. Check whether the Lean statement says what the paper says, and whether the proposed text changes are accurate. Conventions as in rounds 1–23. Round 23 (pending) covers `rule_fails_4_5` and `rule_fails_19_20` for the first sentence of the passage below; this round covers only the last sentence.

## Paper passage (P3, Section 9, computations away from r = 1)

\item For the rule $\beta=1$, $\gamma=0$, exact computation shows that property (P) fails at $r=4/5$, with perturbation size $1/100$, for every $N=6,\ldots,14$, and at $r=19/20$, with perturbation size $1/1000$, for every $N=4,\ldots,14$. The period-four sign pattern at $r=1$ does not persist in general for $r<1$: at $r=4/5$ the first-order derivatives are $512/1875$ for $N=4$ and $-71936/5859375$ for $N=8$.

The rule (β, γ) defines the direction v_N with δb_n = β(n/N) for 1 ≤ n < N and δc_n = γ(n/N) for 1 ≤ n ≤ N (P3, Definition 9.3); the arrays K_{N,r} + ε v_N are `krawDir N δb δc r ε` (accepted in rounds 6–10 for r = 1 and in round 23 for r < 1):

```lean
def stochArray (N : ℕ) (b c : ℕ → ℝ) : Coefficients N where
  a i := if i = 0 then 1 else if i = N then 0 else 1 - b i - c i
  b i := if i = 0 then 0 else if i = N then 1 - c N else b i
  c i := if i = 0 then 0 else c i

/-- `K_{N,r} + ε v` for the direction `v = (δb, δc)` in the coordinates of `stochArray`. -/
noncomputable def krawDir (N : ℕ) (δb δc : ℕ → ℝ) (r ε : ℝ) : Coefficients N :=
  stochArray N (fun n => (1 - r) * n / N + ε * δb n) (fun n => r * n / N + ε * δc n)
```

## Lean declaration

```lean
/-- **P3, Section 9**: at `r = 4/5` the first-order derivative of `g(N,N;N)` along the rule `β = 1`, `γ = 0` is
`512/1875` for `N = 4` and `-71936/5859375` for `N = 8`. -/
theorem rule_deriv_4_5 :
    HasDerivAt (fun ε => productMatrix (krawDir 4 (fun _ => 1) (fun _ => 0) (4 / 5) ε) 4 (Fin.last 4) (Fin.last 4))
      (512 / 1875) 0 ∧
    HasDerivAt (fun ε => productMatrix (krawDir 8 (fun _ => 1) (fun _ => 0) (4 / 5) ε) 8 (Fin.last 8) (Fin.last 8))
      (-71936 / 5859375) 0 := …
```

The proof writes g(N,N;N)(ε) = H(ε)/S(ε) with integer polynomials near ε = 0 and reads the derivative from their first two coefficients (not to be checked).

## Proposed changes (applied only after this round and round 23 pass)

1. P3 Lean table: new row `Section~\ref{sec:limits}: first-order derivatives along the rule $\beta=1$, $\gamma=0$ at $r=4/5$ & \path{Szkraw.PolyCol.rule_deriv_4_5}`.
2. papers/FORMALIZATION.md, in the Section 9 sentence proposed in round 23: "except the one-kink example with $N=500$ and the two first-order derivatives $512/1875$ and $-71936/5859375$" becomes "and the first-order derivatives $512/1875$ and $-71936/5859375$ (\path{Szkraw.PolyCol.rule_deriv_4_5}), except the one-kink example with $N=500$".

Please answer: MATCH / MISMATCH for the statement and each change, then an overall verdict (PASS / PASS WITH MINOR FIXES / FAIL), with exact replacement text for any fix.
