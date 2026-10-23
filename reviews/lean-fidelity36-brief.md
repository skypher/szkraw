# Lean statement fidelity, round 36: the one-kink counterexample with N = 500 (P3, Section 9 table)

Repository: github.com/skypher/szkraw, commit e2dec22: lean/Szkraw/Kink500.lean (statement), lean/Szkraw/WindowColumn.lean (windowed column), lean/Szkraw/Kink500Chunk1-4.lean and Kink500Data150/250/350.lean (kernel chunks and intermediate states), lean/Szkraw/ProfileCounterexamples.lean (the accepted `KinkFails` form of the other one-kink examples). Default audit lean/axioms.log (400 lines); audit of the optional target lean/axioms-kink500.log (6 lines); both list only propext, Classical.choice, Quot.sound.

As in earlier rounds, **do not check proofs**. Check whether the Lean statement says what the passage says, and whether the P3 table row, the new P3 sentence and the shortened not-formalized paragraph are accurate. Report MATCH / MISMATCH per item with exact replacement text for any fix.

## Paper passage (P3, Section 9)

\item Below $r=\tfrac12$, the counterexamples we found to shape conditions occur at sizes that grow as $r$ decreases; we did not determine minimal sizes or prove a scaling. For constant-ratio arrays with convex profile, one-kink counterexamples ($m$ unit increments, then $1+\delta$) have $g(N,N;N)<0$ in exact arithmetic at
\begin{center}
\begin{tabular}{@{}lccccccc@{}}
$r$&$2/5$&$1/3$&$3/10$&$1/4$&$2/7$&$1/5$&$1/10$\\
$N$&$20$&$40$&$40$&$60$&$80$&$100$&$500$
\end{tabular}
\end{center}

The parameters of each column are those of `smallr_probe.py` (repository root), `COUNTEREXAMPLES = [  # (r, N, m, delta)`, whose last entry is `(F(1, 10), 500, 450, F(1, 10))`.

## Lean (accepted definitions)

```lean
/-- The normalized profile with increments `e`: `d_i = (Σ_{j<i} e_j) / (Σ_{j<N} e_j)`. -/
noncomputable def incProfile (e : ℕ → ℝ) (N i : ℕ) : ℝ := (∑ j ∈ range i, e j) / ∑ j ∈ range N, e j

/-- One-kink increments: `1` for the first `m` steps, then `1 + δ`. -/
noncomputable def kinkInc (m : ℕ) (δ : ℝ) (j : ℕ) : ℝ := if j < m then 1 else 1 + δ

/-- Shape of the one-kink statements: constant ratio `r`, profile with increments `kinkInc m δ`. -/
def KinkFails (r δ : ℝ) (N m : ℕ) : Prop :=
  (∃ v : Coefficients N, Admissible v ∧ (∀ i, i ≤ N → profile v i = incProfile (kinkInc m δ) N i) ∧
    ∀ i, i ≤ N → v.c i = r * profile v i) ∧
  ∀ v : Coefficients N, Admissible v → (∀ i, i ≤ N → profile v i = incProfile (kinkInc m δ) N i) →
    (∀ i, i ≤ N → v.c i = r * profile v i) → productMatrix v N (Fin.last N) (Fin.last N) < 0

/-- `r = 1/5`, `N = 100`, `m = 80`, `δ = 1/10` (P3, Section 9 table). -/
theorem kink100_1_5_fails : KinkFails (1 / 5) (1 / 10) 100 80 := …
```

## Lean (new)

```lean
/-- **P3, Section 9 table**: `r = 1/10`, `N = 500`, `m = 450`, `δ = 1/10`. -/
theorem kink500_1_10_fails : KinkFails (1 / 10) (1 / 10) 500 450 := …
```

The proof decides the sign of the column entry `H_500(500)` of `ColCheck.ccol` (the method accepted for `kink100_1_5_fails`) through these statements:

```lean
/-- Entries of column `N` vanish below the triangle: `H_m(n) = 0` for `n + m < N`. -/
theorem ccol_triangle (hA : A.length = N + 1) (hB : B.length = N + 1) (hC : C.length = N + 1) :
    ∀ m, (∀ n, n + m < N → eG (ccol A B C N N m).2 n = 0) ∧
      (∀ n, n + m < N + 1 → eG (ccol A B C N N m).1 n = 0) := …

/-- **The windowed computation.** For column `N`, the state after `m` windowed steps is the pair of suffixes
`(H_{m-1} on [lo_{m-1}, N], H_m on [lo_m, N])` of the column computed by `ccol`. -/
theorem witer_eq (hA : A.length = N + 1) (hB : B.length = N + 1) (hC : C.length = N + 1) (hN : 1 ≤ N) :
    ∀ m, m ≤ N → witer A B C N 0 m (winit N) =
      (loP N m, (ccol A B C N N m).1.drop (loP N m), lo N m, (ccol A B C N N m).2.drop (lo N m)) := …
```

`witer` computes the column only on `n ≥ lo_m = max(m, N - m)`; the four chunks are `witer … = <stated state>` and a final sign, each `decide +kernel`. The chunks are not part of `make lean` (about 6 minutes and 20 GB in parallel); `make lean-kink500` builds them and `make axioms-kink500` audits them.

## P3 changes at e2dec22

Table row (was "the one-kink counterexamples with $N\leq100$ and the exact log-concave-increment counterexamples"; `kink500_1_10_fails` added):

Section~\ref{sec:limits}: the one-kink counterexamples and the exact log-concave-increment counterexamples & \path{Szkraw.kink20_2_5_fails}, \path{Szkraw.kink40_1_3_fails}, \path{Szkraw.kink40_3_10_fails}, \path{Szkraw.kink60_1_4_fails}, \path{Szkraw.kink80_2_7_fails}, \path{Szkraw.kink100_1_5_fails}, \path{Szkraw.kink500_1_10_fails}, \path{Szkraw.stepInc_logconcave}, \path{Szkraw.logconcave32_fails}, \path{Szkraw.logconcave80_fails}, \path{Szkraw.logconcave90_fails}\\[3pt]

New sentence before the not-formalized paragraph:

The finite counterexamples are decided by exact integer columns of the product table evaluated in the Lean kernel; for the one-kink example with $N=500$ the column is computed only on the entries $n\geq\max(m,N-m)$ at step $m$, which determine $g(N,N;N)$, in four chunks that the kernel checks against stated intermediate states (\path{Szkraw.ColCheck.witer_eq}, \path{Szkraw.kink500_1_10_fails}). This certificate is not part of \verb|make lean|: \verb|make lean-kink500| builds it and \verb|make axioms-kink500| audits it, which takes about 6 minutes and up to about 20~GB of memory.

The not-formalized paragraph, Section 9 part (the item "the one-kink example with $N=500$, which is checked in exact arithmetic by \path{smallr_probe.py}, but whose documented Lean-kernel evaluation did not finish within 50 minutes;" was removed):

In Section~\ref{sec:limits}, the following are not formalized: the reduction of arbitrary finite systems to the chosen normalization (the Lean development starts from the normalized recurrence); the equispaced-interpolation interpretation of $\Omega$; and the exact contour representation of the first-order change along the terminal row, with the accompanying saddle-point discussion, which is heuristic.

Questions: (1) Does `kink500_1_10_fails` formalize the `r = 1/10`, `N = 500` column of the table, with `m = 450` unit increments followed by `1 + δ`, `δ = 1/10`, in the same sense as the accepted `kink100_1_5_fails`? (2) Is the new sentence accurate? (3) Are the table row and the shortened paragraph accurate?

Answer per item, then an overall verdict (PASS / PASS WITH MINOR FIXES / FAIL).
