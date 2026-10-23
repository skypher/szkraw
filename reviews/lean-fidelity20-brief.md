# Lean statement fidelity, round 20: three remarks (P1 and P3 Krawtchouk sharpness, P1 log-concavity violation, P2 linear-profile arrays)

Repository: github.com/skypher/szkraw, commit f2bd5d5, file lean/Szkraw/LateRemarks.lean. Axiom audit: lean/axioms.log (only propext, Classical.choice, Quot.sound).

As in earlier rounds, **do not check proofs**. Check whether each Lean statement says what the cited remark says (Lean hypotheses equivalent or weaker, conclusions equivalent or stronger), and whether the proposed text changes are accurate. Conventions as in rounds 1–19 (`Coefficients`, `Admissible` = (2.1), `MatrixPositivity`, `profile`, `newtonCoeff`, `productMatrix v m i j = g(m,i;j)`, `geometricCoefficients N p q` = the array (eq:parameters) with p = 1/r).

## Paper statements

1. P2, after Theorem 4.1 (= paper.tex after Theorem 8.9): "For the linear profile $d_i=i/N$ the condition reads $\kappa\leq\frac N{2N-1}(1-r)$, and these are arrays of Proposition~3.3." (The first half is already formalized as `affine_range_remarks`; Proposition 3.3 = Quadratic arrays: $b_n=\beta_1n+\beta_2\binom n2$, $c_n=\kappa_1n+\kappa_2\binom n2$, $\kappa_2\geq0$, $\kappa_2+\beta_2\geq0$, $b$ nondecreasing.)
2. P1, paragraph "How sharp is log-concavity?": "Log-concavity is not necessary either. For $0<\mu<1$ and $q>1$ let $D(i)=(1-\mu)i+\mu[i]_q$, whose Newton coefficients are $\nu_1=1$ and $\nu_k=\mu(q-1)^{k-1}$ for $k\geq2$; thus $\nu_1\nu_3/\nu_2^2=1/\mu$ ... For $\mu=\frac1{10}$ and $q=\frac{11}{10}$, the constant-ratio arrays with profile $d_i=D(i)/D(N)$ have property (P) for every $r\in(0,1]$ and $N\in\{6,8,10,12\}$ ... For $\mu=\frac1{100}$ and the same $q$, already $N=6$ gives a negative coefficient $g(6,6;6)$ at $r=1$." ONLY the last sentence (the failing case) is formalized; the positive statement for μ = 1/10 is not.
3. P1 Corollary 3.6 and P3 Corollary 6.1 (proof): "The range is sharp in this endpoint normalization: if $1/2<p_0<1$, then $r=p_0/(1-p_0)>1$ and $g(1,1;1)=b_1=(1-r)/N<0$."

## Lean statements

```lean
/-- **Remark after Theorem 8.9.** Linear-profile arrays of Theorem 8.9 are arrays of Proposition 8.8. -/
theorem affine_linear_quadratic {N : ℕ} (vv : Coefficients N) (hN : 1 ≤ N) {r κ : ℝ} (hκ : 0 ≤ κ)
    (hlin : ∀ i, i ≤ N → profile vv i = (i : ℝ) / N)
    (hc : ∀ i, i ≤ N → vv.c i = (r + κ * i / N) * profile vv i)
    (hb : ∀ i, i < N → vv.b i ≤ vv.b (i + 1)) : QuadHyp vv

/-- The profile `d_i = D(i)/D(6)`, `D(i) = (99/100) i + (1/100) [i]_{11/10}`, scaled by `D(6) = 60171561/10⁷`. -/
noncomputable def sharpD (i : ℕ) : ℝ :=
  (if i = 0 then 0 else if i = 1 then 10000000 else if i = 2 then 20010000 else if i = 3 then 30031000
    else if i = 4 then 40064100 else if i = 5 then 50110510 else 60171561) / 60171561

/-- The constant-ratio array with `r = 1` on this profile: `a = 1 - d`, `b = 0`, `c = d`. -/
noncomputable def sharpEx : Coefficients 6 where
  a i := 1 - sharpD i
  b _ := 0
  c i := sharpD i

/-- **P1, "log-concavity is not necessary either", the failing case.** For `D(i) = (1-μ) i + μ [i]_q` with
`μ = 1/100`, `q = 11/10`, the constant-ratio array with `r = 1` and profile `d_i = D(i)/D(6)` is admissible, its
Newton coefficients satisfy `ν₁ ν₃ = (1/μ) ν₂² = 100 ν₂²`, and `g(6,6;6) < 0`. -/
theorem lc_violation_fails :
    Admissible sharpEx ∧
      (∀ i, i ≤ 6 → profile sharpEx i = ((99 / 100) * (i : ℝ) + (1 / 100) * ∑ j ∈ range i, (11 / 10 : ℝ) ^ j) /
        ((99 / 100) * 6 + (1 / 100) * ∑ j ∈ range 6, (11 / 10 : ℝ) ^ j)) ∧
      (∀ i, i ≤ 6 → sharpEx.c i = 1 * profile sharpEx i) ∧
      newtonCoeff (profile sharpEx) 1 * newtonCoeff (profile sharpEx) 3 = 100 * newtonCoeff (profile sharpEx) 2 ^ 2 ∧
      productMatrix sharpEx 6 6 6 < 0 ∧ ¬ MatrixPositivity sharpEx

/-- For `a₀ = 1`, `b₀ = 0` the first product matrix is the recurrence matrix, so `g(1,1;i) = b_i` on the diagonal. -/
theorem productMatrix_one {N : ℕ} (v : Coefficients N) (ha0 : v.a 0 = 1) (hb0 : v.b 0 = 0) :
    productMatrix v 1 = recurrenceMatrix v

/-- **Sharpness in Corollary 6.1** (proof of P3 Corollary 6.1). For `1/2 < p₀ < 1`, i.e. `r = p₀/(1-p₀) > 1`, the
Krawtchouk array normalized at `j = 0` has `g(1,1;1) = b₁ = (1-r)/N < 0`. -/
theorem krawtchouk_range_sharp (N : ℕ) (hN : 1 ≤ N) (p₀ : ℝ) (h1 : 1 / 2 < p₀) (h2 : p₀ < 1) :
    productMatrix (geometricCoefficients N ((1 - p₀) / p₀) 1) 1 ⟨1, by omega⟩ ⟨1, by omega⟩ =
        (1 - p₀ / (1 - p₀)) / N ∧
      (1 - p₀ / (1 - p₀)) / N < 0 ∧ ¬ MatrixPositivity (geometricCoefficients N ((1 - p₀) / p₀) 1)
```

## Proposed changes (applied only after this round passes)

1. P2 Lean table, row "Remarks after Theorem 4.1": add `\path{Szkraw.affine_linear_quadratic}`.
2. P1 Lean table: row "Corollary 3.6: Krawtchouk range": add `\path{Szkraw.krawtchouk_range_sharp}`; new row `The failing example in the paragraph ``How sharp is log-concavity?'' & \path{Szkraw.lc_violation_fails}`.
3. P3 Lean table, row "Corollary 6.1": add `\path{Szkraw.krawtchouk_range_sharp}`.
4. papers/FORMALIZATION.md: "the sharpness remark in its proof is not formalized" becomes "the sharpness remark in its proof is \path{Szkraw.krawtchouk_range_sharp}, stated for $N\geq1$ and $1/2<p_0<1$ with the value $g(1,1;1)=(1-r)/N$"; "that the linear-profile arrays are arrays of Proposition~8.8 is not stated separately" becomes "that the linear-profile arrays are arrays of Proposition~8.8 is \path{Szkraw.affine_linear_quadratic}"; new sentence: "In the paragraph of P1 on how sharp log-concavity is, only the failing case is formalized (\path{Szkraw.lc_violation_fails}: $\mu=\frac1{100}$, $q=\frac{11}{10}$, $N=6$, $r=1$, with $\nu_1\nu_3=100\nu_2^2$ and $g(6,6;6)<0$); the statement that for $\mu=\frac1{10}$ the arrays have (P) for every $r\in(0,1]$ and $N\in\{6,8,10,12\}$ is checked in exact arithmetic by \path{runs/sharp/lc_violation_cert.py} and is not formalized."

Answer format: MATCH / MISMATCH per item with reason, exact fixes, overall verdict (PASS / PASS WITH MINOR FIXES / FAIL). Terse.
