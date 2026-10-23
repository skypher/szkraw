# Lean statement fidelity, round 17: Proposition 8.14 (products of Newton sequences)

Repository: github.com/skypher/szkraw, commit f74ef1e. File: lean/Szkraw/NewtonProduct.lean (with lean/Szkraw/LCConvolution.lean and LCSequences.lean). Axiom audit: lean/axioms.log (only propext, Classical.choice, Quot.sound).

Check that the Lean statement `Szkraw.newton_product_LCNZ`, together with `nval_mul` and `nval_inj`, states exactly Proposition 8.14 of paper.tex, with no hidden narrowing. Also check the proposed table row and scope sentence below, which will be added only after this round passes. This is a statement-fidelity review; the proof is checked by Lean.

Points to check:
1. Does `LCNZ` match "nonnegative and log-concave without internal zeros", with sequences on ℕ (extension by zero at negative indices is implicit)?
2. Do `nval`, `nval_mul` and `nval_inj` correctly identify "the Newton coefficients κ_k = Δ^k(fg)(0) of fg" for f(x) = Σ_i ρ_i C(x,i) and g(x) = Σ_j ν_j C(x,j) on x ∈ ℤ_{≥0}, as the paper's statement specifies? Note the paper allows infinite sequences with finite sums on ℤ_{≥0}; `nval` sums over i ≤ x.
3. Is anything in the paper's statement not covered: nonnegativity, log-concavity, no internal zeros, the identically zero case?
4. Is the proposed scope sentence accurate?

Answer format: MATCH / MISMATCH per item, exact fixes, terse.

## Paper statement

```latex
\begin{proposition}[Products]\label{prop:np}
Let $(\rho_i)_{i\geq0}$ and $(\nu_j)_{j\geq0}$ be nonnegative and log-concave without internal zeros, extended by zero at negative indices, and let $f(x)=\sum_i\rho_i\binom xi$ and $g(x)=\sum_j\nu_j\binom xj$ for $x\in\mathbb Z_{\geq0}$, where the sums are finite. Then the Newton coefficients $\kappa_k=\Delta^k(fg)(0)$ of $fg$ are nonnegative and log-concave without internal zeros.
\end{proposition}
```

## Lean statements

```lean
def LCNZ (u : ℕ → ℝ) : Prop :=
  (∀ i, 0 ≤ u i) ∧ (∀ i, u i * u (i + 2) ≤ u (i + 1) ^ 2) ∧
  (∀ i j k, i ≤ j → j ≤ k → 0 < u i → 0 < u k → 0 < u j)

def nval (ρ : ℕ → ℝ) (x : ℕ) : ℝ := ∑ i ∈ range (x + 1), (x.choose i : ℝ) * ρ i

/-- **Proposition 8.14** (Walkup, Theorem 2, in the Newton basis). If `ρ` and `ν` are nonnegative and
log-concave without internal zeros, then the Newton coefficients of the product of their Newton series,
`f(x) g(x) = Σ_k C(x,k) κ_k` on `ℕ`, are nonnegative and log-concave without internal zeros. -/
theorem newton_product_LCNZ {ρ ν κ : ℕ → ℝ} (hρ : LCNZ ρ) (hν : LCNZ ν)
    (hκ : ∀ x, nval ρ x * nval ν x = nval κ x) : LCNZ κ

/-- The Newton series with coefficients `κ = kap ρ ν` is the product of those of `ρ` and `ν`. -/
theorem nval_mul (ρ ν : ℕ → ℝ) (x : ℕ) : nval ρ x * nval ν x = nval (kap ρ ν) x

/-- Newton coefficients are determined by the values on `ℕ`. -/
theorem nval_inj {a b : ℕ → ℝ} (h : ∀ x, nval a x = nval b x) : a = b
```

## Proposed paper changes

1. New row in the Lean table, after Corollary 8.13:
   `Proposition~\ref{prop:np}: products of Newton sequences & \path{Szkraw.newton_product_LCNZ}`
2. New scope sentence in the formalization section, after the sentence on Corollary 8.13:
   "Proposition~\ref{prop:np} is stated for real sequences on $\mathbb N$ with the predicate \path{Szkraw.LCNZ} (nonnegative, $u_iu_{i+2}\leq u_{i+1}^2$, positive entries forming an interval) and for every sequence $\kappa$ with $f(x)g(x)=\sum_k\binom xk\kappa_k$ for all $x\in\mathbb N$ (\path{Szkraw.nval}); such $\kappa$ exists and is unique (\path{Szkraw.nval_mul}, \path{Szkraw.nval_inj}), and the proof formalizes the layer cake, the box identity, (T1)--(T3) and the five cases."
3. In the AI-use disclosure, "that proof passed a further review round with minor fixes and is not machine-verified" becomes "... and is machine-verified".
