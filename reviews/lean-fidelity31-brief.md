# Lean statement fidelity, round 31: remarks of P1 and P2 formalized after round 30

Repository: github.com/skypher/szkraw, commit 3f6ee84. Axiom audit: lean/axioms.log (380 lines, only propext, Classical.choice, Quot.sound).

As in earlier rounds, **do not check proofs**. Check whether each Lean statement says what the cited passage says (hypotheses equivalent or weaker, conclusions equivalent or stronger), and report MATCH / MISMATCH per item with reasons and exact replacement text for any fix. Conventions as in rounds 1–25 (`Coefficients`, `Admissible`, `MatrixPositivity`, `productMatrix v m n k = g(m,n;k)`, `profile`, `newtonCoeff d k = Δ^k d(0)`, `krawCoefficients N r` = K_{N,r}, `geometricCoefficients N p q` with p = 1/r, `szwarcCoefficients N p` = (eq:szwarc-q)/(eq:qarray) of length 2N+1, `revCoeff` = reversed array, `krawDir`/`stochArray` as in round 23). Paper passages: read them at the commit in papers/p1.tex, p2.tex, p3.tex; each declaration's docstring names its passage, and the paper's Lean table (section "Code and formalization") lists it. Where a Lean statement transcribes a condition from another paper (Szwarc's Theorem 3.3 from his survey; Miclo's condition as P3 states it), say whether the transcription matches what the paper says.

## P1 (papers/p1.tex)

```lean
theorem binomial_mean (N : ℕ) (x y : ℝ) :
    ∑ n ∈ range (N + 1), (N.choose n : ℝ) * y ^ (N - n) * x ^ n * n = N * x * (x + y) ^ (N - 1) := …

/-- **P1, footnote**: with the weights `w_n = C(N,n) p^(N-n) (1-p)^n` at the points `n`, `Σ w_n = 1`,
`Σ w_n n = N(1-p)`, and `Σ w_n K_1(n) = (1-2p)/(1-p)` for `K_1(x) = (x - pN)/((1-p)N)`. -/
theorem szwarc_footnote (N : ℕ) (hN : 1 ≤ N) (p : ℝ) (hp1 : p < 1) :
    ∑ n ∈ range (N + 1), (N.choose n : ℝ) * p ^ (N - n) * (1 - p) ^ n = 1 ∧
    ∑ n ∈ range (N + 1), (N.choose n : ℝ) * p ^ (N - n) * (1 - p) ^ n * n = N * (1 - p) ∧
    ∑ n ∈ range (N + 1), (N.choose n : ℝ) * p ^ (N - n) * (1 - p) ^ n * (((n : ℝ) - p * N) / ((1 - p) * N)) =
      (1 - 2 * p) / (1 - p) := …

/-- The Krawtchouk profile `i/N` has `ν = (1/N, 0, …, 0)`; the profile `[i]_q/[N]_q` of `G_{N,q,r}` (`q > 1`) has
`ν_k = (q-1)^(k-1)/[N]_q`, log-concave with equality; an admissible convex quadratic profile `ν₁ i + ν₂ C(i,2)` has
`ν_1 = ν₁`, `ν_2 = ν₂` and `ν_k = 0` for `k ≥ 3`. -/
theorem newton_examples (N : ℕ) (hN : 1 ≤ N) :
    (∀ k, 1 ≤ k → newtonCoeff (fun i => (i : ℝ) / N) k = if k = 1 then (1 : ℝ) / N else (0 : ℝ)) ∧
    (∀ q : ℝ, 1 < q → ∀ k, 1 ≤ k → newtonCoeff (fun i => qInteger q i / qInteger q N) k =
      (q - 1) ^ (k - 1) / qInteger q N) ∧
    (∀ q : ℝ, 1 < q → ∀ k, 2 ≤ k →
      (q - 1) ^ (k - 1 - 1) / qInteger q N * ((q - 1) ^ (k + 1 - 1) / qInteger q N) =
        ((q - 1) ^ (k - 1) / qInteger q N) ^ 2) ∧
    (∀ ν₁ ν₂ : ℝ, ∀ k, newtonCoeff (fun i => ν₁ * i + ν₂ * (i.choose 2 : ℝ)) k =
      if k = 1 then ν₁ else if k = 2 then ν₂ else 0) := …

/-- The convex counterexamples of P3 have Newton coefficients of both signs: `ν_8 > 0 > ν_9` (`N = 14`),
`ν_13 > 0 > ν_14` (`N = 20`), `ν_15 > 0 > ν_16` (log-convex increments, `N = 18`). -/
theorem convex_counterexamples_newton_signs :
    (0 < newtonCoeff (incProfile (kinkInc 7 (1 / 5)) 14) 8 ∧ newtonCoeff (incProfile (kinkInc 7 (1 / 5)) 14) 9 < 0) ∧
    (0 < newtonCoeff (incProfile (kinkInc 12 (1 / 20)) 20) 13 ∧
      newtonCoeff (incProfile (kinkInc 12 (1 / 20)) 20) 14 < 0) ∧
    (0 < newtonCoeff (incProfile cvxInc 18) 15 ∧ newtonCoeff (incProfile cvxInc 18) 16 < 0) := …

/-- **P1, Section 4**: Szwarc's Theorem 3.3 (`x p_n = γ_n p_{n+1} + β_n p_n + α_n p_{n-1}`; hypotheses `β ≡ 0`,
`α_{2n}`, `α_{2n+1}`, `α_{2n} + γ_{2n}`, `α_{2n+1} + γ_{2n+1}` nondecreasing, `α_n ≤ γ_n`) applied to (eq:szwarc-q)
(`γ = a`, `β = b`, `α = c`, length `2N + 1`): the monotonicity hypotheses hold; `α_n ≤ γ_n` holds at odd `n` exactly
when `p₀ ≤ 1/2`, and at `n = 2m` exactly when `m ≤ N - m`; in every admissible finite array `α_N ≤ γ_N` fails. -/
theorem szwarc_thm33_check (N : ℕ) (hN : 1 ≤ N) (p : ℝ) :
    let v := szwarcCoefficients N p
    (∀ n, v.b n = 0) ∧
    (∀ m, 2 * m + 2 ≤ 2 * N → v.c (2 * m) ≤ v.c (2 * (m + 1))) ∧
    (∀ m, 2 * m + 3 ≤ 2 * N → v.c (2 * m + 1) ≤ v.c (2 * (m + 1) + 1)) ∧
    (∀ m, 2 * m + 2 ≤ 2 * N → v.c (2 * m) + v.a (2 * m) ≤ v.c (2 * (m + 1)) + v.a (2 * (m + 1))) ∧
    (∀ m, 2 * m + 3 ≤ 2 * N → v.c (2 * m + 1) + v.a (2 * m + 1) ≤ v.c (2 * (m + 1) + 1) + v.a (2 * (m + 1) + 1)) ∧
    (∀ m, 2 * m + 1 ≤ 2 * N → (v.c (2 * m + 1) ≤ v.a (2 * m + 1) ↔ p ≤ 1 / 2)) ∧
    (∀ m, m ≤ N → (v.c (2 * m) ≤ v.a (2 * m) ↔ m ≤ N - m)) ∧
    (∀ (M : ℕ) (w : Coefficients M), Admissible w → ¬ w.c M ≤ w.a M) := …
```
(`incProfile`, `kinkInc`, `cvxInc` are as accepted in round 23.)

## P2 (papers/p2.tex)

```lean
/-- The quadratic array with parameters `β₁ β₂ κ₁ κ₂`. -/
noncomputable def quadArray (N : ℕ) (β₁ β₂ κ₁ κ₂ : ℝ) : Coefficients N where
  a n := 1 - (β₁ * n + β₂ * (n.choose 2 : ℝ)) - (κ₁ * n + κ₂ * (n.choose 2 : ℝ))
  b n := β₁ * n + β₂ * (n.choose 2 : ℝ)
  c n := κ₁ * n + κ₂ * (n.choose 2 : ℝ)

/-- **P2, after Proposition 3.3**: each hypothesis of Proposition 3.3 is needed. -/
theorem quadratic_hypotheses_needed :
    -- `κ₂ ≥ 0` dropped
    (Admissible (quadArray 3 (1 / 57) (2 / 19) (17 / 57) (-5 / 57)) ∧ (-5 / 57 : ℝ) < 0 ∧
      (0 : ℝ) ≤ -5 / 57 + 2 / 19 ∧
      (∀ n, n < 3 → (quadArray 3 (1 / 57) (2 / 19) (17 / 57) (-5 / 57)).b n ≤
        (quadArray 3 (1 / 57) (2 / 19) (17 / 57) (-5 / 57)).b (n + 1)) ∧
      productMatrix (quadArray 3 (1 / 57) (2 / 19) (17 / 57) (-5 / 57)) 3 3 3 < 0) ∧
    -- `κ₂ + β₂ ≥ 0` dropped
    (Admissible (quadArray 3 (1 / 3) (-2 / 13) (5 / 39) (1 / 39)) ∧ (0 : ℝ) ≤ 1 / 39 ∧
      (1 / 39 + -2 / 13 : ℝ) < 0 ∧
      (∀ n, n < 3 → (quadArray 3 (1 / 3) (-2 / 13) (5 / 39) (1 / 39)).b n ≤
        (quadArray 3 (1 / 3) (-2 / 13) (5 / 39) (1 / 39)).b (n + 1)) ∧
      productMatrix (quadArray 3 (1 / 3) (-2 / 13) (5 / 39) (1 / 39)) 3 3 3 < 0) ∧
    -- `b` nondecreasing dropped
    (Admissible (quadArray 3 (1 / 5) (-1 / 5) (2 / 15) (1 / 5)) ∧ (0 : ℝ) ≤ 1 / 5 ∧ (0 : ℝ) ≤ 1 / 5 + -1 / 5 ∧
      (quadArray 3 (1 / 5) (-1 / 5) (2 / 15) (1 / 5)).b 3 < (quadArray 3 (1 / 5) (-1 / 5) (2 / 15) (1 / 5)).b 2 ∧
      productMatrix (quadArray 3 (1 / 5) (-1 / 5) (2 / 15) (1 / 5)) 3 3 3 < 0) := …

/-- If `c_i = κ₁ i + κ₂ C(i,2)` with `κ₁, κ₂ > 0` and `b_i = w₁ κ₁ i + w₂ κ₂ C(i,2)` with `w₁ > w₂ ≥ 0` (any common
positive scaling), the ratio `c_i/(b_i + c_i)` increases strictly for `i ≥ 1`. -/
theorem strict_ratio_example (κ₁ κ₂ w₁ w₂ s : ℝ) (hκ₁ : 0 < κ₁) (hκ₂ : 0 < κ₂) (hw : w₂ < w₁) (hw₂ : 0 ≤ w₂)
    (hs : 0 < s) (i : ℕ) (hi : 1 ≤ i) :
    let c := fun n : ℕ => s * (κ₁ * n + κ₂ * (n.choose 2 : ℝ))
    let b := fun n : ℕ => s * (w₁ * κ₁ * n + w₂ * κ₂ * (n.choose 2 : ℝ))
    c i / (b i + c i) < c (i + 1) / (b (i + 1) + c (i + 1)) := …

/-- The counterexample `d = (0,25,55,91)/91`, `c = (0,24,54,90)/91` has `b = (0,1,1,1)/91`, whose Newton coefficients
have both signs. -/
theorem openEx1_b_newton :
    let b : ℕ → ℝ := fun i => if i = 0 then 0 else 1 / 91
    0 < newtonCoeff b 1 ∧ newtonCoeff b 2 < 0 := …

/-- A strictly increasing linear ratio `ρ_i = r + κ i/N` (`κ > 0`) on the linear profile `d_i = i/N` has concave
diagonal `b_i = (1 - ρ_i) d_i`; its second Newton coefficient is `-2κ/N² < 0`, so it is excluded by Corollary 3.2. -/
theorem linear_ratio_concave_b (N : ℕ) (hN : 1 ≤ N) (r κ : ℝ) (hκ : 0 < κ) :
    let b : ℕ → ℝ := fun i => (1 - (r + κ * i / N)) * (i / N)
    (∀ i, b (i + 2) - 2 * b (i + 1) + b i = -2 * κ / N ^ 2) ∧ newtonCoeff b 2 = -2 * κ / N ^ 2 ∧
      newtonCoeff b 2 < 0 := …

/-- Exponential ratios `ρ(x) = r(1+ε)^x`, `r > 0`, `ε ≥ 0`: the Newton coefficients are `r ε^k`, they are log-concave
without internal zeros, and the arrays with this ratio, a log-concave Newton profile and nondecreasing `b` satisfy
the hypothesis of Theorem 5.5, hence have property (P). -/
theorem exponential_ratio (r ε : ℝ) (hr : 0 < r) (hε : 0 ≤ ε) :
    (∀ k, newtonCoeff (fun i => r * (1 + ε) ^ i) k = r * ε ^ k) ∧ LCNZ (fun k => r * ε ^ k) ∧
    ∀ (N : ℕ) (v : Coefficients N), Admissible v → LogConcaveNoInternalZeros N (newtonCoeff (profile v)) →
      (∀ i, i < N → v.b i ≤ v.b (i + 1)) → (∀ i, i ≤ N → v.c i = r * (1 + ε) ^ i * profile v i) →
      GenRatioHyp v ∧ MatrixPositivity v := …

/-- The ratio of the cubic counterexample (`N = 4`), Newton coefficients `ν_0, …, ν_4 = (19/20, 0, 0, 1/320, 0)`:
nonnegative and satisfying every log-concavity inequality `ν_k ν_{k+2} ≤ ν_{k+1}²`, `k + 2 ≤ 4`, but with internal
zeros (`ν_0, ν_3 > 0 = ν_1`). -/
theorem cubic_example_ratio_newton :
    let ρ : ℕ → ℝ := fun i => 19 / 20 + (i.choose 3 : ℝ) / 320
    newtonCoeff ρ 0 = 19 / 20 ∧ newtonCoeff ρ 1 = 0 ∧ newtonCoeff ρ 2 = 0 ∧ newtonCoeff ρ 3 = 1 / 320 ∧
      newtonCoeff ρ 4 = 0 ∧ (∀ k, k + 2 ≤ 4 → newtonCoeff ρ k * newtonCoeff ρ (k + 2) ≤ newtonCoeff ρ (k + 1) ^ 2) ∧
      (0 < newtonCoeff ρ 0 ∧ newtonCoeff ρ 1 = 0 ∧ 0 < newtonCoeff ρ 3) := …

/-- Theorem 5.5 contains Theorem 4.1, Corollary 4.4 and the case `t² ≥ rτ` of Theorem 5.3: their hypotheses imply
those of Theorem 5.5. -/
theorem general_contains {N : ℕ} (hN : 1 ≤ N) (v : Coefficients N) :
    (AffineRatioHyp v → GenRatioHyp v) ∧ (LowDegRatioHyp v → GenRatioHyp v) ∧
    ((∃ r t τ : ℝ, 0 < r ∧ 0 ≤ t ∧ 0 ≤ τ ∧ r * τ ≤ t ^ 2 ∧ (∀ i, i < N → v.b i ≤ v.b (i + 1)) ∧
      (∀ i, i ≤ N → v.c i = (r + t * i + τ * (i.choose 2 : ℝ)) * profile v i) ∧
      LogConcaveNoInternalZeros N (newtonCoeff (profile v))) → GenRatioHyp v) := …

/-- Theorem 5.3 and Corollary 4.4 are not comparable. -/
theorem quad_lowdeg_incomparable :
    (∃ v : Coefficients 3, Admissible v ∧ QuadRatioHyp v ∧ ¬ LowDegRatioHyp v) ∧
    (∃ v : Coefficients 4, Admissible v ∧ LowDegRatioHyp v ∧ ¬ QuadRatioHyp v) := …

/-- **P2, after Lemma 5.4**: the weight sums are the coefficients of `Q` on geometric sequences,
`Q(1, r, r², …) = Σ_W N_W(Q) r^W`, for `Q(u) = Σ_{i ≤ j ≤ M} q_{ij} u_i u_j` and
`N_W(Q) = Σ_{i ≤ j, i + j = W} q_{ij}`. -/
theorem weight_sums_geometric (M : ℕ) (q : ℕ → ℕ → ℝ) (r : ℝ) :
    ∑ p ∈ (range (M + 1) ×ˢ range (M + 1)).filter (fun p => p.1 ≤ p.2), q p.1 p.2 * (r ^ p.1 * r ^ p.2) =
      ∑ W ∈ range (2 * M + 1),
        (∑ p ∈ (range (M + 1) ×ˢ range (M + 1)).filter (fun p => p.1 ≤ p.2 ∧ p.1 + p.2 = W), q p.1 p.2) * r ^ W := …

/-- `ρ(x) = 1 + x/2 + x²/2` has Newton coefficients `(1, 1, 1, 0, …)` (log-concave without internal zeros) but
`(log ρ)''(0) = 3/4 > 0`. -/
theorem log_rho_not_concave :
    newtonCoeff (fun i : ℕ => 1 + (i : ℝ) / 2 + (i : ℝ) ^ 2 / 2) 0 = 1 ∧
    newtonCoeff (fun i : ℕ => 1 + (i : ℝ) / 2 + (i : ℝ) ^ 2 / 2) 1 = 1 ∧
    newtonCoeff (fun i : ℕ => 1 + (i : ℝ) / 2 + (i : ℝ) ^ 2 / 2) 2 = 1 ∧
    deriv (deriv fun x : ℝ => Real.log (1 + x / 2 + x ^ 2 / 2)) 0 = 3 / 4 := …

/-- The coefficient of `tτ` in (eq:cubic-B) at `(ℓ, n) = (0, 3)`. -/
noncomputable def kapTTau (v : ℕ → ℝ) : ℝ :=
  (((3 : ℕ) : ℝ) + 1) * (((3 : ℕ) : ℝ) + 2) * (PhiC 0 1 0 0 0 2 v * PhiC 0 0 1 0 (0 + 1) 3 (fun k => v k + v (k + 1)) +
    PhiC 0 0 1 0 0 2 v * PhiC 0 1 0 0 (0 + 1) 3 (fun k => v k + v (k + 1))) -
  8 * (((3 : ℕ) : ℝ) - 1) * (rhoC 0 1 0 0 (0 + 1) * (v 0 + v 1) * PhiC 0 0 1 0 0 (3 + 2) v +
    rhoC 0 0 1 0 (0 + 1) * (v 0 + v 1) * PhiC 0 1 0 0 0 (3 + 2) v)

/-- The coefficient of `rσ` in (eq:cubic-B) at `(ℓ, n) = (0, 3)`. -/
noncomputable def kapRSig (v : ℕ → ℝ) : ℝ :=
  (((3 : ℕ) : ℝ) + 1) * (((3 : ℕ) : ℝ) + 2) * (PhiC 1 0 0 0 0 2 v * PhiC 0 0 0 1 (0 + 1) 3 (fun k => v k + v (k + 1)) +
    PhiC 0 0 0 1 0 2 v * PhiC 1 0 0 0 (0 + 1) 3 (fun k => v k + v (k + 1))) -
  8 * (((3 : ℕ) : ℝ) - 1) * (rhoC 1 0 0 0 (0 + 1) * (v 0 + v 1) * PhiC 0 0 0 1 0 (3 + 2) v +
    rhoC 0 0 0 1 (0 + 1) * (v 0 + v 1) * PhiC 1 0 0 0 0 (3 + 2) v)

/-- The geometric Newton sequence `u_0 = 0`, `u_k = q^(k-1)`. -/
noncomputable def geoSeq (q : ℝ) (k : ℕ) : ℝ := if k = 0 then 0 else q ^ (k - 1)

/-- The geometric Newton sequence `u_0 = 0`, `u_k = q^(k-1)`. -/
noncomputable def geoSeq (q : ℝ) (k : ℕ) : ℝ := if k = 0 then 0 else q ^ (k - 1)

theorem geometric_kappa_values (q : ℝ) :
    kapRSig (geoSeq q) = -20 * q * (4 * q ^ 3 + 11 * q ^ 2 + 9 * q + 1) ∧
    kapTTau (geoSeq q) = 20 * (q + 1) * (8 * q ^ 3 + 33 * q ^ 2 + 30 * q + 6) := …

/-- **P2, after Theorem 5.6**: on geometric profiles `κ_tτ/|κ_rσ| → 2`, and for every `u > 2` some `q > 0` gives
`κ_tτ + u κ_rσ < 0`, so the coefficientwise test fails for `rσ ≤ u tτ` with `u > 2`. -/
theorem geometric_kappa :
    Tendsto (fun q => kapTTau (geoSeq q) / |kapRSig (geoSeq q)|) atTop (𝓝 2) ∧
    ∀ u : ℝ, 2 < u → ∃ q : ℝ, 0 < q ∧ kapTTau (geoSeq q) + u * kapRSig (geoSeq q) < 0 := …
```
Hypothesis predicates used (lean/Szkraw/VRAffineMain.lean `AffineRatioHyp` = Theorem 4.1, VRLowDegree.lean `LowDegRatioHyp` = Corollary 4.4, VRQuadMain.lean `QuadRatioHyp` = Theorem 5.3, GenMain.lean `GenRatioHyp` = Theorem 5.5, VRCorollaries.lean `QuadHyp` = Proposition 3.3), accepted in earlier rounds. `kapTTau`/`kapRSig` are the polarized coefficients of tτ and rσ in (eq:cubic-B) at (ℓ,n) = (0,3) in the form used by `Szkraw.cubic_ratio_matrix` (lean/Szkraw/CubicB.lean, `kapB_three_ttaurs`).

Please also check the P1 and P2 Lean-table rows added at 3f6ee84.

Answer per item, then an overall verdict (PASS / PASS WITH MINOR FIXES / FAIL).
