# Lean statement fidelity, round 33: Λ_N values and the top-mass direction (P3, after Proposition 9.8)

Repository: github.com/skypher/szkraw, commit 077e5e5: lean/Szkraw/LambdaN.lean (statements), lean/Szkraw/JetColumn.lean (method), lean/Szkraw/Interior.lean (definitions accepted for Proposition 9.8 in round 7). Axiom audit lean/axioms.log (386 lines, only propext, Classical.choice, Quot.sound).

As in earlier rounds, **do not check proofs**. Check whether each Lean statement says what the passage says, and whether the new P3 table row and the shortened not-formalized paragraph are accurate. Report MATCH / MISMATCH per item with exact replacement text for any fix.

## Paper passage (P3, Proposition 9.8, its proof, and the remarks after it)

\begin{proposition}[Interior points near the symmetric endpoint]\label{prop:interior}
For every $N\geq2$ there is $\Lambda_N<\infty$ such that, for $\Lambda>\Lambda_N$ and all sufficiently small $\varepsilon>0$, the measure of $K_{N,1-\Lambda\varepsilon}$ with its top mass lowered by $\varepsilon$ has $g(m,n;k)>0$ for all $|m-n|\leq k\leq\min(m+n,N)$. Consequently, after the affine normalization of Section~\ref{sec:criterion}, a relatively open set of arrays near it has property (P).
\end{proposition}
\begin{proof}
By the model of Lemma~\ref{lem:margin}, $K_{N,r}$ has
\begin{gather*}
g(m,n;k)=\sum_jH(m,n;j)\binom js r^{j-s}(1-r)^s,\\
H(m,n;j)=\frac{\binom mj\binom{N-m}{n-j}}{\binom Nn},\qquad s=k-m-n+2j,
\end{gather*}
where the sum is over $\max(0,m+n-N)\leq j\leq\min(m,n)$ with $0\leq s\leq j$.
At $r=1$ only $s=0$ survives, so a triangle coefficient of $K_{N,1}$ vanishes exactly when $m+n+k$ is odd or $m+n+k>2N$. Both deformations are smooth in $(r,\varepsilon)$, so only these zeros need first-order positivity.
\begin{itemize}
\item If $m+n+k>2N$, all three tails in Lemma~\ref{lem:topmass}(2) vanish, since $g(y,z;k)=0$ for $k>2N-y-z$. The top-mass rate is therefore $2\pi_k>0$, and the rate of decreasing $r$ is nonnegative because $g\geq0$ for $r\leq1$.
\item If $m+n+k$ is odd and at most $2N+1$, the rate of decreasing $r$ is the $s=1$ term $H(m,n;j)\,j$ with $j=(1+m+n-k)/2$. It is positive, because $j\geq1$ and $\max(0,m+n-N)\leq j\leq\min(m,n)$.
\end{itemize}
These cases cover all zeros. Let $\mathcal Z_N$ be the set of triangle triples whose coefficient vanishes at $K_{N,1}$. For $z\in\mathcal Z_N$, write $A_z$ for the top-mass rate and $B_z$ for the rate of decreasing $r$, and define
\[
\Lambda_N=\max\Bigl(\{0\}\cup\Bigl\{-\frac{A_z}{B_z}:z\in\mathcal Z_N,\ A_z<0\Bigr\}\Bigr).
\]
Every denominator appearing here is positive by the preceding cases. Hence $\Lambda>\Lambda_N$ makes every reference-zero derivative strictly positive, and finiteness of $\mathcal Z_N$ gives a common threshold for $\varepsilon$.

Here the measure of $K_{N,r}$ is its probability orthogonality measure. Choose $\varepsilon$ so small that $r=1-\Lambda\varepsilon>0$ and $\varepsilon<(r/(1+r))^N$, so that the lowered top mass remains positive. The affine coordinate $y=(1-\varepsilon)x+\varepsilon=R_1^\varepsilon(x)$ restores the basic recurrence normalization and leaves all product coefficients unchanged. Strict positivity on the triangle gives $b_n=g(1,n;n)>0$ for $1\leq n\leq N$. Lemma~\ref{lem:stability}, with $\Sigma$ the whole triangle, therefore gives a relatively open neighborhood with property (P) in the affine space defined by the basic boundary and row-sum equalities.
\end{proof}

Exact rational computation of the maximum above gives $\Lambda_N=4,10,18,28,52,90,165$ for $N=4,\ldots,10$. These finite-size values do not establish an asymptotic growth law or a geometric thickness estimate. At $K_{N,1}$, in the fixed spectral coordinate, Lemma~\ref{lem:topmass}(1) gives
\[
\dot c_n=-\frac nN\binom Nn,\qquad\dot b_n=\Bigl(\frac{2n}{N}-1\Bigr)\binom Nn.
\]
After the affine normalization restoring $R_1=x$, the top-mass direction is
\[
\delta a_n=\frac{N-n}{N}\Bigl(\binom Nn-1\Bigr),\qquad
\delta b_n=1+\Bigl(\frac{2n}{N}-1\Bigr)\binom Nn,\qquad
\delta c_n=-\frac nN\Bigl(1+\binom Nn\Bigr).
\]
Its binomial dependence on $N$ is not a uniform rule of Definition~\ref{def:rule}, consistently with Theorem~\ref{thm:uniform}.

Also, Section 9: "The deformation that raises the top mass has the binomial profile of the masses and is not a uniform rule."

## Definitions (Interior.lean, accepted in round 7)

```lean
/-- `A_n = 1 - ε Σ_{j<n} C(N,j) r^{-j}`. -/
noncomputable def lowA (N : ℕ) (r ε : ℝ) (n : ℕ) : ℝ := 1 - ε * ∑ j ∈ range n, (N.choose j : ℝ) / r ^ j

/-- `K_{N,r}` with the top mass lowered by `ε`, in the fixed coordinate `x`. -/
noncomputable def lowK (N : ℕ) (r ε : ℝ) : Coefficients N where
  a n := ((N : ℝ) - n) / N * lowA N r ε n / lowA N r ε (n + 1)
  b n := 1 - ((N : ℝ) - n) / N * lowA N r ε n / lowA N r ε (n + 1) - r * n / N * lowA N r ε (n + 1) / lowA N r ε n
  c n := r * n / N * lowA N r ε (n + 1) / lowA N r ε n

/-- The family is smooth in `(r, ε)` near `(1, 0)`. -/
theorem lowK_contDiffAt (m : ℕ) (hm : m ≤ N) (n k : Fin (N + 1)) :
    ContDiffAt ℝ 1 (fun p : ℝ × ℝ => productMatrix (lowK N p.1 p.2) m n k) (1, 0) := by
  have hA : ∀ i, ContDiffAt ℝ 1 (fun p : ℝ × ℝ => lowA N p.1 p.2 i) (1, 0) := by
    intro i
    simp only [lowA]
    refine contDiffAt_const.sub (contDiffAt_snd.mul (ContDiffAt.sum fun j _ => ?_))
    exact contDiffAt_const.div (contDiffAt_fst.pow j) (by simp)
  have hA0 : ∀ i, lowA N (1, (0 : ℝ)).1 (1, (0 : ℝ)).2 i ≠ 0 := fun i => by simp [lowA]
  have hcoef : ∀ i, ContDiffAt ℝ 1 (fun p : ℝ × ℝ => (lowK N p.1 p.2).a i) (1, 0) ∧
      ContDiffAt ℝ 1 (fun p : ℝ × ℝ => (lowK N p.1 p.2).b i) (1, 0) ∧
      ContDiffAt ℝ 1 (fun p : ℝ × ℝ => (lowK N p.1 p.2).c i) (1, 0) := by
    intro i
    have ha : ContDiffAt ℝ 1 (fun p : ℝ × ℝ => (lowK N p.1 p.2).a i) (1, 0) :=
      ((contDiffAt_const.mul (hA i)).div (hA (i + 1)) (hA0 _))
    have hc : ContDiffAt ℝ 1 (fun p : ℝ × ℝ => (lowK N p.1 p.2).c i) (1, 0) :=
      ((((contDiffAt_fst.mul contDiffAt_const).div_const _).mul (hA (i + 1))).div (hA i) (hA0 _))
    refine ⟨ha, ?_, hc⟩
    exact (contDiffAt_const.sub ha).sub hc
  have hpos : ∀ i, i < m → (lowK N (1, (0 : ℝ)).1 (1, (0 : ℝ)).2).a i ≠ 0 := by
    intro i hi'
    have hi : i < N := by omega
    simp only [lowK, lowA_zero, div_one, mul_one]
    have : (i : ℝ) < N := by exact_mod_cast hi
    exact (div_pos (by linarith) (by linarith)).ne'
  exact productMatrix_contDiffAt (fun p : ℝ × ℝ => lowK N p.1 p.2) (1, 0) (fun i => (hcoef i).1)
    (fun i => (hcoef i).2.1) (fun i => (hcoef i).2.2) m hpos n k

/-! ### Derivatives of the family at `(1, 0)` -/

/-- `G(r, ε) = g(m,n;k)` of `lowK N r ε`. -/
noncomputable def lowG (N m : ℕ) (n k : Fin (N + 1)) (p : ℝ × ℝ) : ℝ := productMatrix (lowK N p.1 p.2) m n k

/-- The constant `Λ_N`: a bound for `∂_ε G / (-∂_r G)` over the triangle. -/
noncomputable def lamN (N : ℕ) : ℝ :=
  ∑ z : Fin (N + 1) × Fin (N + 1) × Fin (N + 1),
    |fderiv ℝ (lowG N z.1 z.2.1 z.2.2) (1, 0) (0, 1)| / |fderiv ℝ (lowG N z.1 z.2.1 z.2.2) (1, 0) (1, 0)|
```
`lowK N r ε` is `K_{N,r}` with its top mass lowered by `ε`, in the fixed coordinate `x` (round 7: `lowK_eq_epsRaw`). The proof's `A_z` (top-mass rate) is `∂_ε g` at `(r, ε) = (1, 0)`, and `B_z` (rate of decreasing `r`) is `-∂_r g` there. Note: Lean's `interior_points` uses the cruder `lamN` (a sum), which is why the computed maxima were previously listed as unformalized.

## New statements (LambdaN.lean)

```lean
/-- **P3, after Proposition 9.8**: exact rational computation of the maximum gives `Λ_N = 4, 10, 18, 28, 52, 90, 165`
for `N = 4, …, 10`: every `-A_z/B_z` with `z ∈ Z_N` and `A_z < 0` is at most `Λ_N` (and `B_z > 0`), and the value is
attained. -/
theorem lambda_values :
    ∀ NΛ ∈ [((4 : ℕ), (4 : ℤ)), (5, 10), (6, 18), (7, 28), (8, 52), (9, 90), (10, 165)],
      let N := NΛ.1
      let A := fun z : Fin (N + 1) × Fin (N + 1) × Fin (N + 1) => fderiv ℝ (lowG N z.1 z.2.1 z.2.2) (1, 0) (0, 1)
      let B := fun z : Fin (N + 1) × Fin (N + 1) × Fin (N + 1) => -fderiv ℝ (lowG N z.1 z.2.1 z.2.2) (1, 0) (1, 0)
      (∀ z : Fin (N + 1) × Fin (N + 1) × Fin (N + 1), Triangle z.1 z.2.1 z.2.2 →
        productMatrix (krawCoefficients N 1) z.1 z.2.1 z.2.2 = 0 → A z < 0 → 0 < B z ∧ -A z / B z ≤ NΛ.2) ∧
      (∃ z : Fin (N + 1) × Fin (N + 1) × Fin (N + 1), Triangle z.1 z.2.1 z.2.2 ∧
        productMatrix (krawCoefficients N 1) z.1 z.2.1 z.2.2 = 0 ∧ A z < 0 ∧ -A z / B z = NΛ.2) := …

/-- **P3, Section 9**: at `K_{N,1}`, in the fixed spectral coordinate, lowering the top mass changes the coefficients
at the rates `ċ_n = -(n/N) C(N,n)` and `ḃ_n = (2n/N - 1) C(N,n)`. -/
theorem topmass_rates (N n : ℕ) (hN : 1 ≤ N) :
    HasDerivAt (fun ε => (lowK N 1 ε).c n) (-((n : ℝ) / N * N.choose n)) 0 ∧
    HasDerivAt (fun ε => (lowK N 1 ε).b n) ((2 * (n : ℝ) / N - 1) * N.choose n) 0 :=
  ⟨lowK_e_c N n, lowK_e_b N n hN⟩

/-- The lowered system after the affine change `y = (1-ε)x + ε`. -/
noncomputable def normK (N : ℕ) (ε : ℝ) : Coefficients N where
  a i := (1 - ε) * (lowK N 1 ε).a i
  b i := (1 - ε) * (lowK N 1 ε).b i + ε
  c i := (1 - ε) * (lowK N 1 ε).c i

/-- **P3, Section 9**: the affine change keeps every product coefficient and restores `a_0 = 1`, `b_0 = 0` and the
row sums; at `ε = 0` it is `K_{N,1}`; the direction is `δa_n = (N-n)/N (C(N,n) - 1)`, `δb_n = 1 + (2n/N - 1) C(N,n)`,
`δc_n = -(n/N)(1 + C(N,n))`. -/
theorem normalized_direction (N : ℕ) (hN : 1 ≤ N) :
    (∀ ε : ℝ, ε ≠ 1 → ∀ m, productMatrix (normK N ε) m = productMatrix (lowK N 1 ε) m) ∧
    (∀ ε : ℝ, ε ≠ 1 → (normK N ε).a 0 = 1 ∧ (normK N ε).b 0 = 0) ∧
    (∀ ε : ℝ, ∀ i, (normK N ε).a i + (normK N ε).b i + (normK N ε).c i = 1) ∧
    (∀ i, i ≤ N → (normK N 0).a i = (krawCoefficients N 1).a i ∧ (normK N 0).b i = (krawCoefficients N 1).b i ∧
      (normK N 0).c i = (krawCoefficients N 1).c i) ∧
    (∀ n, n ≤ N →
      HasDerivAt (fun ε => (normK N ε).a n) (((N : ℝ) - n) / N * (N.choose n - 1)) 0 ∧
      HasDerivAt (fun ε => (normK N ε).b n) (1 + (2 * (n : ℝ) / N - 1) * N.choose n) 0 ∧
      HasDerivAt (fun ε => (normK N ε).c n) (-((n : ℝ) / N * (1 + N.choose n))) 0) := …

/-- The lowered system after the affine change `y = (1-ε)x + ε`. -/
noncomputable def normK (N : ℕ) (ε : ℝ) : Coefficients N where
  a i := (1 - ε) * (lowK N 1 ε).a i
  b i := (1 - ε) * (lowK N 1 ε).b i + ε
  c i := (1 - ε) * (lowK N 1 ε).c i

/-- **P3, Section 9**: the affine change keeps every product coefficient and restores `a_0 = 1`, `b_0 = 0` and the
row sums; at `ε = 0` it is `K_{N,1}`; the direction is `δa_n = (N-n)/N (C(N,n) - 1)`, `δb_n = 1 + (2n/N - 1) C(N,n)`,
`δc_n = -(n/N)(1 + C(N,n))`. -/

/-- **P3, Section 9**: the affine change keeps every product coefficient and restores `a_0 = 1`, `b_0 = 0` and the
row sums; at `ε = 0` it is `K_{N,1}`; the direction is `δa_n = (N-n)/N (C(N,n) - 1)`, `δb_n = 1 + (2n/N - 1) C(N,n)`,
`δc_n = -(n/N)(1 + C(N,n))`. -/
theorem normalized_direction (N : ℕ) (hN : 1 ≤ N) :
    (∀ ε : ℝ, ε ≠ 1 → ∀ m, productMatrix (normK N ε) m = productMatrix (lowK N 1 ε) m) ∧
    (∀ ε : ℝ, ε ≠ 1 → (normK N ε).a 0 = 1 ∧ (normK N ε).b 0 = 0) ∧
    (∀ ε : ℝ, ∀ i, (normK N ε).a i + (normK N ε).b i + (normK N ε).c i = 1) ∧
    (∀ i, i ≤ N → (normK N 0).a i = (krawCoefficients N 1).a i ∧ (normK N 0).b i = (krawCoefficients N 1).b i ∧
      (normK N 0).c i = (krawCoefficients N 1).c i) ∧
    (∀ n, n ≤ N →
      HasDerivAt (fun ε => (normK N ε).a n) (((N : ℝ) - n) / N * (N.choose n - 1)) 0 ∧
      HasDerivAt (fun ε => (normK N ε).b n) (1 + (2 * (n : ℝ) / N - 1) * N.choose n) 0 ∧
      HasDerivAt (fun ε => (normK N ε).c n) (-((n : ℝ) / N * (1 + N.choose n))) 0) := …

/-- **P3, Section 9**: neither the affine-normalized top-mass direction nor its negative (raising the top mass) is a
uniform rule `δb_n = β(n/N)`, `δc_n = γ(n/N)`: its dependence on `N` is binomial (`N = 2, n = 1` and `N = 4, n = 2`). -/
theorem direction_not_uniform (σ : ℝ) (hσ : σ = 1 ∨ σ = -1) :
    ¬ ∃ β γ : ℝ → ℝ, ∀ N : ℕ, 1 ≤ N →
      (∀ n, 1 ≤ n → n < N → σ * (1 + (2 * (n : ℝ) / N - 1) * N.choose n) = β (n / N)) ∧
      (∀ n, 1 ≤ n → n ≤ N → σ * -((n : ℝ) / N * (1 + N.choose n)) = γ (n / N)) := …
```

Questions: (1) Do `lambda_values`' two clauses express "exact rational computation of the maximum above gives Λ_N = …" for the max as defined in the proof (with `Z_N` the triangle triples whose coefficient vanishes at `K_{N,1}`)? (2) Does `normK` (with `affine_product`-based invariance, `a_0 = 1`, `b_0 = 0`, row sums) express the affine normalization `y = (1-ε)x + ε` of the proof, and are the derivative formulas the displayed `δa_n, δb_n, δc_n`? (3) Is `direction_not_uniform` (σ = 1: the normalized lowering direction; σ = -1: its negative) an accurate formalization of "is not a uniform rule of Definition 9.3" and of the raising remark? (4) The new P3 table row and the P3 not-formalized paragraph at 077e5e5.

Answer per item, then an overall verdict (PASS / PASS WITH MINOR FIXES / FAIL).
