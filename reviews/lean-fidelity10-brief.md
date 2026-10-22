# Independent review, round 10: the description of Ω in Lean

As in rounds 1–9 (round 9: PASS WITH MINOR FIXES, documentation only), **do not check proofs**. Check only whether each Lean statement faithfully expresses the paper's claim, under the acceptance rule: Lean hypotheses equivalent to or weaker than the paper's, and Lean conclusion equivalent to or stronger. Where the Lean statement covers less than the paper claims, say exactly what is missing.

This round covers the sentence describing Ω = {U ≤ −1} before Lemma 9.5: "It contains [0,1], has nonanalytic boundary points (with vertical tangents) at 0 and 1, and meets the line Re x = ½ at Im x = ±0.26276…".
- `omega_contains`: [0,1] ⊆ Ω.
- `omega_half_line`: some y₀ with 0.26276 < y₀ < 0.26277 has ½ + iy ∈ Ω iff |y| ≤ y₀. This is offered as the meaning of "meets the line Re x = ½ at Im x = ±0.26276…": Ω ∩ {Re x = ½} is the segment between ½ ± i y₀.
- `omega_corner_zero` is offered as the meaning of "nonanalytic boundary point with vertical tangent at 0". For some β > 0 and a function a:
  - a(0) = 0;
  - in the box |Re x| < β, |Im x| < β, Ω is the set Re x ≥ a(Im x);
  - in the box, the topological frontier of Ω is exactly the curve Re x = a(Im x);
  - a(b)/b → 0 as b → 0, so the curve is tangent to the imaginary axis at 0;
  - a is not real-analytic at 0, so the boundary curve, written as a graph over its tangent line, is not analytic there.
- `omega_corner_one`: the same at 1, with Ω the set Re x ≤ a(Im x) near 1, a(0) = 1, (a(b) − 1)/b → 0, and a not analytic at 0.
- Also check the new scope sentence.

Question for the reviewer: is "a is not analytic at 0", for the graph over the tangent line, an adequate formalization of "nonanalytic boundary point"? If not, state the strengthening needed.

Answer format: a table (paper claim | Lean declaration | MATCH / MATCH, SCOPE NOTED / MISMATCH | reason), exact fixes, and an overall verdict (PASS / PASS WITH MINOR FIXES / FAIL). Be terse.

## Part A. Paper text

#### Paragraph before Lemma 9.5 (the claims under review)
```latex
The polynomial hypothesis can be replaced by analyticity on a fixed region. Let $U(x)=\int_0^1\log|x-t|\,dt$ and $\Omega=\{x\in\mathbb C:U(x)\leq-1\}$, the region of convergence of equispaced interpolation. It contains $[0,1]$, has nonanalytic boundary points (with vertical tangents) at $0$ and $1$, and meets the line $\operatorname{Re}x=\tfrac12$ at $\operatorname{Im}x=\pm0.26276\ldots$.
```

#### Code-and-formalization section: new scope sentence
```latex
The description of $\Omega$ before Lemma~\ref{lem:nr} is formalized as well: $\Omega$ contains $[0,1]$ (\path{Szkraw.omega_contains}); there is $y_0$ with $0.26276<y_0<0.26277$ such that $\tfrac12+iy\in\Omega$ exactly when $|y|\leq y_0$ (\path{Szkraw.omega_half_line}, from certified bounds for $\log$, $\arctan$, $\log2$ and $\pi$); and near $0$, $\Omega$ is the region $\operatorname{Re}x\geq a(\operatorname{Im}x)$ whose frontier is the curve $\operatorname{Re}x=a(\operatorname{Im}x)$, where $a(0)=0$, $a(b)/b\to0$ (vertical tangent) and $a$ is not real-analytic at $0$, because $a(b)>b/(2\log(1/b))$ for small $b>0$ (\path{Szkraw.omega_corner_zero}); the corner at $1$ is its mirror image under $x\mapsto1-\bar x$ (\path{Szkraw.omega_corner_one}). The remaining prose of Section~\ref{sec:limits}, the computations and heuristics away from $r=1$, is not formalized.
```

## Part B. Lean statements

### lean/Szkraw/NorlundU.lean
```lean
/-- The logarithmic potential `U(x) = ∫_0^1 log|x - t| dt`. -/
noncomputable def Ulog (x : ℂ) : ℝ := ∫ t : ℝ in (0 : ℝ)..1, Real.log ‖x - t‖
```

### lean/Szkraw/OmegaShape.lean
```lean
/-- The region `Ω = {U ≤ -1}`. -/
def Omega : Set ℂ := {x | Ulog x ≤ -1}

/-- `Ω` contains `[0,1]`. -/
theorem omega_contains {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : (t : ℂ) ∈ Omega := …

/-- **`Ω` on the line `Re x = 1/2`**: there is `y₀` with `0.26276 < y₀ < 0.26277` such that
`1/2 + iy ∈ Ω` iff `|y| ≤ y₀`. -/
theorem omega_half_line :
    ∃ y₀ : ℝ, 26276 / 100000 < y₀ ∧ y₀ < 26277 / 100000 ∧
      ∀ y : ℝ, (1 / 2 + y * I : ℂ) ∈ Omega ↔ |y| ≤ y₀ := …

/-- **The corner of `Ω` at `0`.** Near `0`, `Ω` is the region `x ≥ a(b)` to the right of a curve
`x = a(b)`, which is the frontier of `Ω` there. The curve has a vertical tangent at `0`
(`a(b)/b → 0`), and `a` is not analytic at `0`. -/
theorem omega_corner_zero :
    ∃ β > 0, ∃ a : ℝ → ℝ, a 0 = 0 ∧ (∀ b, |b| < β → 0 ≤ a b ∧ a b ≤ |b|) ∧
      (∀ x b : ℝ, |x| < β → |b| < β → ((x : ℂ) + b * I ∈ Omega ↔ a b ≤ x)) ∧
      (∀ x b : ℝ, |x| < β → |b| < β → ((x : ℂ) + b * I ∈ frontier Omega ↔ x = a b)) ∧
      Tendsto (fun b => a b / b) (𝓝[≠] 0) (𝓝 0) ∧ ¬AnalyticAt ℝ a 0 := …

/-- **The corner of `Ω` at `1`**, the mirror image of the corner at `0` under `z ↦ 1 - z̄`. -/
theorem omega_corner_one :
    ∃ β > 0, ∃ a : ℝ → ℝ, a 0 = 1 ∧
      (∀ x b : ℝ, |x - 1| < β → |b| < β → ((x : ℂ) + b * I ∈ Omega ↔ x ≤ a b)) ∧
      (∀ x b : ℝ, |x - 1| < β → |b| < β → ((x : ℂ) + b * I ∈ frontier Omega ↔ x = a b)) ∧
      Tendsto (fun b => (a b - 1) / b) (𝓝[≠] 0) (𝓝 0) ∧ ¬AnalyticAt ℝ a 0 := …
```
