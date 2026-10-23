# Lean statement fidelity, round 22: P1, the positive example of "Log-concavity is not necessary either"

Repository: github.com/skypher/szkraw, commit 1fb1d1e, file lean/Szkraw/LCViolationPos.lean. Axiom audit: lean/axioms.log (only propext, Classical.choice, Quot.sound; `Szkraw.lc_violation_holds` is its last line). The four computational checks `check6`…`check12` are `decide +kernel` (kernel evaluation, no `native_decide`, no extra axioms).

As in earlier rounds, **do not check proofs**. Check whether the Lean statement says what the paper says (Lean hypotheses equivalent or weaker, conclusions equivalent or stronger), and whether the proposed text changes are accurate. Conventions as in rounds 1–21 (`Coefficients`, `Admissible` = (2.1), `MatrixPositivity` = all g(m,n;k) ≥ 0 for m, n, k ≤ N, `profile v i = b_i + c_i`, `newtonCoeff d k = Δ^k d(0)`, `LogConcaveNoInternalZeros` as in Theorem 3.1). Round 20 accepted `Szkraw.lc_violation_fails` for the failing case μ = 1/100 of the same paragraph.

## Paper statement (P1, paragraph "How sharp is log-concavity?")

Log-concavity is not necessary either. For $0<\mu<1$ and $q>1$ let $D(i)=(1-\mu)i+\mu[i]_q$, whose Newton coefficients are $\nu_1=1$ and $\nu_k=\mu(q-1)^{k-1}$ for $k\geq2$; thus $\nu_1\nu_3/\nu_2^2=1/\mu$, and the other log-concavity inequalities hold with equality. For $\mu=\frac1{10}$ and $q=\frac{11}{10}$, the constant-ratio arrays with profile $d_i=D(i)/D(N)$ have property (P) for every $r\in(0,1]$ and $N\in\{6,8,10,12\}$: every coefficient $g(m,n;k)$ is a polynomial in $r$ with nonnegative Bernstein coefficients (\path{runs/sharp/lc_violation_cert.py}). For $\mu=\frac1{100}$ and the same $q$, already $N=6$ gives a negative coefficient $g(6,6;6)$ at $r=1$.

The claim to check is the third sentence: for μ = 1/10, q = 11/10 the constant-ratio arrays with profile d_i = D(i)/D(N) have (P) for every r ∈ (0,1] and N ∈ {6,8,10,12}; together with the first two sentences specialized to μ = 1/10 (ν₁ν₃/ν₂² = 1/μ = 10, so log-concavity fails). "Constant-ratio array" means c_i = r d_i, b_i = (1 − r) d_i, a_i = 1 − d_i, as in Theorem 3.1 (`ConstantRatioLogConcave`: c_i = r · profile_i with 0 < r ≤ 1).

## Lean declarations

```lean
/-- `D(i) = (1 - μ) i + μ [i]_q` with `μ = 1/10`, `q = 11/10`. -/
noncomputable def lcvD (i : ℕ) : ℝ := (1 - 1 / 10) * i + 1 / 10 * ∑ j ∈ range i, (11 / 10 : ℝ) ^ j

/-- `evH r s [p₀, …, p_d] = Σ pₑ rᵉ s^(d-e)`. -/
noncomputable def evH (r s : ℝ) : List ℤ → ℝ
  | [] => 0
  | x :: p => (x : ℝ) * s ^ p.length + r * evH r s p

def padd (p q : List ℤ) : List ℤ := List.zipWith (· + ·) p q
def pscale (c : ℤ) (p : List ℤ) : List ℤ := p.map (c * ·)
/-- Multiplication by `r`. -/
def mulR (p : List ℤ) : List ℤ := 0 :: p
/-- Multiplication by `s`. -/
def mulS (p : List ℤ) : List ℤ := p ++ [0]
/-- Multiplication by `r + s`. -/
def mulT (p : List ℤ) : List ℤ := padd (mulR p) (mulS p)

abbrev Tab := List (List (List ℤ))

/-- Entry `(n, k)` of a table, with the zero polynomial of length `d` outside it. -/
def tget (T : Tab) (d n k : ℕ) : List ℤ := (T.getD n []).getD k (List.replicate d 0)

def build (N : ℕ) (f : ℕ → ℕ → List ℤ) : Tab :=
  (List.range (N + 1)).map fun n => (List.range (N + 1)).map fun k => f n k

/-- `E_i`, read from the list `E`. -/
def eE (E : List ℤ) (i : ℕ) : ℤ := E.getD i 0

/-- One step of the scaled recurrence: from `H_{m-1}` (`P`) and `H_m` (`C`) to `H_{m+1}`. -/
def hstep (E : List ℤ) (N m : ℕ) (P C : Tab) : Tab :=
  build N fun n k =>
    padd (padd (padd
      (pscale (eE E N - eE E n) (mulT (tget C (m + 1) (n + 1) k)))
      (pscale (eE E n - eE E m) (mulS (tget C (m + 1) n k))))
      (pscale (eE E n) (mulR (tget C (m + 1) (n - 1) k))))
      (pscale (-(eE E m * (eE E N - eE E (m - 1)))) (mulR (mulT (tget P m n k))))

/-- `(H_{m-1}, H_m)`. -/
def htab (E : List ℤ) (N : ℕ) : ℕ → Tab × Tab
  | 0 => ([], build N fun n k => if n = k then [1] else [0])
  | m + 1 => ((htab E N m).2, hstep E N m (htab E N m).1 (htab E N m).2)

/-- All coefficients of all `H_m(n, k)`, `m, n, k ≤ N`, are nonnegative. -/
def checkAll (E : List ℤ) (N : ℕ) : Bool :=
  (List.range (N + 1)).all fun m => (List.range (N + 1)).all fun n => (List.range (N + 1)).all fun k =>
    (tget (htab E N m).2 (m + 1) n k).all fun x => decide (0 ≤ x)

/-- **P1, "Log-concavity is not necessary either", the positive case.** Let `D(i) = (1-μ) i + μ [i]_q` with
`μ = 1/10`, `q = 11/10` (`lcvD`), `N ∈ {6, 8, 10, 12}` and `0 < r ≤ 1`. The constant-ratio array with ratio `r`
and profile `d_i = D(i)/D(N)` exists and is admissible; every such array has Newton coefficients with
`ν₁ ν₃ = (1/μ) ν₂² = 10 ν₂²`, so they are not log-concave, and it has property (P): every `g(m,n;k)` is
nonnegative. -/
theorem lc_violation_holds (N : ℕ) (hN : N = 6 ∨ N = 8 ∨ N = 10 ∨ N = 12) (r : ℝ) (hr0 : 0 < r)
    (hr1 : r ≤ 1) :
    (∃ v : Coefficients N, Admissible v ∧ (∀ i, i ≤ N → v.c i = r * profile v i) ∧
      ∀ i, i ≤ N → profile v i = lcvD i / lcvD N) ∧
    ∀ v : Coefficients N, Admissible v → (∀ i, i ≤ N → v.c i = r * profile v i) →
      (∀ i, i ≤ N → profile v i = lcvD i / lcvD N) →
      newtonCoeff (profile v) 1 * newtonCoeff (profile v) 3 = 10 * newtonCoeff (profile v) 2 ^ 2 ∧
      ¬ LogConcaveNoInternalZeros N (newtonCoeff (profile v)) ∧ MatrixPositivity v
```

The statement universally quantifies over admissible arrays with c_i = r d_i and the given profile on 0 ≤ i ≤ N (so b_i = (1 − r) d_i and a_i = 1 − d_i are forced by admissibility), and separately asserts that such an array exists. The proof (not to be checked) writes S_m g(m,n;k), S_m = ∏_{j<m}(E_N − E_j) with E_i = 10^N D(i) ∈ ℤ, as a homogeneous polynomial of degree m in (r, 1 − r) (`evH`) whose integer coefficients satisfy an exact recurrence (`htab`), and the kernel checks they are all nonnegative (`checkAll`). This is the paper's Bernstein-coefficient certificate in homogeneous form.

## Proposed changes (applied only after this round passes)

1. P1 Lean table: the row `The failing example in the paragraph ``How sharp is log-concavity?'' & \path{Szkraw.lc_violation_fails}` becomes `The two examples in the paragraph ``How sharp is log-concavity?'' ($\mu=\frac1{10}$ and $\mu=\frac1{100}$) & \path{Szkraw.lc_violation_holds}, \path{Szkraw.lc_violation_fails}`.
2. P1 paragraph: "every coefficient $g(m,n;k)$ is a polynomial in $r$ with nonnegative Bernstein coefficients (\path{runs/sharp/lc_violation_cert.py})." becomes "every coefficient $g(m,n;k)$ is a polynomial in $r$ with nonnegative Bernstein coefficients (\path{runs/sharp/lc_violation_cert.py}; machine-verified as \path{Szkraw.lc_violation_holds})."
3. papers/FORMALIZATION.md: the sentence "In the paragraph of P1 on how sharp log-concavity is, only the failing case is formalized (\path{Szkraw.lc_violation_fails}: $\mu=\frac1{100}$, $q=\frac{11}{10}$, $N=6$, $r=1$, with $\nu_1\nu_3=100\nu_2^2$ and $g(6,6;6)<0$); the statement that for $\mu=\frac1{10}$ the arrays have (P) for every $r\in(0,1]$ and $N\in\{6,8,10,12\}$ is checked in exact arithmetic by \path{runs/sharp/lc_violation_cert.py} and is not formalized." becomes "In the paragraph of P1 on how sharp log-concavity is, both examples are formalized: \path{Szkraw.lc_violation_fails} ($\mu=\frac1{100}$, $q=\frac{11}{10}$, $N=6$, $r=1$, with $\nu_1\nu_3=100\nu_2^2$ and $g(6,6;6)<0$) and \path{Szkraw.lc_violation_holds} ($\mu=\frac1{10}$, $q=\frac{11}{10}$: for $N\in\{6,8,10,12\}$ and $0<r\leq1$ an admissible array with constant ratio $r$ and this profile exists, and every such array has $\nu_1\nu_3=10\nu_2^2$, so its Newton coefficients are not log-concave, and has (P)). The proof of \path{Szkraw.lc_violation_holds} computes the Bernstein coefficients of $g(m,n;k)$, scaled by a positive constant, by an exact integer recurrence and checks their signs in the Lean kernel (\verb|decide +kernel|). The float and high-precision searches in that paragraph are not formalized."

Please answer per item: MATCH / MISMATCH with reasons, then an overall verdict (PASS / PASS WITH MINOR FIXES / FAIL), with exact replacement text for any fix.
