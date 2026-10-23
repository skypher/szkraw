# Lean statement fidelity, round 37: every finite system reduces to the normalized recurrence (P3, Section 9)

Repository: github.com/skypher/szkraw, commit 98ac91c: lean/Szkraw/FiniteSystem.lean (new); definitions in lean/Szkraw/Statements.lean (accepted). Axiom audit lean/axioms.log (405 lines, only propext, Classical.choice, Quot.sound).

As in earlier rounds, **do not check proofs**. Check whether the Lean statement says what the passage says, and whether the P3 table row and the shortened not-formalized paragraph are accurate. Report MATCH / MISMATCH per item with exact replacement text for any fix.

## Paper passage (P3)

Section 2 (the basic conditions (2.1) = `eq:basic` and the recurrence):

Consider real coefficients indexed by $0\leq i\leq N$, where $N\geq1$, satisfying
\begin{equation}\label{eq:basic}
\begin{gathered}
a_0=1,\quad b_0=c_0=0,\quad a_N=0,\quad a_i+b_i+c_i=1,\\
a_i>0\ (i<N),\qquad c_i>0\ (i>0).
\end{gathered}
\end{equation}
Set $R_{-1}=0$, $R_0=1$, and determine $R_1,\ldots,R_N$ by
\begin{equation}\label{eq:recurrence}
xR_i=a_iR_{i+1}+b_iR_i+c_iR_{i-1}\qquad(0\leq i<N).
\end{equation}
At $i=0$, \eqref{eq:recurrence} gives $R_1=x$; induction at $x=1$, using the row sums and $a_i>0$ for $i<N$, gives $R_i(1)=1$ for $0\leq i\leq N$.
The terminal relation is $(x-b_N)R_N-c_NR_{N-1}=0$ on the orthogonality support. Linearization means equality of functions on this support, rather than an unrestricted polynomial identity when the degree sum exceeds $N$.

Section 9, opening (the sentence in question is the one beginning "An affine change of $x$"):

Write $K_{N,r}$ for the Krawtchouk array \eqref{eq:parameters} with $q=1$, and use the coordinates $b_1,\ldots,b_{N-1},c_1,\ldots,c_N$ of a stochastic array with $b_0=0$, $a_0=1$, $a_N=0$, $b_N=1-c_N$ and $a_n=1-b_n-c_n$ otherwise. An affine change of $x$, together with the positive normalization $R_n(x_0)=1$ at the largest support point $x_0$, reduces every finite system to this form. 

## Lean definitions (accepted)

```lean
def Admissible {N : ℕ} (v : Coefficients N) : Prop :=
  1 ≤ N ∧ v.a 0 = 1 ∧ v.b 0 = 0 ∧ v.c 0 = 0 ∧ v.a N = 0 ∧
  (∀ i, i ≤ N → v.a i + v.b i + v.c i = 1) ∧
  (∀ i, i < N → 0 < v.a i) ∧
  (∀ i, 0 < i → i ≤ N → 0 < v.c i)

def recurrenceMatrix {N : ℕ} (v : Coefficients N) :
    Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ := fun i j =>
  if j.val = i.val + 1 then v.a i.val
  else if j = i then v.b i.val
  else if i.val = j.val + 1 then v.c i.val else 0

noncomputable def matrixPair {N : ℕ} (v : Coefficients N) :
    ℕ → Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ ×
      Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ
  | 0 => (0, 1)
  | n + 1 => let t := matrixPair v n
      (t.2, (v.a n)⁻¹ •
        ((recurrenceMatrix v - v.b n • (1 : Matrix _ _ ℝ)) * t.2 - v.c n • t.1))

noncomputable def productMatrix {N : ℕ} (v : Coefficients N) (m : ℕ) :
    Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ := (matrixPair v m).2

noncomputable def polynomialPair {N : ℕ} (v : Coefficients N) :
    ℕ → Polynomial ℝ × Polynomial ℝ
  | 0 => (0, 1)
  | n + 1 => let t := polynomialPair v n
      (t.2, Polynomial.C (v.a n)⁻¹ *
        ((Polynomial.X - Polynomial.C (v.b n)) * t.2 - Polynomial.C (v.c n) * t.1))

noncomputable def recurrencePolynomial {N : ℕ} (v : Coefficients N) (m : ℕ) :
    Polynomial ℝ := (polynomialPair v m).2

/-- A positive discrete orthogonality measure on exactly N+1 points together
with the terminal relation and matrix-to-polynomial product identity. -/
def FiniteRealization {N : ℕ} (v : Coefficients N) : Prop :=
  ∃ x w : Fin (N+1) → ℝ, Function.Injective x ∧
    (∀ t, 0 < w t) ∧ (∑ t, w t) = 1 ∧
    (∀ m, m ≤ N → (recurrencePolynomial v m).eval 1 = 1) ∧
    (∀ (m : ℕ) (n : Fin (N+1)), m ≤ N →
      ∑ k : Fin (N+1), productMatrix v m n k = 1) ∧
    (∀ m n, m ≤ N → n ≤ N → m ≠ n →
      ∑ t, w t * (recurrencePolynomial v m).eval (x t) *
        (recurrencePolynomial v n).eval (x t) = 0) ∧
    (∀ m, m ≤ N → 0 < ∑ t, w t * ((recurrencePolynomial v m).eval (x t))^2) ∧
    (∀ t, (x t-v.b N) * (recurrencePolynomial v N).eval (x t) -
      v.c N * (recurrencePolynomial v (N-1)).eval (x t) = 0) ∧
    (∀ (m : ℕ) (n t : Fin (N+1)), m ≤ N →
      (recurrencePolynomial v m).eval (x t) *
        (recurrencePolynomial v n.val).eval (x t) =
      ∑ k : Fin (N+1), productMatrix v m n k *
        (recurrencePolynomial v k.val).eval (x t))
```

## New Lean statement

```lean
/-- **P3, Section 9: reduction of finite systems to the normalized recurrence.** Let `Σ_t w_t δ_{x_t}` be a
positive measure on `N + 1 ≥ 2` distinct real points with largest point `x_{t₀}`. Then there are an array `v`
satisfying (2.1) and an affine change `y = s x + c` with `s > 0` and `y(x_{t₀}) = 1` such that the polynomials
`R_n` of `v`, at the points `y_t = s x_t + c`, are orthogonal for the weights `w_t`, satisfy the terminal relation
and the product identity `R_m R_n = Σ_k g(m,n;k) R_k`; and every family `p_n` (`deg p_n = n`) of orthogonal
polynomials of the measure with `p_n(x_{t₀}) = 1` is `p_n(z) = R_n(s z + c)`. -/
theorem finite_system_reduction (hN : 1 ≤ N) (hx : Function.Injective x) (hw : ∀ t, 0 < w t)
    (t0 : Fin (N + 1)) (htop : ∀ t, x t ≤ x t0) :
    ∃ (v : Coefficients N) (s c : ℝ), Admissible v ∧ 0 < s ∧ s * x t0 + c = 1 ∧
      (∀ m n, m ≤ N → n ≤ N → m ≠ n →
        ∑ t, w t * (recurrencePolynomial v m).eval (s * x t + c) * (recurrencePolynomial v n).eval (s * x t + c) = 0) ∧
      (∀ t, (s * x t + c - v.b N) * (recurrencePolynomial v N).eval (s * x t + c) -
        v.c N * (recurrencePolynomial v (N - 1)).eval (s * x t + c) = 0) ∧
      (∀ (m : ℕ) (n t : Fin (N + 1)), m ≤ N →
        (recurrencePolynomial v m).eval (s * x t + c) * (recurrencePolynomial v n.val).eval (s * x t + c) =
          ∑ k : Fin (N + 1), productMatrix v m n k * (recurrencePolynomial v k.val).eval (s * x t + c)) ∧
      (∀ p : ℕ → ℝ[X], (∀ n, n ≤ N → (p n).natDegree = n) →
        (∀ m n, m ≤ N → n ≤ N → m ≠ n → ∑ t, w t * (p m).eval (x t) * (p n).eval (x t) = 0) →
        (∀ n, n ≤ N → (p n).eval (x t0) = 1) →
        ∀ n, n ≤ N → ∀ z, (p n).eval z = (recurrencePolynomial v n).eval (s * z + c)) := …
```

Notes. (a) "Finite system" is read as a positive measure on `N + 1` distinct real points (`N ≥ 1`, as in (2.1)) together with its orthogonal polynomials; the statement takes the measure as `(x, w)` with `x` injective, `w > 0`, and `x_{t₀}` its largest point. (b) The array's polynomials at `y_t = s x_t + c` are orthogonal for `w`, satisfy the terminal relation and the product identity at every node; the last clause says every degree-`n` orthogonal family of the measure normalized by `p_n(x_{t₀}) = 1` is `R_n(s z + c)`, so the linearization coefficients of the finite system in this normalization are the `g(m,n;k) = productMatrix v m n k` of the array. (c) The clauses of `FiniteRealization` (accepted for Theorem 2.1) are the model for the orthogonality, terminal and product clauses.

## P3 changes at 98ac91c

New table row:

Section~\ref{sec:limits}: the reduction of every finite system to the normalized recurrence & \path{Szkraw.FinSys.finite_system_reduction}\\[3pt]

Not-formalized paragraph, Section 9 part (the item "the reduction of arbitrary finite systems to the chosen normalization (the Lean development starts from the normalized recurrence);" was removed):

In Section~\ref{sec:limits}, the following are not formalized: the equispaced-interpolation interpretation of $\Omega$ and the exact contour representation of the first-order change along the terminal row, with the accompanying saddle-point discussion, which is heuristic.

Questions: (1) Does `finite_system_reduction` formalize "An affine change of $x$, together with the positive normalization $R_n(x_0)=1$ at the largest support point $x_0$, reduces every finite system to this form", with "this form" the stochastic arrays satisfying (2.1)? (2) Are the table row and the shortened paragraph accurate?

Answer per item, then an overall verdict (PASS / PASS WITH MINOR FIXES / FAIL).
