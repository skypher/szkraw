import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs

namespace Szkraw

structure Coefficients (N : ℕ) where
  a : ℕ → ℝ
  b : ℕ → ℝ
  c : ℕ → ℝ

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

def Geometric {N : ℕ} (v : Coefficients N) : Prop :=
  ∃ β q : ℝ, 0 ≤ β ∧ 1 ≤ q ∧
    (∀ i, 0 < i → i ≤ N → v.b i = β * v.c i) ∧
    (∀ i, 0 < i → i ≤ N → 0 < (v.b i + v.c i) - (v.b (i-1) + v.c (i-1))) ∧
    (∀ i, 0 < i → i < N →
      (v.b (i+1) + v.c (i+1)) - (v.b i + v.c i) =
        q * ((v.b i + v.c i) - (v.b (i-1) + v.c (i-1))))

def MatrixPositivity {N : ℕ} (v : Coefficients N) : Prop :=
  ∀ m, m ≤ N → ∀ i j, 0 ≤ productMatrix v m i j

noncomputable def perturbationRadius (N : ℕ) (r : ℝ) : ℝ :=
  (1 / 2 : ℝ) * (min r (1-r) / (32 * N)) ^ N

def CloseToKrawtchouk {N : ℕ} (v : Coefficients N) (r : ℝ) : Prop :=
  (∀ i, i ≤ N → 0 ≤ v.b i) ∧
  ∀ i, i ≤ N →
    |v.a i - ((N : ℝ) - i) / N| ≤ perturbationRadius N r ∧
    |v.b i - ((1-r) * i) / N| ≤ perturbationRadius N r ∧
    |v.c i - (r * i) / N| ≤ perturbationRadius N r

/-- Geometric increment theorem, matrix-positivity conclusion. All finite sizes,
all matrix entries, and the original scalar hypotheses are quantified.
The spectral realization is a separate statement still to be integrated. -/
def Stmt_geometric_matrix : Prop :=
  ∀ (N : ℕ) (v : Coefficients N), Admissible v → Geometric v → MatrixPositivity v

/-- Perturbation theorem, matrix-positivity conclusion, with the paper's radius.
The reference is not assumed positive here; its positivity must be supplied. -/
def Stmt_perturbation_matrix : Prop :=
  ∀ (N : ℕ) (v : Coefficients N) (r : ℝ),
    Admissible v → 0 < r → r < 1 → CloseToKrawtchouk v r → MatrixPositivity v

/-- Full geometric criterion: discrete realization and positivity, with no
realization or positivity hypotheses moved to the caller. -/
def Stmt_geometric : Prop :=
  ∀ (N : ℕ) (v : Coefficients N), Admissible v → Geometric v →
    FiniteRealization v ∧ MatrixPositivity v

def Triangle (m n k : ℕ) : Prop := m ≤ n+k ∧ n ≤ m+k ∧ k ≤ m+n

def PerturbationMargin {N : ℕ} (v : Coefficients N) (r : ℝ) : Prop :=
  ∀ (m : ℕ) (n k : Fin (N+1)), m ≤ N →
    (Triangle m n.val k.val →
      (1/2 : ℝ)*(min r (1-r)/4)^N ≤ productMatrix v m n k) ∧
    (¬ Triangle m n.val k.val → productMatrix v m n k = 0)

/-- Full perturbation criterion at the stated coefficient radius. -/
def Stmt_perturbation : Prop :=
  ∀ (N : ℕ) (v : Coefficients N) (r : ℝ),
    Admissible v → 0 < r → r < 1 → CloseToKrawtchouk v r →
    FiniteRealization v ∧ MatrixPositivity v ∧ PerturbationMargin v r

/-- Scalar amplification estimate consumed by the perturbation matrix theorem.
It is a source extraction of the explicit induction with L = 8N. -/
def Stmt_error_amplification : Prop :=
  ∀ (N : ℕ) (η : ℝ) (e : ℕ → ℝ), 1 ≤ N → 0 ≤ η →
    e 0 = 0 → e 1 ≤ 3*η →
    (∀ m, 1 ≤ m → m < N → e (m+1) ≤ 4*N*e m + 2*N*e (m-1) + 12*N*η) →
    ∀ m, 1 ≤ m → m ≤ N → e m ≤ η*(8*N)^m

end Szkraw
