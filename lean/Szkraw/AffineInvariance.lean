import Szkraw.Statements
import Mathlib.Tactic.Module

/-!
# Product coefficients are invariant under affine changes of `x`

If `ã_n = s a_n`, `b̃_n = s b_n + β` and `c̃_n = s c_n` with `s ≠ 0` (the substitution
`y = s x + β`), then every `g(m, n; k)` is unchanged.
-/

namespace Szkraw

variable {N : ℕ}

theorem affine_matrixPair (v w : Coefficients N) {s β : ℝ} (hs : s ≠ 0)
    (ha : ∀ i, w.a i = s * v.a i) (hb : ∀ i, w.b i = s * v.b i + β) (hc : ∀ i, w.c i = s * v.c i) :
    ∀ m, matrixPair w m = matrixPair v m := by
  have hJ : recurrenceMatrix w = s • recurrenceMatrix v + β • (1 : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) := by
    ext i j
    simp only [recurrenceMatrix, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, ha, hb, hc,
      Fin.ext_iff]
    split_ifs <;> first | (exfalso; omega) | ring
  intro m
  induction m with
  | zero => rfl
  | succ n ih =>
    have key : recurrenceMatrix w - w.b n • (1 : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) =
        s • (recurrenceMatrix v - v.b n • (1 : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)) := by
      rw [hJ, hb]; module
    show ((matrixPair w n).2, (w.a n)⁻¹ • ((recurrenceMatrix w - w.b n • 1) * (matrixPair w n).2 -
        w.c n • (matrixPair w n).1)) =
      ((matrixPair v n).2, (v.a n)⁻¹ • ((recurrenceMatrix v - v.b n • 1) * (matrixPair v n).2 -
        v.c n • (matrixPair v n).1))
    rw [ih, key, ha, hc, Matrix.smul_mul, mul_smul, ← smul_sub, smul_smul, mul_inv, mul_assoc,
      mul_comm ((v.a n)⁻¹) s, ← mul_assoc, inv_mul_cancel₀ hs, one_mul]

/-- `g(m,n;k)` is invariant under the affine substitution `y = s x + β`. -/
theorem affine_product (v w : Coefficients N) {s β : ℝ} (hs : s ≠ 0)
    (ha : ∀ i, w.a i = s * v.a i) (hb : ∀ i, w.b i = s * v.b i + β) (hc : ∀ i, w.c i = s * v.c i) (m : ℕ) :
    productMatrix w m = productMatrix v m := by
  rw [productMatrix, productMatrix, affine_matrixPair v w hs ha hb hc m]

end Szkraw
