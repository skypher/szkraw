import Szkraw.Elementary
import Mathlib.Tactic.Algebra.Basic

namespace Szkraw

theorem qInteger_lower (q : ℝ) (n k : ℕ) (hk : k ≤ n) :
    q^k * qInteger q (n+1-k) = q^k * qInteger q (n-k) + q^n := by
  have hs : n+1-k = (n-k)+1 := by omega
  have he : k+(n-k) = n := by omega
  rw [hs, qInteger, mul_add, ← pow_add, he]

theorem head_product_re (p q : ℝ) (n : ℕ) (U V : (tower p q n).Carrier) :
    (((tower p q (n+1)).sum *
      (⟨U,V⟩ : (tower p q (n+1)).Carrier)).re) =
      (tower p q n).sum * U + (p*q^n) • V := by
  change (tower p q n).sum * U +
    algebraMap ℝ (tower p q n).Carrier (p*q^n) * 1 * V = _
  algebra with ℝ

theorem head_product_im (p q : ℝ) (n : ℕ) (U V : (tower p q n).Carrier) :
    (((tower p q (n+1)).sum *
      (⟨U,V⟩ : (tower p q (n+1)).Carrier)).im) =
      U + q • ((tower p q n).sum * V) + (p-1) • V := by
  change (tower p q n).sum * V + 1*U +
    ((q-1) • (tower p q n).sum + algebraMap ℝ (tower p q n).Carrier (p-1))*1*V = _
  algebra with ℝ

def Stmt_elementary_three_term : Prop :=
  ∀ (p q : ℝ) (n k : ℕ),
    (tower p q n).sum * elementary p q n (k+1) =
      qInteger q (k+2) • elementary p q n (k+2) +
      ((p-1)*qInteger q (k+1)) • elementary p q n (k+1) +
      (p*q^k*qInteger q (n-k)) • elementary p q n k

theorem elementary_three_term : Stmt_elementary_three_term := by
  intro p q n
  induction n with
  | zero =>
      intro k
      cases k <;> simp [tower, elementary, qInteger]
  | succ n ih =>
      intro k
      have hone_re : (1 : (tower p q (n+1)).Carrier).re = (1 : (tower p q n).Carrier) := rfl
      have hone_im : (1 : (tower p q (n+1)).Carrier).im = (0 : (tower p q n).Carrier) := rfl
      by_cases hk : k ≤ n
      · apply QuadraticAlgebra.ext
        · change (((tower p q (n+1)).sum *
              (⟨elementary p q n (k+1), elementary p q n k⟩ : (tower p q (n+1)).Carrier)).re) = _
          rw [head_product_re, ih k]
          cases k with
          | zero =>
              simp only [elementary, QuadraticAlgebra.re_add, QuadraticAlgebra.re_smul]
              have hl := qInteger_lower q n 0 (by omega)
              simp only [pow_zero, one_mul, Nat.sub_zero] at hl
              simp only [Nat.zero_add, Nat.sub_zero, pow_zero, mul_one,
                hone_re, elementary_zero]
              rw [hl]
              algebra with ℝ
          | succ k =>
              simp only [elementary, QuadraticAlgebra.re_add, QuadraticAlgebra.re_smul]
              have hl := qInteger_lower q n (k+1) hk
              have hlp : p*q^(k+1)*qInteger q (n+1-(k+1)) =
                  p*q^(k+1)*qInteger q (n-(k+1)) + p*q^n := by
                calc
                  _ = p*(q^(k+1)*qInteger q (n+1-(k+1))) := by ring
                  _ = p*(q^(k+1)*qInteger q (n-(k+1))+q^n) := by rw [hl]
                  _ = _ := by ring
              rw [hlp]
              algebra with ℝ
        · cases k with
          | zero =>
              change (((tower p q (n+1)).sum *
                (⟨elementary p q n 1, elementary p q n 0⟩ : (tower p q (n+1)).Carrier)).im) = _
              rw [head_product_im]
              simp only [elementary, QuadraticAlgebra.im_add, QuadraticAlgebra.im_smul]
              rw [hone_im]
              rw [elementary_zero, elementary_one]
              simp only [qInteger, pow_zero, pow_one, zero_add]
              change (tower p q n).sum + q • ((tower p q n).sum * 1) + (p-1) • (1 : (tower p q n).Carrier) = _
              algebra with ℝ
          | succ k =>
              change (((tower p q (n+1)).sum *
                (⟨elementary p q n (k+2), elementary p q n (k+1)⟩ : (tower p q (n+1)).Carrier)).im) = _
              rw [head_product_im, ih k]
              simp only [elementary, QuadraticAlgebra.im_add, QuadraticAlgebra.im_smul]
              have hs : n+1-(k+1) = n-k := by omega
              rw [hs, qInteger_succ q (k+2), qInteger_succ q (k+1), pow_succ]
              algebra with ℝ
      · have hk1 : n+1 < k+1 := by omega
        have hk2 : n+1 < k+2 := by omega
        rw [elementary_above p q (n+1) (k+1) hk1,
          elementary_above p q (n+1) (k+2) hk2]
        have hz : n+1-k = 0 := by omega
        simp [hz, qInteger]

example : Stmt_elementary_three_term := elementary_three_term

end Szkraw
