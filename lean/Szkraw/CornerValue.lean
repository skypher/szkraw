import Szkraw.BooleanMatrix

/-!
# Lemma 9.1 (Corner value)

For `0 < r ≤ 1` the Krawtchouk array `K_{N,r}` has `g(N,N;N) = (1 - r)^N`: in the Boolean model,
`U_N^2 = Π_i ((1 - r) y_i + r)` has coefficient `(1 - r)^N` at `y_1 ⋯ y_N`.
-/

namespace Szkraw

theorem bitsWeight_true : ∀ N : ℕ, bitsWeight N (fun _ => true) = N
  | 0 => rfl
  | N + 1 => by
    show (if (fun _ : Fin (N + 1) => true) 0 then 1 else 0) + bitsWeight N (Fin.tail fun _ => true) = N + 1
    rw [if_pos rfl, show (Fin.tail fun _ : Fin (N + 1) => true) = (fun _ => true) from rfl,
      bitsWeight_true N]
    ring

theorem boolean_corner (r : ℝ) (hr : 0 < r) :
    ∀ N : ℕ, booleanProduct r N N N (fun _ => true) = (1 - r) ^ N
  | 0 => by
    simp [booleanProduct, elementary_zero, coordinate, bitsWeight]
  | N + 1 => by
    have e : (fun _ : Fin (N + 1) => true) = Fin.cons true (fun _ : Fin N => true) := by
      funext i; refine Fin.cases ?_ ?_ i <;> simp
    rw [e, boolean_product_true r hr N N N, boolean_corner r hr N]
    have z1 : booleanProduct r N (N + 1) N (fun _ => true) = 0 := by
      simp [booleanProduct, elementary_above (1 / r) 1 N (N + 1) (by omega), coordinate_zero]
    have z2 : booleanProduct r N N (N + 1) (fun _ => true) = 0 := by
      simp [booleanProduct, elementary_above (1 / r) 1 N (N + 1) (by omega), coordinate_zero]
    rw [z1, z2, pow_succ]; ring

/-- **Lemma 9.1** (Corner value). -/
theorem corner_value (N : ℕ) (hN : 1 ≤ N) (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1) :
    productMatrix (krawCoefficients N r) N ⟨N, by omega⟩ ⟨N, by omega⟩ = (1 - r) ^ N := by
  have h := boolean_matrix_coefficient N hN r hr hr1 N le_rfl ⟨N, by omega⟩ ⟨N, by omega⟩
    (fun _ => true) (bitsWeight_true N)
  simp only [Nat.choose_self, Nat.cast_one, mul_one] at h
  rw [← h, boolean_corner r hr N]

end Szkraw
