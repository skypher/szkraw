import Szkraw.VRAffine

/-!
# The Leibniz rule for iterated forward differences of a product

`Δ^n (f g)(x) = Σ_{j ≤ n} C(n,j) Δ^j f(x + n - j) Δ^{n-j} g(x)` on `ℕ`.
-/

namespace Szkraw

open Finset

/-- Shorthand for the iterated forward difference with step one. -/
noncomputable abbrev Dn (n : ℕ) (f : ℕ → ℝ) : ℕ → ℝ := (fwdDiff 1)^[n] f

theorem Dn_succ (f : ℕ → ℝ) (n x : ℕ) : Dn (n + 1) f x = Dn n f (x + 1) - Dn n f x :=
  fwdDiff_iter_succ f n x

/-- Shift identity: `Δ^j f (y + 1) = Δ^j f y + Δ^{j+1} f y`. -/
theorem Dn_shift (f : ℕ → ℝ) (j y : ℕ) : Dn j f (y + 1) = Dn j f y + Dn (j + 1) f y := by
  rw [Dn_succ]; ring

theorem leibniz_general (f g : ℕ → ℝ) : ∀ n x : ℕ,
    Dn n (fun i => f i * g i) x =
      ∑ j ∈ range (n + 1), (n.choose j : ℝ) * (Dn j f (x + (n - j)) * Dn (n - j) g x)
  | 0, x => by simp [Dn]
  | n + 1, x => by
    rw [Dn_succ, leibniz_general f g n (x + 1), leibniz_general f g n x, ← sum_sub_distrib]
    -- each term splits into the targets j and j + 1
    have hterm : ∀ j ∈ range (n + 1),
        (n.choose j : ℝ) * (Dn j f (x + 1 + (n - j)) * Dn (n - j) g (x + 1)) -
          (n.choose j : ℝ) * (Dn j f (x + (n - j)) * Dn (n - j) g x) =
        (n.choose j : ℝ) * (Dn j f (x + (n + 1 - j)) * Dn (n + 1 - j) g x) +
          (n.choose j : ℝ) * (Dn (j + 1) f (x + (n + 1 - (j + 1))) * Dn (n + 1 - (j + 1)) g x) := by
      intro j hj
      simp only [mem_range] at hj
      have e1 : x + 1 + (n - j) = x + (n + 1 - j) := by omega
      have e2 : n + 1 - j = (n - j) + 1 := by omega
      have e3 : n + 1 - (j + 1) = n - j := by omega
      rw [e1, e3, e2, Dn_shift g (n - j) x]
      have e4 : x + ((n - j) + 1) = x + (n - j) + 1 := by omega
      rw [e4, Dn_shift f j (x + (n - j))]
      ring
    rw [sum_congr rfl hterm, sum_add_distrib]
    have key : ∀ T : ℕ → ℝ, ∑ j ∈ range (n + 1), (n.choose j : ℝ) * T j +
        ∑ j ∈ range (n + 1), (n.choose j : ℝ) * T (j + 1) = ∑ j ∈ range (n + 1 + 1), ((n + 1).choose j : ℝ) * T j := by
      intro T
      rw [sum_range_succ' (fun j => ((n + 1).choose j : ℝ) * T j)]
      simp only [Nat.choose_succ_succ', Nat.cast_add, add_mul, sum_add_distrib, Nat.choose_zero_right]
      rw [sum_range_succ' (fun j => (n.choose j : ℝ) * T j), sum_range_succ (fun j => (n.choose (j + 1) : ℝ) * T (j + 1)),
        Nat.choose_succ_self, Nat.cast_zero, zero_mul, add_zero, Nat.choose_zero_right]
      ring
    exact key (fun j => Dn j f (x + (n + 1 - j)) * Dn (n + 1 - j) g x)

end Szkraw
