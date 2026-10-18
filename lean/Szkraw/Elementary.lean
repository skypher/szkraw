import Szkraw.QuadraticTower
import Mathlib.Tactic.Ring

namespace Szkraw

def qInteger (q : ℝ) : ℕ → ℝ
  | 0 => 0
  | n+1 => qInteger q n + q^n

theorem qInteger_succ (q : ℝ) (n : ℕ) :
    qInteger q (n+1) = 1 + q*qInteger q n := by
  induction n with
  | zero => simp [qInteger]
  | succ n ih =>
      calc
        qInteger q (n+2) = (1+q*qInteger q n)+q^(n+1) := by rw [qInteger, ih]
        _ = 1+q*qInteger q (n+1) := by rw [qInteger, pow_succ]; ring

noncomputable def elementary (p q : ℝ) : (n : ℕ) → ℕ → (tower p q n).Carrier
  | 0, 0 => 1
  | 0, _+1 => 0
  | _+1, 0 => 1
  | n+1, k+1 => ⟨elementary p q n (k+1), elementary p q n k⟩

theorem elementary_zero (p q : ℝ) (n : ℕ) : elementary p q n 0 = 1 := by
  cases n <;> rfl

theorem elementary_above (p q : ℝ) (n k : ℕ) (h : n < k) :
    elementary p q n k = 0 := by
  induction n generalizing k with
  | zero => cases k with
    | zero => omega
    | succ k => rfl
  | succ n ih =>
    cases k with
    | zero => omega
    | succ k =>
      apply QuadraticAlgebra.ext
      · exact ih (k+1) (by omega)
      · exact ih k (by omega)

theorem elementary_one (p q : ℝ) (n : ℕ) :
    elementary p q n 1 = (tower p q n).sum := by
  induction n with
  | zero => rfl
  | succ n ih =>
      apply QuadraticAlgebra.ext
      · exact ih
      · exact elementary_zero p q n

theorem elementary_nonneg (p q : ℝ) (n k : ℕ) :
    towerNonneg p q n (elementary p q n k) := by
  induction n generalizing k with
  | zero =>
    cases k with
    | zero => exact (show (0 : ℝ) ≤ 1 by norm_num)
    | succ k => exact (show (0 : ℝ) ≤ 0 by norm_num)
  | succ n ih =>
    cases k with
    | zero => exact tower_nonneg_one p q (n+1)
    | succ k => exact ⟨ih (k+1), ih k⟩

noncomputable def coordinate (p q : ℝ) :
    (n : ℕ) → (tower p q n).Carrier → (Fin n → Bool) → ℝ
  | 0, x, _ => x
  | n+1, x, b => if b 0 then coordinate p q n x.im (Fin.tail b)
                  else coordinate p q n x.re (Fin.tail b)

def bitsWeight : (n : ℕ) → (Fin n → Bool) → ℕ
  | 0, _ => 0
  | n+1, b => (if b 0 then 1 else 0) + bitsWeight n (Fin.tail b)

theorem coordinate_nonneg (p q : ℝ) (n : ℕ) (x : (tower p q n).Carrier)
    (hx : towerNonneg p q n x) (b : Fin n → Bool) :
    0 ≤ coordinate p q n x b := by
  induction n with
  | zero => exact hx
  | succ n ih =>
      simp only [coordinate]
      split
      · exact ih x.im hx.2 _
      · exact ih x.re hx.1 _

theorem coordinate_zero (p q : ℝ) (n : ℕ) (b : Fin n → Bool) :
    coordinate p q n 0 b = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [coordinate]
      split <;> exact ih _

theorem coordinate_add (p q : ℝ) (n : ℕ) (x y : (tower p q n).Carrier)
    (b : Fin n → Bool) :
    coordinate p q n (x+y) b = coordinate p q n x b + coordinate p q n y b := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [coordinate]
      split <;> exact ih _ _ _

theorem coordinate_smul (p q r : ℝ) (n : ℕ) (x : (tower p q n).Carrier)
    (b : Fin n → Bool) :
    coordinate p q n (r • x) b = r * coordinate p q n x b := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [coordinate]
      split <;> exact ih _ _

theorem coordinate_elementary (p q : ℝ) (n k : ℕ) (b : Fin n → Bool) :
    coordinate p q n (elementary p q n k) b = if k = bitsWeight n b then 1 else 0 := by
  induction n generalizing k with
  | zero => cases k <;> rfl
  | succ n ih =>
      have hre : (1 : (tower p q (n+1)).Carrier).re = (1 : (tower p q n).Carrier) := rfl
      have him : (1 : (tower p q (n+1)).Carrier).im = (0 : (tower p q n).Carrier) := rfl
      cases k with
      | zero =>
          cases hb : b 0 with
          | false =>
              simpa [elementary_zero, coordinate, bitsWeight, hb, hre]
                using ih 0 (Fin.tail b)
          | true =>
              have hneq : ¬ (0 = 1 + bitsWeight n (Fin.tail b)) := by omega
              simp [elementary_zero, coordinate, bitsWeight, hb,
                him, coordinate_zero, hneq]
      | succ k =>
          cases hb : b 0 with
          | false => simpa [elementary, coordinate, bitsWeight, hb] using ih (k+1) (Fin.tail b)
          | true =>
              have heq : k+1 = 1+bitsWeight n (Fin.tail b) ↔ k = bitsWeight n (Fin.tail b) := by omega
              simpa [elementary, coordinate, bitsWeight, hb, heq] using ih k (Fin.tail b)

theorem bitsWeight_exists (n k : ℕ) (hk : k ≤ n) :
    ∃ b : Fin n → Bool, bitsWeight n b = k := by
  induction n generalizing k with
  | zero =>
      have : k = 0 := by omega
      subst k
      exact ⟨fun i => Fin.elim0 i, rfl⟩
  | succ n ih =>
      cases k with
      | zero =>
          obtain ⟨b,hb⟩ := ih 0 (by omega)
          exact ⟨Fin.cons false b, by simpa [bitsWeight] using hb⟩
      | succ k =>
          obtain ⟨b,hb⟩ := ih k (by omega)
          exact ⟨Fin.cons true b, by simp [bitsWeight, hb, Nat.add_comm]⟩

theorem coordinate_sum {ι : Type*} (p q : ℝ) (n : ℕ) (s : Finset ι)
    (f : ι → (tower p q n).Carrier) (b : Fin n → Bool) :
    coordinate p q n (∑ i ∈ s, f i) b = ∑ i ∈ s, coordinate p q n (f i) b := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [coordinate_zero]
  | @insert i s hi ih => simp only [Finset.sum_insert hi, coordinate_add, ih]

theorem elementary_coefficients_nonneg (p q : ℝ) (n : ℕ)
    (g : Fin (n+1) → ℝ)
    (hg : towerNonneg p q n (∑ k : Fin (n+1), g k • elementary p q n k.val)) :
    ∀ k, 0 ≤ g k := by
  intro k
  obtain ⟨b,hb⟩ := bitsWeight_exists n k.val (by omega)
  have h := coordinate_nonneg p q n _ hg b
  rw [coordinate_sum] at h
  simpa [coordinate_smul, coordinate_elementary, hb, Fin.val_inj] using h

end Szkraw
