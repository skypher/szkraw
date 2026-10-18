import Szkraw.Parameters
import Szkraw.NormalizedRecurrence

namespace Szkraw

theorem sum_nat_delta {A : Type*} [AddCommMonoid A] [Module ℝ A]
    (N t : ℕ) (s : ℝ) (U : ℕ → A) (hU : ∀ j, N < j → U j = 0) :
    (∑ j : Fin (N+1), (if j.val = t then s else 0) • U j.val) = s • U t := by
  classical
  by_cases ht : t ≤ N
  · let it : Fin (N+1) := ⟨t,by omega⟩
    have hc : ∀ j : Fin (N+1), j.val = t ↔ j = it := by
      intro j
      change j.val = it.val ↔ j = it
      exact Fin.val_inj
    simp [hc, it]
  · have hc : ∀ j : Fin (N+1), j.val ≠ t := by intro j; have := j.isLt; omega
    simp [hc,hU t (by omega)]

theorem recurrence_entry_decomposition {N : ℕ} (v : Coefficients N)
    (i j : Fin (N+1)) : recurrenceMatrix v i j =
      (if j.val = i.val+1 then v.a i.val else 0) +
      (if j = i then v.b i.val else 0) +
      (if i.val = j.val+1 then v.c i.val else 0) := by
  by_cases h1 : j.val = i.val+1
  · have h2 : j ≠ i := by intro h; have := congrArg Fin.val h; omega
    have h3 : i.val ≠ j.val+1 := by omega
    simp only [recurrenceMatrix, if_pos h1, if_neg h2, if_neg h3, add_zero]
  · by_cases h2 : j = i
    · subst j
      simp [recurrenceMatrix]
    · simp [recurrenceMatrix,h1,h2]

theorem recurrence_row_action {N : ℕ} {A : Type*} [AddCommMonoid A] [Module ℝ A]
    (v : Coefficients N) (U : ℕ → A) (hU : ∀ j, N < j → U j = 0)
    (i : Fin (N+1)) :
    (∑ j : Fin (N+1), recurrenceMatrix v i j • U j.val) =
      v.a i.val • U (i.val+1) + v.b i.val • U i.val +
      (if i.val = 0 then 0 else v.c i.val • U (i.val-1)) := by
  classical
  simp_rw [recurrence_entry_decomposition, add_smul, Finset.sum_add_distrib]
  rw [sum_nat_delta N (i.val+1) (v.a i.val) U hU]
  have hd : (∑ j : Fin (N+1), (if j = i then v.b i.val else 0) • U j.val) =
      v.b i.val • U i.val := by simp
  rw [hd]
  congr 1
  by_cases hi : i.val = 0
  · have hc : ∀ j : Fin (N+1), ¬ (i.val = j.val+1) := by intro j; omega
    simp [hi,hc]
  · have hc : ∀ j : Fin (N+1), i.val = j.val+1 ↔ j.val = i.val-1 := by
      intro j
      omega
    simp_rw [hc]
    rw [sum_nat_delta N (i.val-1) (v.c i.val) U hU]
    simp [hi]

theorem normalized_elementary_above (p q : ℝ) (N k : ℕ) (hk : N < k) :
    normalizedElementary p q N k = 0 := by
  simp [normalizedElementary, elementary_above p q N k hk]

theorem geometric_row_action (p q : ℝ) (hp : 1 ≤ p) (hq : 1 ≤ q)
    (N : ℕ) (hN : 1 ≤ N) (i : Fin (N+1)) :
    normalizedElementary p q N 1 * normalizedElementary p q N i.val =
      ∑ j : Fin (N+1), recurrenceMatrix (geometricCoefficients N p q) i j •
        normalizedElementary p q N j.val := by
  rw [recurrence_row_action (geometricCoefficients N p q)
    (normalizedElementary p q N) (fun j hj => normalized_elementary_above p q N j hj)]
  cases hi : i.val with
  | zero =>
      have hQN := ne_of_gt (qInteger_pos q hq N (by omega))
      simp [geometricCoefficients, hi, qInteger, hQN, normalized_elementary_zero]
  | succ k =>
      have hk : k+1 ≤ N := by have := i.isLt; omega
      simpa [geometricCoefficients, hi] using normalized_three_term p q hp hq N k hk

end Szkraw
