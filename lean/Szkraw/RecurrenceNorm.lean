import Szkraw.RowNorm

open scoped Matrix.Norms.Operator

namespace Szkraw

theorem sum_nat_indicator_le (N t : ℕ) (s : ℝ) (hs : 0 ≤ s) :
    (∑ j : Fin (N+1), if j.val = t then s else 0) ≤ s := by
  classical
  by_cases ht : t ≤ N
  · let it : Fin (N+1) := ⟨t,by omega⟩
    have hh (j : Fin (N+1)) : j.val = t ↔ j = it := by
      change j.val = it.val ↔ j = it
      exact Fin.val_inj
    simp [hh]
  · have hh (j : Fin (N+1)) : j.val ≠ t := by have := j.isLt; omega
    simpa [hh] using hs

theorem recurrence_abs_row_le {N : ℕ} (v : Coefficients N) (i : Fin (N+1)) :
    (∑ j, |recurrenceMatrix v i j|) ≤ |v.a i.val|+|v.b i.val|+|v.c i.val| := by
  classical
  have hentry (j : Fin (N+1)) : |recurrenceMatrix v i j| ≤
      (if j.val = i.val+1 then |v.a i.val| else 0) +
      (if j = i then |v.b i.val| else 0) +
      (if i.val = j.val+1 then |v.c i.val| else 0) := by
    simp only [recurrenceMatrix]
    split_ifs <;> norm_num <;> nlinarith [abs_nonneg (v.a i.val),abs_nonneg (v.b i.val),abs_nonneg (v.c i.val)]
  have hs := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hentry j)
  simp only [Finset.sum_add_distrib] at hs
  have ha := sum_nat_indicator_le N (i.val+1) |v.a i.val| (abs_nonneg _)
  have hb : (∑ j : Fin (N+1), if j = i then |v.b i.val| else 0) = |v.b i.val| := by simp
  have hc : (∑ j : Fin (N+1), if i.val = j.val+1 then |v.c i.val| else 0) ≤ |v.c i.val| := by
    by_cases hi : i.val = 0
    · have hh (j : Fin (N+1)) : i.val ≠ j.val+1 := by omega
      simpa [hh] using abs_nonneg (v.c i.val)
    · have hh (j : Fin (N+1)) : i.val = j.val+1 ↔ j.val = i.val-1 := by omega
      simp_rw [hh]
      exact sum_nat_indicator_le N (i.val-1) |v.c i.val| (abs_nonneg _)
  linarith

theorem recurrence_difference_norm {N : ℕ} (v w : Coefficients N)
    (η : ℝ) (hη : 0 ≤ η)
    (h : ∀ i, i ≤ N → |w.a i-v.a i| ≤ η ∧ |w.b i-v.b i| ≤ η ∧ |w.c i-v.c i| ≤ η) :
    ‖recurrenceMatrix w-recurrenceMatrix v‖ ≤ 3*η := by
  let d : Coefficients N := ⟨fun i => w.a i-v.a i,fun i => w.b i-v.b i,fun i => w.c i-v.c i⟩
  have hd : recurrenceMatrix w-recurrenceMatrix v = recurrenceMatrix d := by
    ext i j
    simp only [Matrix.sub_apply,recurrenceMatrix]
    dsimp [d]
    split_ifs <;> ring
  rw [hd]
  apply row_norm_le _ _ (by positivity)
  intro i
  have hh := recurrence_abs_row_le d i
  have hi := h i.val (by omega)
  dsimp [d] at hh
  linarith [hi.1,hi.2.1,hi.2.2]

theorem admissible_sign_bounds {N : ℕ} (v : Coefficients N) (hv : Admissible v)
    (hb : ∀ i, i ≤ N → 0 ≤ v.b i) (i : ℕ) (hi : i ≤ N) :
    0 ≤ v.a i ∧ 0 ≤ v.c i ∧ v.b i ≤ 1 ∧ v.c i ≤ 1 := by
  have ha : 0 ≤ v.a i := by
    by_cases hh : i = N
    · rw [hh,hv.2.2.2.2.1]
    · exact le_of_lt (hv.2.2.2.2.2.2.1 i (by omega))
  have hc : 0 ≤ v.c i := by
    by_cases hh : i = 0
    · rw [hh,hv.2.2.2.1]
    · exact le_of_lt (hv.2.2.2.2.2.2.2 i (by omega) hi)
  have hs := hv.2.2.2.2.2.1 i hi
  have hb0 := hb i hi
  exact ⟨ha,hc,by linarith,by linarith⟩

theorem admissible_recurrence_norm {N : ℕ} (v : Coefficients N) (hv : Admissible v)
    (hb : ∀ i, i ≤ N → 0 ≤ v.b i) : ‖recurrenceMatrix v‖ ≤ 1 := by
  apply stochastic_norm_le _ _ (recurrence_row_sum v hv)
  intro i j
  have hs := admissible_sign_bounds v hv hb i.val (by omega)
  dsimp [recurrenceMatrix]
  split_ifs <;> first | exact hs.1 | exact hb i.val (by omega) | exact hs.2.1 | positivity

end Szkraw
