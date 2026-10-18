import Szkraw.BooleanCoordinates

namespace Szkraw

/-- Select one squarefree coordinate and one positive reduction term, uniformly in size. -/
theorem boolean_margin_exists (r : ℝ) (hr : 0 < r) (hr1 : r < 1)
    (N m n k : ℕ) (hm : m ≤ N) (hn : n ≤ N) (hk : k ≤ N)
    (ht : Triangle m n k) :
    ∃ b : Fin N → Bool, bitsWeight N b = k ∧
      (min r (1-r))^N ≤ booleanProduct r N m n b := by
  let s := min r (1-r)
  have hs0 : 0 ≤ s := le_min (le_of_lt hr) (by linarith)
  have hs1 : s ≤ 1 := (min_le_left _ _).trans (le_of_lt hr1)
  have hsr : s ≤ r := min_le_left _ _
  have hst : s ≤ 1-r := min_le_right _ _
  have hnon := boolean_product_nonneg r hr (le_of_lt hr1)
  induction N generalizing m n k with
  | zero =>
      have hm0 : m = 0 := by omega
      have hn0 : n = 0 := by omega
      have hk0 : k = 0 := by omega
      subst m; subst n; subst k
      refine ⟨fun i => Fin.elim0 i,rfl,?_⟩
      simp [booleanProduct,elementary,coordinate,bitsWeight]
  | succ N ih =>
      have hstep (c x : ℝ) (hc : s ≤ c) (hx : s^N ≤ x) : s^(N+1) ≤ c*x := by
        rw [pow_succ]
        exact (mul_le_mul hx hc hs0 ((pow_nonneg hs0 N).trans hx)).trans_eq (mul_comm _ _)
      have hweak (x : ℝ) (hx : s^N ≤ x) : s^(N+1) ≤ x := by
        simpa only [one_mul] using hstep 1 x hs1 hx
      by_cases hm0 : m = 0
      · subst m
        have hnK : n = k := by dsimp [Triangle] at ht; omega
        obtain ⟨b,hb⟩ := bitsWeight_exists (N+1) k hk
        refine ⟨b,hb,?_⟩
        rw [boolean_product_zero_left r hr,hnK,if_pos hb.symm]
        exact pow_le_one₀ hs0 hs1
      · by_cases hn0 : n = 0
        · subst n
          have hmK : m = k := by dsimp [Triangle] at ht; omega
          obtain ⟨b,hb⟩ := bitsWeight_exists (N+1) k hk
          refine ⟨b,hb,?_⟩
          rw [boolean_product_comm,boolean_product_zero_left r hr,hmK,if_pos hb.symm]
          exact pow_le_one₀ hs0 hs1
        · obtain ⟨a,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm0
          obtain ⟨d,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn0
          cases k with
          | zero =>
              have htd : Triangle a d 0 := by dsimp [Triangle] at *; omega
              obtain ⟨b,hb,hpos⟩ := ih a d 0 (by omega) (by omega) (by omega) htd
              refine ⟨Fin.cons false b,by simpa [bitsWeight] using hb,?_⟩
              rw [boolean_product_false r hr]
              have hw := hstep r _ hsr hpos
              have hother := hnon N (a+1) (d+1) b
              linarith
          | succ k =>
              have hcases :
                  (a+1 ≤ N ∧ d+1 ≤ N ∧ k+1 ≤ N ∧ Triangle (a+1) (d+1) (k+1)) ∨
                  (a ≤ N ∧ d ≤ N ∧ k+1 ≤ N ∧ Triangle a d (k+1)) ∨
                  (a+1 ≤ N ∧ d ≤ N ∧ k ≤ N ∧ Triangle (a+1) d k) ∨
                  (a ≤ N ∧ d+1 ≤ N ∧ k ≤ N ∧ Triangle a (d+1) k) ∨
                  (a ≤ N ∧ d ≤ N ∧ k ≤ N ∧ Triangle a d k) := by
                dsimp [Triangle] at *
                omega
              rcases hcases with h|h|h|h|h
              · obtain ⟨b,hb,hpos⟩ := ih (a+1) (d+1) (k+1) h.1 h.2.1 h.2.2.1 h.2.2.2
                refine ⟨Fin.cons false b,by simpa [bitsWeight] using hb,?_⟩
                rw [boolean_product_false r hr]
                have hw := hweak _ hpos
                have ho := mul_nonneg (le_of_lt hr) (hnon N a d b)
                linarith
              · obtain ⟨b,hb,hpos⟩ := ih a d (k+1) h.1 h.2.1 h.2.2.1 h.2.2.2
                refine ⟨Fin.cons false b,by simpa [bitsWeight] using hb,?_⟩
                rw [boolean_product_false r hr]
                have hw := hstep r _ hsr hpos
                have ho := hnon N (a+1) (d+1) b
                linarith
              · obtain ⟨b,hb,hpos⟩ := ih (a+1) d k h.1 h.2.1 h.2.2.1 h.2.2.2
                refine ⟨Fin.cons true b,by simp [bitsWeight,hb,Nat.add_comm],?_⟩
                rw [boolean_product_true r hr]
                have hw := hweak _ hpos
                have ho := hnon N a (d+1) b
                have ho' := mul_nonneg (by linarith : 0 ≤ 1-r) (hnon N a d b)
                linarith
              · obtain ⟨b,hb,hpos⟩ := ih a (d+1) k h.1 h.2.1 h.2.2.1 h.2.2.2
                refine ⟨Fin.cons true b,by simp [bitsWeight,hb,Nat.add_comm],?_⟩
                rw [boolean_product_true r hr]
                have hw := hweak _ hpos
                have ho := hnon N (a+1) d b
                have ho' := mul_nonneg (by linarith : 0 ≤ 1-r) (hnon N a d b)
                linarith
              · obtain ⟨b,hb,hpos⟩ := ih a d k h.1 h.2.1 h.2.2.1 h.2.2.2
                refine ⟨Fin.cons true b,by simp [bitsWeight,hb,Nat.add_comm],?_⟩
                rw [boolean_product_true r hr]
                have hw := hstep (1-r) _ hst hpos
                have ho := hnon N (a+1) d b
                have ho' := hnon N a (d+1) b
                linarith

end Szkraw
