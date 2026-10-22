import Szkraw.KrawCube
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add

/-!
# The coefficients of `K_{N,r}` at `r = 1` and their `r`-derivative

From `kraw_g_formula`: at `r = 1` a triangle coefficient `g(m,n;k)` is positive exactly when
`m + n + k` is even and at most `2N`, and for `m + n + k` odd its derivative in `r` at `r = 1` is
negative (Proposition 9.8).
-/

namespace Szkraw

open Finset

variable {N : ℕ}

theorem card_symmDiff_add (S T : Finset (Fin N)) :
    (symmDiff S T).card + 2 * (S ∩ T).card = S.card + T.card := by
  have h1 := card_sdiff_add_card_inter S T
  have h2 := card_sdiff_add_card_inter T S
  have hsym : symmDiff S T = (S \ T) ∪ (T \ S) := by rw [symmDiff_def, sup_eq_union]
  rw [hsym, card_union_of_disjoint disjoint_sdiff_sdiff, inter_comm T S] at *
  omega

/-- The interval `{i : a ≤ i < b}` in `Fin N`. -/
def ivl (N a b : ℕ) (h : b ≤ N) : Finset (Fin N) := (Ico a b).attachFin (fun i hi => by
  rw [mem_Ico] at hi; omega)

theorem mem_ivl {a b : ℕ} {h : b ≤ N} (i : Fin N) : i ∈ ivl N a b h ↔ a ≤ i.val ∧ i.val < b := by
  rw [ivl, mem_attachFin, mem_Ico]

theorem card_ivl {a b : ℕ} (h : b ≤ N) : (ivl N a b h).card = b - a := by
  rw [ivl, card_attachFin, Nat.card_Ico]

/-- At `r = 1` only `J = ∅` survives. -/
theorem countP_one (m n : ℕ) (U : Finset (Fin N)) :
    countP N m n U 1 = ∑ S ∈ univ.filter (fun S : Finset (Fin N) => S.card = m),
      ∑ T ∈ univ.filter (fun T : Finset (Fin N) => T.card = n), if symmDiff S T = U then (1 : ℝ) else 0 := by
  rw [countP]
  refine sum_congr rfl fun S _ => sum_congr rfl fun T _ => ?_
  rw [sum_eq_single ∅]
  · simp
  · intro J _ hJ
    have : J.card ≠ 0 := fun h => hJ (card_eq_zero.mp h)
    split_ifs <;> simp [zero_pow this]
  · intro h; exact absurd (empty_mem_powerset _) h

theorem symmDiff_inter_card_le (S T : Finset (Fin N)) : (symmDiff S T).card + (S ∩ T).card ≤ N := by
  have hd : Disjoint (symmDiff S T) (S ∩ T) := by
    rw [disjoint_left]
    intro x hx hx'
    rw [mem_symmDiff] at hx
    rw [mem_inter] at hx'
    tauto
  rw [← card_union_of_disjoint hd]
  calc _ ≤ (univ : Finset (Fin N)).card := card_le_univ _
    _ = N := by simp

/-- At `r = 1` the count vanishes when `m + n + k` is odd or exceeds `2N`. -/
theorem countP_one_zero (m n k : ℕ) (U : Finset (Fin N)) (hU : U.card = k)
    (h : (m + n + k) % 2 = 1 ∨ 2 * N < m + n + k) : countP N m n U 1 = 0 := by
  rw [countP_one]
  refine sum_eq_zero fun S hS => sum_eq_zero fun T hT => ?_
  simp only [mem_filter, mem_univ, true_and] at hS hT
  rw [if_neg]
  intro hST
  have h1 := card_symmDiff_add S T
  have h2 := symmDiff_inter_card_le S T
  rw [hST, hU, hS, hT] at h1
  rw [hST, hU] at h2
  omega

/-- At `r = 1` the count is positive on the remaining triangle triples. -/
theorem countP_one_pos (m n k : ℕ) (hk : k ≤ N) (h1 : m ≤ n + k) (h2 : n ≤ m + k)
    (h3 : k ≤ m + n) (heven : (m + n + k) % 2 = 0) (hle : m + n + k ≤ 2 * N) :
    0 < countP N m n (ivl N 0 k hk) 1 := by
  rw [countP_one]
  set j := (m + n - k) / 2
  have hj : m + n = k + 2 * j := by omega
  have hkj : k + j ≤ N := by omega
  set S := ivl N 0 (m - j) (by omega) ∪ ivl N k (k + j) hkj
  set T := ivl N (m - j) k hk ∪ ivl N k (k + j) hkj
  have hS : S.card = m := by
    rw [card_union_of_disjoint, card_ivl, card_ivl]
    · omega
    · rw [disjoint_left]; intro x hx hx'; rw [mem_ivl] at hx hx'; omega
  have hT : T.card = n := by
    rw [card_union_of_disjoint, card_ivl, card_ivl]
    · omega
    · rw [disjoint_left]; intro x hx hx'; rw [mem_ivl] at hx hx'; omega
  have hsd : symmDiff S T = ivl N 0 k hk := by
    ext x
    simp only [mem_symmDiff, S, T, mem_union, mem_ivl]
    omega
  have hnn : ∀ S' ∈ univ.filter (fun S : Finset (Fin N) => S.card = m),
      0 ≤ ∑ T' ∈ univ.filter (fun T : Finset (Fin N) => T.card = n),
        if symmDiff S' T' = ivl N 0 k hk then (1 : ℝ) else 0 :=
    fun _ _ => sum_nonneg fun _ _ => by split_ifs <;> norm_num
  refine lt_of_lt_of_le ?_ (single_le_sum hnn (mem_filter.mpr ⟨mem_univ S, hS⟩))
  refine lt_of_lt_of_le ?_ (single_le_sum (fun _ _ => by split_ifs <;> norm_num) (mem_filter.mpr ⟨mem_univ T, hT⟩))
  rw [if_pos hsd]; norm_num

theorem sum_le_single_of_nonpos {ι : Type*} [DecidableEq ι] {s : Finset ι} {f : ι → ℝ} {a : ι} (ha : a ∈ s)
    (hf : ∀ x ∈ s, f x ≤ 0) : ∑ x ∈ s, f x ≤ f a := by
  rw [← add_sum_erase s f ha]
  have : ∑ x ∈ s.erase a, f x ≤ 0 := sum_nonpos fun x hx => hf x (mem_of_mem_erase hx)
  linarith

/-- The derivative of `(1 - r)^a r^c` at `r = 1`. -/
def dval (a c : ℕ) : ℝ := if a = 0 then c else if a = 1 then -1 else 0

theorem hasDerivAt_term (a c : ℕ) : HasDerivAt (fun r : ℝ => (1 - r) ^ a * r ^ c) (dval a c) 1 := by
  have h := (((hasDerivAt_id (1 : ℝ)).const_sub 1).pow a).mul (hasDerivAt_pow c (1 : ℝ))
  refine h.congr_deriv ?_
  simp only [id, sub_self, one_pow, mul_one, dval]
  rcases Nat.lt_trichotomy a 1 with h | h | h
  · have : a = 0 := by omega
    subst this; simp
  · subst h; simp
  · rw [if_neg (by omega), if_neg (by omega)]; simp [Pi.pow_apply, show a ≠ 0 by omega, show a - 1 ≠ 0 by omega]

/-- The derivative of the count at `r = 1`. -/
theorem countP_hasDerivAt (m n : ℕ) (U : Finset (Fin N)) :
    HasDerivAt (countP N m n U) (∑ S ∈ univ.filter (fun S : Finset (Fin N) => S.card = m),
      ∑ T ∈ univ.filter (fun T : Finset (Fin N) => T.card = n), ∑ J ∈ (S ∩ T).powerset,
        if symmDiff S T ∪ J = U then dval J.card ((S ∩ T).card - J.card) else 0) 1 := by
  unfold countP
  refine HasDerivAt.fun_sum fun S _ => HasDerivAt.fun_sum fun T _ => HasDerivAt.fun_sum fun J _ => ?_
  split_ifs
  · exact hasDerivAt_term _ _
  · exact hasDerivAt_const _ _

/-- For `m + n + k` odd the derivative at `r = 1` is negative on the triangle. -/
theorem countP_deriv_neg (m n k : ℕ) (hk : k ≤ N) (h1 : m ≤ n + k) (h2 : n ≤ m + k) (h3 : k ≤ m + n)
    (hodd : (m + n + k) % 2 = 1) (hle : m + n + k ≤ 2 * N + 1) :
    (∑ S ∈ univ.filter (fun S : Finset (Fin N) => S.card = m),
      ∑ T ∈ univ.filter (fun T : Finset (Fin N) => T.card = n), ∑ J ∈ (S ∩ T).powerset,
        if symmDiff S T ∪ J = ivl N 0 k hk then dval J.card ((S ∩ T).card - J.card) else 0) < 0 := by
  -- every term is `≤ 0`
  have hterm : ∀ S ∈ univ.filter (fun S : Finset (Fin N) => S.card = m),
      ∀ T ∈ univ.filter (fun T : Finset (Fin N) => T.card = n), ∀ J ∈ (S ∩ T).powerset,
        (if symmDiff S T ∪ J = ivl N 0 k hk then dval J.card ((S ∩ T).card - J.card) else 0) ≤ 0 := by
    intro S hS T hT J hJ
    simp only [mem_filter, mem_univ, true_and] at hS hT
    rw [mem_powerset] at hJ
    split_ifs with hc
    · rw [dval]
      split_ifs with h0 h1'
      · -- `J = ∅` is impossible by parity
        exfalso
        rw [card_eq_zero] at h0
        rw [h0, union_empty] at hc
        have := card_symmDiff_add S T
        rw [hc, card_ivl, hS, hT] at this
        omega
      · norm_num
      · rfl
    · rfl
  -- the witness
  set j := (m + n + 1 - k) / 2
  have hj : m + n + 1 = k + 2 * j := by omega
  have hj1 : 1 ≤ j := by omega
  have hkj : k + j - 1 ≤ N := by omega
  have hk1 : 1 ≤ k := by omega
  set I := ivl N 0 1 (by omega) ∪ ivl N k (k + j - 1) hkj
  set S := ivl N 1 (m - j + 1) (by omega) ∪ I
  set T := ivl N (m - j + 1) k hk ∪ I
  set J := ivl N 0 1 (by omega)
  have hS : S.card = m := by
    rw [card_union_of_disjoint, card_union_of_disjoint, card_ivl, card_ivl, card_ivl]
    · omega
    · rw [disjoint_left]; intro x hx hx'; rw [mem_ivl] at hx hx'; omega
    · rw [disjoint_left]; intro x hx hx'; rw [mem_union, mem_ivl, mem_ivl] at hx'; rw [mem_ivl] at hx; omega
  have hT : T.card = n := by
    rw [card_union_of_disjoint, card_union_of_disjoint, card_ivl, card_ivl, card_ivl]
    · omega
    · rw [disjoint_left]; intro x hx hx'; rw [mem_ivl] at hx hx'; omega
    · rw [disjoint_left]; intro x hx hx'; rw [mem_union, mem_ivl, mem_ivl] at hx'; rw [mem_ivl] at hx; omega
  have hJsub : J ⊆ S ∩ T := by
    intro x hx; simp only [J, mem_ivl] at hx
    simp only [S, T, I, mem_inter, mem_union, mem_ivl]; omega
  have hJc : J.card = 1 := by rw [card_ivl]
  have hcond : symmDiff S T ∪ J = ivl N 0 k hk := by
    ext x
    simp only [mem_union, mem_symmDiff, S, T, I, J, mem_ivl]
    omega
  have hSm : S ∈ univ.filter (fun S : Finset (Fin N) => S.card = m) := mem_filter.mpr ⟨mem_univ _, hS⟩
  have hTn : T ∈ univ.filter (fun T : Finset (Fin N) => T.card = n) := mem_filter.mpr ⟨mem_univ _, hT⟩
  have hJm : J ∈ (S ∩ T).powerset := mem_powerset.mpr hJsub
  have hval : (if symmDiff S T ∪ J = ivl N 0 k hk then dval J.card ((S ∩ T).card - J.card) else 0) = -1 := by
    rw [if_pos hcond, hJc, dval]; simp
  -- the sum is at most the witness term
  have hin : ∀ S' ∈ univ.filter (fun S : Finset (Fin N) => S.card = m),
      ∑ T' ∈ univ.filter (fun T : Finset (Fin N) => T.card = n), ∑ J' ∈ (S' ∩ T').powerset,
        (if symmDiff S' T' ∪ J' = ivl N 0 k hk then dval J'.card ((S' ∩ T').card - J'.card) else 0) ≤ 0 :=
    fun S' hS' => sum_nonpos fun T' hT' => sum_nonpos fun J' hJ' => hterm S' hS' T' hT' J' hJ'
  calc _ ≤ ∑ T' ∈ univ.filter (fun T : Finset (Fin N) => T.card = n), ∑ J' ∈ (S ∩ T').powerset,
        (if symmDiff S T' ∪ J' = ivl N 0 k hk then dval J'.card ((S ∩ T').card - J'.card) else 0) :=
        sum_le_single_of_nonpos (f := fun S' => ∑ T' ∈ univ.filter (fun T : Finset (Fin N) => T.card = n),
          ∑ J' ∈ (S' ∩ T').powerset, (if symmDiff S' T' ∪ J' = ivl N 0 k hk then
            dval J'.card ((S' ∩ T').card - J'.card) else 0)) hSm hin
    _ ≤ ∑ J' ∈ (S ∩ T).powerset,
        (if symmDiff S T ∪ J' = ivl N 0 k hk then dval J'.card ((S ∩ T).card - J'.card) else 0) :=
        sum_le_single_of_nonpos (f := fun T' => ∑ J' ∈ (S ∩ T').powerset, (if symmDiff S T' ∪ J' = ivl N 0 k hk
          then dval J'.card ((S ∩ T').card - J'.card) else 0)) hTn
          fun T' hT' => sum_nonpos fun J' hJ' => hterm S hSm T' hT' J' hJ'
    _ ≤ -1 := by
        rw [← hval]
        exact sum_le_single_of_nonpos (f := fun J' => (if symmDiff S T ∪ J' = ivl N 0 k hk
          then dval J'.card ((S ∩ T).card - J'.card) else 0)) hJm fun J' hJ' => hterm S hSm T hTn J' hJ'
    _ < 0 := by norm_num

theorem kraw_const_pos (m n k : ℕ) (hm : m ≤ N) (hn : n ≤ N) (hk : k ≤ N) :
    0 < ((N.choose k : ℕ) : ℝ) / (((N.choose m : ℕ) : ℝ) * ((N.choose n : ℕ) : ℝ)) := by
  have h1 : (0 : ℝ) < N.choose k := by exact_mod_cast Nat.choose_pos hk
  have h2 : (0 : ℝ) < N.choose m := by exact_mod_cast Nat.choose_pos hm
  have h3 : (0 : ℝ) < N.choose n := by exact_mod_cast Nat.choose_pos hn
  positivity

/-- At `K_{N,1}`: `g(m,n;k) = 0` when `m + n + k` is odd or exceeds `2N`. -/
theorem kraw1_zero (hN : 1 ≤ N) (m : ℕ) (hm : m ≤ N) (n k : Fin (N + 1))
    (h : (m + n.val + k.val) % 2 = 1 ∨ 2 * N < m + n.val + k.val) :
    productMatrix (krawCoefficients N 1) m n k = 0 := by
  rw [kraw_g_formula hN (by norm_num) m hm n k (ivl N 0 k (by omega)) (card_ivl _),
    countP_one_zero m n k _ (by rw [card_ivl]; omega) h, mul_zero]

/-- At `K_{N,1}`: `g(m,n;k) > 0` on the triangle when `m + n + k` is even and at most `2N`. -/
theorem kraw1_pos (hN : 1 ≤ N) (m : ℕ) (hm : m ≤ N) (n k : Fin (N + 1)) (h1 : m ≤ n.val + k.val)
    (h2 : n.val ≤ m + k.val) (h3 : k.val ≤ m + n.val) (heven : (m + n.val + k.val) % 2 = 0)
    (hle : m + n.val + k.val ≤ 2 * N) :
    0 < productMatrix (krawCoefficients N 1) m n k := by
  rw [kraw_g_formula hN (by norm_num) m hm n k (ivl N 0 k (by omega)) (card_ivl _)]
  exact mul_pos (kraw_const_pos m n k hm (by omega) (by omega))
    (countP_one_pos m n k (by omega) h1 h2 h3 heven hle)

/-- For `m + n + k` odd on the triangle, `g(m,n;k)` of `K_{N,r}` has negative `r`-derivative at
`r = 1`. -/
theorem kraw_deriv_neg (hN : 1 ≤ N) (m : ℕ) (hm : m ≤ N) (n k : Fin (N + 1)) (h1 : m ≤ n.val + k.val)
    (h2 : n.val ≤ m + k.val) (h3 : k.val ≤ m + n.val) (hodd : (m + n.val + k.val) % 2 = 1)
    (hle : m + n.val + k.val ≤ 2 * N + 1) :
    ∃ D < 0, HasDerivAt (fun r => productMatrix (krawCoefficients N r) m n k) D 1 := by
  set C := ((N.choose k : ℕ) : ℝ) / (((N.choose m : ℕ) : ℝ) * ((N.choose n : ℕ) : ℝ))
  have hC := kraw_const_pos m n k hm (by omega) (by omega)
  have hD := countP_deriv_neg (N := N) m n k (by omega) h1 h2 h3 hodd hle
  refine ⟨C * _, mul_neg_of_pos_of_neg hC hD, ?_⟩
  have hev : (fun r => productMatrix (krawCoefficients N r) m n k) =ᶠ[nhds 1]
      fun r => C * countP N m n (ivl N 0 k (by omega)) r := by
    filter_upwards [(continuous_const.add continuous_id).continuousAt.eventually_ne (by norm_num : (1 : ℝ) + 1 ≠ 0)]
      with r hr
    exact kraw_g_formula hN hr m hm n k _ (card_ivl _)
  exact ((countP_hasDerivAt m n _).const_mul C).congr_of_eventuallyEq hev

end Szkraw
