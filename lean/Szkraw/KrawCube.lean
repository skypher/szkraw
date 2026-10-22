import Szkraw.EdgeIdempotents
import Szkraw.LCAssembly
import Szkraw.Krawtchouk
import Szkraw.RowZero
import Szkraw.Representation

/-!
# The Krawtchouk system in the quadratic algebra

In a commutative algebra with `y_j^2 = (1 - r) y_j + r`, squarefree monomials multiply by
`y_S y_T = Σ_{J ⊆ S ∩ T} (1-r)^{|J|} r^{|S∩T| - |J|} y_{(S Δ T) ∪ J}`, and the normalized
elementary sums `U_k = C(N,k)⁻¹ Σ_{|S| = k} y_S` satisfy the three-term relation of `K_{N,r}`
with `X = U_1`. Comparing coefficients gives `g(m, n; k)` of `K_{N,r}` as an explicit count.
-/

namespace Szkraw

open Finset

section algebra

variable {N : ℕ} {A : Type*} [CommRing A] [Algebra ℝ A] {r : ℝ} {y : Fin N → A}

omit [Algebra ℝ A] in
theorem ySet_union {S T : Finset (Fin N)} (h : Disjoint S T) : ySet y (S ∪ T) = ySet y S * ySet y T :=
  prod_union h

/-- `y_I^2 = Σ_{J ⊆ I} (1-r)^{|J|} r^{|I| - |J|} y_J`. -/
theorem ySet_sq (hy : QuadRel r y) (I : Finset (Fin N)) :
    ySet y I * ySet y I = ∑ J ∈ I.powerset, ((1 - r) ^ J.card * r ^ (I.card - J.card)) • ySet y J := by
  have h1 : ySet y I * ySet y I = ∏ i ∈ I, ((1 - r) • y i + algebraMap ℝ A r) := by
    rw [ySet, ← prod_mul_distrib]; exact prod_congr rfl fun i _ => hy i
  rw [h1, prod_add]
  refine sum_congr rfl fun J hJ => ?_
  rw [mem_powerset] at hJ
  rw [prod_const, card_sdiff_of_subset hJ]
  simp only [Algebra.smul_def, prod_mul_distrib, prod_const, ySet, map_mul, map_pow]
  ring

/-- `y_S y_T = Σ_{J ⊆ S ∩ T} (1-r)^{|J|} r^{|S∩T| - |J|} y_{(S Δ T) ∪ J}`. -/
theorem ySet_mul (hy : QuadRel r y) (S T : Finset (Fin N)) :
    ySet y S * ySet y T = ∑ J ∈ (S ∩ T).powerset,
      ((1 - r) ^ J.card * r ^ ((S ∩ T).card - J.card)) • ySet y (symmDiff S T ∪ J) := by
  have hd1 : Disjoint (S \ T) (S ∩ T) := disjoint_sdiff_inter S T
  have hd2 : Disjoint (T \ S) (S ∩ T) := by rw [inter_comm]; exact disjoint_sdiff_inter T S
  have hd3 : Disjoint (S \ T) (T \ S) := disjoint_sdiff_sdiff
  have hsym : symmDiff S T = (S \ T) ∪ (T \ S) := by rw [symmDiff_def, sup_eq_union]
  have eS : ySet y S = ySet y (S \ T) * ySet y (S ∩ T) := by rw [← ySet_union hd1, sdiff_union_inter]
  have eT : ySet y T = ySet y (T \ S) * ySet y (S ∩ T) := by
    rw [← ySet_union hd2, inter_comm, sdiff_union_inter]
  have e : ySet y S * ySet y T = ySet y (symmDiff S T) * (ySet y (S ∩ T) * ySet y (S ∩ T)) := by
    rw [eS, eT, hsym, ySet_union hd3]; ring
  rw [e, ySet_sq hy, mul_sum]
  refine sum_congr rfl fun J hJ => ?_
  rw [mem_powerset] at hJ
  have hdJ : Disjoint (symmDiff S T) J := by
    rw [hsym]
    exact disjoint_union_left.mpr ⟨disjoint_of_subset_right hJ hd1, disjoint_of_subset_right hJ hd2⟩
  rw [mul_smul_comm, ySet_union hdJ]

theorem levelSum_zero : levelSum (N := N) y 0 = 1 := by
  rw [levelSum]
  have : univ.filter (fun S : Finset (Fin N) => S.card = 0) = {∅} := by
    ext S; simp [card_eq_zero]
  rw [this, sum_singleton, ySet, prod_empty]

theorem levelSum_top (k : ℕ) (hk : N < k) : levelSum (N := N) y k = 0 := by
  apply sum_eq_zero
  intro S hS
  simp only [mem_filter, mem_univ, true_and] at hS
  have := card_le_univ S
  rw [Fintype.card_fin] at this; omega

/-- `Σ_j y_j · Σ_{|S| = k} y_S = (k+1) e_{k+1} + (1-r) k e_k + r (N - k + 1) e_{k-1}` for `k ≥ 1`. -/
theorem sum_y_mul_levelSum (hy : QuadRel r y) (k : ℕ) (hk : 1 ≤ k) :
    (∑ j, y j) * levelSum y k = ((k + 1 : ℕ) : ℝ) • levelSum y (k + 1) + ((1 - r) * k) • levelSum y k +
      (r * ((N - (k - 1) : ℕ) : ℝ)) • levelSum y (k - 1) := by
  rw [sum_mul]
  -- split each `S` by `j ∉ S` / `j ∈ S`
  have hsplit : ∀ j : Fin N, y j * levelSum y k =
      ∑ S ∈ univ.filter (fun S : Finset (Fin N) => j ∉ S ∧ S.card = k), ySet y (insert j S) +
        ((1 - r) • ∑ S ∈ univ.filter (fun S : Finset (Fin N) => j ∈ S ∧ S.card = k), ySet y S +
          r • ∑ S ∈ univ.filter (fun S : Finset (Fin N) => j ∉ S ∧ S.card = k - 1), ySet y S) := by
    intro j
    rw [levelSum, mul_sum, ← sum_filter_add_sum_filter_not _ (fun S => j ∉ S)]
    congr 1
    · rw [filter_filter]
      refine sum_congr (by ext S; simp [and_comm]) fun S hS => ?_
      simp only [mem_filter, mem_univ, true_and] at hS
      rw [ySet, ySet, prod_insert hS.1]
    · rw [filter_filter]
      have e : ∀ S ∈ univ.filter (fun S : Finset (Fin N) => S.card = k ∧ ¬j ∉ S), y j * ySet y S =
          (1 - r) • ySet y S + r • ySet y (S.erase j) := by
        intro S hS
        simp only [mem_filter, mem_univ, true_and, not_not] at hS
        have hS' : ySet y S = y j * ySet y (S.erase j) := (mul_prod_erase S y hS.2).symm
        rw [hS', ← mul_assoc, hy j, add_mul, smul_mul_assoc, ← Algebra.smul_def]
      rw [sum_congr rfl e, sum_add_distrib, ← smul_sum, ← smul_sum]
      congr 2
      · exact sum_congr (by ext S; simp [and_comm]) fun _ _ => rfl
      · apply sum_nbij' (fun S => S.erase j) (fun T => insert j T)
        · intro S hS
          simp only [mem_filter, mem_univ, true_and, not_not] at hS ⊢
          exact ⟨notMem_erase j S, by rw [card_erase_of_mem hS.2, hS.1]⟩
        · intro T hT
          simp only [mem_filter, mem_univ, true_and, not_not] at hT ⊢
          exact ⟨by rw [card_insert_of_notMem hT.1, hT.2]; omega, mem_insert_self j T⟩
        · intro S hS; simp only [mem_filter, mem_univ, true_and, not_not] at hS; exact insert_erase hS.2
        · intro T hT; simp only [mem_filter, mem_univ, true_and] at hT; exact erase_insert hT.1
        · intro _ _; rfl
  rw [sum_congr rfl fun j _ => hsplit j, sum_add_distrib, sum_add_distrib, ← smul_sum, ← smul_sum,
    count_in (n := k), count_out (n := k - 1)]
  have hin : ∑ j : Fin N, ∑ S ∈ univ.filter (fun S : Finset (Fin N) => j ∈ S ∧ S.card = k), ySet y S =
      (k : ℝ) • levelSum y k := by
    simp_rw [sum_filter]
    rw [sum_comm, levelSum, sum_filter, smul_sum]
    refine sum_congr rfl fun S _ => ?_
    split_ifs with h
    · rw [sum_congr rfl (fun l _ => if_congr (and_iff_left h) rfl rfl), ← sum_filter, sum_const,
        ← Nat.cast_smul_eq_nsmul ℝ]
      have : univ.filter (fun l => l ∈ S) = S := by ext; simp
      rw [this, h]
    · rw [smul_zero]; exact sum_eq_zero (fun l _ => if_neg (fun h' => h h'.2))
  rw [hin, smul_smul, smul_smul, add_assoc]

theorem levelSum_one : levelSum (N := N) y 1 = ∑ j, y j := by
  have h : univ.filter (fun S : Finset (Fin N) => S.card = 1) = powersetCard 1 univ := by
    rw [powersetCard_eq_filter, powerset_univ]
  rw [levelSum, h, powersetCard_one, sum_map]
  simp [ySet]

end algebra

/-- The module form of a row of the recurrence matrix. -/
theorem J_smul_apply {N : ℕ} {M : Type*} [AddCommGroup M] [Module ℝ M] (v : Coefficients N) (F : ℕ → M)
    (i : Fin (N + 1)) :
    ∑ k : Fin (N + 1), recurrenceMatrix v i k • F k.val =
      (if i.val + 1 ≤ N then v.a i • F (i + 1) else 0) + v.b i • F i +
        (if 1 ≤ i.val then v.c i • F (i - 1) else 0) := by
  simp_rw [J_entry, add_smul, sum_add_distrib, ite_smul, zero_smul]
  rw [Fin.sum_univ_eq_sum_range (fun l => if l = i.val + 1 then v.a i • F l else 0) (N + 1),
    Fin.sum_univ_eq_sum_range (fun l => if l = i.val then v.b i • F l else 0) (N + 1),
    Fin.sum_univ_eq_sum_range (fun l => if l + 1 = i.val then v.c i • F l else 0) (N + 1),
    sum_ite_eq' (range (N + 1)) (i.val + 1), sum_ite_eq' (range (N + 1)) i.val]
  simp only [mem_range]
  congr 1
  · congr 1
    · split_ifs <;> first | rfl | omega
    · rw [if_pos i.isLt]
  · rcases Nat.eq_zero_or_pos i.val with h0 | hpos
    · rw [if_neg (by omega)]
      exact sum_eq_zero fun l _ => if_neg (by omega)
    · rw [if_pos (by omega), sum_eq_single (i.val - 1)]
      · rw [if_pos (by omega)]
      · intro l _ hl; rw [if_neg (by omega)]
      · intro h; exact absurd (mem_range.mpr (by omega)) h

section kraw

variable {N : ℕ} {A : Type*} [CommRing A] [Algebra ℝ A] {r : ℝ} {y : Fin N → A}

variable (y) in
/-- `U_k = C(N,k)⁻¹ Σ_{|S| = k} y_S`. -/
noncomputable def Ukr (k : ℕ) : A := ((N.choose k : ℕ) : ℝ)⁻¹ • levelSum y k

/-- The three-term action of `K_{N,r}`: `U_1 U_k = a_k U_{k+1} + b_k U_k + c_k U_{k-1}`. -/
theorem kraw_action (hy : QuadRel r y) (hN : 1 ≤ N) (k : ℕ) (hk : k ≤ N) :
    Ukr y 1 * Ukr y k = (krawCoefficients N r).a k • Ukr y (k + 1) + (krawCoefficients N r).b k • Ukr y k +
      (krawCoefficients N r).c k • Ukr y (k - 1) := by
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  simp only [Ukr, krawCoefficients, Nat.choose_one_right, levelSum_one]
  rcases Nat.eq_zero_or_pos k with h0 | hpos
  · subst h0
    simp only [Nat.choose_zero_right, Nat.cast_one, inv_one, one_smul, levelSum_zero, mul_one, zero_add,
      Nat.cast_zero, sub_zero, div_one, mul_zero, zero_div, zero_smul, add_zero, Nat.zero_sub]
    rw [div_self hN0, one_smul, levelSum_one, Nat.choose_one_right]
  · rw [smul_mul_smul_comm, sum_y_mul_levelSum hy k hpos]
    have hC : (0 : ℝ) < N.choose k := by exact_mod_cast Nat.choose_pos hk
    have hC1 : (0 : ℝ) < N.choose (k - 1) := by exact_mod_cast Nat.choose_pos (by omega)
    have e1 : (N.choose (k + 1) : ℝ) * ((k + 1 : ℕ) : ℝ) = N.choose k * ((N - k : ℕ) : ℝ) := by
      exact_mod_cast Nat.choose_succ_right_eq N k
    have e2 : (N.choose k : ℝ) * (k : ℝ) = N.choose (k - 1) * ((N - (k - 1) : ℕ) : ℝ) := by
      have := Nat.choose_succ_right_eq N (k - 1)
      rw [show k - 1 + 1 = k by omega] at this
      exact_mod_cast this
    rw [Nat.cast_sub hk] at e1
    rw [smul_add, smul_add, smul_smul, smul_smul, smul_smul]
    congr 1
    congr 1
    · -- the `U_{k+1}` term
      rcases Nat.lt_or_ge k N with hlt | hge
      · rw [smul_smul]
        have hC2 : (0 : ℝ) < N.choose (k + 1) := by exact_mod_cast Nat.choose_pos (by omega)
        congr 1
        field_simp
        linear_combination e1
      · simp [levelSum_top (y := y) (k + 1) (by omega)]
    · rw [smul_smul]; congr 1; field_simp
    · rw [smul_smul]
      congr 1
      field_simp
      linear_combination -r * e2

theorem Ukr_zero : Ukr (N := N) y 0 = 1 := by simp [Ukr, levelSum_zero]

theorem kraw_one_a_ne' (i : ℕ) (hi : i < N) : (krawCoefficients N r).a i ≠ 0 := by
  simp only [krawCoefficients]
  have : (i : ℝ) < N := by exact_mod_cast hi
  exact (div_pos (by linarith) (by linarith)).ne'

/-- `U_m U_n = Σ_l g(m,n;l) U_l` for `K_{N,r}`. -/
theorem kraw_product_alg (hy : QuadRel r y) (hN : 1 ≤ N) (m : ℕ) (hm : m ≤ N) (n : Fin (N + 1)) :
    Ukr y m * Ukr y n = ∑ l : Fin (N + 1), productMatrix (krawCoefficients N r) m n l • Ukr y l := by
  have hJ : ∀ i : Fin (N + 1), Ukr y 1 * Ukr y i = ∑ j, recurrenceMatrix (krawCoefficients N r) i j • Ukr y j := by
    intro i
    rw [J_smul_apply (krawCoefficients N r) (fun k => Ukr y k) i, kraw_action hy hN i (by omega)]
    have ha : (if i.val + 1 ≤ N then (krawCoefficients N r).a i • Ukr y (i + 1) else 0) =
        (krawCoefficients N r).a i • Ukr y (i + 1) := by
      split_ifs with h
      · rfl
      · rw [show (krawCoefficients N r).a i = 0 by simp [krawCoefficients, show i.val = N by omega], zero_smul]
    have hc : (if 1 ≤ i.val then (krawCoefficients N r).c i • Ukr y (i - 1) else 0) =
        (krawCoefficients N r).c i • Ukr y (i - 1) := by
      split_ifs with h
      · rfl
      · rw [show (krawCoefficients N r).c i = 0 by simp [krawCoefficients, show i.val = 0 by omega], zero_smul]
    rw [ha, hc]
  have hrep := fun j => representation_product (krawCoefficients N r) (fun i => Ukr y i) (Ukr y 1) hJ m j
  have hm' : Polynomial.aeval (Ukr y 1) (recurrencePolynomial (krawCoefficients N r) m) = Ukr y m := by
    have h := hrep 0
    simp only [Fin.val_zero, Ukr_zero, mul_one] at h
    rw [h, sum_eq_single ⟨m, by omega⟩]
    · rw [row_zero _ kraw_one_a_ne' m hm]; simp
    · intro k _ hk; rw [row_zero _ kraw_one_a_ne' m hm, if_neg (fun h => hk (Fin.ext h)), zero_smul]
    · intro h; exact absurd (mem_univ _) h
  rw [← hm']
  exact hrep n

/-- The count `Σ_{|S|=m, |T|=n, J ⊆ S ∩ T, (S Δ T) ∪ J = U} (1-r)^{|J|} r^{|S∩T| - |J|}`. -/
noncomputable def countP (N m n : ℕ) (U : Finset (Fin N)) (r : ℝ) : ℝ :=
  ∑ S ∈ univ.filter (fun S : Finset (Fin N) => S.card = m), ∑ T ∈ univ.filter (fun T : Finset (Fin N) => T.card = n),
    ∑ J ∈ (S ∩ T).powerset, if symmDiff S T ∪ J = U then (1 - r) ^ J.card * r ^ ((S ∩ T).card - J.card) else 0

/-- **Explicit coefficients of `K_{N,r}`**: `g(m,n;k) / C(N,k) = countP / (C(N,m) C(N,n))` for any `U`
with `|U| = k`. -/
theorem kraw_g_count (hy : QuadRel r y) (hN : 1 ≤ N) (B : Module.Basis (Finset (Fin N)) ℝ A)
    (hB : ∀ S, B S = ySet y S) (m : ℕ) (hm : m ≤ N) (n k : Fin (N + 1)) (U : Finset (Fin N)) (hU : U.card = k) :
    productMatrix (krawCoefficients N r) m n k * ((N.choose k : ℕ) : ℝ)⁻¹ =
      ((N.choose m : ℕ) : ℝ)⁻¹ * ((N.choose n : ℕ) : ℝ)⁻¹ * countP N m n U r := by
  have h := congrArg (fun z => B.repr z U) (kraw_product_alg hy hN m hm n)
  have hset : ∀ S : Finset (Fin N), B.repr (ySet y S) U = if S = U then 1 else 0 := by
    intro S; rw [← hB, B.repr_self, Finsupp.single_apply]
  have hrepl : ∀ l : ℕ, B.repr (Ukr y l) U = if U.card = l then ((N.choose l : ℕ) : ℝ)⁻¹ else 0 := by
    intro l
    rw [Ukr, levelSum, map_smul, map_sum, Finsupp.smul_apply, Finsupp.finsetSum_apply]
    simp_rw [hset]
    rw [sum_ite_eq' (univ.filter fun S : Finset (Fin N) => S.card = l) U]
    simp only [mem_filter, mem_univ, true_and, smul_eq_mul]
    split_ifs <;> simp
  -- the right side
  rw [map_sum, Finsupp.finsetSum_apply] at h
  simp only [map_smul, Finsupp.smul_apply, smul_eq_mul, hrepl] at h
  rw [sum_eq_single k] at h
  · rw [if_pos hU] at h
    rw [← h]
    -- the left side
    rw [Ukr, Ukr, smul_mul_smul_comm, levelSum, levelSum, sum_mul_sum]
    simp_rw [ySet_mul hy]
    simp only [map_smul, map_sum, Finsupp.smul_apply, Finsupp.finsetSum_apply, smul_eq_mul, hset, countP,
      mul_sum]
    refine sum_congr rfl fun S _ => sum_congr rfl fun T _ => sum_congr rfl fun J _ => ?_
    split_ifs <;> ring
  · intro l _ hl
    rw [if_neg (fun h' => hl (Fin.ext (by rw [← h', hU]))), mul_zero]
  · intro h'; exact absurd (mem_univ _) h'

end kraw

/-- **Explicit coefficients of `K_{N,r}`** (`r ≠ -1`):
`g(m,n;k) = C(N,k) / (C(N,m) C(N,n)) · countP N m n U r` for any `U` with `|U| = k`. -/
theorem kraw_g_formula {N : ℕ} {r : ℝ} (hN : 1 ≤ N) (hr : 1 + r ≠ 0) (m : ℕ) (hm : m ≤ N) (n k : Fin (N + 1))
    (U : Finset (Fin N)) (hU : U.card = k) :
    productMatrix (krawCoefficients N r) m n k =
      ((N.choose k : ℕ) : ℝ) / (((N.choose m : ℕ) : ℝ) * ((N.choose n : ℕ) : ℝ)) * countP N m n U r := by
  obtain ⟨hrel, B, hB⟩ := cube_model N r hr
  have h := kraw_g_count hrel hN B hB m hm n k U hU
  have hk : ((N.choose k : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos (by omega)).ne'
  rw [mul_inv_eq_iff_eq_mul₀ hk] at h
  rw [h]; field_simp

end Szkraw
