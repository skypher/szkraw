import Szkraw.NewtonProduct
import Szkraw.GenMain
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Data.Fintype.EquivFin

/-!
# P2, after Proposition 4.3: the random-set reading of the product theorem (Walkup)

For independent random subsets `S`, `T` of `[n]` with laws invariant under permutations, `Pr(S = A) = ρ_{|A|}` and
`Pr(T = B) = ν_{|B|}`, and `Pr(|S ∪ T| = k) = C(n,k) κ_k` with `κ = kap ρ ν` the Newton coefficients of the product
(`union_card_law`). Hence, if the cardinalities `|S|` and `|T|` are ultra-log-concave of order `n`, so is
`|S ∪ T|` (`random_sets_ulc`). Laws are nonnegative functions on `Finset (Fin n)`; the joint law of the independent
pair is the product; normalization to total mass one plays no role.
-/

namespace Szkraw

open Finset

namespace RandomSets

/-- `p_0, …, p_n` is ultra-log-concave of order `n`: `p_k / C(n,k)` (`k ≤ n`, extended by zero) is nonnegative and
log-concave without internal zeros. -/
def ULC (n : ℕ) (p : ℕ → ℝ) : Prop := LCNZ (fun k => if k ≤ n then p k / (n.choose k : ℝ) else 0)

/-- The law of `|S|`. -/
noncomputable def cardLaw {n : ℕ} (pS : Finset (Fin n) → ℝ) (i : ℕ) : ℝ := ∑ A ∈ powersetCard i univ, pS A

/-- The law of `|S ∪ T|` for independent `S`, `T`. -/
noncomputable def unionLaw {n : ℕ} (pS pT : Finset (Fin n) → ℝ) (k : ℕ) : ℝ :=
  ∑ A : Finset (Fin n), ∑ B : Finset (Fin n), if (A ∪ B).card = k then pS A * pT B else 0

/-! ### Exchangeable laws depend only on the cardinality -/

theorem perm_invariant_card {n : ℕ} (p : Finset (Fin n) → ℝ)
    (hp : ∀ (σ : Equiv.Perm (Fin n)) (A : Finset (Fin n)), p (A.map σ.toEmbedding) = p A)
    (A B : Finset (Fin n)) (h : A.card = B.card) : p A = p B := by
  classical
  let e : {x // x ∈ A} ≃ {x // x ∈ B} := Finset.equivOfCardEq h
  let σ : Equiv.Perm (Fin n) := e.extendSubtype
  have hsub : A.map σ.toEmbedding ⊆ B := by
    intro y hy
    rw [Finset.mem_map] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact Equiv.extendSubtype_mem e x hx
  have heq : A.map σ.toEmbedding = B := Finset.eq_of_subset_of_card_le hsub (by rw [Finset.card_map, h])
  rw [← heq, hp]

/-! ### Counting -/

/-- Every `B ⊆ [n]` splits as `(B ∩ A) ∪ (B \ A)` with `B ∩ A ⊆ A` and `B \ A ⊆ Aᶜ`. -/
theorem sum_split {n : ℕ} (A : Finset (Fin n)) (f : Finset (Fin n) → ℝ) :
    ∑ B : Finset (Fin n), f B = ∑ C ∈ A.powerset, ∑ D ∈ Aᶜ.powerset, f (C ∪ D) := by
  classical
  rw [← sum_product']
  symm
  refine Finset.sum_nbij' (fun p => p.1 ∪ p.2) (fun B => (B ∩ A, B \ A)) ?_ ?_ ?_ ?_ ?_
  · intro p _; exact mem_univ _
  · intro B _
    simp only [mem_product, mem_powerset]
    exact ⟨inter_subset_right, fun x hx => by simp at hx ⊢; exact hx.2⟩
  · intro p hp
    simp only [mem_product, mem_powerset] at hp
    obtain ⟨hC, hD⟩ := hp
    ext x
    · simp only [mem_inter, mem_union]
      constructor
      · rintro ⟨h | h, hA⟩
        · exact h
        · exact absurd hA (by simpa using hD h)
      · intro h; exact ⟨Or.inl h, hC h⟩
    · simp only [mem_sdiff, mem_union]
      constructor
      · rintro ⟨h | h, hA⟩
        · exact absurd (hC h) hA
        · exact h
      · intro h; exact ⟨Or.inr h, by simpa using hD h⟩
  · intro B _
    ext x; simp only [mem_union, mem_inter, mem_sdiff]; tauto
  · intro p _; rfl

theorem sum_powerset_card {n : ℕ} (A : Finset (Fin n)) (g : ℕ → ℝ) :
    ∑ C ∈ A.powerset, g C.card = ∑ c ∈ range (A.card + 1), (A.card.choose c : ℝ) * g c := by
  rw [Finset.sum_powerset_apply_card]
  exact sum_congr rfl fun c _ => by rw [nsmul_eq_mul]

/-- For fixed `A` with `|A| = i ≤ k ≤ n`: `Σ_B [|A ∪ B| = k] ν_{|B|} = C(n-i, k-i) Σ_c C(i,c) ν_{c + k - i}`. -/
theorem inner_count {n : ℕ} (A : Finset (Fin n)) (ν : ℕ → ℝ) (k : ℕ) (hk : k ≤ n) :
    ∑ B : Finset (Fin n), (if (A ∪ B).card = k then ν B.card else 0) =
      if A.card ≤ k then ((n - A.card).choose (k - A.card) : ℝ) *
        ∑ c ∈ range (A.card + 1), (A.card.choose c : ℝ) * ν (c + (k - A.card)) else 0 := by
  classical
  rw [sum_split A]
  have hcard : ∀ C ∈ A.powerset, ∀ D ∈ Aᶜ.powerset,
      (if (A ∪ (C ∪ D)).card = k then ν (C ∪ D).card else 0) =
        if A.card + D.card = k then ν (C.card + D.card) else 0 := by
    intro C hC D hD
    rw [mem_powerset] at hC hD
    have hdisjAD : Disjoint A D := by
      rw [Finset.disjoint_left]; intro x hx hxD; have := hD hxD; simp at this; exact this hx
    have hdisjCD : Disjoint C D := by
      rw [Finset.disjoint_left]; intro x hx hxD; have := hD hxD; simp at this; exact this (hC hx)
    have hu : A ∪ (C ∪ D) = A ∪ D := by
      ext x; simp only [mem_union]; constructor
      · rintro (h | h | h)
        · exact Or.inl h
        · exact Or.inl (hC h)
        · exact Or.inr h
      · rintro (h | h)
        · exact Or.inl h
        · exact Or.inr (Or.inr h)
    rw [hu, card_union_of_disjoint hdisjAD, card_union_of_disjoint hdisjCD]
  rw [sum_congr rfl fun C hC => sum_congr rfl fun D hD => hcard C hC D hD]
  have hAc : Aᶜ.card = n - A.card := by rw [card_compl, Fintype.card_fin]
  have hD : ∀ C : Finset (Fin n), ∑ D ∈ Aᶜ.powerset, (if A.card + D.card = k then ν (C.card + D.card) else 0) =
      if A.card ≤ k then ((n - A.card).choose (k - A.card) : ℝ) * ν (C.card + (k - A.card)) else 0 := by
    intro C
    rw [sum_powerset_card Aᶜ (fun d => if A.card + d = k then ν (C.card + d) else 0), hAc]
    split_ifs with h
    · rw [sum_eq_single (k - A.card)]
      · rw [if_pos (by omega)]
      · intro d _ hd; rw [if_neg (by omega), mul_zero]
      · intro hd; simp at hd; omega
    · exact sum_eq_zero fun d _ => by rw [if_neg (by omega), mul_zero]
  rw [sum_congr rfl fun C _ => hD C]
  split_ifs with h
  · rw [← mul_sum]
    congr 1
    exact sum_powerset_card A (fun c => ν (c + (k - A.card)))
  · simp

/-- `Σ_{c ≤ i} C(i,c) ν_{c + k - i} = Σ_{j ≤ k} C(i, k-j) ν_j` for `i ≤ k`. -/
theorem reindex (ν : ℕ → ℝ) (i k : ℕ) (hik : i ≤ k) :
    ∑ c ∈ range (i + 1), (i.choose c : ℝ) * ν (c + (k - i)) = ∑ j ∈ range (k + 1), (i.choose (k - j) : ℝ) * ν j := by
  rw [← Finset.sum_range_reflect (fun j => (i.choose (k - j) : ℝ) * ν j) (k + 1)]
  rw [← Finset.sum_range_reflect (fun c => (i.choose c : ℝ) * ν (c + (k - i))) (i + 1)]
  have hsub : range (i + 1) ⊆ range (k + 1) := range_subset_range.mpr (by omega)
  rw [← Finset.sum_subset hsub (fun m hm hm' => by
    simp only [mem_range] at hm hm'
    rw [show k + 1 - 1 - m = k - m by omega, show k - (k - m) = m by omega,
      Nat.choose_eq_zero_of_lt (by omega : i < m), Nat.cast_zero, zero_mul])]
  refine sum_congr rfl fun m hm => ?_
  simp only [mem_range] at hm
  rw [show i + 1 - 1 - m = i - m by omega, show k + 1 - 1 - m = k - m by omega, show k - (k - m) = m by omega,
    Nat.choose_symm (by omega : m ≤ i), show i - m + (k - i) = k - m by omega]

/-- **The law of `|S ∪ T|`.** For exchangeable laws `Pr(S = A) = ρ_{|A|}`, `Pr(T = B) = ν_{|B|}` on `[n]`,
`Pr(|S ∪ T| = k) = C(n,k) κ_k` for `k ≤ n`, where `κ = kap ρ ν` are the Newton coefficients of the product of the
Newton series of `ρ` and `ν` (`nval_mul`). -/
theorem union_card_law (n : ℕ) (ρ ν : ℕ → ℝ) (k : ℕ) (hk : k ≤ n) :
    ∑ A : Finset (Fin n), ∑ B : Finset (Fin n), (if (A ∪ B).card = k then ρ A.card * ν B.card else 0) =
      (n.choose k : ℝ) * kap ρ ν k := by
  classical
  have h1 : ∀ A : Finset (Fin n), ∑ B : Finset (Fin n), (if (A ∪ B).card = k then ρ A.card * ν B.card else 0) =
      ρ A.card * (if A.card ≤ k then ((n - A.card).choose (k - A.card) : ℝ) *
        ∑ c ∈ range (A.card + 1), (A.card.choose c : ℝ) * ν (c + (k - A.card)) else 0) := by
    intro A
    rw [← inner_count A ν k hk, mul_sum]
    exact sum_congr rfl fun B _ => by split_ifs <;> ring
  rw [sum_congr rfl fun A _ => h1 A]
  have h2 := Finset.sum_powerset_apply_card (fun i => ρ i * (if i ≤ k then ((n - i).choose (k - i) : ℝ) *
      ∑ c ∈ range (i + 1), (i.choose c : ℝ) * ν (c + (k - i)) else 0)) (x := (univ : Finset (Fin n)))
  rw [Finset.powerset_univ] at h2
  rw [h2, card_univ, Fintype.card_fin, kap_nat ρ ν k k le_rfl, mul_sum]
  have hsub : range (k + 1) ⊆ range (n + 1) := range_subset_range.mpr (by omega)
  rw [← Finset.sum_subset hsub (fun i hi hi' => by
    simp only [mem_range] at hi hi'
    rw [if_neg (by omega), mul_zero, smul_zero])]
  refine sum_congr rfl fun i hi => ?_
  simp only [mem_range] at hi
  rw [if_pos (by omega), nsmul_eq_mul, reindex ν i k (by omega)]
  set X := ∑ j ∈ range (k + 1), (i.choose (k - j) : ℝ) * ν j with hX
  have hR : ∑ j ∈ range (k + 1), (Hn k i j : ℝ) * (ρ i * ν j) = (k.choose i : ℝ) * ρ i * X := by
    rw [hX, mul_sum]
    refine sum_congr rfl fun j hj => ?_
    simp only [mem_range] at hj
    simp only [Hn, if_pos (show j ≤ k by omega)]
    push_cast
    ring
  rw [hR]
  have hc : (n.choose i : ℝ) * ((n - i).choose (k - i) : ℝ) = (n.choose k : ℝ) * (k.choose i : ℝ) := by
    exact_mod_cast (Nat.choose_mul (n := n) (by omega : i ≤ k)).symm
  linear_combination (ρ i * X) * hc


/-- **Walkup's double-binomial convolution** `h_k = Σ_i Σ_r C(k,i) C(i,r) ρ_i ν_{k-r}` is `κ_k = kap ρ ν k`
(substitute `j = k - r`). -/
theorem walkup_convolution (ρ ν : ℕ → ℝ) (k : ℕ) :
    ∑ i ∈ range (k + 1), ∑ r ∈ range (i + 1), (k.choose i : ℝ) * (i.choose r : ℝ) * ρ i * ν (k - r) =
      kap ρ ν k := by
  rw [kap_nat ρ ν k k le_rfl]
  refine sum_congr rfl fun i hi => ?_
  simp only [mem_range] at hi
  have h1 : ∑ r ∈ range (i + 1), (i.choose r : ℝ) * ν (k - r) =
      ∑ j ∈ range (k + 1), (i.choose (k - j) : ℝ) * ν j := by
    rw [← Finset.sum_range_reflect (fun j => (i.choose (k - j) : ℝ) * ν j) (k + 1)]
    have hsub : range (i + 1) ⊆ range (k + 1) := range_subset_range.mpr (by omega)
    rw [← Finset.sum_subset hsub (fun m hm hm' => by
      simp only [mem_range] at hm hm'
      rw [show k + 1 - 1 - m = k - m by omega, show k - (k - m) = m by omega,
        Nat.choose_eq_zero_of_lt (by omega : i < m), Nat.cast_zero, zero_mul])]
    refine sum_congr rfl fun m hm => ?_
    simp only [mem_range] at hm
    rw [show k + 1 - 1 - m = k - m by omega, show k - (k - m) = m by omega]
  have h2 : ∑ r ∈ range (i + 1), (k.choose i : ℝ) * (i.choose r : ℝ) * ρ i * ν (k - r) =
      (k.choose i : ℝ) * ρ i * ∑ r ∈ range (i + 1), (i.choose r : ℝ) * ν (k - r) := by
    rw [mul_sum]; exact sum_congr rfl fun r _ => by ring
  rw [h2, h1, mul_sum]
  refine sum_congr rfl fun j hj => ?_
  simp only [mem_range] at hj
  simp only [Hn, if_pos (show j ≤ k by omega)]
  push_cast
  ring

/-! ### Ultra-log-concavity of `|S ∪ T|` -/

theorem LCNZ_trunc {u : ℕ → ℝ} (hu : LCNZ u) (n : ℕ) : LCNZ (fun k => if k ≤ n then u k else 0) := by
  obtain ⟨h0, hlc, hint⟩ := hu
  refine ⟨fun k => by dsimp only; split_ifs; exacts [h0 k, le_rfl], fun k => ?_, fun i j k hij hjk hi hk => ?_⟩
  · dsimp only
    by_cases h2 : k + 2 ≤ n
    · rw [if_pos (by omega), if_pos h2, if_pos (by omega)]; exact hlc k
    · rw [if_neg h2, mul_zero]; exact sq_nonneg _
  · dsimp only at hi hk ⊢
    have hkn : k ≤ n := by by_contra h; rw [if_neg h] at hk; exact lt_irrefl _ hk
    rw [if_pos (by omega)] at hi ⊢
    rw [if_pos hkn] at hk
    exact hint i j k hij hjk hi hk

/-- **P2, after Proposition 4.3 (random sets, Walkup's Theorem 4 for two sets).** Let `S`, `T` be independent
random subsets of `[n]` whose laws `pS`, `pT` are invariant under permutations, and whose cardinalities are
ultra-log-concave of order `n`. Then `|S ∪ T|` is ultra-log-concave of order `n`. (Nonnegativity of the laws
follows from the permutation invariance together with the ultra-log-concavity of the cardinalities and is not
assumed separately.) -/
theorem random_sets_ulc (n : ℕ) (pS pT : Finset (Fin n) → ℝ)
    (hSinv : ∀ (σ : Equiv.Perm (Fin n)) (A : Finset (Fin n)), pS (A.map σ.toEmbedding) = pS A)
    (hTinv : ∀ (σ : Equiv.Perm (Fin n)) (B : Finset (Fin n)), pT (B.map σ.toEmbedding) = pT B)
    (hSulc : ULC n (cardLaw pS)) (hTulc : ULC n (cardLaw pT)) : ULC n (unionLaw pS pT) := by
  classical
  set ρ : ℕ → ℝ := fun i => if i ≤ n then cardLaw pS i / (n.choose i : ℝ) else 0 with hρ
  set ν : ℕ → ℝ := fun j => if j ≤ n then cardLaw pT j / (n.choose j : ℝ) else 0 with hν
  -- an exchangeable law is `ρ` of the cardinality
  have hexch : ∀ (p : Finset (Fin n) → ℝ), (∀ (σ : Equiv.Perm (Fin n)) A, p (A.map σ.toEmbedding) = p A) →
      ∀ A : Finset (Fin n), p A = (fun i => if i ≤ n then cardLaw p i / (n.choose i : ℝ) else 0) A.card := by
    intro p hp A
    have hAn : A.card ≤ n := by simpa using card_le_univ A
    dsimp only
    rw [if_pos hAn, cardLaw, eq_div_iff (by exact_mod_cast (Nat.choose_pos hAn).ne')]
    rw [sum_congr rfl fun B hB => perm_invariant_card p hp B A (by rw [(mem_powersetCard.mp hB).2])]
    rw [sum_const, card_powersetCard, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_comm]
  have hSA : ∀ A, pS A = ρ A.card := hexch pS hSinv
  have hTB : ∀ B, pT B = ν B.card := hexch pT hTinv
  have hlaw : ∀ k, k ≤ n → unionLaw pS pT k = (n.choose k : ℝ) * kap ρ ν k := fun k hk => by
    rw [← union_card_law n ρ ν k hk, unionLaw]
    exact sum_congr rfl fun A _ => sum_congr rfl fun B _ => by rw [hSA, hTB]
  have hK : LCNZ (kap ρ ν) := kap_LCNZ hSulc hTulc
  have e : (fun k => if k ≤ n then unionLaw pS pT k / (n.choose k : ℝ) else 0) =
      (fun k => if k ≤ n then kap ρ ν k else 0) := by
    funext k
    split_ifs with hk
    · rw [hlaw k hk, mul_div_cancel_left₀ _ (by exact_mod_cast (Nat.choose_pos hk).ne')]
    · rfl
  unfold ULC
  rw [e]
  exact LCNZ_trunc hK n

end RandomSets

end Szkraw
