import Szkraw.UniformRules

/-!
# Proposition 9.9 (1): families depending on `N`

Let `v_N = (δb_N, δc_N)` be directions such that a set with property (P) contains
`K_{N,1} + ε v_N` for all large `N` and small `ε > 0`, and let `A_N` be the alternating sum of
Lemma 9.2 for `v_N`. Then `s_N A_N ≥ 0` for all large `N`. Along either parity class `A_N` is
neither eventually strictly positive nor eventually strictly negative, and an eventual weak sign
forces `A_N = 0` on the residue class modulo 4 where that sign conflicts with the sign of `s_N`.
-/

namespace Szkraw

open Finset Filter Topology

/-- The alternating sum `A_N` of Lemma 9.2 for the direction `v_N = (vb N, vc N)`. -/
noncomputable def altSum (vb vc : ℕ → ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ range (N + 1), (-1 : ℝ) ^ n * (N.choose n : ℝ) * cornerF N (vb N) (vc N) n

/-- A family of sets contains `K_{N,1} + ε v_N` for all large `N` and small `ε > 0`. -/
def ContainsFamily (S : (N : ℕ) → Set (Coefficients N)) (vb vc : ℕ → ℕ → ℝ) : Prop :=
  ∃ N₀, ∀ N, N₀ ≤ N → ∃ εN > 0, ∀ ε, 0 < ε → ε < εN → krawDir N (vb N) (vc N) 1 ε ∈ S N

/-- A negative first-order change of `g(N,N;N)` excludes `K_{N,1} + ε v` for small `ε > 0`. -/
theorem corner_deriv_nonneg {N : ℕ} (hN : 2 ≤ N) (δb δc : ℕ → ℝ)
    (hpos : ∃ εN > 0, ∀ ε, 0 < ε → ε < εN → MatrixPositivity (krawDir N δb δc 1 ε)) :
    0 ≤ sN N * ∑ n ∈ range (N + 1), (-1 : ℝ) ^ n * (N.choose n : ℝ) * cornerF N δb δc n := by
  by_contra hneg'
  have hneg := lt_of_not_ge hneg'
  obtain ⟨εN, hεN, hmem⟩ := hpos
  have h0 : productMatrix (krawDir N δb δc 1 0) N (Fin.last N) (Fin.last N) = 0 := by
    rw [krawDir_zero (by omega) 1 N (by omega)]
    have := corner_value N (by omega) 1 (by norm_num) le_rfl
    rw [sub_self, zero_pow (by omega)] at this
    exact this
  obtain ⟨ε₀, hε₀, hlt⟩ := neg_right_of_deriv (corner_identity hN) h0 hneg
  set ε := min εN ε₀ / 2 with hεdef
  have hmin : 0 < min εN ε₀ := lt_min hεN hε₀
  have hε : 0 < ε := by rw [hεdef]; linarith
  have h1 : ε < εN := by have := min_le_left εN ε₀; rw [hεdef]; linarith
  have h2 : ε < ε₀ := by have := min_le_right εN ε₀; rw [hεdef]; linarith
  exact absurd (hlt ε hε h2) (not_lt.mpr (hmem ε hε h1 N le_rfl (Fin.last N) (Fin.last N)))

theorem sN_neg_of_mod4 {N : ℕ} (h : N % 4 = 0 ∨ N % 4 = 1) : sN N < 0 := by
  rw [sN]
  have hC : (0 : ℝ) < (N - 1).choose ((N - 1) / 2) := by exact_mod_cast Nat.choose_pos (by omega)
  obtain ⟨k, hk⟩ : ∃ k, N / 2 = 2 * k := ⟨N / 4, by omega⟩
  rw [hk, pow_succ, pow_mul]
  norm_num
  exact div_neg_of_neg_of_pos (by norm_num) hC

theorem sN_pos_of_mod4 {N : ℕ} (h : N % 4 = 2 ∨ N % 4 = 3) : 0 < sN N := by
  rw [sN]
  have hC : (0 : ℝ) < (N - 1).choose ((N - 1) / 2) := by exact_mod_cast Nat.choose_pos (by omega)
  obtain ⟨k, hk⟩ : ∃ k, N / 2 + 1 = 2 * k := ⟨N / 4 + 1, by omega⟩
  rw [hk, pow_mul]
  norm_num
  exact_mod_cast hC

/-- **Proposition 9.9** (Families depending on `N`), first statement: `s_N A_N ≥ 0` for all
large `N`. -/
theorem families_sign (S : (N : ℕ) → Set (Coefficients N)) (hS : ∀ N, ∀ v ∈ S N, MatrixPositivity v)
    {vb vc : ℕ → ℕ → ℝ} (hfam : ContainsFamily S vb vc) :
    ∃ M, ∀ N, M ≤ N → 0 ≤ sN N * altSum vb vc N := by
  obtain ⟨N₀, hN₀⟩ := hfam
  refine ⟨N₀ + 2, fun N hN => ?_⟩
  obtain ⟨εN, hεN, hmem⟩ := hN₀ N (by omega)
  exact corner_deriv_nonneg (by omega) _ _ ⟨εN, hεN, fun ε hε h => hS N _ (hmem ε hε h)⟩

/-- **Proposition 9.9 (1)**: if `A_N ≥ 0` eventually along the parity class `p`, then `A_N = 0`
for all large `N` of that class with `s_N < 0`; if `A_N ≤ 0` eventually, then `A_N = 0` for all
large `N` of that class with `s_N > 0`. -/
theorem families_weak_sign (S : (N : ℕ) → Set (Coefficients N)) (hS : ∀ N, ∀ v ∈ S N, MatrixPositivity v)
    {vb vc : ℕ → ℕ → ℝ} (hfam : ContainsFamily S vb vc) (p : ℕ) :
    ((∃ M, ∀ N, M ≤ N → N % 2 = p → 0 ≤ altSum vb vc N) →
      ∃ M, ∀ N, M ≤ N → N % 2 = p → sN N < 0 → altSum vb vc N = 0) ∧
    ((∃ M, ∀ N, M ≤ N → N % 2 = p → altSum vb vc N ≤ 0) →
      ∃ M, ∀ N, M ≤ N → N % 2 = p → 0 < sN N → altSum vb vc N = 0) := by
  obtain ⟨M₀, hM₀⟩ := families_sign S hS hfam
  constructor
  · rintro ⟨M, hM⟩
    refine ⟨max M M₀, fun N hN hp hs => ?_⟩
    have h1 := hM N (le_trans (le_max_left _ _) hN) hp
    have h2 := hM₀ N (le_trans (le_max_right _ _) hN)
    have : sN N * altSum vb vc N ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hs.le h1
    have h3 : sN N * altSum vb vc N = 0 := le_antisymm this h2
    exact (mul_eq_zero.mp h3).resolve_left hs.ne
  · rintro ⟨M, hM⟩
    refine ⟨max M M₀, fun N hN hp hs => ?_⟩
    have h1 := hM N (le_trans (le_max_left _ _) hN) hp
    have h2 := hM₀ N (le_trans (le_max_right _ _) hN)
    have : sN N * altSum vb vc N ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hs.le h1
    have h3 : sN N * altSum vb vc N = 0 := le_antisymm this h2
    exact (mul_eq_zero.mp h3).resolve_left hs.ne'

/-- **Proposition 9.9 (1)**: along either parity class, `A_N` is neither eventually strictly
positive nor eventually strictly negative. -/
theorem families_no_strict_sign (S : (N : ℕ) → Set (Coefficients N))
    (hS : ∀ N, ∀ v ∈ S N, MatrixPositivity v) {vb vc : ℕ → ℕ → ℝ} (hfam : ContainsFamily S vb vc)
    (p : ℕ) (hp : p < 2) :
    ¬(∃ M, ∀ N, M ≤ N → N % 2 = p → 0 < altSum vb vc N) ∧
      ¬(∃ M, ∀ N, M ≤ N → N % 2 = p → altSum vb vc N < 0) := by
  obtain ⟨M₀, hM₀⟩ := families_sign S hS hfam
  constructor
  · rintro ⟨M, hM⟩
    set N := 4 * (M + M₀) + p
    have hs := sN_neg_of_mod4 (N := N) (by omega)
    have h1 := hM N (by omega) (by omega)
    have h2 := hM₀ N (by omega)
    exact absurd h2 (not_le.mpr (mul_neg_of_neg_of_pos hs h1))
  · rintro ⟨M, hM⟩
    set N := 4 * (M + M₀) + p + 2
    have hs := sN_pos_of_mod4 (N := N) (by omega)
    have h1 := hM N (by omega) (by omega)
    have h2 := hM₀ N (by omega)
    exact absurd h2 (not_le.mpr (mul_neg_of_pos_of_neg hs h1))

end Szkraw
