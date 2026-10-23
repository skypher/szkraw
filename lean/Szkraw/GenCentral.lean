import Szkraw.GenPhaseA

/-!
# Theorem 8.16, central sums: splitting identities

`GenSsum f a σ i = Σ_{k ∈ Icc i (σ-i)} M_{k,σ-k}` (the central sums of `MC`), and the identities
`M_{k,0} = 0`, `S_{σ,0} = S_{σ,1} + M_{0,σ}`, `S_{σ,1} = S_{σ,2} + M_{1,σ-1} + M_{σ-1,1}`.
-/

set_option linter.unusedSectionVars false

namespace Szkraw

open Finset

/-- The central sum `S_{σ,i}` of the matrix `MC`. -/
noncomputable def GenSsum (f : ℕ → ℝ) (a σ i : ℕ) : ℝ :=
  ∑ k ∈ Icc i (σ - i), MC f a k (σ - k)

theorem sum_Icc_zero_split (g : ℕ → ℝ) (p : ℕ) :
    ∑ k ∈ Icc 0 (p + 1), g k = g 0 + ∑ k ∈ Icc 1 p, g k + g (p + 1) := by
  rw [Finset.Icc_eq_cons_Ioc (by omega : 0 ≤ p + 1), Finset.sum_cons,
    show Finset.Ioc 0 (p + 1) = Finset.Icc 1 (p + 1) from (Finset.Icc_succ_left_eq_Ioc 0 (p + 1)).symm,
    Finset.sum_Icc_succ_top (by omega : 1 ≤ p + 1)]
  ring

theorem sum_Icc_one_split (g : ℕ → ℝ) (p : ℕ) (hp : 1 ≤ p) :
    ∑ k ∈ Icc 1 (p + 1), g k = g 1 + ∑ k ∈ Icc 2 p, g k + g (p + 1) := by
  rw [Finset.Icc_eq_cons_Ioc (by omega : 1 ≤ p + 1), Finset.sum_cons,
    show Finset.Ioc 1 (p + 1) = Finset.Icc 2 (p + 1) from (Finset.Icc_succ_left_eq_Ioc 1 (p + 1)).symm,
    Finset.sum_Icc_succ_top (by omega : 2 ≤ p + 1)]
  ring

/-- `M_{k,0} = 0`. -/
theorem MC_right_zero (f : ℕ → ℝ) (a k : ℕ) : MC f a k 0 = 0 := by
  have hd : deltaC f a 0 = dd f a - dd f (a - 1) := by
    unfold deltaC; simp
  have hc : chiC f a 0 = dd f a - dd f 0 := by
    unfold chiC; simp
  have hc' : chi'C f a 0 = dd f (a - 1) - dd f 1 := by
    unfold chi'C; simp
  have hz : zetaC f a 0 = Hstar f a := by
    unfold zetaC Hstar; simp
  have hn : nuC f a 0 = 0 := by
    unfold nuC; simp
  unfold MC
  rw [hd, hc, hc', hz, hn]
  ring

/-- `S_{σ,0} = M_{0,σ} + S_{σ,1}` for `σ = p + 1`. -/
theorem Ssum_zero_split (f : ℕ → ℝ) (a p : ℕ) :
    GenSsum f a (p + 1) 0 = MC f a 0 (p + 1) + GenSsum f a (p + 1) 1 := by
  have h := sum_Icc_zero_split (fun k => MC f a k (p + 1 - k)) p
  simp only [Nat.sub_self, Nat.sub_zero, MC_right_zero, add_zero] at h
  unfold GenSsum
  simp only [Nat.sub_zero, Nat.add_sub_cancel]
  linarith [h]

/-- `S_{σ,1} = M_{1,σ-1} + S_{σ,2} + M_{σ-1,1}` for `σ = p + 2`, `p ≥ 1`. -/
theorem Ssum_one_split (f : ℕ → ℝ) (a p : ℕ) (hp : 1 ≤ p) :
    GenSsum f a (p + 2) 1 = MC f a 1 (p + 1) + GenSsum f a (p + 2) 2 + MC f a (p + 1) 1 := by
  unfold GenSsum
  rw [show p + 2 - 1 = p + 1 by omega, sum_Icc_one_split _ p hp, show p + 2 - 2 = p by omega]
  have e : p + 2 - (p + 1) = 1 := by omega
  rw [e, show p + 2 - 1 = p + 1 by omega]


/-! ### The pieces of `CentralLowStmt`, and `CentralStmt` from them -/

/-- `M_{0,s} ≥ 0` for `s ≥ 3` (paper (iv), via `K″` and `Q_s`). -/
def M0Stmt : Prop :=
  ∀ (f : ℕ → ℝ), LCNZ f → 0 < f 1 → ∀ a : ℕ, 3 ≤ a → ∀ s : ℕ, 3 ≤ s → 0 ≤ MC f a 0 s

/-- `M_{1,m} + M_{m,1} ≥ 0` for `m ≥ 2` (paper (iii′)). -/
def MM1Stmt : Prop :=
  ∀ (f : ℕ → ℝ), LCNZ f → 0 < f 1 → ∀ a : ℕ, 3 ≤ a → ∀ m : ℕ, 2 ≤ m →
    0 ≤ MC f a 1 m + MC f a m 1

/-- `S_{2,0} = M_{0,2} + M_{1,1} ≥ 0` (paper (v)). -/
def S20Stmt : Prop :=
  ∀ (f : ℕ → ℝ), LCNZ f → 0 < f 1 → ∀ a : ℕ, 3 ≤ a → 0 ≤ MC f a 0 2 + MC f a 1 1

/-- `M_{0,1} ≥ 0` (paper (iii), `λ₁ ≥ 0`). -/
def M01Stmt : Prop :=
  ∀ (f : ℕ → ℝ), LCNZ f → 0 < f 1 → ∀ a : ℕ, 3 ≤ a → 0 ≤ MC f a 0 1

/-- `M_{1,1} ≥ 0` (paper (iii), `φ₁₁ ≥ 0`). -/
def M11Stmt : Prop :=
  ∀ (f : ℕ → ℝ), LCNZ f → 0 < f 1 → ∀ a : ℕ, 3 ≤ a → 0 ≤ MC f a 1 1

theorem Ssum_two_one (f : ℕ → ℝ) (a : ℕ) : GenSsum f a 2 1 = MC f a 1 1 := by
  unfold GenSsum; simp

theorem Ssum_three_two (f : ℕ → ℝ) (a : ℕ) : GenSsum f a 3 2 = 0 := by
  unfold GenSsum; simp

theorem Ssum_one_nonneg (hM : MM1Stmt) (hM11 : M11Stmt)
    {f : ℕ → ℝ} (hf : LCNZ f) (hf1 : 0 < f 1) {a : ℕ} (ha : 3 ≤ a) (σ : ℕ) (hσ : 2 ≤ σ) :
    0 ≤ GenSsum f a σ 1 := by
  rcases Nat.lt_or_ge σ 3 with h3 | h3
  · have e : σ = 2 := by omega
    subst e
    rw [Ssum_two_one]
    exact hM11 f hf hf1 a ha
  · obtain ⟨p, rfl⟩ : ∃ p, σ = p + 2 := ⟨σ - 2, by omega⟩
    rw [Ssum_one_split f a p (by omega)]
    have hmid : 0 ≤ GenSsum f a (p + 2) 2 := by
      rcases Nat.lt_or_ge p 2 with hp | hp
      · have e : p = 1 := by omega
        subst e
        rw [show (1 + 2 : ℕ) = 3 from rfl, Ssum_three_two]
      · exact central_ge2 hf hf1 ha (p + 2) 2 le_rfl (by omega)
    have h1 := hM f hf hf1 a ha (p + 1) (by omega)
    linarith

theorem central_low_of (h0 : M0Stmt) (hM : MM1Stmt) (hS20 : S20Stmt) (hM01 : M01Stmt)
    (hM11 : M11Stmt) :
    ∀ (f : ℕ → ℝ), LCNZ f → 0 < f 1 → ∀ a : ℕ, 3 ≤ a → ∀ σ i : ℕ, i ≤ 1 → 2 * i ≤ σ →
      0 ≤ GenSsum f a σ i := by
  intro f hf hf1 a ha σ i hi hσ
  interval_cases i
  · rcases Nat.lt_or_ge σ 2 with hs | hs
    · rcases Nat.lt_or_ge σ 1 with hs0 | hs0
      · have e : σ = 0 := by omega
        subst e
        unfold GenSsum; simp [MC_right_zero]
      · have e : σ = 1 := by omega
        subst e
        have h : GenSsum f a 1 0 = MC f a 0 1 + GenSsum f a 1 1 := Ssum_zero_split f a 0
        have h1 : GenSsum f a 1 1 = 0 := by unfold GenSsum; simp
        rw [h, h1, add_zero]
        exact hM01 f hf hf1 a ha
    · rcases Nat.lt_or_ge σ 3 with hs3 | hs3
      · have e : σ = 2 := by omega
        subst e
        have h : GenSsum f a 2 0 = MC f a 0 2 + GenSsum f a 2 1 := Ssum_zero_split f a 1
        rw [h, Ssum_two_one]
        exact hS20 f hf hf1 a ha
      · obtain ⟨p, rfl⟩ : ∃ p, σ = p + 1 := ⟨σ - 1, by omega⟩
        rw [Ssum_zero_split f a p]
        have h1 := h0 f hf hf1 a ha (p + 1) (by omega)
        have h2 := Ssum_one_nonneg hM hM11 hf hf1 ha (p + 1) (by omega)
        linarith
  · exact Ssum_one_nonneg hM hM11 hf hf1 ha σ (by omega)


/-- `CentralStmt` (the central sums of `MC` are nonnegative) from the five pieces. -/
theorem central_of_pieces (h0 : M0Stmt) (hM : MM1Stmt) (hS20 : S20Stmt) (hM01 : M01Stmt)
    (hM11 : M11Stmt) : CentralStmt := by
  intro f hf hf1 a ha σ i hσ
  rcases Nat.lt_or_ge i 2 with hi | hi
  · exact central_low_of h0 hM hS20 hM01 hM11 f hf hf1 a ha σ i (by omega) hσ
  · exact central_ge2 hf hf1 ha σ i hi hσ

end Szkraw
