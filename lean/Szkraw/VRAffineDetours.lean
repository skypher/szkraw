import Szkraw.VRAffine

/-!
# Theorem 8.9: weights from functions and the detour inequalities

`WtF F p q ℓ a = Σ_{p ≤ n ≤ a} C(n-p+q, q) C(a,n) F(ℓ, n)` generalizes `Wt` to arbitrary
functions `F(ℓ, n)` in place of the iterated shift sums; `H_j` and `V_j` are formed from
`h_n(ℓ) = (s - t(ℓ+n)) f_n(ℓ)` and `v_n(ℓ) = t n f_{n-1}(ℓ)`. The generic second detour gives the
`H`, `V` and `C'` detours (with the constant `4`), from the mixed inequality
`c_{ℓ+1} f_{n+2}(ℓ) ≤ φ_2(ℓ) f_n(ℓ+1)`.
-/

namespace Szkraw

open Finset

/-- `W^F_{p,q}(ℓ,a) = Σ_{p ≤ n ≤ a} C(n-p+q, q) C(a,n) F(ℓ,n)`. -/
noncomputable def WtF (F : ℕ → ℕ → ℝ) (p q ℓ a : ℕ) : ℝ :=
  ∑ n ∈ range (a + 1), (if p ≤ n then ((n - p + q).choose q : ℝ) else 0) * (a.choose n : ℝ) * F ℓ n

section WtF

variable {F F' : ℕ → ℕ → ℝ} {p q ℓ a : ℕ}

theorem Wt_eq_WtF (u : ℕ → ℝ) (p q ℓ a : ℕ) :
    Wt u p q ℓ a = WtF (fun ℓ n => Szkraw.iterShift u ℓ n) p q ℓ a := rfl

theorem WtF_nonneg (hF : ∀ n, p ≤ n → n ≤ a → 0 ≤ F ℓ n) : 0 ≤ WtF F p q ℓ a := by
  unfold WtF
  refine sum_nonneg fun n hn => ?_
  by_cases hpn : p ≤ n
  · rw [if_pos hpn]
    exact mul_nonneg (by positivity) (hF n hpn (by have := mem_range.mp hn; omega))
  · rw [if_neg hpn]; simp

theorem WtF_eq_zero (h : a < p) : WtF F p q ℓ a = 0 := by
  unfold WtF
  refine sum_eq_zero fun n hn => ?_
  rw [mem_range] at hn
  rw [if_neg (by omega)]; simp

theorem WtF_congr (h : ∀ n, n ≤ a → F ℓ n = F' ℓ n) : WtF F p q ℓ a = WtF F' p q ℓ a := by
  unfold WtF
  exact sum_congr rfl fun n hn => by rw [h n (by have := mem_range.mp hn; omega)]

theorem WtF_sub : WtF (fun ℓ n => F ℓ n - F' ℓ n) p q ℓ a = WtF F p q ℓ a - WtF F' p q ℓ a := by
  unfold WtF
  rw [← sum_sub_distrib]
  exact sum_congr rfl fun n _ => by ring

/-- Integer inequality behind the `H` and `V` detours: `8 C(m-j-1, j) ≤ C(m,2) C(m-j-2, j-1)`
for `j ≥ 2`, `m ≥ 2j+1`. -/
theorem coeffHV (j m : ℕ) (hj : 2 ≤ j) (hm : 2 * j + 1 ≤ m) :
    8 * (m - j - 1).choose j ≤ m.choose 2 * (m - j - 2).choose (j - 1) := by
  have key := Nat.add_one_mul_choose_eq (m - j - 2) (j - 1)
  have e1 : m - j - 2 + 1 = m - j - 1 := by omega
  have e2 : j - 1 + 1 = j := by omega
  rw [e1, e2] at key
  have hc2 := choose_two_mul m
  set X := (m - j - 2).choose (j - 1)
  set Y := (m - j - 1).choose j
  have h16 : 16 * (m - j - 1) ≤ j * (m * (m - 1)) := by
    have h2 : 16 * (m - 3) ≤ 2 * (m * (m - 1)) := by
      have h3 : 3 ≤ m := by omega
      zify [h3, (by omega : 1 ≤ m)]
      nlinarith [sq_nonneg (2 * (m : ℤ) - 9)]
    calc 16 * (m - j - 1) ≤ 16 * (m - 3) := by omega
      _ ≤ 2 * (m * (m - 1)) := h2
      _ ≤ j * (m * (m - 1)) := Nat.mul_le_mul_right _ hj
  have : 2 * j * (8 * Y) ≤ 2 * j * (m.choose 2 * X) := by
    have lhs : 2 * j * (8 * Y) = 16 * (Y * j) := by ring
    have rhs : 2 * j * (m.choose 2 * X) = j * (m.choose 2 * 2) * X := by ring
    rw [lhs, rhs, ← key, hc2]
    calc 16 * ((m - j - 1) * X) = (16 * (m - j - 1)) * X := by ring
      _ ≤ (j * (m * (m - 1))) * X := Nat.mul_le_mul_right _ h16
  exact Nat.le_of_mul_le_mul_left this (by omega)

/-- Generic second detour for `WtF`: if `c F(ℓ, n+2) ≤ K φ₂ F(ℓ+1, n)` for `p ≤ n ≤ a-2` and
`C(a,2) φ₂ ≤ B₀`, then
`Σ_m [p+2 ≤ m] C(m-2-p+q, q) C(m,2) C(a,m) c F(ℓ,m) ≤ K B₀ W^F_{p,q}(ℓ+1, a-2)`. -/
theorem detour_secondF {B0 c φ2 K : ℝ} (ha : 2 ≤ a) (hK : 0 ≤ K)
    (hB0 : (a.choose 2 : ℝ) * φ2 ≤ B0) (hF1 : ∀ n, n + 2 ≤ a → 0 ≤ F (ℓ + 1) n)
    (hloc : ∀ n, p ≤ n → n + 2 ≤ a → c * F ℓ (n + 2) ≤ K * (φ2 * F (ℓ + 1) n)) :
    ∑ m ∈ range (a + 1), (if p + 2 ≤ m then ((m - 2 - p + q).choose q : ℝ) else 0) *
        ((m.choose 2 : ℝ) * (a.choose m : ℝ)) * (c * F ℓ m) ≤
      K * (B0 * WtF F p q (ℓ + 1) (a - 2)) := by
  set G : ℕ → ℝ := fun m => (if p + 2 ≤ m then ((m - 2 - p + q).choose q : ℝ) else 0) *
        ((m.choose 2 : ℝ) * (a.choose m : ℝ)) * (c * F ℓ m) with hG
  have hsplit' : a - 2 + 1 = a - 1 := by omega
  have hre : ∑ m ∈ range (a + 1), G m = ∑ n ∈ range (a - 1), G (n + 2) := by
    rw [reindex2 G (a - 1) (by simp [hG]) (by simp [hG]), show a - 1 + 2 = a + 1 by omega]
  have hWnn : 0 ≤ WtF F p q (ℓ + 1) (a - 2) := WtF_nonneg fun n _ hn => hF1 n (by omega)
  calc ∑ m ∈ range (a + 1), G m = ∑ n ∈ range (a - 1), G (n + 2) := hre
    _ ≤ ∑ n ∈ range (a - 1), (if p ≤ n then ((n - p + q).choose q : ℝ) else 0) *
          ((a - 2).choose n : ℝ) * F (ℓ + 1) n * (K * ((a.choose 2 : ℝ) * φ2)) := by
        refine sum_le_sum (fun n hn => ?_)
        rw [mem_range] at hn
        simp only [hG]
        by_cases hpn : p ≤ n
        · rw [if_pos (by omega), if_pos hpn]
          have e1 : n + 2 - 2 - p + q = n - p + q := by omega
          rw [e1]
          have hc := Nat.choose_mul (n := a) (k := n + 2) (s := 2) (by omega)
          have e2 : n + 2 - 2 = n := by omega
          rw [e2] at hc
          have hc' : ((n + 2).choose 2 : ℝ) * (a.choose (n + 2) : ℝ) =
              (a.choose 2 : ℝ) * ((a - 2).choose n : ℝ) := by
            have : ((a.choose (n + 2) * (n + 2).choose 2 : ℕ) : ℝ) =
                ((a.choose 2 * (a - 2).choose n : ℕ) : ℝ) := by rw [hc]
            push_cast at this; linarith
          rw [hc']
          have key := hloc n hpn (by omega)
          have hC : (0 : ℝ) ≤ ((n - p + q).choose q : ℝ) * ((a.choose 2 : ℝ) * ((a - 2).choose n : ℝ)) := by
            positivity
          calc ((n - p + q).choose q : ℝ) * ((a.choose 2 : ℝ) * ((a - 2).choose n : ℝ)) * (c * F ℓ (n + 2))
              ≤ ((n - p + q).choose q : ℝ) * ((a.choose 2 : ℝ) * ((a - 2).choose n : ℝ)) *
                (K * (φ2 * F (ℓ + 1) n)) := mul_le_mul_of_nonneg_left key hC
            _ = _ := by ring
        · rw [if_neg (by omega), if_neg hpn]; simp
    _ = (K * ((a.choose 2 : ℝ) * φ2)) * WtF F p q (ℓ + 1) (a - 2) := by
        rw [WtF, hsplit', mul_sum]; refine sum_congr rfl (fun n _ => by ring)
    _ ≤ K * (B0 * WtF F p q (ℓ + 1) (a - 2)) := by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hB0 hWnn) hK

/-- The `H`/`V` detour: `4 c W^F_{2j+1,j}(ℓ,a) ≤ B₀ W^F_{2j-1,j-1}(ℓ+1,a-2)` for `j ≥ 2`, from the
mixed inequality with constant `2`. -/
theorem detour_HV {B0 c φ2 : ℝ} (j : ℕ) (hj : 2 ≤ j) (hc : 0 ≤ c) (hB0nn : 0 ≤ B0)
    (hB0 : (a.choose 2 : ℝ) * φ2 ≤ B0)
    (hF0 : ∀ m, m ≤ a → 0 ≤ F ℓ m) (hF1 : ∀ n, n + 2 ≤ a → 0 ≤ F (ℓ + 1) n)
    (hloc : ∀ n, 2 * j - 1 ≤ n → n + 2 ≤ a → c * F ℓ (n + 2) ≤ 2 * (φ2 * F (ℓ + 1) n)) :
    4 * c * WtF F (2 * j + 1) j ℓ a ≤ B0 * WtF F (2 * j - 1) (j - 1) (ℓ + 1) (a - 2) := by
  by_cases ha : a < 2 * j + 1
  · rw [WtF_eq_zero ha, mul_zero]
    exact mul_nonneg hB0nn (WtF_nonneg fun n hpn hn => hF1 n (by omega))
  push Not at ha
  have hd := detour_secondF (F := F) (p := 2 * j - 1) (q := j - 1) (ℓ := ℓ) (by omega) (by norm_num : (0 : ℝ) ≤ 2)
    hB0 hF1 hloc
  suffices h : 2 * (4 * c * WtF F (2 * j + 1) j ℓ a) ≤ 2 * (B0 * WtF F (2 * j - 1) (j - 1) (ℓ + 1) (a - 2)) by
    linarith
  refine le_trans ?_ hd
  rw [WtF, mul_sum, mul_sum]
  refine sum_le_sum fun m hm => ?_
  rw [mem_range] at hm
  by_cases h : 2 * j + 1 ≤ m
  · rw [if_pos h, if_pos (by omega)]
    have e1 : m - (2 * j + 1) + j = m - j - 1 := by omega
    have e2 : m - 2 - (2 * j - 1) + (j - 1) = m - j - 2 := by omega
    rw [e1, e2]
    have hco : (8 : ℝ) * ((m - j - 1).choose j : ℝ) ≤ (m.choose 2 : ℝ) * ((m - j - 2).choose (j - 1) : ℝ) := by
      exact_mod_cast coeffHV j m hj h
    have hF := hF0 m (by omega)
    have hcF : 0 ≤ (a.choose m : ℝ) * (c * F ℓ m) := mul_nonneg (Nat.cast_nonneg _) (mul_nonneg hc hF)
    calc 2 * (4 * c * (((m - j - 1).choose j : ℝ) * (a.choose m : ℝ) * F ℓ m))
        = (8 * ((m - j - 1).choose j : ℝ)) * ((a.choose m : ℝ) * (c * F ℓ m)) := by ring
      _ ≤ ((m.choose 2 : ℝ) * ((m - j - 2).choose (j - 1) : ℝ)) * ((a.choose m : ℝ) * (c * F ℓ m)) :=
          mul_le_mul_of_nonneg_right hco hcF
      _ = _ := by ring
  · rw [if_neg h, if_neg (by omega)]; simp

/-- The `C'` detour: `4 c W^F_{2j+2,j+1}(ℓ,a) ≤ B₀ W^F_{2j,j}(ℓ+1,a-2)` for `j ≥ 1`, from the
mixed inequality with constant `1`. -/
theorem detour_Cf {B0 c φ2 : ℝ} (j : ℕ) (hj : 1 ≤ j) (hc : 0 ≤ c) (hB0nn : 0 ≤ B0)
    (hB0 : (a.choose 2 : ℝ) * φ2 ≤ B0)
    (hF0 : ∀ m, m ≤ a → 0 ≤ F ℓ m) (hF1 : ∀ n, n + 2 ≤ a → 0 ≤ F (ℓ + 1) n)
    (hloc : ∀ n, 2 * j ≤ n → n + 2 ≤ a → c * F ℓ (n + 2) ≤ 1 * (φ2 * F (ℓ + 1) n)) :
    4 * c * WtF F (2 * j + 2) (j + 1) ℓ a ≤ B0 * WtF F (2 * j) j (ℓ + 1) (a - 2) := by
  by_cases ha : a < 2 * j + 2
  · rw [WtF_eq_zero ha, mul_zero]
    exact mul_nonneg hB0nn (WtF_nonneg fun n hpn hn => hF1 n (by omega))
  push Not at ha
  have hd := detour_secondF (F := F) (p := 2 * j) (q := j) (ℓ := ℓ) (by omega) (by norm_num : (0 : ℝ) ≤ 1)
    hB0 hF1 hloc
  rw [one_mul] at hd
  refine le_trans ?_ hd
  rw [WtF, mul_sum]
  refine sum_le_sum fun m hm => ?_
  rw [mem_range] at hm
  by_cases h : 2 * j + 2 ≤ m
  · rw [if_pos h, if_pos h]
    have e1 : m - (2 * j + 2) + (j + 1) = m - j - 1 := by omega
    have e2 : m - 2 - 2 * j + j = m - j - 2 := by omega
    rw [e1, e2]
    have hco : (4 : ℝ) * ((m - j - 1).choose (j + 1) : ℝ) ≤ (m.choose 2 : ℝ) * ((m - j - 2).choose j : ℝ) := by
      exact_mod_cast coeffC j m hj h
    have hF := hF0 m (by omega)
    have hcF : 0 ≤ (a.choose m : ℝ) * (c * F ℓ m) := mul_nonneg (Nat.cast_nonneg _) (mul_nonneg hc hF)
    calc 4 * c * (((m - j - 1).choose (j + 1) : ℝ) * (a.choose m : ℝ) * F ℓ m)
        = (4 * ((m - j - 1).choose (j + 1) : ℝ)) * ((a.choose m : ℝ) * (c * F ℓ m)) := by ring
      _ ≤ ((m.choose 2 : ℝ) * ((m - j - 2).choose j : ℝ)) * ((a.choose m : ℝ) * (c * F ℓ m)) :=
          mul_le_mul_of_nonneg_right hco hcF
      _ = _ := by ring
  · rw [if_neg h, if_neg h]; simp

end WtF

end Szkraw
