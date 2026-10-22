import Szkraw.VRQuadLeib
import Szkraw.VRQuadKey
import Szkraw.VRMoves2

/-!
# Theorem 8.11: the setting, the weights and the detours

`ν` is the padded Newton sequence of the profile and `u` that of `c`, with
`f_n(ℓ) = iterShift ν ℓ n` and, on `Ω`, `φ_n(ℓ) = iterShift u ℓ n = Φ_n(ℓ, f(ℓ))` (quadratic Leibniz
rule). The Newton sequence of `b` splits as `ψ_n = h_n - v_n - w_n`. The detours: `B` from the weighted
inequality (eq. `quad-B`) with factor `8(n-1)/((n+1)(n+2))`, `C'` and `H` from
`c_{ℓ+1} f_{n+2}(ℓ) ≤ φ₂(ℓ) f_n(ℓ+1)`, `V` and `W` with factors `n²/((n+1)(n+2))` and
`n(n-1)/((n+1)(n+2))`; the constants are `4` (`B`, `C'`, `H`, `V`) and `3` (`W`).
-/

set_option linter.unusedSectionVars false

namespace Szkraw

open Finset

/-- The Newton sequence of `b`. -/
noncomputable def quadW (ν u : ℕ → ℝ) (i : ℕ) : ℝ := ν i - u i

/-- The setting of Theorem 8.11: `ν` is log-concave without internal zeros with `ν 0 = 0 < ν 1`,
`u ≥ 0` satisfies the Leibniz rule on `Ω`, and `b`, with values `dd (quadW ν u) m`, is nondecreasing. -/
structure QuadSetting (N : ℕ) (r t τ : ℝ) (ν u : ℕ → ℝ) : Prop where
  hN : 1 ≤ N
  hr : 0 < r
  ht : 0 ≤ t
  hτ : 0 ≤ τ
  hν : LCNZ ν
  hν0 : ν 0 = 0
  hν1 : 0 < ν 1
  hu_nn : ∀ i, 0 ≤ u i
  hφ : ∀ ℓ n, ℓ + n ≤ N → Szkraw.iterShift u ℓ n = PhiQ r t τ ℓ n (Szkraw.iterShift ν ℓ)
  hb : ∀ m, m < N → dd (quadW ν u) m ≤ dd (quadW ν u) (m + 1)

/-- `h_n(ℓ) = (1 - ρ(ℓ+n)) f_n(ℓ)`. -/
noncomputable def hQ (r t τ : ℝ) (ν : ℕ → ℝ) (ℓ n : ℕ) : ℝ :=
  (1 - rhoN r t τ (ℓ + n)) * Szkraw.iterShift ν ℓ n

/-- `v_n(ℓ) = n Δρ(ℓ+n-1) f_{n-1}(ℓ)`. -/
noncomputable def vQ (t τ : ℝ) (ν : ℕ → ℝ) (ℓ n : ℕ) : ℝ :=
  (n : ℝ) * drhoQ t τ ((ℓ : ℝ) + n - 1) * Szkraw.iterShift ν ℓ (n - 1)

/-- `w_n(ℓ) = C(n,2) τ f_{n-2}(ℓ)`. -/
noncomputable def wQ (τ : ℝ) (ν : ℕ → ℝ) (ℓ n : ℕ) : ℝ :=
  (n : ℝ) * ((n : ℝ) - 1) / 2 * τ * Szkraw.iterShift ν ℓ (n - 2)

/-- `H_j = W^h_{2j+1,j}`. -/
noncomputable def quadH (r t τ : ℝ) (ν : ℕ → ℝ) (j ℓ a : ℕ) : ℝ := WtF (hQ r t τ ν) (2 * j + 1) j ℓ a

/-- `V_j = W^v_{2j+1,j}`. -/
noncomputable def quadV (t τ : ℝ) (ν : ℕ → ℝ) (j ℓ a : ℕ) : ℝ := WtF (vQ t τ ν) (2 * j + 1) j ℓ a

/-- `W_j = W^w_{2j+1,j}`. -/
noncomputable def quadWw (τ : ℝ) (ν : ℕ → ℝ) (j ℓ a : ℕ) : ℝ := WtF (wQ τ ν) (2 * j + 1) j ℓ a

/-- Detour factor of `B`: `8(n-1)/((n+1)(n+2))`. -/
noncomputable def kapB (n : ℕ) : ℝ := 8 * ((n : ℝ) - 1) / (((n : ℝ) + 1) * ((n : ℝ) + 2))

/-- Detour factor of `V`: `n²/((n+1)(n+2))`. -/
noncomputable def kapV (n : ℕ) : ℝ := (n : ℝ) ^ 2 / (((n : ℝ) + 1) * ((n : ℝ) + 2))

/-- Detour factor of `W`: `n(n-1)/((n+1)(n+2))`. -/
noncomputable def kapW (n : ℕ) : ℝ := (n : ℝ) * ((n : ℝ) - 1) / (((n : ℝ) + 1) * ((n : ℝ) + 2))

theorem PhiQ_zero (r t τ base : ℝ) (v : ℕ → ℝ) : PhiQ r t τ base 0 v = rhoQ r t τ base * v 0 := by
  simp [PhiQ]

theorem rhoQ_add (r t τ : ℝ) (ℓ n : ℕ) : rhoQ r t τ ((ℓ : ℝ) + n) = rhoN r t τ (ℓ + n) := by
  rw [rhoN_eq, Nat.cast_add]

/-- `ρ(x+k) = ρ(x) + k Δρ(x) + τ C(k,2)`. -/
theorem rhoN_add (r t τ : ℝ) (x k : ℕ) :
    rhoN r t τ (x + k) = rhoN r t τ x + k * (t + τ * x) + τ * (k.choose 2 : ℝ) := by
  unfold rhoN; rw [choose2_real, choose2_real, choose2_real]; push_cast; ring

/-! ### A detour with an index-dependent factor -/

/-- Generic detour: from `κ n · c F(ℓ,n+2) ≤ φ₂ F(ℓ+1,n)` for `p ≤ n ≤ a-2`, `C(a,2) φ₂ ≤ B₀` and the
coefficient bounds `κ₀ C(m-p-2+Q, Q) ≤ C(m-2-p+q, q) C(m,2) κ(m-2)`:
`κ₀ c W^F_{p+2,Q}(ℓ,a) ≤ B₀ W^F_{p,q}(ℓ+1,a-2)`. -/
theorem detour_gen {F : ℕ → ℕ → ℝ} {p q Q ℓ a : ℕ} {B0 c φ2 κ0 : ℝ} {κ : ℕ → ℝ} (hc : 0 ≤ c)
    (hB0nn : 0 ≤ B0) (hB0 : (a.choose 2 : ℝ) * φ2 ≤ B0)
    (hF0 : ∀ m, m ≤ a → 0 ≤ F ℓ m) (hF1 : ∀ n, 0 ≤ F (ℓ + 1) n)
    (hloc : ∀ n, p ≤ n → n + 2 ≤ a → κ n * (c * F ℓ (n + 2)) ≤ φ2 * F (ℓ + 1) n)
    (hcoef : ∀ m, p + 2 ≤ m → m ≤ a → κ0 * ((m - (p + 2) + Q).choose Q : ℝ) ≤
      ((m - 2 - p + q).choose q : ℝ) * (m.choose 2 : ℝ) * κ (m - 2)) :
    κ0 * c * WtF F (p + 2) Q ℓ a ≤ B0 * WtF F p q (ℓ + 1) (a - 2) := by
  have hWnn : 0 ≤ WtF F p q (ℓ + 1) (a - 2) := WtF_nonneg fun n _ _ => hF1 n
  by_cases ha : a < p + 2
  · rw [WtF_eq_zero ha, mul_zero]; exact mul_nonneg hB0nn hWnn
  push Not at ha
  set G : ℕ → ℝ := fun m => (if p + 2 ≤ m then ((m - 2 - p + q).choose q : ℝ) * (m.choose 2 : ℝ) * κ (m - 2)
    else 0) * (a.choose m : ℝ) * (c * F ℓ m) with hG
  have step1 : κ0 * c * WtF F (p + 2) Q ℓ a ≤ ∑ m ∈ range (a + 1), G m := by
    rw [WtF, mul_sum]
    refine sum_le_sum fun m hm => ?_
    rw [mem_range] at hm
    simp only [hG]
    by_cases h : p + 2 ≤ m
    · rw [if_pos h, if_pos h]
      have hco := hcoef m h (by omega)
      have hcF : 0 ≤ (a.choose m : ℝ) * (c * F ℓ m) :=
        mul_nonneg (Nat.cast_nonneg _) (mul_nonneg hc (hF0 m (by omega)))
      calc κ0 * c * (((m - (p + 2) + Q).choose Q : ℝ) * (a.choose m : ℝ) * F ℓ m)
          = (κ0 * ((m - (p + 2) + Q).choose Q : ℝ)) * ((a.choose m : ℝ) * (c * F ℓ m)) := by ring
        _ ≤ (((m - 2 - p + q).choose q : ℝ) * (m.choose 2 : ℝ) * κ (m - 2)) * ((a.choose m : ℝ) * (c * F ℓ m)) :=
            mul_le_mul_of_nonneg_right hco hcF
        _ = _ := by ring
    · rw [if_neg h, if_neg h]; simp
  have hre : ∑ m ∈ range (a + 1), G m = ∑ n ∈ range (a - 1), G (n + 2) := by
    rw [reindex2 G (a - 1) (by simp [hG]) (by simp [hG]), show a - 1 + 2 = a + 1 by omega]
  have step2 : ∑ n ∈ range (a - 1), G (n + 2) ≤ ∑ n ∈ range (a - 1),
      (if p ≤ n then ((n - p + q).choose q : ℝ) else 0) * ((a - 2).choose n : ℝ) * F (ℓ + 1) n *
        ((a.choose 2 : ℝ) * φ2) := by
    refine sum_le_sum fun n hn => ?_
    rw [mem_range] at hn
    simp only [hG]
    by_cases hpn : p ≤ n
    · rw [if_pos (by omega), if_pos hpn, show n + 2 - 2 = n by omega]
      have hc' : ((n + 2).choose 2 : ℝ) * (a.choose (n + 2) : ℝ) = (a.choose 2 : ℝ) * ((a - 2).choose n : ℝ) := by
        have hc2 := Nat.choose_mul (n := a) (k := n + 2) (s := 2) (by omega)
        rw [show n + 2 - 2 = n by omega] at hc2
        have : ((a.choose (n + 2) * (n + 2).choose 2 : ℕ) : ℝ) = ((a.choose 2 * (a - 2).choose n : ℕ) : ℝ) := by
          rw [hc2]
        push_cast at this; linarith
      have key := hloc n hpn (by omega)
      have hC : (0 : ℝ) ≤ ((n - p + q).choose q : ℝ) * ((a.choose 2 : ℝ) * ((a - 2).choose n : ℝ)) := by
        positivity
      calc ((n - p + q).choose q : ℝ) * ((n + 2).choose 2 : ℝ) * κ n * (a.choose (n + 2) : ℝ) * (c * F ℓ (n + 2))
          = ((n - p + q).choose q : ℝ) * (((n + 2).choose 2 : ℝ) * (a.choose (n + 2) : ℝ)) *
              (κ n * (c * F ℓ (n + 2))) := by ring
        _ = ((n - p + q).choose q : ℝ) * ((a.choose 2 : ℝ) * ((a - 2).choose n : ℝ)) *
              (κ n * (c * F ℓ (n + 2))) := by rw [hc']
        _ ≤ ((n - p + q).choose q : ℝ) * ((a.choose 2 : ℝ) * ((a - 2).choose n : ℝ)) * (φ2 * F (ℓ + 1) n) :=
            mul_le_mul_of_nonneg_left key hC
        _ = _ := by ring
    · rw [if_neg (by omega), if_neg hpn]; simp
  have step3 : ∑ n ∈ range (a - 1), (if p ≤ n then ((n - p + q).choose q : ℝ) else 0) *
      ((a - 2).choose n : ℝ) * F (ℓ + 1) n * ((a.choose 2 : ℝ) * φ2) =
      ((a.choose 2 : ℝ) * φ2) * WtF F p q (ℓ + 1) (a - 2) := by
    rw [WtF, show a - 2 + 1 = a - 1 by omega, mul_sum]; exact sum_congr rfl fun n _ => by ring
  have step4 : ((a.choose 2 : ℝ) * φ2) * WtF F p q (ℓ + 1) (a - 2) ≤ B0 * WtF F p q (ℓ + 1) (a - 2) :=
    mul_le_mul_of_nonneg_right hB0 hWnn
  linarith [step1, hre, step2, step3, step4]

/-- `M C(M-1, j-1) = j C(M, j)`. -/
theorem choose_pred_rel {M j : ℕ} (hM : 1 ≤ M) (hj : 1 ≤ j) :
    (M : ℝ) * ((M - 1).choose (j - 1) : ℝ) = (M.choose j : ℝ) * (j : ℝ) := by
  have key := Nat.add_one_mul_choose_eq (M - 1) (j - 1)
  rw [show M - 1 + 1 = M by omega, show j - 1 + 1 = j by omega] at key
  exact_mod_cast key

/-- Coefficients of the `B` detour: `4 C(m-j-2, j) ≤ 4(m-3) C(m-j-3, j-1)`. -/
theorem coefB {j m : ℕ} (hj : 1 ≤ j) (hm : 2 * j + 2 ≤ m) :
    4 * ((m - (2 * j + 2) + j).choose j : ℝ) ≤
      ((m - 2 - 2 * j + (j - 1)).choose (j - 1) : ℝ) * (m.choose 2 : ℝ) * kapB (m - 2) := by
  obtain ⟨M, hM⟩ : ∃ M, M + j + 2 = m := ⟨m - j - 2, by omega⟩
  rw [show m - (2 * j + 2) + j = M by omega, show m - 2 - 2 * j + (j - 1) = M - 1 by omega]
  have hrel := choose_pred_rel (M := M) (j := j) (by omega) hj
  have hMm : (M : ℝ) + j + 2 = m := by exact_mod_cast hM
  have hm4 : (4 : ℝ) ≤ m := by exact_mod_cast (show 4 ≤ m by omega)
  have hk : (m.choose 2 : ℝ) * kapB (m - 2) = 4 * ((m : ℝ) - 3) := by
    unfold kapB
    rw [choose2_real, Nat.cast_sub (by omega : 2 ≤ m), Nat.cast_ofNat, show (m : ℝ) - 2 + 1 = (m : ℝ) - 1 by ring,
      show (m : ℝ) - 2 + 2 = (m : ℝ) by ring]
    have h1 : (m : ℝ) - 1 ≠ 0 := by linarith
    have h2 : (m : ℝ) ≠ 0 := by linarith
    field_simp
    ring
  rw [mul_assoc, hk]
  have hX : (0 : ℝ) ≤ ((M - 1).choose (j - 1) : ℝ) := Nat.cast_nonneg _
  have hj' : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hle : (M : ℝ) ≤ j * ((m : ℝ) - 3) := by
    nlinarith [mul_nonneg (sub_nonneg.2 hj') (by linarith : (0 : ℝ) ≤ (m : ℝ) - 2)]
  have h1 : (j : ℝ) * (4 * (M.choose j : ℝ)) ≤ (j : ℝ) * (((M - 1).choose (j - 1) : ℝ) * (4 * ((m : ℝ) - 3))) := by
    have e : (j : ℝ) * (4 * (M.choose j : ℝ)) = 4 * ((M : ℝ) * ((M - 1).choose (j - 1) : ℝ)) := by
      rw [hrel]; ring
    rw [e]
    have := mul_le_mul_of_nonneg_right hle hX
    nlinarith
  exact le_of_mul_le_mul_left h1 (by linarith)

/-- Coefficients of the `V` detour: `8(m-j-1) ≤ j(m-2)²`. -/
theorem coefV {j m : ℕ} (hj : 2 ≤ j) (hm : 2 * j + 1 ≤ m) :
    4 * ((m - (2 * j - 1 + 2) + j).choose j : ℝ) ≤
      ((m - 2 - (2 * j - 1) + (j - 1)).choose (j - 1) : ℝ) * (m.choose 2 : ℝ) * kapV (m - 2) := by
  obtain ⟨M, hM⟩ : ∃ M, M + j + 1 = m := ⟨m - j - 1, by omega⟩
  rw [show m - (2 * j - 1 + 2) + j = M by omega, show m - 2 - (2 * j - 1) + (j - 1) = M - 1 by omega]
  have hrel := choose_pred_rel (M := M) (j := j) (by omega) (by omega)
  have hMm : (M : ℝ) + j + 1 = m := by exact_mod_cast hM
  have hm5 : (5 : ℝ) ≤ m := by exact_mod_cast (show 5 ≤ m by omega)
  have hk : (m.choose 2 : ℝ) * kapV (m - 2) = ((m : ℝ) - 2) ^ 2 / 2 := by
    unfold kapV
    rw [choose2_real, Nat.cast_sub (by omega : 2 ≤ m), Nat.cast_ofNat, show (m : ℝ) - 2 + 1 = (m : ℝ) - 1 by ring,
      show (m : ℝ) - 2 + 2 = (m : ℝ) by ring]
    have h1 : (m : ℝ) - 1 ≠ 0 := by linarith
    have h2 : (m : ℝ) ≠ 0 := by linarith
    field_simp
  rw [mul_assoc, hk]
  have hX : (0 : ℝ) ≤ ((M - 1).choose (j - 1) : ℝ) := Nat.cast_nonneg _
  have hj' : (2 : ℝ) ≤ j := by exact_mod_cast hj
  have hle : 8 * (M : ℝ) ≤ j * ((m : ℝ) - 2) ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.2 hj') (sq_nonneg ((m : ℝ) - 2)), sq_nonneg ((m : ℝ) - 4)]
  have h1 : (j : ℝ) * (4 * (M.choose j : ℝ)) ≤ (j : ℝ) * (((M - 1).choose (j - 1) : ℝ) * (((m : ℝ) - 2) ^ 2 / 2)) := by
    have e : (j : ℝ) * (4 * (M.choose j : ℝ)) = 4 * ((M : ℝ) * ((M - 1).choose (j - 1) : ℝ)) := by
      rw [hrel]; ring
    rw [e]
    have := mul_le_mul_of_nonneg_right hle hX
    nlinarith
  exact le_of_mul_le_mul_left h1 (by linarith)

/-- Coefficients of the `W` detour: `6(m-j-1) ≤ j(m-2)(m-3)`. -/
theorem coefW {j m : ℕ} (hj : 2 ≤ j) (hm : 2 * j + 1 ≤ m) :
    3 * ((m - (2 * j - 1 + 2) + j).choose j : ℝ) ≤
      ((m - 2 - (2 * j - 1) + (j - 1)).choose (j - 1) : ℝ) * (m.choose 2 : ℝ) * kapW (m - 2) := by
  obtain ⟨M, hM⟩ : ∃ M, M + j + 1 = m := ⟨m - j - 1, by omega⟩
  rw [show m - (2 * j - 1 + 2) + j = M by omega, show m - 2 - (2 * j - 1) + (j - 1) = M - 1 by omega]
  have hrel := choose_pred_rel (M := M) (j := j) (by omega) (by omega)
  have hMm : (M : ℝ) + j + 1 = m := by exact_mod_cast hM
  have hm5 : (5 : ℝ) ≤ m := by exact_mod_cast (show 5 ≤ m by omega)
  have hk : (m.choose 2 : ℝ) * kapW (m - 2) = ((m : ℝ) - 2) * ((m : ℝ) - 3) / 2 := by
    unfold kapW
    rw [choose2_real, Nat.cast_sub (by omega : 2 ≤ m), Nat.cast_ofNat, show (m : ℝ) - 2 + 1 = (m : ℝ) - 1 by ring,
      show (m : ℝ) - 2 + 2 = (m : ℝ) by ring]
    have h1 : (m : ℝ) - 1 ≠ 0 := by linarith
    have h2 : (m : ℝ) ≠ 0 := by linarith
    field_simp
    ring
  rw [mul_assoc, hk]
  have hX : (0 : ℝ) ≤ ((M - 1).choose (j - 1) : ℝ) := Nat.cast_nonneg _
  have hj' : (2 : ℝ) ≤ j := by exact_mod_cast hj
  have hle : 6 * (M : ℝ) ≤ j * (((m : ℝ) - 2) * ((m : ℝ) - 3)) := by
    nlinarith [mul_nonneg (sub_nonneg.2 hj') (mul_nonneg (by linarith : (0 : ℝ) ≤ (m : ℝ) - 2)
      (by linarith : (0 : ℝ) ≤ (m : ℝ) - 3)),
      mul_nonneg (by linarith : (0 : ℝ) ≤ (m : ℝ) - 3) (by linarith : (0 : ℝ) ≤ (m : ℝ) - 5)]
  have h1 : (j : ℝ) * (3 * (M.choose j : ℝ)) ≤
      (j : ℝ) * (((M - 1).choose (j - 1) : ℝ) * (((m : ℝ) - 2) * ((m : ℝ) - 3) / 2)) := by
    have e : (j : ℝ) * (3 * (M.choose j : ℝ)) = 3 * ((M : ℝ) * ((M - 1).choose (j - 1) : ℝ)) := by
      rw [hrel]; ring
    rw [e]
    have := mul_le_mul_of_nonneg_right hle hX
    nlinarith
  exact le_of_mul_le_mul_left h1 (by linarith)

/-! ### Consequences of the setting -/

section Setting

variable {N : ℕ} {r t τ : ℝ} {ν u : ℕ → ℝ} (S : QuadSetting N r t τ ν u)
include S

theorem QuadSetting.f_nn (ℓ n : ℕ) : 0 ≤ Szkraw.iterShift ν ℓ n := iterShift_nonneg S.hν ℓ n

theorem QuadSetting.f1_pos (ℓ : ℕ) : 0 < Szkraw.iterShift ν ℓ 1 := iterShift_one_pos S.hν S.hν1 ℓ

theorem QuadSetting.g_nn (ℓ n : ℕ) : 0 ≤ Szkraw.iterShift u ℓ n := iterShift_nonneg_of S.hu_nn ℓ n

theorem QuadSetting.cc_nn (ℓ : ℕ) : 0 ≤ dd u (ℓ + 1) := S.g_nn (ℓ + 1) 0

theorem QuadSetting.rho_pos (i : ℕ) : 0 < rhoN r t τ i := by
  have := S.hr; have := S.ht; have := S.hτ; unfold rhoN; positivity

theorem QuadSetting.rho_mono {i j : ℕ} (h : i ≤ j) : rhoN r t τ i ≤ rhoN r t τ j := by
  unfold rhoN
  have hij : (i : ℝ) ≤ j := by exact_mod_cast h
  have hc : (i.choose 2 : ℝ) ≤ (j.choose 2 : ℝ) := by exact_mod_cast Nat.choose_le_choose 2 h
  have := mul_le_mul_of_nonneg_left hij S.ht
  have := mul_le_mul_of_nonneg_left hc S.hτ
  linarith

theorem QuadSetting.drho_nn {x : ℝ} (hx : 0 ≤ x) : 0 ≤ drhoQ t τ x := by
  unfold drhoQ; have := S.ht; have := S.hτ; positivity

/-- `φ_n ≥ ρ(ℓ+n) f_n`. -/
theorem QuadSetting.Phi_ge (ℓ n : ℕ) :
    rhoN r t τ (ℓ + n) * Szkraw.iterShift ν ℓ n ≤ PhiQ r t τ ℓ n (Szkraw.iterShift ν ℓ) := by
  have h2 : 0 ≤ (n : ℝ) * drhoQ t τ ((ℓ : ℝ) + n - 1) * Szkraw.iterShift ν ℓ (n - 1) := by
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; simp
    · have h1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
      have hd := S.drho_nn (x := (ℓ : ℝ) + n - 1) (by have := (Nat.cast_nonneg ℓ : (0 : ℝ) ≤ ℓ); linarith)
      exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hd) (S.f_nn ℓ _)
  have h3 : 0 ≤ (n : ℝ) * ((n : ℝ) - 1) / 2 * τ * Szkraw.iterShift ν ℓ (n - 2) := by
    rw [← choose2_real]; exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) S.hτ) (S.f_nn ℓ _)
  unfold PhiQ
  rw [rhoQ_add]
  linarith

theorem QuadSetting.Phi_nn (ℓ n : ℕ) : 0 ≤ PhiQ r t τ ℓ n (Szkraw.iterShift ν ℓ) :=
  le_trans (mul_nonneg (S.rho_pos _).le (S.f_nn ℓ n)) (S.Phi_ge ℓ n)

theorem QuadSetting.hu1 : 0 < u 1 := by
  have h := S.hφ 0 1 (by have := S.hN; omega)
  have e : Szkraw.iterShift u 0 1 = u 1 := rfl
  rw [e] at h
  rw [h]
  have := S.Phi_ge 0 1
  have := mul_pos (S.rho_pos (0 + 1)) (S.f1_pos 0)
  linarith

theorem QuadSetting.dd_u {m : ℕ} (hm : m ≤ N) : dd u m = rhoN r t τ m * dd ν m := by
  show Szkraw.iterShift u m 0 = rhoN r t τ m * Szkraw.iterShift ν m 0
  rw [S.hφ m 0 (by omega), PhiQ_zero, rhoN_eq]

theorem QuadSetting.dd_w {m : ℕ} (hm : m ≤ N) : dd (quadW ν u) m = (1 - rhoN r t τ m) * dd ν m := by
  have e : dd (quadW ν u) m = dd ν m - dd u m := by
    unfold dd quadW; rw [iterShift_sub]
  rw [e, S.dd_u hm]; ring

theorem QuadSetting.b_chain {ℓ k : ℕ} (h : ℓ + k ≤ N) : dd (quadW ν u) ℓ ≤ dd (quadW ν u) (ℓ + k) := by
  induction k with
  | zero => simp
  | succ k ih => exact le_trans (ih (by omega)) (S.hb (ℓ + k) (by omega))

theorem QuadSetting.rho_le_one {i : ℕ} (hi : i ≤ N) : rhoN r t τ i ≤ 1 := by
  have hc := S.b_chain (ℓ := 0) (k := N) (by omega)
  have h0 : dd (quadW ν u) 0 = 0 := by
    rw [S.dd_w (by omega)]; show _ * ν 0 = 0; rw [S.hν0]; ring
  rw [h0, zero_add, S.dd_w le_rfl] at hc
  have hd : 0 < dd ν N := dd_pos S.hν S.hν1 S.hN
  have h1 : rhoN r t τ N ≤ 1 := by
    by_contra hneg; push Not at hneg
    have : (1 - rhoN r t τ N) * dd ν N < 0 := mul_neg_of_neg_of_pos (by linarith) hd
    linarith
  exact le_trans (S.rho_mono hi) h1

/-- `ψ_n = h_n - v_n - w_n` on `Ω`. -/
theorem QuadSetting.psi {ℓ n : ℕ} (h : ℓ + n ≤ N) :
    Szkraw.iterShift (quadW ν u) ℓ n = hQ r t τ ν ℓ n - vQ t τ ν ℓ n - wQ τ ν ℓ n := by
  unfold quadW
  rw [iterShift_sub, S.hφ ℓ n h]
  unfold PhiQ hQ vQ wQ
  rw [rhoQ_add]; ring

theorem QuadSetting.dd_le (ℓ : ℕ) : Szkraw.iterShift ν ℓ 0 ≤ ℓ * Szkraw.iterShift ν ℓ 1 := by
  induction ℓ with
  | zero => show ν 0 ≤ _; rw [S.hν0]; simp
  | succ ℓ ih =>
    have e0 : Szkraw.iterShift ν (ℓ + 1) 0 = Szkraw.iterShift ν ℓ 0 + Szkraw.iterShift ν ℓ 1 := rfl
    have e1 : Szkraw.iterShift ν (ℓ + 1) 1 = Szkraw.iterShift ν ℓ 1 + Szkraw.iterShift ν ℓ 2 := rfl
    rw [e0, e1]
    have h2 := S.f_nn ℓ 2
    have h1 := S.f_nn ℓ 1
    have : 0 ≤ ((ℓ : ℝ) + 1) * Szkraw.iterShift ν ℓ 2 := mul_nonneg (by positivity) h2
    push_cast; nlinarith

/-- The mixed inequality `c_{ℓ+1} f_{l+2}(ℓ) ≤ φ₂(ℓ) f_l(ℓ+1)` for `ℓ + l + 2 ≤ N`, `l ≥ 1`. -/
theorem QuadSetting.mi {ℓ l : ℕ} (h : ℓ + l + 2 ≤ N) (hl : 1 ≤ l) :
    dd u (ℓ + 1) * Szkraw.iterShift ν ℓ (l + 2) ≤ Szkraw.iterShift u ℓ 2 * Szkraw.iterShift ν (ℓ + 1) l := by
  rw [S.dd_u (by omega), S.hφ ℓ 2 (by omega)]
  have h83 := lemma_8_3 S.hν ℓ (i := 2) (l := l) (by norm_num) hl
  rw [add_comm 2 l] at h83
  have hφ := S.Phi_ge ℓ 2
  have hρ : rhoN r t τ (ℓ + 1) ≤ rhoN r t τ (ℓ + 2) := S.rho_mono (by omega)
  have hρ0 := S.rho_pos (ℓ + 1)
  have hf2 := S.f_nn ℓ 2
  have hf1 := S.f_nn (ℓ + 1) l
  have hdd : dd ν (ℓ + 1) = Szkraw.iterShift ν (ℓ + 1) 0 := rfl
  rw [hdd]
  calc rhoN r t τ (ℓ + 1) * Szkraw.iterShift ν (ℓ + 1) 0 * Szkraw.iterShift ν ℓ (l + 2)
      = rhoN r t τ (ℓ + 1) * (Szkraw.iterShift ν (ℓ + 1) 0 * Szkraw.iterShift ν ℓ (l + 2)) := by ring
    _ ≤ rhoN r t τ (ℓ + 1) * (Szkraw.iterShift ν ℓ 2 * Szkraw.iterShift ν (ℓ + 1) l) :=
        mul_le_mul_of_nonneg_left h83 hρ0.le
    _ = (rhoN r t τ (ℓ + 1) * Szkraw.iterShift ν ℓ 2) * Szkraw.iterShift ν (ℓ + 1) l := by ring
    _ ≤ (rhoN r t τ (ℓ + 2) * Szkraw.iterShift ν ℓ 2) * Szkraw.iterShift ν (ℓ + 1) l :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hρ hf2) hf1
    _ ≤ PhiQ r t τ ℓ 2 (Szkraw.iterShift ν ℓ) * Szkraw.iterShift ν (ℓ + 1) l :=
        mul_le_mul_of_nonneg_right hφ hf1

theorem QuadSetting.B0_ge_phi2 (ℓ a : ℕ) :
    (a.choose 2 : ℝ) * Szkraw.iterShift u ℓ 2 ≤ Wt u 2 0 ℓ a := by
  rcases Nat.lt_or_ge a 2 with ha | ha
  · rw [Nat.choose_eq_zero_of_lt ha, Nat.cast_zero, zero_mul]; exact Wt_nonneg_of S.hu_nn _ _ _ _
  · have := Wt_ge_term_of S.hu_nn 2 0 ℓ a 2 le_rfl ha
    simpa using this

/-- `B₀(ℓ,a) ≥ ρ(ℓ+1) Y` on `Ω`. -/
theorem QuadSetting.B0_ge {ℓ a : ℕ} (h : ℓ + a ≤ N) :
    rhoN r t τ (ℓ + 1) * Wt ν 2 0 ℓ a ≤ Wt u 2 0 ℓ a := by
  unfold Wt
  rw [mul_sum]
  refine sum_le_sum fun n hn => ?_
  rw [mem_range] at hn
  by_cases h2 : 2 ≤ n
  · rw [if_pos h2]
    have hφ := S.Phi_ge ℓ n
    rw [← S.hφ ℓ n (by omega)] at hφ
    have hρ : rhoN r t τ (ℓ + 1) ≤ rhoN r t τ (ℓ + n) := S.rho_mono (by omega)
    have hc : (0 : ℝ) ≤ ((n - 2 + 0).choose 0 : ℝ) * (a.choose n : ℝ) := by positivity
    have hf := S.f_nn ℓ n
    calc rhoN r t τ (ℓ + 1) * (((n - 2 + 0).choose 0 : ℝ) * (a.choose n : ℝ) * Szkraw.iterShift ν ℓ n)
        = (((n - 2 + 0).choose 0 : ℝ) * (a.choose n : ℝ)) * (rhoN r t τ (ℓ + 1) * Szkraw.iterShift ν ℓ n) := by
          ring
      _ ≤ (((n - 2 + 0).choose 0 : ℝ) * (a.choose n : ℝ)) * Szkraw.iterShift u ℓ n :=
          mul_le_mul_of_nonneg_left (le_trans (mul_le_mul_of_nonneg_right hρ hf) hφ) hc
      _ = _ := by ring
  · rw [if_neg h2]; simp

/-! ### Nonnegativity of the weights -/

theorem QuadSetting.hQ_nn {ℓ n : ℕ} (h : ℓ + n ≤ N) : 0 ≤ hQ r t τ ν ℓ n :=
  mul_nonneg (by linarith [S.rho_le_one h]) (S.f_nn ℓ n)

theorem QuadSetting.vQ_nn (ℓ n : ℕ) : 0 ≤ vQ t τ ν ℓ n := by
  unfold vQ
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp
  · have h1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hd := S.drho_nn (x := (ℓ : ℝ) + n - 1) (by have := (Nat.cast_nonneg ℓ : (0 : ℝ) ≤ ℓ); linarith)
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hd) (S.f_nn ℓ _)

theorem QuadSetting.wQ_nn (ℓ n : ℕ) : 0 ≤ wQ τ ν ℓ n := by
  unfold wQ
  rw [← choose2_real]; exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) S.hτ) (S.f_nn ℓ _)

theorem QuadSetting.H_nn {j ℓ a : ℕ} (h : ℓ + a ≤ N) : 0 ≤ quadH r t τ ν j ℓ a :=
  WtF_nonneg fun n _ hn => S.hQ_nn (by omega)

theorem QuadSetting.V_nn (j ℓ a : ℕ) : 0 ≤ quadV t τ ν j ℓ a := WtF_nonneg fun n _ _ => S.vQ_nn ℓ n

theorem QuadSetting.W_nn (j ℓ a : ℕ) : 0 ≤ quadWw τ ν j ℓ a := WtF_nonneg fun n _ _ => S.wQ_nn ℓ n

/-- The split `A_j = H_j - V_j - W_j` on `Ω`. -/
theorem QuadSetting.A_split {j ℓ a : ℕ} (h : ℓ + a ≤ N) :
    Wt (quadW ν u) (2 * j + 1) j ℓ a = quadH r t τ ν j ℓ a - quadV t τ ν j ℓ a - quadWw τ ν j ℓ a := by
  rw [Wt_eq_WtF, quadH, quadV, quadWw, ← WtF_sub, ← WtF_sub]
  exact WtF_congr fun n hn => S.psi (by omega)

theorem QuadSetting.wC_eq (j ℓ a : ℕ) : wC u (quadW ν u) j ℓ a = Wt ν (2 * j + 2) (j + 1) ℓ a := by
  unfold wC
  rw [Wt_add]
  congr 1
  funext i; unfold quadW; ring

theorem QuadSetting.A0_nn {ℓ a : ℕ} (h : ℓ + a ≤ N) : 0 ≤ Wt (quadW ν u) 1 0 ℓ a := by
  rw [Wt_one_zero]
  linarith [S.b_chain h]

/-! ### The detours -/

/-- The `B` detour (from eq. `quad-B`). -/
theorem QuadSetting.domB {j ℓ a : ℕ} (hj : 1 ≤ j) (h : ℓ + a ≤ N) :
    4 * dd u (ℓ + 1) * Wt u (2 * j + 2) j ℓ a ≤ Wt u 2 0 ℓ a * Wt u (2 * j) (j - 1) (ℓ + 1) (a - 2) := by
  rw [Wt_eq_WtF u (2 * j + 2), Wt_eq_WtF u (2 * j)]
  refine detour_gen (κ := kapB) (p := 2 * j) (S.cc_nn ℓ) (Wt_nonneg_of S.hu_nn _ _ _ _) (S.B0_ge_phi2 ℓ a)
    (fun m _ => S.g_nn ℓ m) (fun n => S.g_nn (ℓ + 1) n) (fun n hn hna => ?_)
    (fun m hm hma => coefB hj hm)
  have hn2 : 2 ≤ n := by omega
  rw [S.dd_u (by omega), S.hφ ℓ (n + 2) (by omega), S.hφ ℓ 2 (by omega), S.hφ (ℓ + 1) n (by omega)]
  have hB := quadB_seq (v := Szkraw.iterShift ν ℓ) (S.hν.iterShift ℓ) (S.f1_pos ℓ) hn2 S.hr S.ht S.hτ
    (Nat.cast_nonneg ℓ) (S.dd_le ℓ)
  have e1 : (fun k => Szkraw.iterShift ν ℓ k + Szkraw.iterShift ν ℓ (k + 1)) = Szkraw.iterShift ν (ℓ + 1) := rfl
  have e2 : rhoQ r t τ ((ℓ : ℝ) + 1) = rhoN r t τ (ℓ + 1) := by rw [rhoN_eq]; push_cast; ring_nf
  have e3 : Szkraw.iterShift ν ℓ 0 + Szkraw.iterShift ν ℓ 1 = dd ν (ℓ + 1) := rfl
  rw [e1, e2, e3] at hB
  rw [show ((ℓ + 1 : ℕ) : ℝ) = (ℓ : ℝ) + 1 by push_cast; ring]
  unfold kapB
  have hpos : (0 : ℝ) < ((n : ℝ) + 1) * ((n : ℝ) + 2) := by positivity
  rw [div_mul_eq_mul_div, div_le_iff₀ hpos]
  linear_combination hB

/-- The `C'` detour. -/
theorem QuadSetting.domC {j ℓ a : ℕ} (hj : 1 ≤ j) (h : ℓ + a ≤ N) :
    4 * dd u (ℓ + 1) * Wt ν (2 * j + 2) (j + 1) ℓ a ≤ Wt u 2 0 ℓ a * Wt ν (2 * j) j (ℓ + 1) (a - 2) := by
  rw [Wt_eq_WtF, Wt_eq_WtF ν (2 * j)]
  refine detour_Cf j hj (S.cc_nn ℓ) (Wt_nonneg_of S.hu_nn _ _ _ _) (S.B0_ge_phi2 ℓ a) (fun m _ => S.f_nn ℓ m)
    (fun n _ => S.f_nn (ℓ + 1) n) (fun n hn hna => ?_)
  rw [one_mul]; exact S.mi (by omega) (by omega)

/-- The `H` detour. -/
theorem QuadSetting.domH {j ℓ a : ℕ} (hj : 2 ≤ j) (h : ℓ + a ≤ N) :
    4 * dd u (ℓ + 1) * quadH r t τ ν j ℓ a ≤ Wt u 2 0 ℓ a * quadH r t τ ν (j - 1) (ℓ + 1) (a - 2) := by
  unfold quadH
  rw [show 2 * (j - 1) + 1 = 2 * j - 1 by omega]
  refine detour_HV j hj (S.cc_nn ℓ) (Wt_nonneg_of S.hu_nn _ _ _ _) (S.B0_ge_phi2 ℓ a)
    (fun m hm => S.hQ_nn (by omega)) (fun n hn => S.hQ_nn (by omega)) (fun n hn hna => ?_)
  have hmi := S.mi (ℓ := ℓ) (l := n) (by omega) (by omega)
  unfold hQ
  have hρa := S.rho_le_one (i := ℓ + (n + 2)) (by omega)
  have hρb : rhoN r t τ (ℓ + 1 + n) ≤ rhoN r t τ (ℓ + (n + 2)) := S.rho_mono (by omega)
  have hφ2 := S.g_nn ℓ 2
  have hf1 := S.f_nn (ℓ + 1) n
  have hpf : 0 ≤ Szkraw.iterShift u ℓ 2 * Szkraw.iterShift ν (ℓ + 1) n := mul_nonneg hφ2 hf1
  calc dd u (ℓ + 1) * ((1 - rhoN r t τ (ℓ + (n + 2))) * Szkraw.iterShift ν ℓ (n + 2))
      = (1 - rhoN r t τ (ℓ + (n + 2))) * (dd u (ℓ + 1) * Szkraw.iterShift ν ℓ (n + 2)) := by ring
    _ ≤ (1 - rhoN r t τ (ℓ + (n + 2))) * (Szkraw.iterShift u ℓ 2 * Szkraw.iterShift ν (ℓ + 1) n) :=
        mul_le_mul_of_nonneg_left hmi (by linarith)
    _ ≤ (1 - rhoN r t τ (ℓ + 1 + n)) * (Szkraw.iterShift u ℓ 2 * Szkraw.iterShift ν (ℓ + 1) n) :=
        mul_le_mul_of_nonneg_right (by linarith) hpf
    _ ≤ 2 * (Szkraw.iterShift u ℓ 2 * ((1 - rhoN r t τ (ℓ + 1 + n)) * Szkraw.iterShift ν (ℓ + 1) n)) := by
        have : 0 ≤ (1 - rhoN r t τ (ℓ + 1 + n)) * (Szkraw.iterShift u ℓ 2 * Szkraw.iterShift ν (ℓ + 1) n) :=
          mul_nonneg (by linarith) hpf
        nlinarith

/-- The `V` detour. -/
theorem QuadSetting.domV {j ℓ a : ℕ} (hj : 2 ≤ j) (h : ℓ + a ≤ N) :
    4 * dd u (ℓ + 1) * quadV t τ ν j ℓ a ≤ Wt u 2 0 ℓ a * quadV t τ ν (j - 1) (ℓ + 1) (a - 2) := by
  unfold quadV
  rw [show 2 * (j - 1) + 1 = 2 * j - 1 by omega, show 2 * j + 1 = 2 * j - 1 + 2 by omega]
  refine detour_gen (κ := kapV) (S.cc_nn ℓ) (Wt_nonneg_of S.hu_nn _ _ _ _) (S.B0_ge_phi2 ℓ a)
    (fun m _ => S.vQ_nn ℓ m) (fun n => S.vQ_nn (ℓ + 1) n) (fun n hn hna => ?_)
    (fun m hm hma => coefV hj (by omega))
  have hmi := S.mi (ℓ := ℓ) (l := n - 1) (by omega) (by omega)
  rw [show n - 1 + 2 = n + 1 by omega] at hmi
  unfold vQ kapV
  rw [show n + 2 - 1 = n + 1 by omega]
  have hn3 : (3 : ℝ) ≤ n := by exact_mod_cast (show 3 ≤ n by omega)
  have hd1 : drhoQ t τ ((ℓ : ℝ) + ((n + 2 : ℕ) : ℝ) - 1) = t + τ * ((ℓ : ℝ) + n + 1) := by
    unfold drhoQ; push_cast; ring
  have hd2 : drhoQ t τ (((ℓ + 1 : ℕ) : ℝ) + n - 1) = t + τ * ((ℓ : ℝ) + n) := by
    unfold drhoQ; push_cast; ring
  rw [hd1, hd2]
  have hD2 : 0 ≤ t + τ * ((ℓ : ℝ) + n) := by have := S.ht; have := S.hτ; positivity
  have hdd : (n : ℝ) * (t + τ * ((ℓ : ℝ) + n + 1)) ≤ ((n : ℝ) + 1) * (t + τ * ((ℓ : ℝ) + n)) := by
    have : ((n : ℝ) + 1) * (t + τ * ((ℓ : ℝ) + n)) - (n : ℝ) * (t + τ * ((ℓ : ℝ) + n + 1)) = t + τ * ℓ := by ring
    have : 0 ≤ t + τ * (ℓ : ℝ) := by have := S.ht; have := S.hτ; positivity
    linarith
  have hX : 0 ≤ dd u (ℓ + 1) * Szkraw.iterShift ν ℓ (n + 1) := mul_nonneg (S.cc_nn ℓ) (S.f_nn ℓ _)
  have hpos : (0 : ℝ) < ((n : ℝ) + 1) * ((n : ℝ) + 2) := by positivity
  rw [div_mul_eq_mul_div, div_le_iff₀ hpos]
  push_cast
  have k1 : (n : ℝ) * ((n : ℝ) + 2) * ((n : ℝ) * (t + τ * ((ℓ : ℝ) + n + 1))) *
      (dd u (ℓ + 1) * Szkraw.iterShift ν ℓ (n + 1)) ≤
      (n : ℝ) * ((n : ℝ) + 2) * (((n : ℝ) + 1) * (t + τ * ((ℓ : ℝ) + n))) *
      (dd u (ℓ + 1) * Szkraw.iterShift ν ℓ (n + 1)) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hdd (by positivity)) hX
  have k2 : (n : ℝ) * ((n : ℝ) + 2) * (((n : ℝ) + 1) * (t + τ * ((ℓ : ℝ) + n))) *
      (dd u (ℓ + 1) * Szkraw.iterShift ν ℓ (n + 1)) ≤
      (n : ℝ) * ((n : ℝ) + 2) * (((n : ℝ) + 1) * (t + τ * ((ℓ : ℝ) + n))) *
      (Szkraw.iterShift u ℓ 2 * Szkraw.iterShift ν (ℓ + 1) (n - 1)) :=
    mul_le_mul_of_nonneg_left hmi (by positivity)
  linear_combination k1 + k2

/-- The `W` detour. -/
theorem QuadSetting.domW {j ℓ a : ℕ} (hj : 2 ≤ j) (h : ℓ + a ≤ N) :
    3 * dd u (ℓ + 1) * quadWw τ ν j ℓ a ≤ Wt u 2 0 ℓ a * quadWw τ ν (j - 1) (ℓ + 1) (a - 2) := by
  unfold quadWw
  rw [show 2 * (j - 1) + 1 = 2 * j - 1 by omega, show 2 * j + 1 = 2 * j - 1 + 2 by omega]
  refine detour_gen (κ := kapW) (S.cc_nn ℓ) (Wt_nonneg_of S.hu_nn _ _ _ _) (S.B0_ge_phi2 ℓ a)
    (fun m _ => S.wQ_nn ℓ m) (fun n => S.wQ_nn (ℓ + 1) n) (fun n hn hna => ?_)
    (fun m hm hma => coefW hj (by omega))
  have hmi := S.mi (ℓ := ℓ) (l := n - 2) (by omega) (by omega)
  rw [show n - 2 + 2 = n by omega] at hmi
  unfold wQ kapW
  rw [show n + 2 - 2 = n by omega]
  have hn3 : (3 : ℝ) ≤ n := by exact_mod_cast (show 3 ≤ n by omega)
  have hpos : (0 : ℝ) < ((n : ℝ) + 1) * ((n : ℝ) + 2) := by positivity
  rw [div_mul_eq_mul_div, div_le_iff₀ hpos]
  push_cast
  have hco : 0 ≤ (n : ℝ) * ((n : ℝ) - 1) * ((n : ℝ) + 1) * ((n : ℝ) + 2) / 2 * τ := by
    have : (0 : ℝ) ≤ (n : ℝ) - 1 := by linarith
    have := S.hτ
    positivity
  have k := mul_le_mul_of_nonneg_left hmi hco
  linear_combination k

end Setting

end Szkraw
