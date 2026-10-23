import Szkraw.CubicLeib

/-!
# Theorem 8.17: the setting, the weights, and the detours of `H`, `C'` and `V`

As for Theorem 8.11 (`QuadSetting`), with the cubic ratio. The Newton sequence of `b` splits as
`ψ_n = h_n - v_n - e_n` with `h_n = (1 - ρ(ℓ+n)) f_n`, `v_n = n Γ_n(ℓ) f_{n-1}`,
`Γ_n(ℓ) = t + τ(ℓ+n-1) + σ(C(ℓ,2) + ℓ(n-1))`, and
`e_n = C(n,2)(τ + σℓ) f_{n-2} + σ C(n,3)(3f_{n-1} + 3f_{n-2} + f_{n-3})`.
-/

set_option linter.unusedSectionVars false

namespace Szkraw

open Finset

/-- The setting of Theorem 8.17. -/
structure CubicSetting (N : ℕ) (r t τ σ : ℝ) (ν u : ℕ → ℝ) : Prop where
  hN : 1 ≤ N
  hr : 0 < r
  ht : 0 ≤ t
  hτ : 0 ≤ τ
  hσ : 0 ≤ σ
  hrs : r * σ ≤ t * τ
  hν : LCNZ ν
  hν0 : ν 0 = 0
  hν1 : 0 < ν 1
  hu_nn : ∀ i, 0 ≤ u i
  hφ : ∀ ℓ n, ℓ + n ≤ N → Szkraw.iterShift u ℓ n = PhiC r t τ σ ℓ n (Szkraw.iterShift ν ℓ)
  hb : ∀ m, m < N → dd (quadW ν u) m ≤ dd (quadW ν u) (m + 1)

/-- `Γ_n(ℓ) = t + τ(ℓ+n-1) + σ(C(ℓ,2) + ℓ(n-1))`. -/
noncomputable def GammaC (t τ σ : ℝ) (ℓ n : ℕ) : ℝ :=
  t + τ * ((ℓ : ℝ) + n - 1) + σ * ((ℓ.choose 2 : ℝ) + ℓ * ((n : ℝ) - 1))

/-- `h_n(ℓ) = (1 - ρ(ℓ+n)) f_n(ℓ)`. -/
noncomputable def hC (r t τ σ : ℝ) (ν : ℕ → ℝ) (ℓ n : ℕ) : ℝ :=
  (1 - rhoC r t τ σ (ℓ + n)) * Szkraw.iterShift ν ℓ n

/-- `v_n(ℓ) = n Γ_n(ℓ) f_{n-1}(ℓ)`. -/
noncomputable def vC (t τ σ : ℝ) (ν : ℕ → ℝ) (ℓ n : ℕ) : ℝ :=
  (n : ℝ) * GammaC t τ σ ℓ n * Szkraw.iterShift ν ℓ (n - 1)

/-- `e_n(ℓ) = C(n,2)(τ + σℓ) f_{n-2} + σ C(n,3)(3f_{n-1} + 3f_{n-2} + f_{n-3})`. -/
noncomputable def eC (τ σ : ℝ) (ν : ℕ → ℝ) (ℓ n : ℕ) : ℝ :=
  (n.choose 2 : ℝ) * (τ + σ * ℓ) * Szkraw.iterShift ν ℓ (n - 2) +
    σ * (n.choose 3 : ℝ) * (3 * Szkraw.iterShift ν ℓ (n - 1) + 3 * Szkraw.iterShift ν ℓ (n - 2) +
      Szkraw.iterShift ν ℓ (n - 3))

noncomputable def cubicH (r t τ σ : ℝ) (ν : ℕ → ℝ) (j ℓ a : ℕ) : ℝ := WtF (hC r t τ σ ν) (2 * j + 1) j ℓ a
noncomputable def cubicV (t τ σ : ℝ) (ν : ℕ → ℝ) (j ℓ a : ℕ) : ℝ := WtF (vC t τ σ ν) (2 * j + 1) j ℓ a
noncomputable def cubicE (τ σ : ℝ) (ν : ℕ → ℝ) (j ℓ a : ℕ) : ℝ := WtF (eC τ σ ν) (2 * j + 1) j ℓ a

theorem PhiC_zero (r t τ σ : ℝ) (ℓ : ℕ) (v : ℕ → ℝ) : PhiC r t τ σ ℓ 0 v = rhoC r t τ σ ℓ * v 0 := by
  unfold PhiC; simp

theorem rhoC_mono {r t τ σ : ℝ} (ht : 0 ≤ t) (hτ : 0 ≤ τ) (hσ : 0 ≤ σ) {i j : ℕ} (h : i ≤ j) :
    rhoC r t τ σ i ≤ rhoC r t τ σ j := by
  unfold rhoC
  have h1 : (i : ℝ) ≤ j := by exact_mod_cast h
  have h2 : (i.choose 2 : ℝ) ≤ (j.choose 2 : ℝ) := by exact_mod_cast Nat.choose_le_choose 2 h
  have h3 : (i.choose 3 : ℝ) ≤ (j.choose 3 : ℝ) := by exact_mod_cast Nat.choose_le_choose 3 h
  nlinarith [mul_le_mul_of_nonneg_left h1 ht, mul_le_mul_of_nonneg_left h2 hτ, mul_le_mul_of_nonneg_left h3 hσ]

/-- `(n+1) Γ_n(ℓ+1) - n Γ_{n+2}(ℓ) = t + τℓ + σ(C(ℓ,2) + n² - 1)`. -/
theorem GammaC_step (t τ σ : ℝ) (ℓ n : ℕ) :
    ((n : ℝ) + 1) * GammaC t τ σ (ℓ + 1) n - (n : ℝ) * GammaC t τ σ ℓ (n + 2) =
      t + τ * ℓ + σ * ((ℓ.choose 2 : ℝ) + (n : ℝ) ^ 2 - 1) := by
  unfold GammaC; rw [choose2_real (ℓ + 1), choose2_real ℓ]; push_cast; ring

/-! ### Consequences of the setting -/

section Setting

variable {N : ℕ} {r t τ σ : ℝ} {ν u : ℕ → ℝ} (S : CubicSetting N r t τ σ ν u)
include S

theorem CubicSetting.f_nn (ℓ n : ℕ) : 0 ≤ Szkraw.iterShift ν ℓ n := iterShift_nonneg S.hν ℓ n

theorem CubicSetting.f1_pos (ℓ : ℕ) : 0 < Szkraw.iterShift ν ℓ 1 := iterShift_one_pos S.hν S.hν1 ℓ

theorem CubicSetting.g_nn (ℓ n : ℕ) : 0 ≤ Szkraw.iterShift u ℓ n := iterShift_nonneg_of S.hu_nn ℓ n

theorem CubicSetting.cc_nn (ℓ : ℕ) : 0 ≤ dd u (ℓ + 1) := S.g_nn (ℓ + 1) 0

theorem CubicSetting.rho_pos (i : ℕ) : 0 < rhoC r t τ σ i := by
  unfold rhoC; have := S.hr; have := S.ht; have := S.hτ; have := S.hσ; positivity

theorem CubicSetting.rho_mono {i j : ℕ} (h : i ≤ j) : rhoC r t τ σ i ≤ rhoC r t τ σ j :=
  rhoC_mono S.ht S.hτ S.hσ h

theorem CubicSetting.drho_nn (i : ℕ) : 0 ≤ drhoC t τ σ i := by
  unfold drhoC; have := S.ht; have := S.hτ; have := S.hσ; positivity

theorem CubicSetting.d2rho_nn (i : ℕ) : 0 ≤ d2rhoC τ σ i := by
  unfold d2rhoC; have := S.hτ; have := S.hσ; positivity

theorem CubicSetting.Phi_ge (ℓ n : ℕ) :
    rhoC r t τ σ (ℓ + n) * Szkraw.iterShift ν ℓ n ≤ PhiC r t τ σ ℓ n (Szkraw.iterShift ν ℓ) := by
  unfold PhiC
  have h2 := mul_nonneg (mul_nonneg (Nat.cast_nonneg n) (S.drho_nn (ℓ + (n - 1)))) (S.f_nn ℓ (n - 1))
  have h3 := mul_nonneg (mul_nonneg (Nat.cast_nonneg (n.choose 2)) (S.d2rho_nn (ℓ + (n - 2)))) (S.f_nn ℓ (n - 2))
  have h4 := mul_nonneg (mul_nonneg (Nat.cast_nonneg (n.choose 3)) S.hσ) (S.f_nn ℓ (n - 3))
  linarith

theorem CubicSetting.Phi_nn (ℓ n : ℕ) : 0 ≤ PhiC r t τ σ ℓ n (Szkraw.iterShift ν ℓ) :=
  le_trans (mul_nonneg (S.rho_pos _).le (S.f_nn ℓ n)) (S.Phi_ge ℓ n)

theorem CubicSetting.hu1 : 0 < u 1 := by
  have h := S.hφ 0 1 (by have := S.hN; omega)
  have e : Szkraw.iterShift u 0 1 = u 1 := rfl
  rw [e] at h
  rw [h]
  have := S.Phi_ge 0 1
  have := mul_pos (S.rho_pos (0 + 1)) (S.f1_pos 0)
  linarith

theorem CubicSetting.dd_u {m : ℕ} (hm : m ≤ N) : dd u m = rhoC r t τ σ m * dd ν m := by
  show Szkraw.iterShift u m 0 = rhoC r t τ σ m * Szkraw.iterShift ν m 0
  rw [S.hφ m 0 (by omega), PhiC_zero]

theorem CubicSetting.dd_w {m : ℕ} (hm : m ≤ N) : dd (quadW ν u) m = (1 - rhoC r t τ σ m) * dd ν m := by
  have e : dd (quadW ν u) m = dd ν m - dd u m := by
    unfold dd quadW; rw [iterShift_sub]
  rw [e, S.dd_u hm]; ring

theorem CubicSetting.b_chain {ℓ k : ℕ} (h : ℓ + k ≤ N) : dd (quadW ν u) ℓ ≤ dd (quadW ν u) (ℓ + k) := by
  induction k with
  | zero => simp
  | succ k ih => exact le_trans (ih (by omega)) (S.hb (ℓ + k) (by omega))

theorem CubicSetting.rho_le_one {i : ℕ} (hi : i ≤ N) : rhoC r t τ σ i ≤ 1 := by
  have hc := S.b_chain (ℓ := 0) (k := N) (by omega)
  have h0 : dd (quadW ν u) 0 = 0 := by
    rw [S.dd_w (by omega)]; show _ * ν 0 = 0; rw [S.hν0]; ring
  rw [h0, zero_add, S.dd_w le_rfl] at hc
  have hd : 0 < dd ν N := dd_pos S.hν S.hν1 S.hN
  have h1 : rhoC r t τ σ N ≤ 1 := by
    by_contra hneg; push Not at hneg
    have : (1 - rhoC r t τ σ N) * dd ν N < 0 := mul_neg_of_neg_of_pos (by linarith) hd
    linarith
  exact le_trans (S.rho_mono hi) h1

/-- `ψ_n = h_n - v_n - e_n` on `Ω`. -/
theorem CubicSetting.psi {ℓ n : ℕ} (h : ℓ + n ≤ N) :
    Szkraw.iterShift (quadW ν u) ℓ n = hC r t τ σ ν ℓ n - vC t τ σ ν ℓ n - eC τ σ ν ℓ n := by
  unfold quadW
  rw [iterShift_sub, S.hφ ℓ n h]
  unfold PhiC hC vC eC
  rcases n with _ | _ | k
  · simp; ring
  · have h13 : Nat.choose 1 3 = 0 := by decide
    simp [GammaC, drhoC, h13]; ring
  · rw [show k + 1 + 1 - 1 = k + 1 by omega, show k + 1 + 1 - 2 = k by omega,
      show k + 1 + 1 - 3 = k - 1 by omega]
    unfold drhoC d2rhoC GammaC
    rw [choose2_real (ℓ + (k + 1)), choose2_real (k + 1 + 1), choose2_real ℓ,
      choose3_real (k + 1 + 1)]
    push_cast; ring

theorem CubicSetting.dd_le (ℓ : ℕ) : Szkraw.iterShift ν ℓ 0 ≤ ℓ * Szkraw.iterShift ν ℓ 1 := by
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
theorem CubicSetting.mi {ℓ l : ℕ} (h : ℓ + l + 2 ≤ N) (hl : 1 ≤ l) :
    dd u (ℓ + 1) * Szkraw.iterShift ν ℓ (l + 2) ≤ Szkraw.iterShift u ℓ 2 * Szkraw.iterShift ν (ℓ + 1) l := by
  rw [S.dd_u (by omega), S.hφ ℓ 2 (by omega)]
  have h83 := lemma_8_3 S.hν ℓ (i := 2) (l := l) (by norm_num) hl
  rw [add_comm 2 l] at h83
  have hφ := S.Phi_ge ℓ 2
  have hρ : rhoC r t τ σ (ℓ + 1) ≤ rhoC r t τ σ (ℓ + 2) := S.rho_mono (by omega)
  have hρ0 := S.rho_pos (ℓ + 1)
  have hf2 := S.f_nn ℓ 2
  have hf1 := S.f_nn (ℓ + 1) l
  have hdd : dd ν (ℓ + 1) = Szkraw.iterShift ν (ℓ + 1) 0 := rfl
  rw [hdd]
  calc rhoC r t τ σ (ℓ + 1) * Szkraw.iterShift ν (ℓ + 1) 0 * Szkraw.iterShift ν ℓ (l + 2)
      = rhoC r t τ σ (ℓ + 1) * (Szkraw.iterShift ν (ℓ + 1) 0 * Szkraw.iterShift ν ℓ (l + 2)) := by ring
    _ ≤ rhoC r t τ σ (ℓ + 1) * (Szkraw.iterShift ν ℓ 2 * Szkraw.iterShift ν (ℓ + 1) l) :=
        mul_le_mul_of_nonneg_left h83 hρ0.le
    _ = (rhoC r t τ σ (ℓ + 1) * Szkraw.iterShift ν ℓ 2) * Szkraw.iterShift ν (ℓ + 1) l := by ring
    _ ≤ (rhoC r t τ σ (ℓ + 2) * Szkraw.iterShift ν ℓ 2) * Szkraw.iterShift ν (ℓ + 1) l :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hρ hf2) hf1
    _ ≤ PhiC r t τ σ ℓ 2 (Szkraw.iterShift ν ℓ) * Szkraw.iterShift ν (ℓ + 1) l :=
        mul_le_mul_of_nonneg_right hφ hf1

theorem CubicSetting.B0_ge_phi2 (ℓ a : ℕ) :
    (a.choose 2 : ℝ) * Szkraw.iterShift u ℓ 2 ≤ Wt u 2 0 ℓ a := by
  rcases Nat.lt_or_ge a 2 with ha | ha
  · rw [Nat.choose_eq_zero_of_lt ha, Nat.cast_zero, zero_mul]; exact Wt_nonneg_of S.hu_nn _ _ _ _
  · have := Wt_ge_term_of S.hu_nn 2 0 ℓ a 2 le_rfl ha
    simpa using this

/-- `B₀(ℓ,a) ≥ C(a,2) φ₂ + C(a,3) φ₃`. -/
theorem CubicSetting.B0_ge_phi23 (ℓ a : ℕ) :
    (a.choose 2 : ℝ) * Szkraw.iterShift u ℓ 2 + (a.choose 3 : ℝ) * Szkraw.iterShift u ℓ 3 ≤ Wt u 2 0 ℓ a := by
  rcases Nat.lt_or_ge a 3 with ha | ha
  · rw [Nat.choose_eq_zero_of_lt ha, Nat.cast_zero, zero_mul, add_zero]; exact S.B0_ge_phi2 ℓ a
  unfold Wt
  have hsub : ({2, 3} : Finset ℕ) ⊆ range (a + 1) := by
    intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx; rw [mem_range]; omega
  have hle := sum_le_sum_of_subset_of_nonneg hsub (f := fun n => (if 2 ≤ n then ((n - 2 + 0).choose 0 : ℝ) else 0) *
    (a.choose n : ℝ) * Szkraw.iterShift u ℓ n) (fun n _ _ => by
      split_ifs
      · exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (S.g_nn ℓ n)
      · simp)
  rw [sum_pair (by norm_num)] at hle
  simpa using hle

/-- `B₀(ℓ,a) ≥ ρ(ℓ+1) Y` on `Ω`. -/
theorem CubicSetting.B0_ge {ℓ a : ℕ} (h : ℓ + a ≤ N) :
    rhoC r t τ σ (ℓ + 1) * Wt ν 2 0 ℓ a ≤ Wt u 2 0 ℓ a := by
  unfold Wt
  rw [mul_sum]
  refine sum_le_sum fun n hn => ?_
  rw [mem_range] at hn
  by_cases h2 : 2 ≤ n
  · rw [if_pos h2]
    have hφ := S.Phi_ge ℓ n
    rw [← S.hφ ℓ n (by omega)] at hφ
    have hρ : rhoC r t τ σ (ℓ + 1) ≤ rhoC r t τ σ (ℓ + n) := S.rho_mono (by omega)
    have hc : (0 : ℝ) ≤ ((n - 2 + 0).choose 0 : ℝ) * (a.choose n : ℝ) := by positivity
    have hf := S.f_nn ℓ n
    calc rhoC r t τ σ (ℓ + 1) * (((n - 2 + 0).choose 0 : ℝ) * (a.choose n : ℝ) * Szkraw.iterShift ν ℓ n)
        = (((n - 2 + 0).choose 0 : ℝ) * (a.choose n : ℝ)) * (rhoC r t τ σ (ℓ + 1) * Szkraw.iterShift ν ℓ n) := by
          ring
      _ ≤ (((n - 2 + 0).choose 0 : ℝ) * (a.choose n : ℝ)) * Szkraw.iterShift u ℓ n :=
          mul_le_mul_of_nonneg_left (le_trans (mul_le_mul_of_nonneg_right hρ hf) hφ) hc
      _ = _ := by ring
  · rw [if_neg h2]; simp

/-! ### Nonnegativity of the weights -/

theorem CubicSetting.Gamma_nn (ℓ : ℕ) {n : ℕ} (hn : 1 ≤ n) : 0 ≤ GammaC t τ σ ℓ n := by
  unfold GammaC
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h1 : (0 : ℝ) ≤ (n : ℝ) - 1 := by linarith
  have h2 : (0 : ℝ) ≤ (ℓ : ℝ) + n - 1 := by have := (Nat.cast_nonneg ℓ : (0 : ℝ) ≤ ℓ); linarith
  exact add_nonneg (add_nonneg S.ht (mul_nonneg S.hτ h2))
    (mul_nonneg S.hσ (add_nonneg (Nat.cast_nonneg _) (mul_nonneg (Nat.cast_nonneg _) h1)))

theorem CubicSetting.hC_nn {ℓ n : ℕ} (h : ℓ + n ≤ N) : 0 ≤ hC r t τ σ ν ℓ n :=
  mul_nonneg (by linarith [S.rho_le_one h]) (S.f_nn ℓ n)

theorem CubicSetting.vC_nn (ℓ n : ℕ) : 0 ≤ vC t τ σ ν ℓ n := by
  unfold vC
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp
  · exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (S.Gamma_nn ℓ hn)) (S.f_nn ℓ _)

theorem CubicSetting.eC_nn (ℓ n : ℕ) : 0 ≤ eC τ σ ν ℓ n := by
  unfold eC
  have h1 := S.f_nn ℓ (n - 1); have h2 := S.f_nn ℓ (n - 2); have h3 := S.f_nn ℓ (n - 3)
  have hτσ : 0 ≤ τ + σ * ℓ := add_nonneg S.hτ (mul_nonneg S.hσ (Nat.cast_nonneg ℓ))
  exact add_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hτσ) h2)
    (mul_nonneg (mul_nonneg S.hσ (Nat.cast_nonneg _)) (by linarith))

theorem CubicSetting.H_nn {j ℓ a : ℕ} (h : ℓ + a ≤ N) : 0 ≤ cubicH r t τ σ ν j ℓ a :=
  WtF_nonneg fun n _ hn => S.hC_nn (by omega)

theorem CubicSetting.V_nn (j ℓ a : ℕ) : 0 ≤ cubicV t τ σ ν j ℓ a := WtF_nonneg fun n _ _ => S.vC_nn ℓ n

theorem CubicSetting.E_nn (j ℓ a : ℕ) : 0 ≤ cubicE τ σ ν j ℓ a := WtF_nonneg fun n _ _ => S.eC_nn ℓ n

/-- The split `A_j = H_j - V_j - E_j` on `Ω`. -/
theorem CubicSetting.A_split {j ℓ a : ℕ} (h : ℓ + a ≤ N) :
    Wt (quadW ν u) (2 * j + 1) j ℓ a = cubicH r t τ σ ν j ℓ a - cubicV t τ σ ν j ℓ a - cubicE τ σ ν j ℓ a := by
  rw [Wt_eq_WtF, cubicH, cubicV, cubicE, ← WtF_sub, ← WtF_sub]
  exact WtF_congr fun n hn => S.psi (by omega)

theorem CubicSetting.wC_eq (j ℓ a : ℕ) : wC u (quadW ν u) j ℓ a = Wt ν (2 * j + 2) (j + 1) ℓ a := by
  unfold wC
  rw [Wt_add]
  congr 1
  funext i; unfold quadW; ring

theorem CubicSetting.A0_nn {ℓ a : ℕ} (h : ℓ + a ≤ N) : 0 ≤ Wt (quadW ν u) 1 0 ℓ a := by
  rw [Wt_one_zero]
  linarith [S.b_chain h]

/-! ### The detours of `C'`, `H` and `V` -/

/-- The `C'` detour. -/
theorem CubicSetting.domC {j ℓ a : ℕ} (hj : 1 ≤ j) (h : ℓ + a ≤ N) :
    4 * dd u (ℓ + 1) * Wt ν (2 * j + 2) (j + 1) ℓ a ≤ Wt u 2 0 ℓ a * Wt ν (2 * j) j (ℓ + 1) (a - 2) := by
  rw [Wt_eq_WtF, Wt_eq_WtF ν (2 * j)]
  refine detour_Cf j hj (S.cc_nn ℓ) (Wt_nonneg_of S.hu_nn _ _ _ _) (S.B0_ge_phi2 ℓ a) (fun m _ => S.f_nn ℓ m)
    (fun n _ => S.f_nn (ℓ + 1) n) (fun n hn hna => ?_)
  rw [one_mul]; exact S.mi (by omega) (by omega)

/-- The `H` detour. -/
theorem CubicSetting.domH {j ℓ a : ℕ} (hj : 2 ≤ j) (h : ℓ + a ≤ N) :
    4 * dd u (ℓ + 1) * cubicH r t τ σ ν j ℓ a ≤ Wt u 2 0 ℓ a * cubicH r t τ σ ν (j - 1) (ℓ + 1) (a - 2) := by
  unfold cubicH
  rw [show 2 * (j - 1) + 1 = 2 * j - 1 by omega]
  refine detour_HV j hj (S.cc_nn ℓ) (Wt_nonneg_of S.hu_nn _ _ _ _) (S.B0_ge_phi2 ℓ a)
    (fun m hm => S.hC_nn (by omega)) (fun n hn => S.hC_nn (by omega)) (fun n hn hna => ?_)
  have hmi := S.mi (ℓ := ℓ) (l := n) (by omega) (by omega)
  unfold hC
  have hρa := S.rho_le_one (i := ℓ + (n + 2)) (by omega)
  have hρb : rhoC r t τ σ (ℓ + 1 + n) ≤ rhoC r t τ σ (ℓ + (n + 2)) := S.rho_mono (by omega)
  have hφ2 := S.g_nn ℓ 2
  have hf1 := S.f_nn (ℓ + 1) n
  have hpf : 0 ≤ Szkraw.iterShift u ℓ 2 * Szkraw.iterShift ν (ℓ + 1) n := mul_nonneg hφ2 hf1
  calc dd u (ℓ + 1) * ((1 - rhoC r t τ σ (ℓ + (n + 2))) * Szkraw.iterShift ν ℓ (n + 2))
      = (1 - rhoC r t τ σ (ℓ + (n + 2))) * (dd u (ℓ + 1) * Szkraw.iterShift ν ℓ (n + 2)) := by ring
    _ ≤ (1 - rhoC r t τ σ (ℓ + (n + 2))) * (Szkraw.iterShift u ℓ 2 * Szkraw.iterShift ν (ℓ + 1) n) :=
        mul_le_mul_of_nonneg_left hmi (by linarith)
    _ ≤ (1 - rhoC r t τ σ (ℓ + 1 + n)) * (Szkraw.iterShift u ℓ 2 * Szkraw.iterShift ν (ℓ + 1) n) :=
        mul_le_mul_of_nonneg_right (by linarith) hpf
    _ ≤ 2 * (Szkraw.iterShift u ℓ 2 * ((1 - rhoC r t τ σ (ℓ + 1 + n)) * Szkraw.iterShift ν (ℓ + 1) n)) := by
        have : 0 ≤ (1 - rhoC r t τ σ (ℓ + 1 + n)) * (Szkraw.iterShift u ℓ 2 * Szkraw.iterShift ν (ℓ + 1) n) :=
          mul_nonneg (by linarith) hpf
        nlinarith

/-- The `V` detour. -/
theorem CubicSetting.domV {j ℓ a : ℕ} (hj : 2 ≤ j) (h : ℓ + a ≤ N) :
    4 * dd u (ℓ + 1) * cubicV t τ σ ν j ℓ a ≤ Wt u 2 0 ℓ a * cubicV t τ σ ν (j - 1) (ℓ + 1) (a - 2) := by
  unfold cubicV
  rw [show 2 * (j - 1) + 1 = 2 * j - 1 by omega, show 2 * j + 1 = 2 * j - 1 + 2 by omega]
  refine detour_gen (κ := kapV) (S.cc_nn ℓ) (Wt_nonneg_of S.hu_nn _ _ _ _) (S.B0_ge_phi2 ℓ a)
    (fun m _ => S.vC_nn ℓ m) (fun n => S.vC_nn (ℓ + 1) n) (fun n hn hna => ?_)
    (fun m hm hma => coefV hj (by omega))
  have hmi := S.mi (ℓ := ℓ) (l := n - 1) (by omega) (by omega)
  rw [show n - 1 + 2 = n + 1 by omega] at hmi
  unfold vC kapV
  rw [show n + 2 - 1 = n + 1 by omega]
  have hn3 : (3 : ℝ) ≤ n := by exact_mod_cast (show 3 ≤ n by omega)
  have hstep := GammaC_step t τ σ ℓ n
  have hG2 : 0 ≤ GammaC t τ σ (ℓ + 1) n := S.Gamma_nn (ℓ + 1) (by omega)
  have hdd : (n : ℝ) * GammaC t τ σ ℓ (n + 2) ≤ ((n : ℝ) + 1) * GammaC t τ σ (ℓ + 1) n := by
    have : 0 ≤ t + τ * ℓ + σ * ((ℓ.choose 2 : ℝ) + (n : ℝ) ^ 2 - 1) := by
      have := S.ht; have := S.hτ; have := S.hσ
      have : (0 : ℝ) ≤ (ℓ.choose 2 : ℝ) + (n : ℝ) ^ 2 - 1 := by
        have := (Nat.cast_nonneg (ℓ.choose 2) : (0 : ℝ) ≤ _); nlinarith
      positivity
    linarith
  have hX : 0 ≤ dd u (ℓ + 1) * Szkraw.iterShift ν ℓ (n + 1) := mul_nonneg (S.cc_nn ℓ) (S.f_nn ℓ _)
  have hpos : (0 : ℝ) < ((n : ℝ) + 1) * ((n : ℝ) + 2) := by positivity
  rw [div_mul_eq_mul_div, div_le_iff₀ hpos]
  push_cast
  have k1 : (n : ℝ) * ((n : ℝ) + 2) * ((n : ℝ) * GammaC t τ σ ℓ (n + 2)) *
      (dd u (ℓ + 1) * Szkraw.iterShift ν ℓ (n + 1)) ≤
      (n : ℝ) * ((n : ℝ) + 2) * (((n : ℝ) + 1) * GammaC t τ σ (ℓ + 1) n) *
      (dd u (ℓ + 1) * Szkraw.iterShift ν ℓ (n + 1)) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hdd (by positivity)) hX
  have k2 : (n : ℝ) * ((n : ℝ) + 2) * (((n : ℝ) + 1) * GammaC t τ σ (ℓ + 1) n) *
      (dd u (ℓ + 1) * Szkraw.iterShift ν ℓ (n + 1)) ≤
      (n : ℝ) * ((n : ℝ) + 2) * (((n : ℝ) + 1) * GammaC t τ σ (ℓ + 1) n) *
      (Szkraw.iterShift u ℓ 2 * Szkraw.iterShift ν (ℓ + 1) (n - 1)) :=
    mul_le_mul_of_nonneg_left hmi (by positivity)
  linear_combination k1 + k2

end Setting

end Szkraw
