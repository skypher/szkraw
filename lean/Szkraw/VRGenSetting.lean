import Szkraw.VRQuadDetours
import Szkraw.VRMoves3
import Szkraw.LCRatioFacts

/-!
# Theorem 8.16: the setting, the weights and the detours `B`, `C'`, `H`, `V`

The ratio has Newton coefficients `ρc` (log-concave without internal zeros, `ρc 0 > 0`), so
`ρ(n) = dd ρc n` and `Δ^j ρ(x) = P_j(x) = iterShift ρc x j`. On `Ω` the Leibniz rule gives
`φ_n(ℓ) = Σ_j C(n,j) P_j(ℓ+n-j) f_{n-j}(ℓ)`, and `ψ_n = h_n - v_n - ŵ_n`.
-/

set_option linter.unusedSectionVars false

namespace Szkraw

open Finset

/-- `φ_n(ℓ) = Σ_j C(n,j) P_j(ℓ+n-j) f_{n-j}`. -/
noncomputable def PhiG (ρc : ℕ → ℝ) (ℓ n : ℕ) (f : ℕ → ℝ) : ℝ :=
  ∑ j ∈ range (n + 1), (n.choose j : ℝ) * Szkraw.iterShift ρc (ℓ + (n - j)) j * f (n - j)

/-- `h_n(ℓ) = (1 - ρ(ℓ+n)) f_n(ℓ)`. -/
noncomputable def hG (ρc ν : ℕ → ℝ) (ℓ n : ℕ) : ℝ := (1 - dd ρc (ℓ + n)) * Szkraw.iterShift ν ℓ n

/-- `v_n(ℓ) = n P_1(ℓ+n-1) f_{n-1}(ℓ)`. -/
noncomputable def vG (ρc ν : ℕ → ℝ) (ℓ n : ℕ) : ℝ :=
  (n : ℝ) * Szkraw.iterShift ρc (ℓ + (n - 1)) 1 * Szkraw.iterShift ν ℓ (n - 1)

/-- The components `w^{(i)}_n(ℓ) = C(n,i) P_i(ℓ+n-i) f_{n-i}(ℓ)`, `2 ≤ i ≤ n`. -/
noncomputable def wcG (ρc ν : ℕ → ℝ) (i ℓ n : ℕ) : ℝ :=
  if 2 ≤ i ∧ i ≤ n then (n.choose i : ℝ) * Szkraw.iterShift ρc (ℓ + (n - i)) i * Szkraw.iterShift ν ℓ (n - i) else 0

/-- `ŵ_n(ℓ) = Σ_{2 ≤ i ≤ n} w^{(i)}_n(ℓ)`. -/
noncomputable def wG (ρc ν : ℕ → ℝ) (ℓ n : ℕ) : ℝ := ∑ i ∈ range (n + 1), wcG ρc ν i ℓ n

noncomputable def genH (ρc ν : ℕ → ℝ) (j ℓ a : ℕ) : ℝ := WtF (hG ρc ν) (2 * j + 1) j ℓ a
noncomputable def genV (ρc ν : ℕ → ℝ) (j ℓ a : ℕ) : ℝ := WtF (vG ρc ν) (2 * j + 1) j ℓ a
noncomputable def genW (ρc ν : ℕ → ℝ) (j ℓ a : ℕ) : ℝ := WtF (wG ρc ν) (2 * j + 1) j ℓ a

/-- The split of `φ_n` into its first two Leibniz terms and the rest. -/
theorem PhiG_split (ρc : ℕ → ℝ) (ℓ n : ℕ) (f : ℕ → ℝ) :
    PhiG ρc ℓ n f = dd ρc (ℓ + n) * f n + (n : ℝ) * Szkraw.iterShift ρc (ℓ + (n - 1)) 1 * f (n - 1) +
      ∑ i ∈ range (n + 1), (if 2 ≤ i ∧ i ≤ n then (n.choose i : ℝ) * Szkraw.iterShift ρc (ℓ + (n - i)) i * f (n - i)
        else 0) := by
  unfold PhiG
  rcases n with _ | k
  · simp; left; rfl
  · rw [sum_range_succ', sum_range_succ', sum_range_succ' (fun i => if 2 ≤ i ∧ i ≤ k + 1 then _ else _),
      sum_range_succ' (fun i => if 2 ≤ i + 1 ∧ i + 1 ≤ k + 1 then _ else _)]
    simp only [show ¬ (2 ≤ 0 + 1 ∧ 0 + 1 ≤ k + 1) by omega, show ¬ (2 ≤ 0 ∧ 0 ≤ k + 1) by omega, if_false,
      add_zero, Nat.choose_zero_right, Nat.cast_one, one_mul, Nat.sub_zero]
    have e : ∀ j ∈ range k, (if 2 ≤ j + 1 + 1 ∧ j + 1 + 1 ≤ k + 1 then ((k + 1).choose (j + 1 + 1) : ℝ) *
        Szkraw.iterShift ρc (ℓ + (k + 1 - (j + 1 + 1))) (j + 1 + 1) * f (k + 1 - (j + 1 + 1)) else 0) =
        ((k + 1).choose (j + 1 + 1) : ℝ) * Szkraw.iterShift ρc (ℓ + (k + 1 - (j + 1 + 1))) (j + 1 + 1) *
          f (k + 1 - (j + 1 + 1)) := by
      intro j hj; simp only [mem_range] at hj; rw [if_pos (by omega)]
    rw [sum_congr rfl e, show k + 1 - 1 = k by omega, show ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 by push_cast; ring]
    have e2 : dd ρc (ℓ + (k + 1)) = Szkraw.iterShift ρc (ℓ + (k + 1)) 0 := rfl
    rw [e2]
    simp only [zero_add, Nat.choose_one_right]
    push_cast
    ring

/-- The setting of Theorem 8.16. -/
structure GenSetting (N : ℕ) (ρc ν u : ℕ → ℝ) : Prop where
  hN : 1 ≤ N
  hρc : LCNZ ρc
  hρ0 : 0 < ρc 0
  hν : LCNZ ν
  hν0 : ν 0 = 0
  hν1 : 0 < ν 1
  hu : LCNZ u
  hφ : ∀ ℓ n, ℓ + n ≤ N → Szkraw.iterShift u ℓ n = PhiG ρc ℓ n (Szkraw.iterShift ν ℓ)
  hb : ∀ m, m < N → dd (quadW ν u) m ≤ dd (quadW ν u) (m + 1)

section Setting

variable {N : ℕ} {ρc ν u : ℕ → ℝ} (S : GenSetting N ρc ν u)
include S

theorem GenSetting.f_nn (ℓ n : ℕ) : 0 ≤ Szkraw.iterShift ν ℓ n := iterShift_nonneg S.hν ℓ n
theorem GenSetting.f1_pos (ℓ : ℕ) : 0 < Szkraw.iterShift ν ℓ 1 := iterShift_one_pos S.hν S.hν1 ℓ
theorem GenSetting.g_nn (ℓ n : ℕ) : 0 ≤ Szkraw.iterShift u ℓ n := iterShift_nonneg S.hu ℓ n
theorem GenSetting.hu_nn (i : ℕ) : 0 ≤ u i := S.hu.1 i
theorem GenSetting.cc_nn (ℓ : ℕ) : 0 ≤ dd u (ℓ + 1) := S.g_nn (ℓ + 1) 0
theorem GenSetting.P_nn (x j : ℕ) : 0 ≤ Szkraw.iterShift ρc x j := iterShift_nonneg S.hρc x j

theorem GenSetting.rho_pos (i : ℕ) : 0 < dd ρc i := by
  show 0 < Szkraw.iterShift ρc i 0
  rw [iterShift_eq]
  have h0 : (i.choose 0 : ℝ) * ρc (0 + 0) ≤ ∑ h ∈ range (i + 1), (i.choose h : ℝ) * ρc (0 + h) :=
    single_le_sum (f := fun h => (i.choose h : ℝ) * ρc (0 + h))
      (fun h _ => mul_nonneg (Nat.cast_nonneg _) (S.hρc.1 _)) (by simp)
  simp only [Nat.choose_zero_right, Nat.cast_one, one_mul, add_zero] at h0
  linarith [S.hρ0]

theorem GenSetting.rho_succ (x : ℕ) : dd ρc (x + 1) = dd ρc x + Szkraw.iterShift ρc x 1 := rfl

theorem GenSetting.rho_mono {i j : ℕ} (h : i ≤ j) : dd ρc i ≤ dd ρc j := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show i + (k + 1) = i + k + 1 by omega, S.rho_succ]
    linarith [ih (by omega), S.P_nn (i + k) 1]

/-- `φ_n ≥ ρ(ℓ+n) f_n`. -/
theorem GenSetting.Phi_ge (ℓ n : ℕ) :
    dd ρc (ℓ + n) * Szkraw.iterShift ν ℓ n ≤ PhiG ρc ℓ n (Szkraw.iterShift ν ℓ) := by
  unfold PhiG
  rw [sum_range_succ']
  simp only [Nat.choose_zero_right, Nat.cast_one, one_mul, Nat.sub_zero]
  have : 0 ≤ ∑ j ∈ range n, ((n.choose (j + 1) : ℝ) * Szkraw.iterShift ρc (ℓ + (n - (j + 1))) (j + 1) *
      Szkraw.iterShift ν ℓ (n - (j + 1))) :=
    sum_nonneg fun j _ => mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (S.P_nn _ _)) (S.f_nn _ _)
  show dd ρc (ℓ + n) * Szkraw.iterShift ν ℓ n ≤ _ + Szkraw.iterShift ρc (ℓ + n) 0 * Szkraw.iterShift ν ℓ n
  have e : dd ρc (ℓ + n) = Szkraw.iterShift ρc (ℓ + n) 0 := rfl
  rw [e]; linarith

theorem GenSetting.hu1 : 0 < u 1 := by
  have h := S.hφ 0 1 (by have := S.hN; omega)
  have e : Szkraw.iterShift u 0 1 = u 1 := rfl
  rw [e] at h
  rw [h]
  have := S.Phi_ge 0 1
  have := mul_pos (S.rho_pos (0 + 1)) (S.f1_pos 0)
  linarith

theorem GenSetting.dd_u {m : ℕ} (hm : m ≤ N) : dd u m = dd ρc m * dd ν m := by
  show Szkraw.iterShift u m 0 = dd ρc m * Szkraw.iterShift ν m 0
  rw [S.hφ m 0 (by omega)]
  unfold PhiG; simp; left; rfl

theorem GenSetting.dd_w {m : ℕ} (hm : m ≤ N) : dd (quadW ν u) m = (1 - dd ρc m) * dd ν m := by
  have e : dd (quadW ν u) m = dd ν m - dd u m := by
    unfold dd quadW; rw [iterShift_sub]
  rw [e, S.dd_u hm]; ring

theorem GenSetting.b_chain {ℓ k : ℕ} (h : ℓ + k ≤ N) : dd (quadW ν u) ℓ ≤ dd (quadW ν u) (ℓ + k) := by
  induction k with
  | zero => simp
  | succ k ih => exact le_trans (ih (by omega)) (S.hb (ℓ + k) (by omega))

theorem GenSetting.rho_le_one {i : ℕ} (hi : i ≤ N) : dd ρc i ≤ 1 := by
  have hc := S.b_chain (ℓ := 0) (k := N) (by omega)
  have h0 : dd (quadW ν u) 0 = 0 := by
    rw [S.dd_w (by omega)]; show _ * ν 0 = 0; rw [S.hν0]; ring
  rw [h0, zero_add, S.dd_w le_rfl] at hc
  have hd : 0 < dd ν N := dd_pos S.hν S.hν1 S.hN
  have h1 : dd ρc N ≤ 1 := by
    by_contra hneg; push Not at hneg
    have : (1 - dd ρc N) * dd ν N < 0 := mul_neg_of_neg_of_pos (by linarith) hd
    linarith
  exact le_trans (S.rho_mono hi) h1

/-- `ψ_n = h_n - v_n - ŵ_n` on `Ω`. -/
theorem GenSetting.psi {ℓ n : ℕ} (h : ℓ + n ≤ N) :
    Szkraw.iterShift (quadW ν u) ℓ n = hG ρc ν ℓ n - vG ρc ν ℓ n - wG ρc ν ℓ n := by
  unfold quadW
  rw [iterShift_sub, S.hφ ℓ n h, PhiG_split]
  unfold hG vG wG wcG
  ring

/-- The mixed inequality `c_{ℓ+1} f_{l+2}(ℓ) ≤ φ₂(ℓ) f_l(ℓ+1)` for `ℓ + l + 2 ≤ N`, `l ≥ 1`. -/
theorem GenSetting.mi {ℓ l : ℕ} (h : ℓ + l + 2 ≤ N) (hl : 1 ≤ l) :
    dd u (ℓ + 1) * Szkraw.iterShift ν ℓ (l + 2) ≤ Szkraw.iterShift u ℓ 2 * Szkraw.iterShift ν (ℓ + 1) l := by
  rw [S.dd_u (by omega), S.hφ ℓ 2 (by omega)]
  have h83 := lemma_8_3 S.hν ℓ (i := 2) (l := l) (by norm_num) hl
  rw [add_comm 2 l] at h83
  have hφ := S.Phi_ge ℓ 2
  have hρ : dd ρc (ℓ + 1) ≤ dd ρc (ℓ + 2) := S.rho_mono (by omega)
  have hρ0 := S.rho_pos (ℓ + 1)
  have hf2 := S.f_nn ℓ 2
  have hf1 := S.f_nn (ℓ + 1) l
  have hdd : dd ν (ℓ + 1) = Szkraw.iterShift ν (ℓ + 1) 0 := rfl
  rw [hdd]
  calc dd ρc (ℓ + 1) * Szkraw.iterShift ν (ℓ + 1) 0 * Szkraw.iterShift ν ℓ (l + 2)
      = dd ρc (ℓ + 1) * (Szkraw.iterShift ν (ℓ + 1) 0 * Szkraw.iterShift ν ℓ (l + 2)) := by ring
    _ ≤ dd ρc (ℓ + 1) * (Szkraw.iterShift ν ℓ 2 * Szkraw.iterShift ν (ℓ + 1) l) :=
        mul_le_mul_of_nonneg_left h83 hρ0.le
    _ = (dd ρc (ℓ + 1) * Szkraw.iterShift ν ℓ 2) * Szkraw.iterShift ν (ℓ + 1) l := by ring
    _ ≤ (dd ρc (ℓ + 2) * Szkraw.iterShift ν ℓ 2) * Szkraw.iterShift ν (ℓ + 1) l :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hρ hf2) hf1
    _ ≤ PhiG ρc ℓ 2 (Szkraw.iterShift ν ℓ) * Szkraw.iterShift ν (ℓ + 1) l :=
        mul_le_mul_of_nonneg_right hφ hf1

theorem GenSetting.B0_ge_phi2 (ℓ a : ℕ) :
    (a.choose 2 : ℝ) * Szkraw.iterShift u ℓ 2 ≤ Wt u 2 0 ℓ a := by
  rcases Nat.lt_or_ge a 2 with ha | ha
  · rw [Nat.choose_eq_zero_of_lt ha, Nat.cast_zero, zero_mul]; exact Wt_nonneg_of S.hu_nn _ _ _ _
  · have := Wt_ge_term_of S.hu_nn 2 0 ℓ a 2 le_rfl ha
    simpa using this

/-! ### Nonnegativity and the split of the weights -/

theorem GenSetting.hG_nn {ℓ n : ℕ} (h : ℓ + n ≤ N) : 0 ≤ hG ρc ν ℓ n :=
  mul_nonneg (by linarith [S.rho_le_one h]) (S.f_nn ℓ n)

theorem GenSetting.vG_nn (ℓ n : ℕ) : 0 ≤ vG ρc ν ℓ n :=
  mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (S.P_nn _ _)) (S.f_nn ℓ _)

theorem GenSetting.wcG_nn (i ℓ n : ℕ) : 0 ≤ wcG ρc ν i ℓ n := by
  unfold wcG; split_ifs
  · exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (S.P_nn _ _)) (S.f_nn ℓ _)
  · exact le_refl 0

theorem GenSetting.wG_nn (ℓ n : ℕ) : 0 ≤ wG ρc ν ℓ n := sum_nonneg fun i _ => S.wcG_nn i ℓ n

theorem GenSetting.H_nn {j ℓ a : ℕ} (h : ℓ + a ≤ N) : 0 ≤ genH ρc ν j ℓ a :=
  WtF_nonneg fun n _ hn => S.hG_nn (by omega)

theorem GenSetting.V_nn (j ℓ a : ℕ) : 0 ≤ genV ρc ν j ℓ a := WtF_nonneg fun n _ _ => S.vG_nn ℓ n

theorem GenSetting.W_nn (j ℓ a : ℕ) : 0 ≤ genW ρc ν j ℓ a := WtF_nonneg fun n _ _ => S.wG_nn ℓ n

theorem GenSetting.A_split {j ℓ a : ℕ} (h : ℓ + a ≤ N) :
    Wt (quadW ν u) (2 * j + 1) j ℓ a = genH ρc ν j ℓ a - genV ρc ν j ℓ a - genW ρc ν j ℓ a := by
  rw [Wt_eq_WtF, genH, genV, genW, ← WtF_sub, ← WtF_sub]
  exact WtF_congr fun n hn => S.psi (by omega)

theorem GenSetting.wC_eq (j ℓ a : ℕ) : wC u (quadW ν u) j ℓ a = Wt ν (2 * j + 2) (j + 1) ℓ a := by
  unfold wC
  rw [Wt_add]
  congr 1
  funext i; unfold quadW; ring

theorem GenSetting.A0_nn {ℓ a : ℕ} (h : ℓ + a ≤ N) : 0 ≤ Wt (quadW ν u) 1 0 ℓ a := by
  rw [Wt_one_zero]
  linarith [S.b_chain h]

/-! ### The detours `B`, `C'`, `H`, `V` -/

theorem GenSetting.domB {j ℓ a : ℕ} (hj : 1 ≤ j) :
    4 * dd u (ℓ + 1) * Wt u (2 * j + 2) j ℓ a ≤ Wt u 2 0 ℓ a * Wt u (2 * j) (j - 1) (ℓ + 1) (a - 2) :=
  lemma_8_4_B S.hu j ℓ a hj

theorem GenSetting.domC {j ℓ a : ℕ} (hj : 1 ≤ j) (h : ℓ + a ≤ N) :
    4 * dd u (ℓ + 1) * Wt ν (2 * j + 2) (j + 1) ℓ a ≤ Wt u 2 0 ℓ a * Wt ν (2 * j) j (ℓ + 1) (a - 2) := by
  rw [Wt_eq_WtF, Wt_eq_WtF ν (2 * j)]
  refine detour_Cf j hj (S.cc_nn ℓ) (Wt_nonneg_of S.hu_nn _ _ _ _) (S.B0_ge_phi2 ℓ a) (fun m _ => S.f_nn ℓ m)
    (fun n _ => S.f_nn (ℓ + 1) n) (fun n hn hna => ?_)
  rw [one_mul]; exact S.mi (by omega) (by omega)

theorem GenSetting.domH {j ℓ a : ℕ} (hj : 2 ≤ j) (h : ℓ + a ≤ N) :
    4 * dd u (ℓ + 1) * genH ρc ν j ℓ a ≤ Wt u 2 0 ℓ a * genH ρc ν (j - 1) (ℓ + 1) (a - 2) := by
  unfold genH
  rw [show 2 * (j - 1) + 1 = 2 * j - 1 by omega]
  refine detour_HV j hj (S.cc_nn ℓ) (Wt_nonneg_of S.hu_nn _ _ _ _) (S.B0_ge_phi2 ℓ a)
    (fun m hm => S.hG_nn (by omega)) (fun n hn => S.hG_nn (by omega)) (fun n hn hna => ?_)
  have hmi := S.mi (ℓ := ℓ) (l := n) (by omega) (by omega)
  unfold hG
  have hρa := S.rho_le_one (i := ℓ + (n + 2)) (by omega)
  have hρb : dd ρc (ℓ + 1 + n) ≤ dd ρc (ℓ + (n + 2)) := S.rho_mono (by omega)
  have hφ2 := S.g_nn ℓ 2
  have hf1 := S.f_nn (ℓ + 1) n
  have hpf : 0 ≤ Szkraw.iterShift u ℓ 2 * Szkraw.iterShift ν (ℓ + 1) n := mul_nonneg hφ2 hf1
  calc dd u (ℓ + 1) * ((1 - dd ρc (ℓ + (n + 2))) * Szkraw.iterShift ν ℓ (n + 2))
      = (1 - dd ρc (ℓ + (n + 2))) * (dd u (ℓ + 1) * Szkraw.iterShift ν ℓ (n + 2)) := by ring
    _ ≤ (1 - dd ρc (ℓ + (n + 2))) * (Szkraw.iterShift u ℓ 2 * Szkraw.iterShift ν (ℓ + 1) n) :=
        mul_le_mul_of_nonneg_left hmi (by linarith)
    _ ≤ (1 - dd ρc (ℓ + 1 + n)) * (Szkraw.iterShift u ℓ 2 * Szkraw.iterShift ν (ℓ + 1) n) :=
        mul_le_mul_of_nonneg_right (by linarith) hpf
    _ ≤ 2 * (Szkraw.iterShift u ℓ 2 * ((1 - dd ρc (ℓ + 1 + n)) * Szkraw.iterShift ν (ℓ + 1) n)) := by
        have : 0 ≤ (1 - dd ρc (ℓ + 1 + n)) * (Szkraw.iterShift u ℓ 2 * Szkraw.iterShift ν (ℓ + 1) n) :=
          mul_nonneg (by linarith) hpf
        nlinarith

/-- The pointwise `V` bound: `φ₂(ℓ) v_n(ℓ+1) ≥ n/(n+2) c_{ℓ+1} v_{n+2}(ℓ)`, in the form with `kapV`. -/
theorem GenSetting.V_loc {ℓ n : ℕ} (hn : 2 ≤ n) (h : ℓ + n + 2 ≤ N) :
    kapV n * (dd u (ℓ + 1) * vG ρc ν ℓ (n + 2)) ≤ Szkraw.iterShift u ℓ 2 * vG ρc ν (ℓ + 1) n := by
  unfold vG
  rw [show n + 2 - 1 = n + 1 by omega, S.dd_u (by omega), S.hφ ℓ 2 (by omega)]
  have hφ := S.Phi_ge ℓ 2
  have h83 := lemma_8_3 S.hν ℓ (i := 2) (l := n - 1) (by norm_num) (by omega)
  rw [show 2 + (n - 1) = n + 1 by omega] at h83
  have hr := ratio_ineq1 S.hρc (fun k => S.rho_pos k) (x := ℓ + 1) (y := ℓ + 1 + (n - 1)) (by omega) 1
  simp only [Pk] at hr
  rw [show ℓ + 1 + (n - 1) + 1 = ℓ + (n + 1) by omega, show ℓ + 1 + 1 = ℓ + 2 by omega] at hr
  have hdd : dd ν (ℓ + 1) = Szkraw.iterShift ν (ℓ + 1) 0 := rfl
  -- shorthand
  set R1 := dd ρc (ℓ + 1); set R2 := dd ρc (ℓ + 2)
  set Pa := Szkraw.iterShift ρc (ℓ + (n + 1)) 1; set Pb := Szkraw.iterShift ρc (ℓ + 1 + (n - 1)) 1
  set D1 := dd ν (ℓ + 1); set Fn1 := Szkraw.iterShift ν ℓ (n + 1)
  set F2 := Szkraw.iterShift ν ℓ 2; set Gm := Szkraw.iterShift ν (ℓ + 1) (n - 1)
  have hR1 : R1 = Szkraw.iterShift ρc (ℓ + 1) 0 := rfl
  have hR2 : R2 = Szkraw.iterShift ρc (ℓ + 2) 0 := rfl
  rw [← hR1, ← hR2] at hr
  rw [← hdd] at h83
  have nR1 : 0 ≤ R1 := (S.rho_pos _).le
  have nPa : 0 ≤ Pa := S.P_nn _ _
  have nPb : 0 ≤ Pb := S.P_nn _ _
  have nD1Fn1 : 0 ≤ D1 * Fn1 := mul_nonneg (dd_pos S.hν S.hν1 (by omega)).le (S.f_nn _ _)
  have nF2Gm : 0 ≤ F2 * Gm := mul_nonneg (S.f_nn _ _) (S.f_nn _ _)
  have nR2F2 : 0 ≤ R2 * F2 := mul_nonneg (S.rho_pos _).le (S.f_nn _ _)
  -- R1 Pa (D1 Fn1) ≤ R2 Pb (F2 Gm) ≤ φ₂ Pb Gm
  have k1 : R1 * Pa * (D1 * Fn1) ≤ R2 * Pb * (F2 * Gm) :=
    mul_le_mul hr h83 nD1Fn1 (mul_nonneg (S.rho_pos _).le nPb)
  have k2 : R2 * F2 * (Pb * Gm) ≤ PhiG ρc ℓ 2 (Szkraw.iterShift ν ℓ) * (Pb * Gm) :=
    mul_le_mul_of_nonneg_right hφ (mul_nonneg nPb (S.f_nn _ _))
  have hk : kapV n * ((n : ℝ) + 2) ≤ (n : ℝ) := by
    unfold kapV
    have hpos : (0 : ℝ) < ((n : ℝ) + 1) * ((n : ℝ) + 2) := by positivity
    rw [div_mul_eq_mul_div, div_le_iff₀ hpos]; nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hk0 : 0 ≤ kapV n := by unfold kapV; positivity
  have nX : 0 ≤ R1 * D1 * (Pa * Fn1) := by nlinarith [mul_nonneg nR1 (mul_nonneg nPa nD1Fn1)]
  push_cast
  calc kapV n * (R1 * D1 * (((n : ℝ) + 2) * Pa * Fn1))
      = (kapV n * ((n : ℝ) + 2)) * (R1 * D1 * (Pa * Fn1)) := by ring
    _ ≤ (n : ℝ) * (R1 * D1 * (Pa * Fn1)) := mul_le_mul_of_nonneg_right hk nX
    _ = (n : ℝ) * (R1 * Pa * (D1 * Fn1)) := by ring
    _ ≤ (n : ℝ) * (R2 * Pb * (F2 * Gm)) := mul_le_mul_of_nonneg_left k1 (Nat.cast_nonneg n)
    _ = (n : ℝ) * (R2 * F2 * (Pb * Gm)) := by ring
    _ ≤ (n : ℝ) * (PhiG ρc ℓ 2 (Szkraw.iterShift ν ℓ) * (Pb * Gm)) :=
        mul_le_mul_of_nonneg_left k2 (Nat.cast_nonneg n)
    _ = _ := by ring

theorem GenSetting.domV {j ℓ a : ℕ} (hj : 2 ≤ j) (h : ℓ + a ≤ N) :
    4 * dd u (ℓ + 1) * genV ρc ν j ℓ a ≤ Wt u 2 0 ℓ a * genV ρc ν (j - 1) (ℓ + 1) (a - 2) := by
  unfold genV
  rw [show 2 * (j - 1) + 1 = 2 * j - 1 by omega, show 2 * j + 1 = 2 * j - 1 + 2 by omega]
  refine detour_gen (κ := kapV) (S.cc_nn ℓ) (Wt_nonneg_of S.hu_nn _ _ _ _) (S.B0_ge_phi2 ℓ a)
    (fun m _ => S.vG_nn ℓ m) (fun n => S.vG_nn (ℓ + 1) n) (fun n hn hna => ?_)
    (fun m hm hma => coefV hj (by omega))
  exact S.V_loc (by omega) (by omega)

end Setting

end Szkraw
