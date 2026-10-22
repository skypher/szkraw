import Szkraw.VRAffineDetours

/-!
# Theorem 8.9: the weights of the recurrence

In the setting `AffSetting` (`ν` log-concave without internal zeros with `ν 0 = 0 < ν 1`,
`0 < r`, `0 ≤ t`, `(2N-1) t ≤ s = 1 - r`), with `κ = affU` (Newton sequence of `c`) and
`β = ν - κ` (Newton sequence of `b`): the Leibniz consequences, the split `A_j = H_j - V_j`, the
nonnegativity of the weights on `Ω`, and the four detour inequalities.
-/

set_option linter.unusedSectionVars false

namespace Szkraw

open Finset

/-- The setting of Theorem 8.9 for the padded Newton sequence `ν` of the profile. -/
structure AffSetting (N : ℕ) (r t : ℝ) (ν : ℕ → ℝ) : Prop where
  hN : 1 ≤ N
  hr : 0 < r
  ht : 0 ≤ t
  hts : (2 * (N : ℝ) - 1) * t ≤ 1 - r
  hν : LCNZ ν
  hν0 : ν 0 = 0
  hν1 : 0 < ν 1

/-- The Newton sequence of `b`. -/
noncomputable def affW (N : ℕ) (r t : ℝ) (ν : ℕ → ℝ) (i : ℕ) : ℝ := ν i - affU N r t ν i

/-- `h_n(ℓ) = (s - t(ℓ+n)) f_n(ℓ)`. -/
noncomputable def hFn (r t : ℝ) (ν : ℕ → ℝ) (ℓ n : ℕ) : ℝ := (1 - r - t * ((ℓ : ℝ) + n)) * Szkraw.iterShift ν ℓ n

/-- `v_n(ℓ) = t n f_{n-1}(ℓ)`. -/
noncomputable def vFn (t : ℝ) (ν : ℕ → ℝ) (ℓ n : ℕ) : ℝ := t * n * Szkraw.iterShift ν ℓ (n - 1)

/-- `H_j = W^h_{2j+1,j}`. -/
noncomputable def affH (r t : ℝ) (ν : ℕ → ℝ) (j ℓ a : ℕ) : ℝ := WtF (hFn r t ν) (2 * j + 1) j ℓ a

/-- `V_j = W^v_{2j+1,j}`. -/
noncomputable def affV (t : ℝ) (ν : ℕ → ℝ) (j ℓ a : ℕ) : ℝ := WtF (vFn t ν) (2 * j + 1) j ℓ a

theorem iterShift_sub (g h : ℕ → ℝ) (ℓ n : ℕ) :
    Szkraw.iterShift (fun i => g i - h i) ℓ n = Szkraw.iterShift g ℓ n - Szkraw.iterShift h ℓ n := by
  rw [iterShift_eq, iterShift_eq, iterShift_eq, ← sum_sub_distrib]
  exact sum_congr rfl fun k _ => by ring

section Weights

variable {N : ℕ} {r t : ℝ} {ν : ℕ → ℝ} (S : AffSetting N r t ν)
include S

theorem AffSetting.s_ge (m : ℕ) (hm : m ≤ N) : t * m ≤ 1 - r := by
  have h := S.hts
  have hN : (1 : ℝ) ≤ N := by exact_mod_cast S.hN
  have : (m : ℝ) ≤ N := by exact_mod_cast hm
  nlinarith [S.ht]

theorem AffSetting.f_nonneg (ℓ n : ℕ) : 0 ≤ Szkraw.iterShift ν ℓ n := iterShift_nonneg S.hν ℓ n

theorem AffSetting.U_lcnz : LCNZ (affU N r t ν) := affU_lcnz S.hr S.ht S.hν S.hν0

theorem AffSetting.U_one : 0 < affU N r t ν 1 := affU_one_pos S.hN S.hr S.ht S.hν S.hν1

theorem AffSetting.dd_U {ℓ : ℕ} (hℓ : ℓ ≤ N) : dd (affU N r t ν) ℓ = (r + t * ℓ) * dd ν ℓ := by
  have := affU_leibniz (N := N) (r := r) (t := t) (ν := ν) ℓ 0 (by omega)
  simp only [Nat.cast_zero, add_zero, mul_zero, zero_mul] at this
  exact this

theorem AffSetting.dd_W {ℓ : ℕ} (hℓ : ℓ ≤ N) : dd (affW N r t ν) ℓ = (1 - r - t * ℓ) * dd ν ℓ := by
  unfold dd affW
  rw [iterShift_sub]
  have := S.dd_U hℓ
  unfold dd at this
  rw [this]; ring

theorem AffSetting.psi_split {ℓ n : ℕ} (h : ℓ + n ≤ N) :
    Szkraw.iterShift (affW N r t ν) ℓ n = hFn r t ν ℓ n - vFn t ν ℓ n := by
  unfold affW hFn vFn
  rw [iterShift_sub, affU_leibniz ℓ n h]
  ring

theorem AffSetting.phi_ge {ℓ n : ℕ} (hn : 1 ≤ n) (h : ℓ + n ≤ N) :
    (r + t * ((ℓ : ℝ) + 1)) * Szkraw.iterShift ν ℓ n ≤ Szkraw.iterShift (affU N r t ν) ℓ n := by
  rw [affU_leibniz ℓ n h]
  have hf := S.f_nonneg ℓ n
  have hf' := S.f_nonneg ℓ (n - 1)
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have : 0 ≤ t * ((n : ℝ) - 1) * Szkraw.iterShift ν ℓ n := mul_nonneg (mul_nonneg S.ht (by linarith)) hf
  have : 0 ≤ t * n * Szkraw.iterShift ν ℓ (n - 1) := mul_nonneg (mul_nonneg S.ht (by linarith)) hf'
  nlinarith

theorem AffSetting.B0_ge {ℓ a : ℕ} (h : ℓ + a ≤ N) :
    (r + t * ((ℓ : ℝ) + 1)) * Wt ν 2 0 ℓ a ≤ Wt (affU N r t ν) 2 0 ℓ a := by
  unfold Wt
  rw [mul_sum]
  refine sum_le_sum fun n hn => ?_
  rw [mem_range] at hn
  by_cases h2 : 2 ≤ n
  · rw [if_pos h2]
    have := S.phi_ge (ℓ := ℓ) (n := n) (by omega) (by omega)
    have hc : (0 : ℝ) ≤ ((n - 2 + 0).choose 0 : ℝ) * (a.choose n : ℝ) := by positivity
    calc (r + t * ((ℓ : ℝ) + 1)) * (((n - 2 + 0).choose 0 : ℝ) * (a.choose n : ℝ) * Szkraw.iterShift ν ℓ n)
        = (((n - 2 + 0).choose 0 : ℝ) * (a.choose n : ℝ)) * ((r + t * ((ℓ : ℝ) + 1)) * Szkraw.iterShift ν ℓ n) := by
          ring
      _ ≤ (((n - 2 + 0).choose 0 : ℝ) * (a.choose n : ℝ)) * Szkraw.iterShift (affU N r t ν) ℓ n :=
          mul_le_mul_of_nonneg_left this hc
      _ = _ := by ring
  · rw [if_neg h2]; simp

theorem AffSetting.B0_ge_phi2 (ℓ a : ℕ) :
    (a.choose 2 : ℝ) * Szkraw.iterShift (affU N r t ν) ℓ 2 ≤ Wt (affU N r t ν) 2 0 ℓ a := by
  rcases Nat.lt_or_ge a 2 with ha | ha
  · rw [Nat.choose_eq_zero_of_lt ha, Nat.cast_zero, zero_mul]; exact Wt_nonneg S.U_lcnz _ _ _ _
  · have := Wt_ge_term S.U_lcnz 2 0 ℓ a 2 le_rfl ha
    simpa using this

/-- The mixed inequality `c_{ℓ+1} f_{l+2}(ℓ) ≤ φ₂(ℓ) f_l(ℓ+1)` for `ℓ + 2 ≤ N`, `l ≥ 1`. -/
theorem AffSetting.mi2 {ℓ l : ℕ} (hℓ : ℓ + 2 ≤ N) (hl : 1 ≤ l) :
    dd (affU N r t ν) (ℓ + 1) * Szkraw.iterShift ν ℓ (l + 2) ≤
      Szkraw.iterShift (affU N r t ν) ℓ 2 * Szkraw.iterShift ν (ℓ + 1) l := by
  rw [S.dd_U (by omega)]
  have h83 := lemma_8_3 S.hν ℓ (i := 2) (l := l) (by norm_num) hl
  rw [add_comm 2 l] at h83
  have hφ := S.phi_ge (ℓ := ℓ) (n := 2) (by norm_num) hℓ
  have hρ : 0 ≤ r + t * ((ℓ : ℝ) + 1) := by have := S.hr; have := S.ht; positivity
  have hf1 := S.f_nonneg (ℓ + 1) l
  push_cast
  have hdd : dd ν (ℓ + 1) = Szkraw.iterShift ν (ℓ + 1) 0 := rfl
  rw [hdd]
  calc (r + t * ((ℓ : ℝ) + 1)) * Szkraw.iterShift ν (ℓ + 1) 0 * Szkraw.iterShift ν ℓ (l + 2)
      = (r + t * ((ℓ : ℝ) + 1)) * (Szkraw.iterShift ν (ℓ + 1) 0 * Szkraw.iterShift ν ℓ (l + 2)) := by ring
    _ ≤ (r + t * ((ℓ : ℝ) + 1)) * (Szkraw.iterShift ν ℓ 2 * Szkraw.iterShift ν (ℓ + 1) l) :=
        mul_le_mul_of_nonneg_left h83 hρ
    _ = ((r + t * ((ℓ : ℝ) + 1)) * Szkraw.iterShift ν ℓ 2) * Szkraw.iterShift ν (ℓ + 1) l := by ring
    _ ≤ Szkraw.iterShift (affU N r t ν) ℓ 2 * Szkraw.iterShift ν (ℓ + 1) l :=
        mul_le_mul_of_nonneg_right hφ hf1

/-! ### Convexity of the profile and `A₀` -/

theorem AffSetting.dd_succ (m : ℕ) : dd ν (m + 1) = dd ν m + Szkraw.iterShift ν m 1 := rfl

theorem AffSetting.f1_mono (m : ℕ) : Szkraw.iterShift ν m 1 ≤ Szkraw.iterShift ν (m + 1) 1 := by
  have : Szkraw.iterShift ν (m + 1) 1 = Szkraw.iterShift ν m 1 + Szkraw.iterShift ν m 2 := rfl
  rw [this]; linarith [S.f_nonneg m 2]

theorem AffSetting.f1_mono' {m m' : ℕ} (h : m ≤ m') : Szkraw.iterShift ν m 1 ≤ Szkraw.iterShift ν m' 1 := by
  induction m' with
  | zero => rw [Nat.le_zero.mp h]
  | succ m' ih =>
    rcases Nat.eq_or_lt_of_le h with e | e
    · rw [e]
    · exact le_trans (ih (by omega)) (S.f1_mono m')

theorem AffSetting.dd_le (ℓ : ℕ) : dd ν ℓ ≤ ℓ * Szkraw.iterShift ν ℓ 1 := by
  induction ℓ with
  | zero => show ν 0 ≤ _; rw [S.hν0]; simp
  | succ ℓ ih =>
    rw [S.dd_succ]
    have := S.f1_mono ℓ
    have := S.f_nonneg ℓ 1
    push_cast; nlinarith

theorem AffSetting.dd_incr (ℓ a : ℕ) : a * Szkraw.iterShift ν ℓ 1 ≤ dd ν (ℓ + a) - dd ν ℓ := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [show ℓ + (a + 1) = ℓ + a + 1 by ring, S.dd_succ]
    have := S.f1_mono' (show ℓ ≤ ℓ + a by omega)
    push_cast; linarith

/-- `A₀(ℓ,a) = α X - t a d_ℓ`, with `α = s - t(ℓ+a)` and `X = d_{ℓ+a} - d_ℓ`. -/
theorem AffSetting.A0_eq {ℓ a : ℕ} (h : ℓ + a ≤ N) :
    Wt (affW N r t ν) 1 0 ℓ a =
      (1 - r - t * ((ℓ : ℝ) + a)) * Wt ν 1 0 ℓ a - t * a * dd ν ℓ := by
  rw [Wt_one_zero, Wt_one_zero, S.dd_W h, S.dd_W (by omega)]
  push_cast; ring

theorem AffSetting.A0_nn {ℓ a : ℕ} (h : ℓ + a ≤ N) : 0 ≤ Wt (affW N r t ν) 1 0 ℓ a := by
  rcases Nat.eq_zero_or_pos a with ha | ha
  · subst ha; rw [Wt_eq_zero _ _ _ _ (by norm_num)]
  rw [S.A0_eq h, Wt_one_zero]
  have hinc := S.dd_incr ℓ a
  have hle := S.dd_le ℓ
  have hf := S.f_nonneg ℓ 1
  have hα : t * (2 * (ℓ : ℝ) + a) ≤ 1 - r := by
    have h1 : 2 * ℓ + a ≤ 2 * N - 1 := by omega
    have h2 : ((2 * ℓ + a : ℕ) : ℝ) ≤ 2 * (N : ℝ) - 1 := by
      have : ((2 * ℓ + a : ℕ) : ℝ) ≤ ((2 * N - 1 : ℕ) : ℝ) := by exact_mod_cast h1
      rw [Nat.cast_sub (by have := S.hN; omega)] at this; push_cast at this ⊢; linarith
    push_cast at h2
    nlinarith [S.hts, S.ht]
  have hα0 : 0 ≤ 1 - r - t * ((ℓ : ℝ) + a) := by nlinarith [S.ht, (Nat.cast_nonneg ℓ : (0 : ℝ) ≤ ℓ)]
  have ha' : (0 : ℝ) ≤ a := Nat.cast_nonneg a
  have p1 : 0 ≤ (1 - r - t * ((ℓ : ℝ) + a)) * (dd ν (ℓ + a) - dd ν ℓ - a * Szkraw.iterShift ν ℓ 1) :=
    mul_nonneg hα0 (by linarith)
  have p2 : 0 ≤ t * a * (ℓ * Szkraw.iterShift ν ℓ 1 - dd ν ℓ) := mul_nonneg (mul_nonneg S.ht ha') (by linarith)
  have p3 : 0 ≤ a * Szkraw.iterShift ν ℓ 1 * (1 - r - t * (2 * (ℓ : ℝ) + a)) :=
    mul_nonneg (mul_nonneg ha' hf) (by linarith)
  nlinarith [p1, p2, p3]

/-! ### Nonnegativity of `H` and `V` -/

theorem AffSetting.hFn_nn {ℓ n : ℕ} (h : ℓ + n ≤ N) : 0 ≤ hFn r t ν ℓ n := by
  unfold hFn
  have := S.s_ge (ℓ + n) h
  push_cast at this
  exact mul_nonneg (by linarith) (S.f_nonneg ℓ n)

theorem AffSetting.vFn_nn (ℓ n : ℕ) : 0 ≤ vFn t ν ℓ n := by
  unfold vFn
  exact mul_nonneg (mul_nonneg S.ht (Nat.cast_nonneg _)) (S.f_nonneg ℓ _)

theorem AffSetting.H_nn {j ℓ a : ℕ} (h : ℓ + a ≤ N) : 0 ≤ affH r t ν j ℓ a :=
  WtF_nonneg fun n _ hn => S.hFn_nn (by omega)

theorem AffSetting.V_nn (j ℓ a : ℕ) : 0 ≤ affV t ν j ℓ a :=
  WtF_nonneg fun n _ _ => S.vFn_nn ℓ n

/-- The split `A_j = H_j - V_j` on `Ω`. -/
theorem AffSetting.A_split {j ℓ a : ℕ} (h : ℓ + a ≤ N) :
    Wt (affW N r t ν) (2 * j + 1) j ℓ a = affH r t ν j ℓ a - affV t ν j ℓ a := by
  rw [Wt_eq_WtF, affH, affV, ← WtF_sub]
  exact WtF_congr fun n hn => S.psi_split (by omega)

theorem AffSetting.wC_eq (j ℓ a : ℕ) :
    wC (affU N r t ν) (affW N r t ν) j ℓ a = Wt ν (2 * j + 2) (j + 1) ℓ a := by
  unfold wC
  rw [Wt_add]
  congr 1
  funext i; unfold affW; ring

/-! ### The detours -/

theorem AffSetting.domC {j ℓ a : ℕ} (hj : 1 ≤ j) (h : ℓ + a ≤ N) :
    4 * dd (affU N r t ν) (ℓ + 1) * Wt ν (2 * j + 2) (j + 1) ℓ a ≤
      Wt (affU N r t ν) 2 0 ℓ a * Wt ν (2 * j) j (ℓ + 1) (a - 2) := by
  rw [Wt_eq_WtF, Wt_eq_WtF ν (2 * j)]
  exact detour_Cf j hj (dd_pos S.U_lcnz S.U_one (by omega)).le (Wt_nonneg S.U_lcnz _ _ _ _)
    (S.B0_ge_phi2 ℓ a) (fun m _ => S.f_nonneg ℓ m) (fun n _ => S.f_nonneg (ℓ + 1) n)
    (fun n hn hna => by rw [one_mul]; exact S.mi2 (by omega) (by omega))

theorem AffSetting.domH {j ℓ a : ℕ} (hj : 2 ≤ j) (h : ℓ + a ≤ N) :
    4 * dd (affU N r t ν) (ℓ + 1) * affH r t ν j ℓ a ≤
      Wt (affU N r t ν) 2 0 ℓ a * affH r t ν (j - 1) (ℓ + 1) (a - 2) := by
  unfold affH
  rw [show 2 * (j - 1) + 1 = 2 * j - 1 by omega]
  refine detour_HV j hj (dd_pos S.U_lcnz S.U_one (by omega)).le (Wt_nonneg S.U_lcnz _ _ _ _)
    (S.B0_ge_phi2 ℓ a) (fun m hm => S.hFn_nn (by omega)) (fun n hn => S.hFn_nn (by omega))
    (fun n hn hna => ?_)
  have hmi := S.mi2 (ℓ := ℓ) (l := n) (by omega) (by omega)
  have hs := S.s_ge (ℓ + n + 2) (by omega)
  have hφ : 0 ≤ Szkraw.iterShift (affU N r t ν) ℓ 2 := iterShift_nonneg S.U_lcnz ℓ 2
  have hf1 := S.f_nonneg (ℓ + 1) n
  have hfn := S.f_nonneg ℓ (n + 2)
  have hc := (dd_pos S.U_lcnz S.U_one (show 1 ≤ ℓ + 1 by omega)).le
  unfold hFn
  push_cast at hs ⊢
  have hs' : 0 ≤ 1 - r - t * ((ℓ : ℝ) + (n + 2)) := by linarith
  have hst : 1 - r - t * ((ℓ : ℝ) + (n + 2)) ≤ 1 - r - t * ((ℓ : ℝ) + 1 + n) := by nlinarith [S.ht]
  have hpf : 0 ≤ Szkraw.iterShift (affU N r t ν) ℓ 2 * Szkraw.iterShift ν (ℓ + 1) n := mul_nonneg hφ hf1
  calc dd (affU N r t ν) (ℓ + 1) * ((1 - r - t * ((ℓ : ℝ) + (n + 2))) * Szkraw.iterShift ν ℓ (n + 2))
      = (1 - r - t * ((ℓ : ℝ) + (n + 2))) * (dd (affU N r t ν) (ℓ + 1) * Szkraw.iterShift ν ℓ (n + 2)) := by ring
    _ ≤ (1 - r - t * ((ℓ : ℝ) + (n + 2))) * (Szkraw.iterShift (affU N r t ν) ℓ 2 * Szkraw.iterShift ν (ℓ + 1) n) :=
        mul_le_mul_of_nonneg_left hmi hs'
    _ ≤ (1 - r - t * ((ℓ : ℝ) + 1 + n)) * (Szkraw.iterShift (affU N r t ν) ℓ 2 * Szkraw.iterShift ν (ℓ + 1) n) :=
        mul_le_mul_of_nonneg_right hst hpf
    _ ≤ 2 * (Szkraw.iterShift (affU N r t ν) ℓ 2 * ((1 - r - t * ((ℓ : ℝ) + 1 + n)) * Szkraw.iterShift ν (ℓ + 1) n)) := by
        have : 0 ≤ (1 - r - t * ((ℓ : ℝ) + 1 + n)) * (Szkraw.iterShift (affU N r t ν) ℓ 2 * Szkraw.iterShift ν (ℓ + 1) n) :=
          mul_nonneg (by linarith) hpf
        nlinarith

theorem AffSetting.domV {j ℓ a : ℕ} (hj : 2 ≤ j) (h : ℓ + a ≤ N) :
    4 * dd (affU N r t ν) (ℓ + 1) * affV t ν j ℓ a ≤
      Wt (affU N r t ν) 2 0 ℓ a * affV t ν (j - 1) (ℓ + 1) (a - 2) := by
  unfold affV
  rw [show 2 * (j - 1) + 1 = 2 * j - 1 by omega]
  refine detour_HV j hj (dd_pos S.U_lcnz S.U_one (by omega)).le (Wt_nonneg S.U_lcnz _ _ _ _)
    (S.B0_ge_phi2 ℓ a) (fun m _ => S.vFn_nn ℓ m) (fun n _ => S.vFn_nn (ℓ + 1) n) (fun n hn hna => ?_)
  have hmi := S.mi2 (ℓ := ℓ) (l := n - 1) (by omega) (by omega)
  rw [show n - 1 + 2 = n + 1 by omega] at hmi
  have hφ : 0 ≤ Szkraw.iterShift (affU N r t ν) ℓ 2 := iterShift_nonneg S.U_lcnz ℓ 2
  have hf1 := S.f_nonneg (ℓ + 1) (n - 1)
  unfold vFn
  rw [show n + 2 - 1 = n + 1 by omega]
  have hn : (3 : ℝ) ≤ n := by exact_mod_cast (show 3 ≤ n by omega)
  have hpf : 0 ≤ Szkraw.iterShift (affU N r t ν) ℓ 2 * Szkraw.iterShift ν (ℓ + 1) (n - 1) := mul_nonneg hφ hf1
  push_cast
  calc dd (affU N r t ν) (ℓ + 1) * (t * ((n : ℝ) + 2) * Szkraw.iterShift ν ℓ (n + 1))
      = t * ((n : ℝ) + 2) * (dd (affU N r t ν) (ℓ + 1) * Szkraw.iterShift ν ℓ (n + 1)) := by ring
    _ ≤ t * ((n : ℝ) + 2) * (Szkraw.iterShift (affU N r t ν) ℓ 2 * Szkraw.iterShift ν (ℓ + 1) (n - 1)) :=
        mul_le_mul_of_nonneg_left hmi (by have := S.ht; positivity)
    _ ≤ 2 * (Szkraw.iterShift (affU N r t ν) ℓ 2 * (t * n * Szkraw.iterShift ν (ℓ + 1) (n - 1))) := by
        have : 0 ≤ t * ((n : ℝ) - 2) * (Szkraw.iterShift (affU N r t ν) ℓ 2 * Szkraw.iterShift ν (ℓ + 1) (n - 1)) :=
          mul_nonneg (mul_nonneg S.ht (by linarith)) hpf
        nlinarith

theorem AffSetting.domB {j ℓ a : ℕ} (hj : 1 ≤ j) :
    4 * dd (affU N r t ν) (ℓ + 1) * wB (affU N r t ν) j ℓ a ≤
      wB (affU N r t ν) 0 ℓ a * wB (affU N r t ν) (j - 1) (ℓ + 1) (a - 2) := by
  unfold wB
  have := lemma_8_4_B S.U_lcnz j ℓ a hj
  have e1 : 2 * (j - 1) + 2 = 2 * j := by omega
  simp only [Nat.mul_zero, zero_add, e1]
  exact this

end Weights

end Szkraw
