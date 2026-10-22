import Szkraw.VRAffineEnds

/-!
# Theorem 8.9: the key inequality under nondecreasing `b` (paper, eq. `affine-key`)

With `u = f(ℓ)`, the inequality reduces to `(eq:affine-red)`, which is linear in `α = s - t(ℓ+a)`
with a nonnegative `α`-coefficient `K`. Monotonicity of `b` and of `d_i/f_1(i)` gives
`α u₁ ≥ t u₀`, and at `α = t u₀/u₁` the difference is `t/u₁` times
`G = u₀ Y Y' + D Y J - D(4 u₀ H_* + 2 u₁ T)`, which is `u₁³ F(u₀/u₁)` for the normalized sequence.
-/

set_option linter.unusedSectionVars false

namespace Szkraw

open Finset

section Scale

variable {u : ℕ → ℝ}

theorem LCNZ.scale (hu : LCNZ u) {c : ℝ} (hc : 0 < c) : LCNZ (fun n => u n / c) := by
  refine ⟨fun n => div_nonneg (hu.1 n) hc.le, fun i => ?_, fun i j k hij hjk hi hk => ?_⟩
  · have := hu.2.1 i
    have h2 : c * c = c ^ 2 := by ring
    simp only
    rw [div_mul_div_comm, div_pow, h2]
    exact div_le_div_of_nonneg_right this (by positivity)
  · simp only at hi hk ⊢
    have hi' : 0 < u i := by
      rcases div_pos_iff.mp hi with h | h
      · exact h.1
      · exact absurd h.2 (not_lt.mpr hc.le)
    have hk' : 0 < u k := by
      rcases div_pos_iff.mp hk with h | h
      · exact h.1
      · exact absurd h.2 (not_lt.mpr hc.le)
    exact _root_.div_pos (hu.2.2 i j k hij hjk hi' hk') hc

theorem sY_div (c : ℝ) (a : ℕ) : sY (fun n => u n / c) a = sY u a / c := by
  unfold sY; rw [sum_div]; exact sum_congr rfl fun n _ => by ring
theorem sJ_div (c : ℝ) (a : ℕ) : sJ (fun n => u n / c) a = sJ u a / c := by
  unfold sJ; rw [sum_div]; exact sum_congr rfl fun n _ => by ring
theorem sYp_div (c : ℝ) (a : ℕ) : sYp (fun n => u n / c) a = sYp u a / c := by
  unfold sYp; rw [sum_div]; exact sum_congr rfl fun n _ => by ring
theorem sH_div (c : ℝ) (a : ℕ) : sH (fun n => u n / c) a = sH u a / c := by
  unfold sH; rw [sum_div]; exact sum_congr rfl fun n _ => by ring
theorem sT_div (c : ℝ) (a : ℕ) : sT (fun n => u n / c) a = sT u a / c := by
  unfold sT; rw [sum_div]; exact sum_congr rfl fun n _ => by ring

/-- `G = u₀ Y Y' + (u₀+u₁) Y J - (u₀+u₁)(4u₀ H_* + 2u₁ T) ≥ 0`. -/
theorem G_nonneg (hu : LCNZ u) (hu1 : 0 < u 1) {a : ℕ} (ha : 3 ≤ a) :
    0 ≤ u 0 * sY u a * sYp u a + (u 0 + u 1) * sY u a * sJ u a -
      (u 0 + u 1) * (4 * u 0 * sH u a + 2 * u 1 * sT u a) := by
  set v : ℕ → ℝ := fun n => u n / u 1 with hv
  have hvl : LCNZ v := hu.scale hu1
  have hv1 : v 1 = 1 := by simp [hv, hu1.ne']
  have hz : 0 ≤ u 0 / u 1 := div_nonneg (hu.1 0) hu1.le
  have hzq : u 0 / u 1 * v 2 ≤ 1 := by
    simp only [hv]
    rw [div_mul_div_comm, div_le_one (by positivity)]
    have := hu.2.1 0; simpa [sq] using this
  have hF := Fz_nonneg hvl hv1 ha hz hzq
  have e : u 0 * sY u a * sYp u a + (u 0 + u 1) * sY u a * sJ u a - (u 0 + u 1) * (4 * u 0 * sH u a + 2 * u 1 * sT u a) =
      u 1 ^ 3 * Fz v a (u 0 / u 1) := by
    unfold Fz
    rw [sY_div, sJ_div, sYp_div, sH_div, sT_div]
    field_simp
  rw [e]; exact mul_nonneg (by positivity) hF

end Scale

/-! ### The sums at the level `ℓ` -/

theorem Wt20_eq (ν : ℕ → ℝ) (ℓ a : ℕ) : Wt ν 2 0 ℓ a = sY (Szkraw.iterShift ν ℓ) a := by
  unfold Wt sY
  refine sum_congr rfl fun n _ => ?_
  split_ifs <;> simp

theorem Wt20_succ_eq (ν : ℕ → ℝ) (ℓ a : ℕ) (ha : 1 ≤ a) :
    Wt ν 2 0 (ℓ + 1) (a - 1) = sYp (Szkraw.iterShift ν ℓ) a := by
  unfold Wt sYp
  rw [show a - 1 + 1 = a by omega]
  refine sum_congr rfl fun n _ => ?_
  have : Szkraw.iterShift ν (ℓ + 1) n = Szkraw.iterShift ν ℓ n + Szkraw.iterShift ν ℓ (n + 1) := rfl
  rw [this]
  split_ifs <;> simp

/-- `X' = (a-2) u₁ + J`. -/
theorem Wt10_succ_eq (ν : ℕ → ℝ) (ℓ a : ℕ) (ha : 3 ≤ a) :
    Wt ν 1 0 (ℓ + 1) (a - 2) = ((a : ℝ) - 2) * Szkraw.iterShift ν ℓ 1 + sJ (Szkraw.iterShift ν ℓ) a := by
  set u := Szkraw.iterShift ν ℓ with hu
  rw [Wt_one_split, Nat.cast_sub (by omega : 2 ≤ a), Nat.cast_ofNat]
  have hF1 : Szkraw.iterShift ν (ℓ + 1) 1 = u 1 + u 2 := rfl
  rw [hF1]
  -- `(a-2) u₂ + Σ_{j ≥ 2} C(a-2,j)(u_j + u_{j+1}) = Σ_{n ≥ 2} C(a-1,n) u_n`
  have hW : Wt ν 2 0 (ℓ + 1) (a - 2) = ∑ j ∈ range (a - 1), (if 2 ≤ j then ((a - 2).choose j : ℝ) else 0) * u j +
      ∑ j ∈ range (a - 1), (if 2 ≤ j then ((a - 2).choose j : ℝ) else 0) * u (j + 1) := by
    unfold Wt
    rw [show a - 2 + 1 = a - 1 by omega, ← sum_add_distrib]
    refine sum_congr rfl fun j _ => ?_
    have : Szkraw.iterShift ν (ℓ + 1) j = u j + u (j + 1) := rfl
    rw [this]; split_ifs <;> simp; ring
  set G : ℕ → ℝ := fun n => (if 3 ≤ n then ((a - 2).choose (n - 1) : ℝ) else 0) * u n with hG
  have hS2 : ∑ j ∈ range (a - 1), (if 2 ≤ j then ((a - 2).choose j : ℝ) else 0) * u (j + 1) = ∑ n ∈ range a, G n := by
    have hr := reindex1 G (a - 1) (by simp [hG])
    rw [show a - 1 + 1 = a by omega] at hr
    rw [← hr]
    refine sum_congr rfl fun j _ => ?_
    simp only [hG]
    by_cases h : 2 ≤ j
    · rw [if_pos h, if_pos (by omega), show j + 1 - 1 = j by omega]
    · rw [if_neg h, if_neg (by omega)]
  have hS1 : ∑ j ∈ range (a - 1), (if 2 ≤ j then ((a - 2).choose j : ℝ) else 0) * u j =
      ∑ n ∈ range a, (if 2 ≤ n then ((a - 2).choose n : ℝ) else 0) * u n := by
    have hr := Finset.sum_range_succ (fun n => (if 2 ≤ n then ((a - 2).choose n : ℝ) else 0) * u n) (a - 1)
    rw [show a - 1 + 1 = a by omega] at hr
    rw [hr, Nat.choose_eq_zero_of_lt (show a - 2 < a - 1 by omega)]
    simp
  have hU2 : ((a : ℝ) - 2) * u 2 = ∑ n ∈ range a, (if n = 2 then ((a : ℝ) - 2) * u n else 0) := by
    rw [sum_ite_eq', if_pos (mem_range.mpr (by omega))]
  rw [hW, hS1, hS2]
  have : ((a : ℝ) - 2) * (u 1 + u 2) = ((a : ℝ) - 2) * u 1 + ((a : ℝ) - 2) * u 2 := by ring
  rw [this, hU2, add_assoc, ← sum_add_distrib, ← sum_add_distrib]
  congr 1
  unfold sJ
  refine sum_congr rfl fun n hn => ?_
  rw [mem_range] at hn
  simp only [hG]
  rcases Nat.lt_or_ge n 2 with h | h
  · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]; ring
  rcases Nat.eq_or_lt_of_le h with e | h3
  · subst e
    rw [if_pos rfl, if_pos le_rfl, if_neg (by omega), if_pos le_rfl]
    have hp : (a - 1).choose 2 = (a - 2).choose 1 + (a - 2).choose 2 := by
      rw [show a - 1 = a - 2 + 1 by omega]; exact Nat.choose_succ_succ' (a - 2) 1
    have hp' : ((a - 1).choose 2 : ℝ) = ((a : ℝ) - 2) + ((a - 2).choose 2 : ℝ) := by
      rw [hp]; push_cast [Nat.choose_one_right, Nat.cast_sub (show 2 ≤ a by omega)]; ring
    rw [hp']; ring
  · rw [if_neg (by omega), if_pos (by omega), if_pos (by omega), if_pos (by omega)]
    have hp : (a - 1).choose n = (a - 2).choose (n - 1) + (a - 2).choose n := by
      rw [show a - 1 = a - 2 + 1 by omega, show n = n - 1 + 1 by omega, Nat.choose_succ_succ',
        show n - 1 + 1 - 1 = n - 1 by omega]
    rw [hp]; push_cast; ring

/-- `4 H₁ - 2 V₁ = 4 α H_* + 2 t T`. -/
theorem HV_eq (r t : ℝ) (ν : ℕ → ℝ) (ℓ a : ℕ) :
    4 * affH r t ν 1 ℓ a - 2 * affV t ν 1 ℓ a =
      4 * (1 - r - t * ((ℓ : ℝ) + a)) * sH (Szkraw.iterShift ν ℓ) a + 2 * t * sT (Szkraw.iterShift ν ℓ) a := by
  rw [V1_reindex]
  unfold affH WtF hFn sH sT
  rw [mul_sum, mul_sum, mul_sum, mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
  refine sum_congr rfl fun n _ => ?_
  rcases Nat.lt_or_ge n 2 with h | h
  · rw [if_neg (show ¬ (2 * 1 + 1 ≤ n) by omega), if_neg (show ¬ (2 ≤ n) by omega),
      if_neg (show ¬ (3 ≤ n) by omega), if_neg (show ¬ (2 ≤ n) by omega)]
    ring
  rcases Nat.eq_or_lt_of_le h with e | h3
  · subst e
    rw [if_neg (show ¬ (2 * 1 + 1 ≤ 2) by omega), if_pos (show 2 ≤ 2 from le_rfl),
      if_neg (show ¬ (3 ≤ 2) by omega), if_pos (show 2 ≤ 2 from le_rfl)]
    push_cast; ring
  · rw [if_pos (show 2 * 1 + 1 ≤ n by omega), if_pos (show 2 ≤ n by omega),
      if_pos (show 3 ≤ n by omega), if_pos (show 2 ≤ n by omega),
      show n - (2 * 1 + 1) + 1 = n - 2 by omega, Nat.choose_one_right, Nat.cast_sub (show 2 ≤ n by omega)]
    push_cast; ring

section Key

variable {N : ℕ} {r t : ℝ} {ν : ℕ → ℝ} (S : AffSetting N r t ν)
include S

theorem AffSetting.f1_pos (i : ℕ) : 0 < Szkraw.iterShift ν i 1 := iterShift_one_pos S.hν S.hν1 i

/-- `d_i/f_1(i)` is nondecreasing, in cross-multiplied form. -/
theorem AffSetting.R_step (i : ℕ) :
    dd ν i * Szkraw.iterShift ν (i + 1) 1 ≤ dd ν (i + 1) * Szkraw.iterShift ν i 1 := by
  have hlc := (S.hν.iterShift i).2.1 0
  have e1 : dd ν (i + 1) = dd ν i + Szkraw.iterShift ν i 1 := rfl
  have e2 : Szkraw.iterShift ν (i + 1) 1 = Szkraw.iterShift ν i 1 + Szkraw.iterShift ν i 2 := rfl
  have e0 : dd ν i = Szkraw.iterShift ν i 0 := rfl
  rw [e1, e2, e0]
  simp only [zero_add] at hlc
  nlinarith [hlc]

theorem AffSetting.R_chain (ℓ k : ℕ) :
    dd ν ℓ * Szkraw.iterShift ν (ℓ + k) 1 ≤ dd ν (ℓ + k) * Szkraw.iterShift ν ℓ 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hs := S.R_step (ℓ + k)
    have hp := S.f1_pos (ℓ + k)
    have hp1 := S.f1_pos (ℓ + k + 1)
    have hpl := S.f1_pos ℓ
    rw [show ℓ + (k + 1) = ℓ + k + 1 by ring]
    have a1 := mul_le_mul_of_nonneg_right ih hp1.le
    have a2 := mul_le_mul_of_nonneg_left hs hpl.le
    have : dd ν ℓ * Szkraw.iterShift ν (ℓ + k + 1) 1 * Szkraw.iterShift ν (ℓ + k) 1 ≤
        dd ν (ℓ + k + 1) * Szkraw.iterShift ν ℓ 1 * Szkraw.iterShift ν (ℓ + k) 1 := by nlinarith
    exact le_of_mul_le_mul_right this hp

/-- `α u₁ ≥ t u₀`, from the monotonicity of `b` at `ℓ + a - 1`. -/
theorem AffSetting.alpha_ge {ℓ a : ℕ} (h : ℓ + a ≤ N) (ha : 1 ≤ a) :
    t * dd ν ℓ ≤ (1 - r - t * ((ℓ : ℝ) + a)) * Szkraw.iterShift ν ℓ 1 := by
  obtain ⟨m, hm⟩ : ∃ m, ℓ + a = m + 1 := ⟨ℓ + a - 1, by omega⟩
  have hstep := S.hb m (by omega)
  rw [S.dd_W (by omega), S.dd_W (by omega)] at hstep
  have e1 : dd ν (m + 1) = dd ν m + Szkraw.iterShift ν m 1 := rfl
  rw [e1] at hstep
  have hm1 : (ℓ : ℝ) + a = (m : ℝ) + 1 := by exact_mod_cast hm
  rw [hm1]
  push_cast at hstep
  have hb' : t * dd ν m ≤ (1 - r - t * ((m : ℝ) + 1)) * Szkraw.iterShift ν m 1 := by linarith
  set α := 1 - r - t * ((m : ℝ) + 1) with hα
  have hα0 : 0 ≤ α := by have := S.s_ge (m + 1) (by omega); push_cast at this; linarith
  have hch := S.R_chain ℓ (m - ℓ)
  rw [show ℓ + (m - ℓ) = m by omega] at hch
  have hd : 0 ≤ dd ν ℓ := S.f_nonneg ℓ 0
  have hdm0 : 0 ≤ dd ν m := S.f_nonneg m 0
  have hfm := S.f1_pos m
  have hfl := S.f1_pos ℓ
  have k1 : α * (dd ν ℓ * Szkraw.iterShift ν m 1) ≤ α * (dd ν m * Szkraw.iterShift ν ℓ 1) :=
    mul_le_mul_of_nonneg_left hch hα0
  have k2 : t * dd ν m * dd ν ℓ ≤ α * Szkraw.iterShift ν m 1 * dd ν ℓ := mul_le_mul_of_nonneg_right hb' hd
  rcases eq_or_lt_of_le hdm0 with hdm | hdm
  · have : dd ν ℓ * Szkraw.iterShift ν m 1 ≤ 0 := by rw [← hdm] at hch; linarith
    have hdl : dd ν ℓ = 0 := le_antisymm (by nlinarith) hd
    rw [hdl, mul_zero]; exact mul_nonneg hα0 hfl.le
  · have : t * dd ν ℓ * dd ν m ≤ α * Szkraw.iterShift ν ℓ 1 * dd ν m := by nlinarith
    exact le_of_mul_le_mul_right this hdm

/-- **The key inequality** (paper, eq. `affine-key`), on `Ω` with `a ≥ 3`, under nondecreasing `b`. -/
theorem AffSetting.key {ℓ a : ℕ} (h : ℓ + a ≤ N) (ha : 3 ≤ a) :
    4 * dd (affU N r t ν) (ℓ + 1) * affH r t ν 1 ℓ a ≤
      Wt (affW N r t ν) 1 0 ℓ a * Wt (affU N r t ν) 2 0 (ℓ + 1) (a - 1) +
      Wt (affU N r t ν) 2 0 ℓ a * Wt (affW N r t ν) 1 0 (ℓ + 1) (a - 2) +
      2 * dd (affU N r t ν) (ℓ + 1) * affV t ν 1 ℓ a := by
  set u := Szkraw.iterShift ν ℓ with hu
  set ρ := r + t * ((ℓ : ℝ) + 1) with hρ
  set D := dd ν (ℓ + 1) with hD
  set X := Wt ν 1 0 ℓ a with hX
  set Y := Wt ν 2 0 ℓ a with hY
  set X' := Wt ν 1 0 (ℓ + 1) (a - 2) with hX'
  set Y' := Wt ν 2 0 (ℓ + 1) (a - 1) with hY'
  set α := 1 - r - t * ((ℓ : ℝ) + a) with hα
  have ht := S.ht
  have hρ0 : 0 < ρ := by have := S.hr; positivity
  have hcc : dd (affU N r t ν) (ℓ + 1) = ρ * D := by rw [S.dd_U (by omega)]; push_cast; ring
  have hA0 : Wt (affW N r t ν) 1 0 ℓ a = α * X - t * a * u 0 := S.A0_eq h
  have hA0'' : Wt (affW N r t ν) 1 0 (ℓ + 1) (a - 2) = (α + t) * X' - t * ((a : ℝ) - 2) * D := by
    rw [S.A0_eq (by omega), Nat.cast_sub (by omega : 2 ≤ a)]
    push_cast; ring
  have nA0 := S.A0_nn h
  have nA0'' := S.A0_nn (show ℓ + 1 + (a - 2) ≤ N by omega)
  have hB0 : ρ * Y ≤ Wt (affU N r t ν) 2 0 ℓ a := S.B0_ge h
  have hY'0 : 0 ≤ Y' := Wt_nonneg S.hν _ _ _ _
  have hB0' : ρ * Y' ≤ Wt (affU N r t ν) 2 0 (ℓ + 1) (a - 1) := by
    have := S.B0_ge (ℓ := ℓ + 1) (a := a - 1) (by omega)
    push_cast at this
    have : ρ * Y' ≤ (r + t * ((ℓ : ℝ) + 1 + 1)) * Y' := mul_le_mul_of_nonneg_right (by linarith) hY'0
    linarith
  -- the reduced inequality `(eq:affine-red)`
  have hU := S.hν.iterShift ℓ
  have hu1 : 0 < u 1 := S.f1_pos ℓ
  have hDu : D = u 0 + u 1 := rfl
  have eX : X = (a : ℝ) * u 1 + sY u a := by rw [hX, Wt_one_split, Wt20_eq]
  have eY : Y = sY u a := Wt20_eq ν ℓ a
  have eX' : X' = ((a : ℝ) - 2) * u 1 + sJ u a := Wt10_succ_eq ν ℓ a ha
  have eY' : Y' = sYp u a := Wt20_succ_eq ν ℓ a (by omega)
  have eHV := HV_eq r t ν ℓ a
  -- `K ≥ 0`
  have hK : 0 ≤ X * Y' + Y * X' - 4 * D * sH u a := by
    have hg := S.gamma_bound ℓ a ha
    have hgs : 4 * sH u a ≤ gammaSum ν ℓ a := by
      unfold sH gammaSum; rw [mul_sum]
      refine sum_le_sum fun n _ => ?_
      have hun := S.f_nonneg ℓ n
      by_cases h3 : 3 ≤ n
      · rw [if_pos h3, if_pos h3]
        have hn : (3 : ℝ) ≤ n := by exact_mod_cast h3
        have hC : (0 : ℝ) ≤ (a.choose n : ℝ) := Nat.cast_nonneg _
        have hcoef : 4 * ((n : ℝ) - 2) ≤ 2 * n + (if 4 ≤ n then (n.choose 2 : ℝ) else 0) := by
          split_ifs with h4
          · have := choose_two_mul n
            have h' : ((n.choose 2 * 2 : ℕ) : ℝ) = ((n * (n - 1) : ℕ) : ℝ) := by rw [this]
            push_cast [Nat.cast_sub (show 1 ≤ n by omega)] at h'
            nlinarith [sq_nonneg ((n : ℝ) - 5 / 2)]
          · have : n = 3 := by omega
            subst this; norm_num
        have : (2 * (n : ℝ) + (if 4 ≤ n then (n.choose 2 : ℝ) else 0)) * (a.choose n : ℝ) * u n =
            (2 * ((n : ℝ) * (a.choose n : ℝ)) + (if 4 ≤ n then (n.choose 2 : ℝ) * (a.choose n : ℝ) else 0)) * u n := by
          split_ifs <;> ring
        rw [← this]
        have := mul_le_mul_of_nonneg_right hcoef (mul_nonneg hC hun)
        linarith
      · rw [if_neg h3, if_neg h3, if_neg (by omega)]; simp
    have hD0 : 0 ≤ D := S.f_nonneg (ℓ + 1) 0
    have := mul_le_mul_of_nonneg_left hgs hD0
    linarith
  have hG := G_nonneg hU hu1 ha
  have hab := S.alpha_ge h (by omega)
  have hu0 : u 0 = dd ν ℓ := rfl
  have h1 : 0 ≤ α * u 1 - t * u 0 := by rw [hu0]; linarith [hab]
  have hE : 0 ≤ (α * X - t * a * u 0) * Y' + Y * ((α + t) * X' - t * ((a : ℝ) - 2) * D) -
      D * (4 * α * sH u a + 2 * t * sT u a) := by
    have e : u 1 * ((α * X - t * a * u 0) * Y' + Y * ((α + t) * X' - t * ((a : ℝ) - 2) * D) -
        D * (4 * α * sH u a + 2 * t * sT u a)) =
        (α * u 1 - t * u 0) * (X * Y' + Y * X' - 4 * D * sH u a) +
        t * (u 0 * sY u a * sYp u a + (u 0 + u 1) * sY u a * sJ u a -
          (u 0 + u 1) * (4 * u 0 * sH u a + 2 * u 1 * sT u a)) := by
      rw [eX, eY, eX', eY', hDu]; ring
    have hpos : 0 ≤ u 1 * ((α * X - t * a * u 0) * Y' + Y * ((α + t) * X' - t * ((a : ℝ) - 2) * D) -
        D * (4 * α * sH u a + 2 * t * sT u a)) := by
      rw [e]; exact add_nonneg (mul_nonneg h1 hK) (mul_nonneg ht hG)
    by_contra hc
    push Not at hc
    have := mul_neg_of_pos_of_neg hu1 hc
    linarith
  have hred : 0 ≤ (α * X - t * a * u 0) * Y' + Y * ((α + t) * X' - t * ((a : ℝ) - 2) * D) -
      D * (4 * affH r t ν 1 ℓ a - 2 * affV t ν 1 ℓ a) := by
    have : 4 * affH r t ν 1 ℓ a - 2 * affV t ν 1 ℓ a = 4 * α * sH u a + 2 * t * sT u a := eHV
    rw [this]; exact hE
  have p1 : 0 ≤ (α * X - t * a * u 0) * (Wt (affU N r t ν) 2 0 (ℓ + 1) (a - 1) - ρ * Y') := by
    rw [← hA0]; exact mul_nonneg nA0 (by linarith)
  have p2 : 0 ≤ (Wt (affU N r t ν) 2 0 ℓ a - ρ * Y) * ((α + t) * X' - t * ((a : ℝ) - 2) * D) := by
    rw [← hA0'']; exact mul_nonneg (by linarith) nA0''
  have p3 := mul_nonneg hρ0.le hred
  rw [hcc, hA0, hA0'']
  linear_combination p1 + p2 + p3

end Key

end Szkraw
