import Szkraw.GenKey

/-!
# Theorem 8.16, Phase A: pure lemmas on a log-concave sequence

For `f` with `LCNZ f` and `0 < f 1`, `dd f i` is its Newton profile, `iterShift f i 1 = f₁(i)`
is the forward difference of the profile, and `R_i = dd f i / f₁(i)` is nondecreasing. The
inequalities (8.9) of the paper follow by summing these over the window.
-/

set_option linter.unusedSectionVars false

namespace Szkraw

open Finset

section PhaseA

theorem dd_succ_eq (f : ℕ → ℝ) (x : ℕ) : dd f (x + 1) = dd f x + iterShift f x 1 := rfl

theorem dd_zero_eq (f : ℕ → ℝ) : dd f 0 = f 0 := by
  unfold dd; rw [iterShift_eq]; simp

theorem dd_one_eq (f : ℕ → ℝ) : dd f 1 = f 0 + f 1 := by
  rw [dd_succ_eq, dd_zero_eq]; rfl

theorem iter_one_eq (f : ℕ → ℝ) (x : ℕ) : iterShift f x 1 = dd f (x + 1) - dd f x := by
  rw [dd_succ_eq]; ring

theorem dd_mono_of {f : ℕ → ℝ} (hf : LCNZ f) {i j : ℕ} (h : i ≤ j) : dd f i ≤ dd f j := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  clear h
  induction k with
  | zero => simp
  | succ k ih =>
    rw [← add_assoc, dd_succ_eq]
    linarith [iterShift_nonneg hf (i + k) 1]

theorem dd_nonneg_of {f : ℕ → ℝ} (hf : LCNZ f) (n : ℕ) : 0 ≤ dd f n := iterShift_nonneg hf n 0

theorem R_step_f {f : ℕ → ℝ} (hf : LCNZ f) (i : ℕ) :
    dd f i * iterShift f (i + 1) 1 ≤ dd f (i + 1) * iterShift f i 1 := by
  have hlc := (hf.iterShift i).2.1 0
  have e1 : dd f (i + 1) = dd f i + iterShift f i 1 := rfl
  have e2 : iterShift f (i + 1) 1 = iterShift f i 1 + iterShift f i 2 := rfl
  have e0 : dd f i = iterShift f i 0 := rfl
  rw [e1, e2, e0]
  simp only [zero_add] at hlc
  nlinarith [hlc]

theorem R_chain_f {f : ℕ → ℝ} (hf : LCNZ f) (hf1 : 0 < f 1) (ℓ k : ℕ) :
    dd f ℓ * iterShift f (ℓ + k) 1 ≤ dd f (ℓ + k) * iterShift f ℓ 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hs := R_step_f hf (ℓ + k)
    have hp := iterShift_one_pos hf hf1 (ℓ + k)
    have hp1 := iterShift_one_pos hf hf1 (ℓ + k + 1)
    have hpl := iterShift_one_pos hf hf1 ℓ
    rw [show ℓ + (k + 1) = ℓ + k + 1 by ring]
    have a1 := mul_le_mul_of_nonneg_right ih hp1.le
    have a2 := mul_le_mul_of_nonneg_left hs hpl.le
    have : dd f ℓ * iterShift f (ℓ + k + 1) 1 * iterShift f (ℓ + k) 1 ≤
        dd f (ℓ + k + 1) * iterShift f ℓ 1 * iterShift f (ℓ + k) 1 := by nlinarith
    exact le_of_mul_le_mul_right this hp

/-- `d_i F ≤ d_{b+1} f₁(i)` for `i ≤ b`, where `F = d_{b+1} - d_b = f₁(b)`. -/
theorem F_le {f : ℕ → ℝ} (hf : LCNZ f) (hf1 : 0 < f 1) {b i : ℕ} (hi : i ≤ b) :
    dd f i * (dd f (b + 1) - dd f b) ≤ dd f (b + 1) * iterShift f i 1 := by
  have h1 := R_chain_f hf hf1 i (b - i)
  rw [show i + (b - i) = b by omega] at h1
  have h2 : dd f b ≤ dd f (b + 1) := dd_mono_of hf (by omega)
  have h3 := mul_le_mul_of_nonneg_right h2 (iterShift_nonneg hf i 1)
  have hF : dd f (b + 1) - dd f b = iterShift f b 1 := by rw [dd_succ_eq]; ring
  rw [hF]
  linarith

/-- Paper (8.9), first form: `A·X'' ≥ (a-1)·d₀·F` with `a = b+1`, `X'' = d_b - d₀`. -/
theorem A2a {f : ℕ → ℝ} (hf : LCNZ f) (hf1 : 0 < f 1) (b : ℕ) :
    (b : ℝ) * dd f 0 * (dd f (b + 1) - dd f b) ≤ dd f (b + 1) * (dd f b - dd f 0) := by
  have hFnn : 0 ≤ dd f (b + 1) - dd f b := by
    rw [dd_succ_eq]; linarith [iterShift_nonneg hf b 1]
  have hsum : ∑ i ∈ range b, dd f i * (dd f (b + 1) - dd f b) ≤
      ∑ i ∈ range b, dd f (b + 1) * iterShift f i 1 :=
    sum_le_sum fun i hi => F_le hf hf1 (by have := mem_range.mp hi; omega)
  rw [← mul_sum] at hsum
  have htel : ∑ i ∈ range b, iterShift f i 1 = dd f b - dd f 0 := by
    simp only [iter_one_eq]
    exact sum_range_sub (dd f) b
  have hlow : (b : ℝ) * dd f 0 * (dd f (b + 1) - dd f b) ≤
      ∑ i ∈ range b, dd f i * (dd f (b + 1) - dd f b) := by
    have e : (b : ℝ) * dd f 0 * (dd f (b + 1) - dd f b) =
        ∑ i ∈ range b, dd f 0 * (dd f (b + 1) - dd f b) := by
      rw [sum_const, card_range, nsmul_eq_mul]; ring
    rw [e]
    exact sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (dd_mono_of hf (Nat.zero_le i)) hFnn
  rw [htel] at hsum
  linarith

/-- Paper (8.9), second form: `A·X' ≥ (a-2)·D·F` with `a = b+1`, `X' = d_b - d₁`, `D = d₁`. -/
theorem A2b {f : ℕ → ℝ} (hf : LCNZ f) (hf1 : 0 < f 1) {b : ℕ} (hb : 1 ≤ b) :
    ((b : ℝ) - 1) * dd f 1 * (dd f (b + 1) - dd f b) ≤ dd f (b + 1) * (dd f b - dd f 1) := by
  have hFnn : 0 ≤ dd f (b + 1) - dd f b := by
    rw [dd_succ_eq]; linarith [iterShift_nonneg hf b 1]
  have hsum : ∑ i ∈ range (b - 1), dd f (i + 1) * (dd f (b + 1) - dd f b) ≤
      ∑ i ∈ range (b - 1), dd f (b + 1) * iterShift f (i + 1) 1 :=
    sum_le_sum fun i hi => F_le hf hf1 (by have := mem_range.mp hi; omega)
  rw [← mul_sum] at hsum
  have htel : ∑ i ∈ range (b - 1), iterShift f (i + 1) 1 = dd f b - dd f 1 := by
    have h := sum_range_sub (fun i => dd f (i + 1)) (b - 1)
    rw [show b - 1 + 1 = b by omega] at h
    simp only [iter_one_eq]
    exact h
  have hlow : ((b : ℝ) - 1) * dd f 1 * (dd f (b + 1) - dd f b) ≤
      ∑ i ∈ range (b - 1), dd f (i + 1) * (dd f (b + 1) - dd f b) := by
    have e : ((b : ℝ) - 1) * dd f 1 * (dd f (b + 1) - dd f b) =
        ∑ i ∈ range (b - 1), dd f 1 * (dd f (b + 1) - dd f b) := by
      rw [sum_const, card_range, nsmul_eq_mul, show ((b - 1 : ℕ) : ℝ) = (b : ℝ) - 1 by
        rw [Nat.cast_sub hb, Nat.cast_one]]
      ring
    rw [e]
    exact sum_le_sum fun i _ => mul_le_mul_of_nonneg_right
      (dd_mono_of hf (show 1 ≤ i + 1 by omega)) hFnn
  rw [htel] at hsum
  linarith


/-- The Newton-profile bounds `F ≥ 0` and `d ≥ 0` in the form used below. -/
theorem F_nonneg_of {f : ℕ → ℝ} (hf : LCNZ f) (b : ℕ) : 0 ≤ dd f (b + 1) - dd f b := by
  rw [dd_succ_eq]; linarith [iterShift_nonneg hf b 1]

theorem choose_bound (b j : ℕ) (hj : 1 ≤ j) :
    2 * b.choose (j + 1) ≤ b.choose j * (b - 1) := by
  have h1 := Nat.choose_succ_right_eq b j
  have h2 : 2 * b.choose (j + 1) ≤ (j + 1) * b.choose (j + 1) := Nat.mul_le_mul_right _ (by omega)
  have h3 : b - j ≤ b - 1 := Nat.sub_le_sub_left hj b
  have h4 := Nat.mul_le_mul_left (b.choose j) h3
  calc 2 * b.choose (j + 1) ≤ (j + 1) * b.choose (j + 1) := h2
    _ = b.choose j * (b - j) := by rw [mul_comm, h1]
    _ ≤ b.choose j * (b - 1) := h4

theorem choose_bound_real (b j : ℕ) (hj : 1 ≤ j) (hb : 1 ≤ b) :
    2 * (b.choose (j + 1) : ℝ) ≤ (b.choose j : ℝ) * ((b : ℝ) - 1) := by
  have h := (Nat.cast_le (α := ℝ)).mpr (choose_bound b j hj)
  rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_sub hb, Nat.cast_one] at h
  push_cast at h
  linarith

/-- `E¹_m ≥ 0` for `m = j+1 ≥ 2` with `a = b+1`: `C(b,j) A (B-d₀) ≥ C(b,j+1) d₀ F`. -/
theorem E1_core {f : ℕ → ℝ} (hf : LCNZ f) (hf1 : 0 < f 1) {b j : ℕ} (hb : 2 ≤ b) (hj : 1 ≤ j) :
    (b.choose (j + 1) : ℝ) * dd f 0 * (dd f (b + 1) - dd f b) ≤
      (b.choose j : ℝ) * dd f (b + 1) * (dd f b - dd f 0) := by
  have hR := choose_bound_real b j hj (by omega)
  have hA := A2a hf hf1 b
  have hD : 0 ≤ dd f 0 * (dd f (b + 1) - dd f b) :=
    mul_nonneg (dd_nonneg_of hf 0) (F_nonneg_of hf b)
  have hCj : (0 : ℝ) ≤ b.choose j := Nat.cast_nonneg _
  have hCj1 : (0 : ℝ) ≤ b.choose (j + 1) := Nat.cast_nonneg _
  have k1 := mul_le_mul_of_nonneg_right hR hD
  have k2 := mul_le_mul_of_nonneg_left hA hCj
  have k3 : (0 : ℝ) ≤ (b.choose (j + 1) : ℝ) * (dd f 0 * (dd f (b + 1) - dd f b)) :=
    mul_nonneg hCj1 hD
  nlinarith

/-- `E²_m ≥ 0` for `m = j+1 ≥ 2`, `a = b+1`: `C(b,j+1) d₁ F ≤ C(b,j) A (B - d₁)`. -/
theorem E2_core {f : ℕ → ℝ} (hf : LCNZ f) (hf1 : 0 < f 1) {b j : ℕ} (hb : 2 ≤ b) (hj : 1 ≤ j) :
    (b.choose (j + 1) : ℝ) * dd f 1 * (dd f (b + 1) - dd f b) ≤
      (b.choose j : ℝ) * dd f (b + 1) * (dd f b - dd f 1) := by
  have hR := choose_bound_real b j hj (by omega)
  have hA := A2b hf hf1 (b := b) (by omega)
  have hD : 0 ≤ dd f 1 * (dd f (b + 1) - dd f b) :=
    mul_nonneg (dd_nonneg_of hf 1) (F_nonneg_of hf b)
  have hCj : (0 : ℝ) ≤ b.choose j := Nat.cast_nonneg _
  have hCj1 : (0 : ℝ) ≤ b.choose (j + 1) := Nat.cast_nonneg _
  have k1 := mul_le_mul_of_nonneg_right hR hD
  have k2 := mul_le_mul_of_nonneg_left hA hCj
  have k3 : (0 : ℝ) ≤ (b.choose (j + 1) : ℝ) * (dd f 1 * (dd f (b + 1) - dd f b)) :=
    mul_nonneg hCj1 hD
  nlinarith

/-- `β_k = C(a,k) d_{a}` for `k ≥ 2`: nonnegative. -/
theorem beta_ge2 {f : ℕ → ℝ} (hf : LCNZ f) (a k : ℕ) (hk : 2 ≤ k) : 0 ≤ betaC f a k := by
  have z0 : ((0 : ℕ).choose k : ℝ) = 0 := by rw [Nat.choose_eq_zero_of_lt (by omega)]; simp
  have z1 : ((1 : ℕ).choose k : ℝ) = 0 := by rw [Nat.choose_eq_zero_of_lt (by omega)]; simp
  have e : betaC f a k = (a.choose k : ℝ) * dd f a := by unfold betaC; rw [z0, z1]; ring
  rw [e]
  exact mul_nonneg (Nat.cast_nonneg _) (dd_nonneg_of hf a)

/-- `β'_k ≥ 0` for `k ≥ 2`, `a ≥ 3`. -/
theorem beta'_ge2 {f : ℕ → ℝ} (hf : LCNZ f) {a k : ℕ} (ha : 3 ≤ a) (hk : 2 ≤ k) :
    0 ≤ beta'C f a k := by
  have hA : 0 ≤ dd f a := dd_nonneg_of hf a
  rcases Nat.lt_or_ge k 3 with h3 | h3
  · have hk2 : k = 2 := by omega
    subst hk2
    have hc2 : ((a.choose 2 : ℕ) : ℝ) = (a : ℝ) * ((a : ℝ) - 1) / 2 := Nat.cast_choose_two ℝ a
    have hC1 : ((1 : ℕ).choose 2 : ℝ) = 0 := by rw [Nat.choose_eq_zero_of_lt (by omega)]; simp
    have hmono : dd f 2 ≤ dd f a := dd_mono_of hf (by omega)
    have ea : (3 : ℝ) ≤ a := by exact_mod_cast ha
    have e : beta'C f a 2 = ((a : ℝ) * ((a : ℝ) - 1) / 2) * dd f a - ((a : ℝ) - 1) * dd f 2 := by
      unfold beta'C
      rw [hc2, hC1]
      simp
    rw [e]
    have h1 : 0 ≤ ((a : ℝ) - 1) * ((a : ℝ) - 2) / 2 * dd f a := by
      apply mul_nonneg; apply div_nonneg (mul_nonneg (by linarith) (by linarith)) (by norm_num)
      exact hA
    have h2 : 0 ≤ ((a : ℝ) - 1) * (dd f a - dd f 2) := mul_nonneg (by linarith) (by linarith)
    nlinarith
  · have z2 : ((2 : ℕ).choose k : ℝ) = 0 := by rw [Nat.choose_eq_zero_of_lt (by omega)]; simp
    have z1 : ((1 : ℕ).choose k : ℝ) = 0 := by rw [Nat.choose_eq_zero_of_lt (by omega)]; simp
    have e : beta'C f a k = (a.choose k : ℝ) * dd f a := by unfold beta'C; rw [z2, z1]; ring
    rw [e]
    exact mul_nonneg (Nat.cast_nonneg _) hA

/-- Paper (ii): the coefficients `l_k ≥ 0` for `2 ≤ k ≤ a`, `a ≥ 3`. -/
theorem linC_ge2 {f : ℕ → ℝ} (hf : LCNZ f) (hf1 : 0 < f 1) {a k : ℕ} (ha : 3 ≤ a)
    (hk : 2 ≤ k) (hka : k ≤ a) : 0 ≤ linC f a k := by
  have hX : 0 ≤ dd f a - dd f 0 := sub_nonneg.2 (dd_mono_of hf (Nat.zero_le a))
  have hX' : 0 ≤ dd f (a - 1) - dd f 1 := sub_nonneg.2 (dd_mono_of hf (by omega))
  have hb := beta_ge2 hf a k hk
  have hb' := beta'_ge2 hf ha hk
  have e : linC f a k = (dd f a - dd f 0) * beta'C f a k + (dd f (a - 1) - dd f 1) * betaC f a k := by
    unfold linC
    rw [if_neg (show ¬ k ≤ 1 by omega)]
    ring
  rw [e]
  exact add_nonneg (mul_nonneg hX hb') (mul_nonneg hX' hb)

/-- Paper (ii): `M_{k,m} ≥ 0` for `k, m ≥ 2`, `a ≥ 3`. -/
theorem MC_ge2 {f : ℕ → ℝ} (hf : LCNZ f) (hf1 : 0 < f 1) {a k m : ℕ} (ha : 3 ≤ a)
    (hk : 2 ≤ k) (hm : 2 ≤ m) : 0 ≤ MC f a k m := by
  obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
  have hb2 : 2 ≤ b := by omega
  have hβ' : 0 ≤ beta'C f (b + 1) k := beta'_ge2 hf (by omega) hk
  have hβ : 0 ≤ betaC f (b + 1) k := beta_ge2 hf (b + 1) k hk
  have hz0 : ((0 : ℕ).choose (j + 1) : ℝ) = 0 := by rw [Nat.choose_zero_succ]; simp
  have hz1 : ((1 : ℕ).choose (j + 1) : ℝ) = 0 := by
    rw [Nat.choose_eq_zero_of_lt (by omega)]; simp
  have hP : ((b + 1).choose (j + 1) : ℝ) = (b.choose j : ℝ) + (b.choose (j + 1) : ℝ) := by
    rw [Nat.choose_succ_succ]; push_cast; ring
  have hE1 : 0 ≤ (dd f (b + 1) - dd f 0) * deltaC f (b + 1) (j + 1) -
      (dd f (b + 1) - dd f (b + 1 - 1)) * chiC f (b + 1) (j + 1) := by
    have hk1 := E1_core hf hf1 hb2 (show 1 ≤ j by omega)
    unfold deltaC chiC
    simp only [Nat.add_sub_cancel]
    rw [hz0, hP]
    have e : (dd f (b + 1) - dd f 0) * (((b.choose j : ℝ) + (b.choose (j + 1) : ℝ)) * dd f (b + 1) -
        (b.choose (j + 1) : ℝ) * dd f b) -
        (dd f (b + 1) - dd f b) * (((b.choose j : ℝ) + (b.choose (j + 1) : ℝ)) * dd f (b + 1) - 0 * dd f 0) =
        (b.choose j : ℝ) * dd f (b + 1) * (dd f b - dd f 0) -
          (b.choose (j + 1) : ℝ) * dd f 0 * (dd f (b + 1) - dd f b) := by ring
    rw [e]; linarith
  have hE2 : 0 ≤ (dd f (b + 1 - 1) - dd f 1) * deltaC f (b + 1) (j + 1) -
      (dd f (b + 1) - dd f (b + 1 - 1)) * chi'C f (b + 1) (j + 1) := by
    have hk1 := E2_core hf hf1 hb2 (show 1 ≤ j by omega)
    unfold deltaC chi'C
    simp only [Nat.add_sub_cancel]
    rw [hz1, hP]
    have e : (dd f b - dd f 1) * (((b.choose j : ℝ) + (b.choose (j + 1) : ℝ)) * dd f (b + 1) -
        (b.choose (j + 1) : ℝ) * dd f b) -
        (dd f (b + 1) - dd f b) * ((b.choose (j + 1) : ℝ) * dd f b - 0 * dd f 1) =
        (b.choose j : ℝ) * dd f (b + 1) * (dd f b - dd f 1) -
          (b.choose (j + 1) : ℝ) * dd f 1 * (dd f (b + 1) - dd f b) := by ring
    rw [e]; linarith
  unfold MC
  rw [if_neg (show ¬ k ≤ 1 by omega)]
  simp only [zero_mul, mul_zero, add_zero]
  exact add_nonneg (mul_nonneg hβ' hE1) (mul_nonneg hβ hE2)

/-- Paper (ii), the central sums with `i ≥ 2`: `S_{σ,i} ≥ 0`. -/
theorem central_ge2 {f : ℕ → ℝ} (hf : LCNZ f) (hf1 : 0 < f 1) {a : ℕ} (ha : 3 ≤ a)
    (σ i : ℕ) (hi : 2 ≤ i) (hσ : 2 * i ≤ σ) :
    0 ≤ ∑ k ∈ Icc i (σ - i), MC f a k (σ - k) := by
  refine sum_nonneg fun k hk => ?_
  rw [mem_Icc] at hk
  exact MC_ge2 hf hf1 ha (by omega) (by omega)

/-- Paper (8.9): `u₀ F ≤ u₁ B`, with `F = d_{b+1} - d_b`, `B = d_b`. -/
theorem A2c {f : ℕ → ℝ} (hf : LCNZ f) (b : ℕ) :
    dd f 0 * (dd f (b + 1) - dd f b) ≤ f 1 * dd f b := by
  rw [dd_zero_eq]
  have hstep : ∀ h : ℕ, f 0 * f (1 + h) ≤ f 1 * f h := by
    intro h
    rcases h with _ | k
    · simp only [Nat.add_zero, mul_comm]; exact le_rfl
    · have := hf.step (x := 0) (y := k) (Nat.zero_le k)
      rw [show 1 + (k + 1) = k + 2 by omega]
      exact this
  have hF : dd f (b + 1) - dd f b = ∑ h ∈ range (b + 1), (b.choose h : ℝ) * f (1 + h) := by
    rw [show dd f (b + 1) - dd f b = iterShift f b 1 by rw [dd_succ_eq]; ring, iterShift_eq]
  have hB : dd f b = ∑ h ∈ range (b + 1), (b.choose h : ℝ) * f h := by
    unfold dd; rw [iterShift_eq]; simp only [zero_add]
  rw [hF, hB, mul_sum, mul_sum]
  refine sum_le_sum fun h _ => ?_
  have := mul_le_mul_of_nonneg_left (hstep h) (Nat.cast_nonneg (α := ℝ) (b.choose h))
  linarith

/-- Paper (8.9): `F·D ≤ u₁ A`, with `D = d₁ = u₀ + u₁`, `A = d_{b+1}`. -/
theorem A2d {f : ℕ → ℝ} (hf : LCNZ f) (b : ℕ) :
    dd f 1 * (dd f (b + 1) - dd f b) ≤ f 1 * dd f (b + 1) := by
  have h := A2c hf b
  rw [dd_zero_eq] at h
  rw [dd_one_eq]
  have e : f 1 * dd f (b + 1) = f 1 * dd f b + f 1 * (dd f (b + 1) - dd f b) := by ring
  rw [e]
  nlinarith

end PhaseA

end Szkraw
