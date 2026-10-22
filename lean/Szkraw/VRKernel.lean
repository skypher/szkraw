import Szkraw.KernelPoly

/-!
# The kernel identity for varying ratios (paper, proof of Theorem 8.6)

In the stochastic normalization, `E_i = e_i R_i` with `e_{i+1}/e_i = a_i/c_{i+1}` satisfies
`x E_i = c_{i+1} E_{i+1} + b_i E_i + a_{i-1} E_{i-1}`, so the generator is
`ℒ_z = z⁻¹ c(θ) + b(θ) + z (1 - b(θ) - c(θ))`. Here `u` is the padded Newton sequence of `c` and
`v` that of `b`, so `dd u = c` and `dd v = b`. This file proves the analogue of `kernel_star`:
a solution of the kernel recurrence of Theorem 8.6 with the support property gives a coefficient
array with `ℒ_z L = ℒ_w L`. The recurrence holds for every array.
-/

namespace Szkraw

open MvPolynomial Finset

/-! ### The operators -/

/-- The coefficient of `z^m w^n` in `ℒ_z F`, `ℒ_z = z⁻¹ c(θ) + b(θ) + z (1 - b(θ) - c(θ))`. -/
noncomputable def LzV (c b : ℕ → ℝ) (F : ℕ → ℕ → ℝ) (m n : ℕ) : ℝ :=
  c (m + 1) * F (m + 1) n + b m * F m n +
    (if 1 ≤ m then (1 - b (m - 1) - c (m - 1)) * F (m - 1) n else 0)

/-- The coefficient of `z^m w^n` in `ℒ_w F`. -/
noncomputable def LwV (c b : ℕ → ℝ) (F : ℕ → ℕ → ℝ) (m n : ℕ) : ℝ :=
  c (n + 1) * F m (n + 1) + b n * F m n +
    (if 1 ≤ n then (1 - b (n - 1) - c (n - 1)) * F m (n - 1) else 0)

variable (u v : ℕ → ℝ)

/-- `ℒ_z (S^a Z^r)`. -/
noncomputable def LzImgV (r a : ℕ) : P2 :=
  ∑ i ∈ range (a + 1), C (Szkraw.iterShift u r i * (a.choose i : ℝ)) *
      (zinv r a i - mono (i + 1) 0 (a - i) r) +
    ∑ i ∈ range (a + 1), C (Szkraw.iterShift v r i * (a.choose i : ℝ)) *
      (mono i 0 (a - i) r - mono (i + 1) 0 (a - i) r) + mono 1 0 a r

/-- `ℒ_w (S^a Z^r)`. -/
noncomputable def LwImgV (r a : ℕ) : P2 :=
  ∑ i ∈ range (a + 1), C (Szkraw.iterShift u r i * (a.choose i : ℝ)) *
      (winv r a i - mono 0 (i + 1) (a - i) r) +
    ∑ i ∈ range (a + 1), C (Szkraw.iterShift v r i * (a.choose i : ℝ)) *
      (mono 0 i (a - i) r - mono 0 (i + 1) (a - i) r) + mono 0 1 a r

theorem cf_LzImgV (r a m n : ℕ) :
    cf (LzImgV u v r a) m n =
      (∑ i ∈ range (a + 1), Szkraw.iterShift u r i * (a.choose i : ℝ) * cf (zinv r a i) m n -
        ∑ i ∈ range (a + 1), Szkraw.iterShift u r i * (a.choose i : ℝ) * Ecf (i + 1) 0 (a - i) r m n) +
      (∑ i ∈ range (a + 1), Szkraw.iterShift v r i * (a.choose i : ℝ) * Ecf i 0 (a - i) r m n -
        ∑ i ∈ range (a + 1), Szkraw.iterShift v r i * (a.choose i : ℝ) * Ecf (i + 1) 0 (a - i) r m n) +
      Ecf 1 0 a r m n := by
  unfold LzImgV
  rw [cf_add, cf_add, cf_sum, cf_sum, cf_mono', ← sum_sub_distrib, ← sum_sub_distrib]
  congr 2
  · apply sum_congr rfl; intro i _
    rw [cf_C_mul, cf_sub, cf_mono']; ring
  · apply sum_congr rfl; intro i _
    rw [cf_C_mul, cf_sub, cf_mono', cf_mono']; ring

theorem cf_LwImgV (r a m n : ℕ) :
    cf (LwImgV u v r a) m n =
      (∑ i ∈ range (a + 1), Szkraw.iterShift u r i * (a.choose i : ℝ) * cf (winv r a i) m n -
        ∑ i ∈ range (a + 1), Szkraw.iterShift u r i * (a.choose i : ℝ) * Ecf 0 (i + 1) (a - i) r m n) +
      (∑ i ∈ range (a + 1), Szkraw.iterShift v r i * (a.choose i : ℝ) * Ecf 0 i (a - i) r m n -
        ∑ i ∈ range (a + 1), Szkraw.iterShift v r i * (a.choose i : ℝ) * Ecf 0 (i + 1) (a - i) r m n) +
      Ecf 0 1 a r m n := by
  unfold LwImgV
  rw [cf_add, cf_add, cf_sum, cf_sum, cf_mono', ← sum_sub_distrib, ← sum_sub_distrib]
  congr 2
  · apply sum_congr rfl; intro i _
    rw [cf_C_mul, cf_sub, cf_mono']; ring
  · apply sum_congr rfl; intro i _
    rw [cf_C_mul, cf_sub, cf_mono', cf_mono']; ring

/-- The `ℒ_z` image of `S^a Z^r`, coefficientwise. Needs `u 0 = 0` (so `c_0 = 0`). -/
theorem LzV_mono (hu0 : u 0 = 0) (r a m n : ℕ) :
    LzV (dd u) (dd v) (fun m n => Ecf 0 0 a r m n) m n = cf (LzImgV u v r a) m n := by
  have h1 : ∑ i ∈ range (a + 1), Szkraw.iterShift u r i * (a.choose i : ℝ) * cf (zinv r a i) m n =
      dd u (m + 1) * Ecf 0 0 a r (m + 1) n := by
    rw [← theta_z]
    apply sum_congr rfl
    intro i _
    unfold zinv
    by_cases hi : i = 0
    · subst hi
      rw [if_pos rfl, cf_mono']
      rcases Nat.eq_zero_or_pos r with hr | hr
      · subst hr
        have : Szkraw.iterShift u 0 0 = 0 := hu0
        rw [this]; ring
      · obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
        rw [Nat.add_sub_cancel, Ecf_zero_one, Nat.sub_zero]
    · rw [if_neg hi, cf_mono']
      obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
      rw [Ecf_succ_left, if_pos (by omega), Nat.add_sub_cancel, Nat.add_sub_cancel]
  have h3 : ∀ w : ℕ → ℝ,
      ∑ i ∈ range (a + 1), Szkraw.iterShift w r i * (a.choose i : ℝ) * Ecf (i + 1) 0 (a - i) r m n =
        if 1 ≤ m then dd w (m - 1) * Ecf 0 0 a r (m - 1) n else 0 := by
    intro w
    simp_rw [Ecf_succ_left]
    split_ifs
    · exact theta_z w a r (m - 1) n
    · simp
  rw [cf_LzImgV, h1, h3 u, h3 v, theta_z v a r m n, Ecf_succ_left]
  unfold LzV
  split_ifs <;> ring

theorem LwV_mono (hu0 : u 0 = 0) (r a m n : ℕ) :
    LwV (dd u) (dd v) (fun m n => Ecf 0 0 a r m n) m n = cf (LwImgV u v r a) m n := by
  have hz := LzV_mono u v hu0 r a n m
  have hs : (fun m n => Ecf 0 0 a r n m) = (fun m n => Ecf 0 0 a r m n) := by
    funext m n; rw [Ecf_swap]
  have hL : LwV (dd u) (dd v) (fun m n => Ecf 0 0 a r m n) m n =
      LzV (dd u) (dd v) (fun m n => Ecf 0 0 a r n m) n m := rfl
  rw [hL, hs, hz, cf_LzImgV, cf_LwImgV]
  simp_rw [cf_winv_swap]
  have e : ∀ (w : ℕ → ℝ) (s : ℕ), ∑ i ∈ range (a + 1), Szkraw.iterShift w r i * (a.choose i : ℝ) *
      Ecf (i + s) 0 (a - i) r n m =
      ∑ i ∈ range (a + 1), Szkraw.iterShift w r i * (a.choose i : ℝ) * Ecf 0 (i + s) (a - i) r m n :=
    fun w s => sum_congr rfl (fun i _ => by rw [Ecf_swap])
  have e0 := e v 0
  have e1u := e u 1
  have e1v := e v 1
  simp only [add_zero] at e0
  rw [e0, e1u, e1v, Ecf_swap 1 0 a r n m]

/-! ### The symmetric-side image `M = (ℒ_z - ℒ_w)/(z - w)` -/

/-- The `c`-part of term `i` (with `X 0 = S`, `X 1 = Z`). -/
noncomputable def McT (r a i : ℕ) : P2 :=
  (if i = 0 then -(X 0 ^ a * X 1 ^ (r - 1)) else if i = 1 then 0 else X 0 ^ (a - i) * X 1 ^ r * hh (i - 2)) -
    X 0 ^ (a - i) * X 1 ^ r * hh i

/-- The `b`-part of term `i`. -/
noncomputable def MbT (r a i : ℕ) : P2 :=
  (if i = 0 then 0 else X 0 ^ (a - i) * X 1 ^ r * hh (i - 1)) - X 0 ^ (a - i) * X 1 ^ r * hh i

/-- `M(S^a Z^r)`. -/
noncomputable def MuV (r a : ℕ) : P2 :=
  X 0 ^ a * X 1 ^ r + ∑ i ∈ range (a + 1), C (Szkraw.iterShift u r i * (a.choose i : ℝ)) * McT r a i +
    ∑ i ∈ range (a + 1), C (Szkraw.iterShift v r i * (a.choose i : ℝ)) * MbT r a i

theorem McT_spec (r a i : ℕ) :
    (X 0 - X 1) * ι (McT r a i) =
      (zinv r a i - mono (i + 1) 0 (a - i) r) - (winv r a i - mono 0 (i + 1) (a - i) r) := by
  unfold McT zinv winv mono
  by_cases h0 : i = 0
  · subst h0
    simp only [if_true, map_sub, map_neg, map_mul, map_pow, ι_X0, ι_X1, hh_zero, map_one, Nat.sub_zero]
    ring
  by_cases h1 : i = 1
  · subst h1
    simp only [if_neg (show (1 : ℕ) ≠ 0 by omega), if_true, map_sub, map_mul, map_pow,
      ι_X0, ι_X1, map_zero, Nat.sub_self, hh_one]
    ring
  obtain ⟨k, rfl⟩ : ∃ k, i = k + 2 := ⟨i - 2, by omega⟩
  have e1 : k + 2 - 2 = k := by omega
  have e2 : k + 2 - 1 = k + 1 := by omega
  simp only [show k + 2 ≠ 0 by omega, show k + 2 ≠ 1 by omega, if_false, map_sub,
    map_mul, map_pow, ι_X0, ι_X1, e1, e2]
  have s0 := hh_spec k
  have s2 := hh_spec (k + 2)
  linear_combination ((X 0 + X 1) ^ (a - (k + 2)) * (X 0 * X 1) ^ r) * s0 -
    ((X 0 + X 1) ^ (a - (k + 2)) * (X 0 * X 1) ^ r) * s2

theorem MbT_spec (r a i : ℕ) :
    (X 0 - X 1) * ι (MbT r a i) =
      (mono i 0 (a - i) r - mono (i + 1) 0 (a - i) r) - (mono 0 i (a - i) r - mono 0 (i + 1) (a - i) r) := by
  unfold MbT mono
  by_cases h0 : i = 0
  · subst h0
    simp only [if_true, map_sub, map_mul, map_pow, ι_X0, ι_X1, hh_zero, map_one, map_zero, Nat.sub_zero]
    ring
  obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
  have e1 : k + 1 - 1 = k := by omega
  simp only [show k + 1 ≠ 0 by omega, if_false, map_sub, map_mul, map_pow, ι_X0, ι_X1, e1]
  have s0 := hh_spec k
  have s1 := hh_spec (k + 1)
  linear_combination ((X 0 + X 1) ^ (a - (k + 1)) * (X 0 * X 1) ^ r) * s0 -
    ((X 0 + X 1) ^ (a - (k + 1)) * (X 0 * X 1) ^ r) * s1

/-- `ℒ_z(S^aZ^r) - ℒ_w(S^aZ^r) = (z - w) M(S^aZ^r)`. -/
theorem image_diffV (r a : ℕ) :
    LzImgV u v r a - LwImgV u v r a = (X 0 - X 1) * ι (MuV u v r a) := by
  unfold LzImgV LwImgV MuV
  rw [map_add, map_add, map_sum ι, map_sum ι, mul_add, mul_add, mul_sum, mul_sum]
  have hT : mono 1 0 a r - mono 0 1 a r = (X 0 - X 1) * ι (X 0 ^ a * X 1 ^ r) := by
    unfold mono; simp only [map_mul, map_pow, ι_X0, ι_X1]; ring
  have hc : ∀ i ∈ range (a + 1),
      C (Szkraw.iterShift u r i * (a.choose i : ℝ)) * (zinv r a i - mono (i + 1) 0 (a - i) r) -
        C (Szkraw.iterShift u r i * (a.choose i : ℝ)) * (winv r a i - mono 0 (i + 1) (a - i) r) =
      (X 0 - X 1) * ι (C (Szkraw.iterShift u r i * (a.choose i : ℝ)) * McT r a i) := by
    intro i _
    rw [map_mul ι, ι_C, mul_left_comm, McT_spec]; ring
  have hb : ∀ i ∈ range (a + 1),
      C (Szkraw.iterShift v r i * (a.choose i : ℝ)) * (mono i 0 (a - i) r - mono (i + 1) 0 (a - i) r) -
        C (Szkraw.iterShift v r i * (a.choose i : ℝ)) * (mono 0 i (a - i) r - mono 0 (i + 1) (a - i) r) =
      (X 0 - X 1) * ι (C (Szkraw.iterShift v r i * (a.choose i : ℝ)) * MbT r a i) := by
    intro i _
    rw [map_mul ι, ι_C, mul_left_comm, MbT_spec]; ring
  rw [← sum_congr rfl hc, ← sum_congr rfl hb, sum_sub_distrib, sum_sub_distrib, ← hT]
  ring

/-! ### Coefficients of `M(S^a Z^r)` -/

theorem cf_McT (r a i x y : ℕ) :
    cf (McT r a i) x y =
      (if i = 0 then -(if a = x ∧ r - 1 = y then 1 else 0) else 0) + Gi r a 2 i x y - Gi r a 0 i x y := by
  unfold McT Gi
  by_cases h0 : i = 0
  · subst h0
    simp only [if_true, cf_sub, cf_neg, cf_XX, Nat.sub_zero, Nat.zero_le,
      show ¬(2 ≤ 0) by omega, if_false]
    ring
  by_cases h1 : i = 1
  · subst h1
    simp only [show (1 : ℕ) ≠ 0 by omega, if_true, if_false, cf_sub, cf_zero,
      Nat.zero_le, show ¬(2 ≤ 1) by omega, Nat.sub_zero]
    ring
  · rw [if_neg h0, if_neg h0, if_neg h1, if_pos (by omega), if_pos (by omega), cf_sub, Nat.sub_zero]
    ring

theorem cf_MbT (r a i x y : ℕ) : cf (MbT r a i) x y = Gi r a 1 i x y - Gi r a 0 i x y := by
  unfold MbT Gi
  by_cases h0 : i = 0
  · subst h0
    simp only [if_true, cf_sub, cf_zero, Nat.zero_le, show ¬(1 ≤ 0) by omega, if_false, Nat.sub_zero]
  · rw [if_neg h0, if_pos (by omega), if_pos (by omega), cf_sub, Nat.sub_zero]

theorem cf_MuV (r a x y : ℕ) :
    cf (MuV u v r a) x y =
      (if a = x ∧ r = y then 1 else 0) - Szkraw.iterShift u r 0 * (if a = x ∧ r - 1 = y then 1 else 0) +
      (if r ≤ y ∧ x + 2 * (y - r) + 2 = a then
        (-1 : ℝ) ^ (y - r) * Wt u (2 * (y - r) + 2) (y - r) r a else 0) -
      (if r ≤ y ∧ x + 2 * (y - r) + 0 = a then
        (-1 : ℝ) ^ (y - r) * Wt u (2 * (y - r) + 0) (y - r) r a else 0) +
      (if r ≤ y ∧ x + 2 * (y - r) + 1 = a then
        (-1 : ℝ) ^ (y - r) * Wt v (2 * (y - r) + 1) (y - r) r a else 0) -
      (if r ≤ y ∧ x + 2 * (y - r) + 0 = a then
        (-1 : ℝ) ^ (y - r) * Wt v (2 * (y - r) + 0) (y - r) r a else 0) := by
  unfold MuV
  rw [cf_add, cf_add, cf_XX, cf_sum, cf_sum]
  simp only [cf_C_mul, cf_McT, cf_MbT, mul_add, mul_sub, sum_add_distrib, sum_sub_distrib]
  rw [← sum_Gi u r a 2 x y, ← sum_Gi u r a 0 x y, ← sum_Gi v r a 1 x y, ← sum_Gi v r a 0 x y]
  have h0 : ∑ i ∈ range (a + 1), Szkraw.iterShift u r i * (a.choose i : ℝ) *
      (if i = 0 then -(if a = x ∧ r - 1 = y then (1 : ℝ) else 0) else 0) =
      -(Szkraw.iterShift u r 0 * (if a = x ∧ r - 1 = y then 1 else 0)) := by
    rw [Finset.sum_eq_single 0]
    · simp
    · intro i _ hi; rw [if_neg hi, mul_zero]
    · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h
  rw [h0]
  ring

/-! ### The kernel recurrence of Theorem 8.6 and the coefficient relation -/

variable (ω : ℕ → ℕ → ℝ)

/-- `A`-moves (from `b`), `B`-moves (from `c`), `C`-moves (from `d = b + c`) into `(ℓ+1, a)`. -/
noncomputable def moveAV (j ℓ a : ℕ) : ℝ := Wt v (2 * j + 1) j (ℓ - j) (a + 2 * j + 1) * ω (ℓ - j) (a + 2 * j + 1)
noncomputable def moveBV (j ℓ a : ℕ) : ℝ := Wt u (2 * j + 2) j (ℓ - j) (a + 2 * j + 2) * ω (ℓ - j) (a + 2 * j + 2)
noncomputable def moveCV (j ℓ a : ℕ) : ℝ :=
  if j < ℓ then (Wt u (2 * j + 2) (j + 1) (ℓ - j - 1) (a + 2 * j + 2) +
    Wt v (2 * j + 2) (j + 1) (ℓ - j - 1) (a + 2 * j + 2)) * ω (ℓ - j - 1) (a + 2 * j + 2) else 0

noncomputable def grpV (j ℓ a : ℕ) : ℝ := moveAV v ω j ℓ a + moveBV u ω j ℓ a + moveCV u v ω j ℓ a

/-- The kernel recurrence of Theorem 8.6. -/
def KernelRecV : Prop :=
  ∀ ℓ a, dd u (ℓ + 1) * ω (ℓ + 1) a =
    (1 - dd v (ℓ + a) - dd u (ℓ + a)) * ω ℓ a + ∑ j ∈ range (ℓ + 1), (-1 : ℝ) ^ j * grpV u v ω j ℓ a

variable {u v ω}

theorem Wt_zero_zero' (w : ℕ → ℝ) (r a : ℕ) : Wt w 0 0 r a = dd w (r + a) := by
  unfold Wt
  rw [dd_split]
  apply sum_congr rfl
  intro n _
  simp [mul_comm]

/-- The recurrence makes `Σ ω_{r,a} M(S^a Z^r)` vanish. -/
theorem kernel_poly_zeroV (hu0 : u 0 = 0) (N : ℕ) (hrec : KernelRecV u v ω)
    (hsupp : ∀ r a, N < r + a → ω r a = 0) :
    ∑ r ∈ range (N + 1), ∑ a ∈ range (N + 1), C (ω r a) * MuV u v r a = 0 := by
  apply P2_ext; intro x y
  rw [cf_zero, cf_sum]
  simp only [cf_sum, cf_C_mul, cf_MuV]
  have hf0 : ∀ r a, ω r a * (Szkraw.iterShift u r 0 * if a = x ∧ r - 1 = y then 1 else 0) =
      ω r a * (Szkraw.iterShift u (y + 1) 0 * if a = x ∧ r = y + 1 then 1 else 0) := by
    intro r a
    by_cases hr : r = 0
    · subst hr
      have : Szkraw.iterShift u 0 0 = 0 := hu0
      rw [this, if_neg (show ¬(a = x ∧ (0 : ℕ) = y + 1) by omega)]; ring
    · by_cases h : a = x ∧ r = y + 1
      · rw [if_pos ⟨h.1, by omega⟩, if_pos h, h.2]
      · rw [if_neg (by omega), if_neg h]; ring
  simp only [mul_add, mul_sub, sum_add_distrib, sum_sub_distrib]
  simp only [hf0]
  have hone : ∀ r a, ω r a * (if a = x ∧ r = y then (1 : ℝ) else 0) =
      ω r a * ((1 : ℝ) * if a = x ∧ r = y then 1 else 0) := fun r a => by ring
  simp only [hone]
  rw [box_point N ω hsupp, box_point N ω hsupp]
  rw [box_line N ω hsupp _ x y 2, box_line N ω hsupp _ x y 1, box_line N ω hsupp _ x y 0,
    box_line N ω hsupp (fun r a => (-1 : ℝ) ^ (y - r) * Wt v (2 * (y - r) + 0) (y - r) r a) x y 0]
  have norm : ∀ (w : ℕ → ℝ) (s : ℕ), ∑ l ∈ range (y + 1), ω (y - l) (x + 2 * l + s) *
      ((-1 : ℝ) ^ (y - (y - l)) * Wt w (2 * (y - (y - l)) + s) (y - (y - l)) (y - l) (x + 2 * l + s)) =
      ∑ l ∈ range (y + 1), (-1 : ℝ) ^ l * (Wt w (2 * l + s) l (y - l) (x + 2 * l + s) *
        ω (y - l) (x + 2 * l + s)) := by
    intro w s
    apply sum_congr rfl; intro l hl; rw [Finset.mem_range] at hl
    have e : y - (y - l) = l := by omega
    rw [e]; ring
  rw [norm u 2, norm u 0, norm v 1, norm v 0]
  have hr := hrec y x
  unfold grpV moveAV moveBV moveCV at hr
  simp only [mul_add, sum_add_distrib] at hr
  -- C-moves against the shifted zero-parts of `u` and `v`
  have hC : ∑ j ∈ range (y + 1), (-1 : ℝ) ^ j * (if j < y then
        (Wt u (2 * j + 2) (j + 1) (y - j - 1) (x + 2 * j + 2) + Wt v (2 * j + 2) (j + 1) (y - j - 1) (x + 2 * j + 2)) *
          ω (y - j - 1) (x + 2 * j + 2) else 0) =
      -(∑ l ∈ range (y + 1), (-1 : ℝ) ^ l * (Wt u (2 * l + 0) l (y - l) (x + 2 * l + 0) *
        ω (y - l) (x + 2 * l + 0))) -
      (∑ l ∈ range (y + 1), (-1 : ℝ) ^ l * (Wt v (2 * l + 0) l (y - l) (x + 2 * l + 0) *
        ω (y - l) (x + 2 * l + 0))) + (dd u (y + x) + dd v (y + x)) * ω y x := by
    rw [Finset.sum_range_succ, if_neg (lt_irrefl y), mul_zero, add_zero,
      Finset.sum_range_succ' (fun l => (-1 : ℝ) ^ l * (Wt u (2 * l + 0) l (y - l) (x + 2 * l + 0) *
        ω (y - l) (x + 2 * l + 0))),
      Finset.sum_range_succ' (fun l => (-1 : ℝ) ^ l * (Wt v (2 * l + 0) l (y - l) (x + 2 * l + 0) *
        ω (y - l) (x + 2 * l + 0)))]
    simp only [pow_zero, one_mul, mul_zero, add_zero, Nat.sub_zero]
    rw [Wt_zero_zero', Wt_zero_zero']
    have hs : ∀ j ∈ range y, (-1 : ℝ) ^ j * (if j < y then
        (Wt u (2 * j + 2) (j + 1) (y - j - 1) (x + 2 * j + 2) + Wt v (2 * j + 2) (j + 1) (y - j - 1) (x + 2 * j + 2)) *
          ω (y - j - 1) (x + 2 * j + 2) else 0) =
        -((-1 : ℝ) ^ (j + 1) * (Wt u (2 * (j + 1)) (j + 1) (y - (j + 1)) (x + 2 * (j + 1)) * ω (y - (j + 1)) (x + 2 * (j + 1))))
        - ((-1 : ℝ) ^ (j + 1) * (Wt v (2 * (j + 1)) (j + 1) (y - (j + 1)) (x + 2 * (j + 1)) * ω (y - (j + 1)) (x + 2 * (j + 1)))) := by
      intro j hj; rw [Finset.mem_range] at hj
      rw [if_pos hj]
      have e1 : 2 * (j + 1) = 2 * j + 2 := by ring
      have e2 : y - (j + 1) = y - j - 1 := by omega
      have e3 : x + (2 * j + 2) = x + 2 * j + 2 := by ring
      rw [e1, e2, e3, pow_succ]; ring
    rw [sum_congr rfl hs, sum_sub_distrib, sum_neg_distrib]
    ring
  rw [hC] at hr
  unfold dd at hr
  linear_combination -hr

/-- The coefficient relation `ℒ_z L = ℒ_w L` for a solution of the kernel recurrence of
Theorem 8.6 with the support property. -/
theorem kernel_starV (hu0 : u 0 = 0) (N : ℕ) (hrec : KernelRecV u v ω)
    (hsupp : ∀ r a, N < r + a → ω r a = 0) (m n : ℕ) :
    LzV (dd u) (dd v) (Lker N ω) m n = LwV (dd u) (dd v) (Lker N ω) m n := by
  have lin_z : ∀ (s : Finset ℕ) (F : ℕ → ℕ → ℕ → ℝ),
      LzV (dd u) (dd v) (fun m n => ∑ x ∈ s, F x m n) m n = ∑ x ∈ s, LzV (dd u) (dd v) (F x) m n := by
    intro s F; unfold LzV; split_ifs <;> simp [mul_sum, sum_add_distrib]
  have lin_w : ∀ (s : Finset ℕ) (F : ℕ → ℕ → ℕ → ℝ),
      LwV (dd u) (dd v) (fun m n => ∑ x ∈ s, F x m n) m n = ∑ x ∈ s, LwV (dd u) (dd v) (F x) m n := by
    intro s F; unfold LwV; split_ifs <;> simp [mul_sum, sum_add_distrib]
  have sm_z : ∀ (c : ℝ) (F : ℕ → ℕ → ℝ), LzV (dd u) (dd v) (fun m n => c * F m n) m n = c * LzV (dd u) (dd v) F m n := by
    intro c F; unfold LzV; split_ifs <;> ring
  have sm_w : ∀ (c : ℝ) (F : ℕ → ℕ → ℝ), LwV (dd u) (dd v) (fun m n => c * F m n) m n = c * LwV (dd u) (dd v) F m n := by
    intro c F; unfold LwV; split_ifs <;> ring
  have hz : LzV (dd u) (dd v) (Lker N ω) m n = ∑ r ∈ range (N + 1), ∑ a ∈ range (N + 1),
      ω r a * LzV (dd u) (dd v) (fun m n => Ecf 0 0 a r m n) m n := by
    unfold Lker
    rw [lin_z]; apply sum_congr rfl; intro r _
    rw [lin_z]; apply sum_congr rfl; intro a _
    rw [sm_z]
  have hw : LwV (dd u) (dd v) (Lker N ω) m n = ∑ r ∈ range (N + 1), ∑ a ∈ range (N + 1),
      ω r a * LwV (dd u) (dd v) (fun m n => Ecf 0 0 a r m n) m n := by
    unfold Lker
    rw [lin_w]; apply sum_congr rfl; intro r _
    rw [lin_w]; apply sum_congr rfl; intro a _
    rw [sm_w]
  rw [← sub_eq_zero, hz, hw, ← sum_sub_distrib]
  have hpoly := congrArg (fun p => cf ((X 0 - X 1) * ι p) m n) (kernel_poly_zeroV hu0 N hrec hsupp)
  simp only [map_zero, mul_zero, cf_zero, map_sum, mul_sum, cf_sum, map_mul ι, ι_C] at hpoly
  rw [← hpoly]
  apply sum_congr rfl; intro r _
  rw [← sum_sub_distrib]
  apply sum_congr rfl; intro a _
  rw [← mul_sub, LzV_mono u v hu0, LwV_mono u v hu0, ← cf_sub, image_diffV, mul_left_comm, cf_C_mul]

end Szkraw
