import Szkraw.ParitySplit
import Szkraw.Stability
import Szkraw.KrawtchoukMargin
import Szkraw.GeometricApplications

/-!
# Lemma 7.4 (Margin for the quadratic system), Theorem 7.6 and Corollary 7.7

The components of Szwarc's array are Krawtchouk arrays: the even one on `N + 1` points and the
odd one on `N` points, both with parameter `r = p_0/(1-p_0)`. Their triangle margins
(Lemma 6.x, `kraw_triangle_margin`) give the margin of the symmetric array through the
decomposition formulas, the weights `π` handling the coefficients with two odd indices.
-/

namespace Szkraw

open Finset

section components

variable {N : ℕ} (hN : 1 ≤ N) {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
include hN hp hp1

/-- The even component of Szwarc's array has the product coefficients of `K_N(r)`. -/
theorem szwarc_even_kraw (m : ℕ) (hm : m ≤ N + 1) :
    productMatrix (evenComp (szwarcCoefficients N p)) m =
      productMatrix (krawCoefficients N (p / (1 - p))) m := by
  set v := szwarcCoefficients N p
  have hv := szwarc_admissible N hN p hp hp1
  have hb : ∀ i, i ≤ 2 * N → v.b i = 0 := fun _ _ => rfl
  have hps := szwarc_parity N hN p
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hp' : 1 - p ≠ 0 := by linarith
  have hd : ∀ n, v.c (2 * n) = (n : ℝ) / N := by
    intro n
    show (if 2 * n % 2 = 0 then ((2 * n / 2 : ℕ) : ℝ) / N else p) = _
    rw [if_pos (by omega), show 2 * n / 2 = n by omega]
  apply product_congr _ _ _ _ _ m hm
  · intro i hi
    show (evenRaw v).a i / (evenRaw v).a 0 = ((N : ℝ) - i) / N
    have hraw : ∀ n, n ≤ N → (evenRaw v).a n = (1 - (n : ℝ) / N) * (1 - p) := by
      intro n hn
      show v.a (2 * n) * v.a (2 * n + 1) = _
      rw [ps_a_even v hv hb n hn, hd]
      rcases Nat.lt_or_ge n N with h | h
      · rw [ps_a_odd v hv hb hps n (by omega)]
      · rw [show n = N by omega]; field_simp; ring
    rw [hraw i hi, hraw 0 (by omega)]
    simp only [Nat.cast_zero, zero_div, sub_zero, one_mul]
    field_simp
  · intro i hi
    rw [(ps_evenComp v hv hb hps i hi).1, hd]
    show _ = (1 - p / (1 - p)) * i / N
    field_simp; ring
  · intro i hi
    rw [(ps_evenComp v hv hb hps i hi).2, hd]
    show _ = p / (1 - p) * i / N
    field_simp

/-- The odd component of Szwarc's array (`N ≥ 2`) has the product coefficients of `K_{N-1}(r)`. -/
theorem szwarc_odd_kraw (hN2 : 2 ≤ N) (m : ℕ) (hm : m ≤ N - 1 + 1) :
    productMatrix (oddComp (szwarcCoefficients N p)) m =
      productMatrix (krawCoefficients (N - 1) (p / (1 - p))) m := by
  set v := szwarcCoefficients N p
  have hv := szwarc_admissible N hN p hp hp1
  have hb : ∀ i, i ≤ 2 * N → v.b i = 0 := fun _ _ => rfl
  have hps := szwarc_parity N hN p
  have hN' : (1 : ℝ) < N := by exact_mod_cast hN2
  have hp' : 1 - p ≠ 0 := by linarith
  have hcast : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by rw [Nat.cast_sub (by omega)]; simp
  have hd : ∀ n, v.c (2 * n) = (n : ℝ) / N := by
    intro n
    show (if 2 * n % 2 = 0 then ((2 * n / 2 : ℕ) : ℝ) / N else p) = _
    rw [if_pos (by omega), show 2 * n / 2 = n by omega]
  have hN1 : (N : ℝ) - 1 ≠ 0 := by linarith
  have hN0 : (N : ℝ) ≠ 0 := by linarith
  apply product_congr _ _ _ _ _ m hm
  · intro i hi
    show (oddRaw v).a i / (oddRaw v).a 0 = (((N - 1 : ℕ) : ℝ) - i) / ((N - 1 : ℕ) : ℝ)
    have hraw : ∀ n, n ≤ N - 1 → (oddRaw v).a n = (1 - p) * (1 - ((n : ℝ) + 1) / N) := by
      intro n hn
      show v.a (2 * n + 1) * v.a (2 * n + 2) = _
      rw [ps_a_odd v hv hb hps n (by omega), show 2 * n + 2 = 2 * (n + 1) by ring,
        ps_a_even v hv hb (n + 1) (by omega), hd]
      push_cast; ring
    rw [hraw i hi, hraw 0 (by omega), hcast]
    simp only [Nat.cast_zero, zero_add]
    have hden : (1 - p) * (1 - 1 / (N : ℝ)) ≠ 0 := by
      apply mul_ne_zero hp'
      have h1 : 1 / (N : ℝ) < 1 := (div_lt_one (by linarith)).mpr hN'
      exact ne_of_gt (by linarith)
    rw [div_eq_div_iff hden hN1]
    field_simp
    ring
  · intro i hi
    rw [(ps_oddComp v hv hb hps hN2 i hi).1, hd]
    rw [show v.c 2 = 1 / N by simpa using hd 1]
    show _ = (1 - p / (1 - p)) * i / ((N - 1 : ℕ) : ℝ)
    rw [hcast]
    field_simp
  · intro i hi
    rw [(ps_oddComp v hv hb hps hN2 i hi).2, hd]
    rw [show v.c 2 = 1 / N by simpa using hd 1]
    show _ = p / (1 - p) * i / ((N - 1 : ℕ) : ℝ)
    rw [hcast]
    field_simp

end components

/-! ### The weights `π` of Szwarc's array -/

section weights

variable {N : ℕ} {p : ℝ}

theorem szwarc_a_even (c : ℕ) : (szwarcCoefficients N p).a (2 * c) = ((N : ℝ) - c) / N := by
  show (if 2 * c % 2 = 0 then ((N : ℝ) - ((2 * c / 2 : ℕ) : ℝ)) / N else 1 - p) = _
  rw [if_pos (by omega), show 2 * c / 2 = c by omega]

theorem szwarc_c_even (c : ℕ) : (szwarcCoefficients N p).c (2 * c) = (c : ℝ) / N := by
  show (if 2 * c % 2 = 0 then ((2 * c / 2 : ℕ) : ℝ) / N else p) = _
  rw [if_pos (by omega), show 2 * c / 2 = c by omega]

theorem szwarc_a_odd (c : ℕ) : (szwarcCoefficients N p).a (2 * c + 1) = 1 - p := by
  show (if (2 * c + 1) % 2 = 0 then _ else 1 - p) = _; rw [if_neg (by omega)]

theorem szwarc_c_odd (c : ℕ) : (szwarcCoefficients N p).c (2 * c + 1) = p := by
  show (if (2 * c + 1) % 2 = 0 then _ else p) = _; rw [if_neg (by omega)]

/-- `π_{2c} = C(N,c) r^{-c}`. -/
theorem szwarc_piW_even (hp : 0 < p) (hp1 : p < 1) (hN : 1 ≤ N) : ∀ c, c ≤ N →
    piW (szwarcCoefficients N p) (2 * c) = (N.choose c : ℝ) / (p / (1 - p)) ^ c := by
  have hN0 : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hq : 1 - p ≠ 0 := by linarith
  intro c
  induction c with
  | zero => intro _; simp [piW]
  | succ c ih =>
    intro hc
    have h := ih (by omega)
    have e : piW (szwarcCoefficients N p) (2 * (c + 1)) = piW (szwarcCoefficients N p) (2 * c) *
        ((szwarcCoefficients N p).a (2 * c) / (szwarcCoefficients N p).c (2 * c + 1)) *
        ((szwarcCoefficients N p).a (2 * c + 1) / (szwarcCoefficients N p).c (2 * c + 1 + 1)) := by
      unfold piW
      rw [show 2 * (c + 1) = 2 * c + 1 + 1 by ring, prod_range_succ, prod_range_succ]
    rw [e, h, szwarc_a_even, szwarc_c_odd, szwarc_a_odd,
      show 2 * c + 1 + 1 = 2 * (c + 1) by ring, szwarc_c_even]
    have hch : ((N.choose (c + 1) : ℕ) : ℝ) * ((c : ℝ) + 1) = (N.choose c : ℝ) * ((N : ℝ) - c) := by
      have h0 := Nat.choose_succ_right_eq N c
      have h' : ((N.choose (c + 1) * (c + 1) : ℕ) : ℝ) = ((N.choose c * (N - c) : ℕ) : ℝ) := by rw [h0]
      push_cast [Nat.cast_sub (show c ≤ N by omega)] at h'
      linarith
    have hc1 : (c : ℝ) + 1 ≠ 0 := by positivity
    rw [pow_succ]
    field_simp
    push_cast
    linear_combination -hch

/-- `π_{2b+1} = C(N-1,b) r^{-b} / p_0`. -/
theorem szwarc_piW_odd (hp : 0 < p) (hp1 : p < 1) (hN : 1 ≤ N) (b : ℕ) (hb : b ≤ N - 1) :
    piW (szwarcCoefficients N p) (2 * b + 1) =
      ((N - 1).choose b : ℝ) / ((p / (1 - p)) ^ b * p) := by
  have hN0 : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hq : 1 - p ≠ 0 := by linarith
  have e : piW (szwarcCoefficients N p) (2 * b + 1) = piW (szwarcCoefficients N p) (2 * b) *
      ((szwarcCoefficients N p).a (2 * b) / (szwarcCoefficients N p).c (2 * b + 1)) := by
    unfold piW; rw [prod_range_succ]
  rw [e, szwarc_piW_even hp hp1 hN b (by omega), szwarc_a_even, szwarc_c_odd]
  have hch : (((N - 1).choose b : ℕ) : ℝ) * (N : ℝ) = (N.choose b : ℝ) * ((N : ℝ) - b) := by
    have := Nat.choose_mul_succ_eq (N - 1) b
    rw [show N - 1 + 1 = N by omega] at this
    rw [← Nat.cast_sub (by omega)]
    exact_mod_cast this
  field_simp
  linear_combination -hch

end weights

/-! ### Lemma 7.4 -/

theorem margin_ineq1 (N : ℕ) {r s : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) (hs : 0 ≤ s) :
    (r * s / 8) ^ N ≤ (s / 4) ^ N :=
  pow_le_pow_left₀ (by positivity) (by nlinarith) N

theorem margin_ineq2 (N : ℕ) (hN : 1 ≤ N) {r s : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) (hs : 0 ≤ s)
    (hs1 : s ≤ 1 / 2) : (r * s / 8) ^ N ≤ 1 / N * (s / 4) ^ (N - 1) := by
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  have h1 : (r * s / 8) ^ (M + 1) ≤ (s / 8) ^ (M + 1) := pow_le_pow_left₀ (by positivity) (by nlinarith) _
  have h2 : (s / 8) ^ (M + 1) = (s / 4) ^ M * ((s / 4) * (1 / 2) ^ (M + 1)) := by
    rw [show s / 8 = (s / 4) * (1 / 2) by ring, mul_pow, pow_succ]; ring
  have h3 : ((M + 1 : ℕ) : ℝ) < 2 ^ (M + 1) := by exact_mod_cast Nat.lt_two_pow_self
  have hM : (0 : ℝ) < ((M + 1 : ℕ) : ℝ) := by positivity
  have h5 : (1 / 2 : ℝ) ^ (M + 1) ≤ 1 / ((M + 1 : ℕ) : ℝ) := by
    rw [one_div_pow]; exact one_div_le_one_div_of_le hM h3.le
  have h6 : (s / 4) * (1 / 2 : ℝ) ^ (M + 1) ≤ (1 / 2 : ℝ) ^ (M + 1) := by
    have : 0 ≤ (1 / 2 : ℝ) ^ (M + 1) := by positivity
    nlinarith
  have h4 := h6.trans h5
  calc (r * s / 8) ^ (M + 1) ≤ (s / 8) ^ (M + 1) := h1
    _ = (s / 4) ^ M * ((s / 4) * (1 / 2) ^ (M + 1)) := h2
    _ ≤ (s / 4) ^ M * (1 / ((M + 1 : ℕ) : ℝ)) := mul_le_mul_of_nonneg_left h4 (by positivity)
    _ = _ := by ring

theorem margin_ineq3 (N : ℕ) (hN : 1 ≤ N) {r s p : ℝ} (hr : 0 < r) (_hr1 : r ≤ 1) (hs : 0 ≤ s)
    (hs1 : s ≤ 1) (hp : r / 2 ≤ p) :
    (r * s / 8) ^ N ≤ p * r ^ (N - 1) * (s / 4) ^ (N - 1) / 2 ^ (N - 1) := by
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  have e : r ^ M * (s / 4) ^ M / 2 ^ M = (r * s / 8) ^ M := by
    rw [← mul_pow, ← div_pow]; congr 1; ring
  calc (r * s / 8) ^ (M + 1) = (r * s / 8) ^ M * (r * s / 8) := pow_succ _ _
    _ ≤ (r * s / 8) ^ M * p := by
        apply mul_le_mul_of_nonneg_left _ (by positivity); nlinarith
    _ = _ := by rw [← e]; ring

section margin

variable {N : ℕ} (hN : 1 ≤ N) {p : ℝ} (hp : 0 < p) (hp2 : p < 1 / 2)
include hN hp hp2

/-- The odd component of Szwarc's array has nonnegative linearization. -/
theorem szwarc_odd_pos : MatrixPositivity (oddComp (szwarcCoefficients N p)) := by
  rcases Nat.lt_or_ge 1 N with hN2 | hN2
  · intro m hm i j
    rw [szwarc_odd_kraw hN hp (by linarith) (by omega) m (by omega)]
    exact kraw_matrix_positivity (N - 1) (by omega) _ (div_pos hp (by linarith))
      (by rw [div_le_one (by linarith)]; linarith) m hm i j
  · intro m hm i j
    have hm0 : m = 0 := by omega
    subst hm0
    show 0 ≤ (1 : Matrix (Fin (N - 1 + 1)) (Fin (N - 1 + 1)) ℝ) i j
    rw [Matrix.one_apply]; split_ifs <;> norm_num

/-- Odd-component margin: `ǧ(x,y;z) ≥ (s/4)^(N-1)` on its triangle. -/
theorem szwarc_odd_margin (col : Fin (N - 1 + 1)) (x y : ℕ) (hx : x ≤ N - 1) (hy : y ≤ N - 1)
    (ht : Triangle x y col.val) :
    (min (p / (1 - p)) (1 - p / (1 - p)) / 4) ^ (N - 1) ≤ Gk (oddRaw (szwarcCoefficients N p)) col x y := by
  have hr : 0 < p / (1 - p) := div_pos hp (by linarith)
  have hr1 : p / (1 - p) < 1 := by rw [div_lt_one (by linarith)]; linarith
  unfold Gk
  rw [dif_pos ⟨hx, hy⟩]
  rcases Nat.lt_or_ge 1 N with hN2 | hN2
  · rw [← product_normalize _ (oddRaw_a0 _ (szwarc_admissible N hN p hp (by linarith)) (by omega)).ne']
    show _ ≤ productMatrix (oddComp (szwarcCoefficients N p)) x ⟨y, by omega⟩ col
    rw [szwarc_odd_kraw hN hp (by linarith) (by omega) x (by omega)]
    exact kraw_triangle_margin (N - 1) (by omega) _ hr hr1 x ⟨y, by omega⟩ col hx ht
  · have hx0 : x = 0 := by omega
    subst hx0
    have h1 : (min (p / (1 - p)) (1 - p / (1 - p)) / 4) ^ (N - 1) = 1 := by
      rw [show N - 1 = 0 by omega, pow_zero]
    rw [h1]
    show (1 : ℝ) ≤ (1 : Matrix (Fin (N - 1 + 1)) (Fin (N - 1 + 1)) ℝ) _ col
    rw [Matrix.one_apply, if_pos (Fin.ext (by have := col.isLt; simp; omega))]

end margin

/-- The final arithmetic for two odd indices. -/
theorem oo_arith {X p rN rb rc C T : ℝ} (hX : 0 ≤ X) (hp : 0 < p) (_hrN : 0 ≤ rN) (hrc : 0 < rc)
    (hrb : 0 < rb) (hC : 0 < C) (hCT : C ≤ T) (hr : rN * rc ≤ rb) :
    p * rN * X / T ≤ X / rc / (C / (rb * p)) := by
  have hT : 0 < T := lt_of_lt_of_le hC hCT
  have e : X / rc / (C / (rb * p)) = X * p * (rb / (rc * C)) := by field_simp
  rw [e, show p * rN * X / T = X * p * (rN / T) by ring]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  rw [div_le_div_iff₀ hT (by positivity)]
  calc rN * (rc * C) = (rN * rc) * C := by ring
    _ ≤ rb * C := mul_le_mul_of_nonneg_right hr hC.le
    _ ≤ rb * T := mul_le_mul_of_nonneg_left hCT hrb.le

/-- **Lemma 7.4** (Margin for the quadratic system). -/
def Stmt_szwarc_margin : Prop :=
  ∀ (N : ℕ), 1 ≤ N → ∀ p : ℝ, 0 < p → p < 1 / 2 →
    ∀ m, m ≤ 2 * N → ∀ n k : Fin (2 * N + 1),
      ((Triangle m n.val k.val ∧ (m + n.val + k.val) % 2 = 0) →
        (p / (1 - p) * min (p / (1 - p)) (1 - p / (1 - p)) / 8) ^ N ≤
          productMatrix (szwarcCoefficients N p) m n k) ∧
      (¬(Triangle m n.val k.val ∧ (m + n.val + k.val) % 2 = 0) →
        productMatrix (szwarcCoefficients N p) m n k = 0)

set_option maxHeartbeats 1000000 in
theorem szwarc_margin : Stmt_szwarc_margin := by
  intro N hN p hp hp2 m hm n k
  have hv := szwarc_admissible N hN p hp (by linarith)
  have hb : ∀ i, i ≤ 2 * N → (szwarcCoefficients N p).b i = 0 := fun _ _ => rfl
  have hq : 0 < 1 - p := by linarith
  have hr0 : 0 < p / (1 - p) := div_pos hp hq
  have hr1 : p / (1 - p) < 1 := by rw [div_lt_one hq]; linarith
  have hs0 : 0 < min (p / (1 - p)) (1 - p / (1 - p)) := lt_min hr0 (by linarith)
  have hs1 : min (p / (1 - p)) (1 - p / (1 - p)) ≤ 1 / 2 := by
    rcases le_total (p / (1 - p)) (1 - p / (1 - p)) with h | h
    · rw [min_eq_left h]; linarith
    · rw [min_eq_right h]; linarith
  have hpr : p / (1 - p) / 2 ≤ p := by
    rw [div_div, div_le_iff₀ (by linarith)]; nlinarith
  generalize hr_def : p / (1 - p) = r at *
  generalize hs_def : min r (1 - r) = s at *
  set v := szwarcCoefficients N p with hv_def
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hnn := coeff_nonneg hv
  have hodd_nn : ∀ (col : Fin (N - 1 + 1)) (x y : ℕ), 0 ≤ Gk (oddRaw v) col x y :=
    fun col x y => oddRaw_Gk_nonneg v hv hN (szwarc_odd_pos hN hp hp2) col x y
  have hmg : ∀ (col : Fin (N - 1 + 1)) (x y : ℕ), x ≤ N - 1 → y ≤ N - 1 → Triangle x y col.val →
      (s / 4) ^ (N - 1) ≤ Gk (oddRaw v) col x y := by
    intro col x y hx hy ht
    have := szwarc_odd_margin hN hp hp2 col x y hx hy ht
    rw [hr_def, hs_def] at this; exact this
  have hG : productMatrix v m n k = Gk v k m n.val := by
    unfold Gk; rw [dif_pos ⟨hm, by omega⟩]
  have ha_lb : ∀ x, x + 1 ≤ N → 1 / (N : ℝ) ≤ v.a (2 * x) := by
    intro x hx
    rw [szwarc_a_even, div_le_div_iff_of_pos_right hN0]
    have : (x : ℝ) + 1 ≤ N := by exact_mod_cast hx
    linarith
  have hc_lb : ∀ x, 1 ≤ x → 1 / (N : ℝ) ≤ v.c (2 * x) := by
    intro x hx
    rw [szwarc_c_even, div_le_div_iff_of_pos_right hN0]
    exact_mod_cast hx
  have hm1 := margin_ineq1 N hr0 hr1.le hs0.le
  have hm2 := margin_ineq2 N hN hr0 hr1.le hs0.le hs1
  have hm3 := margin_ineq3 N hN hr0 hr1.le hs0.le (by linarith) hpr
  have hX : 0 ≤ (s / 4) ^ (N - 1) := by positivity
  refine ⟨fun ⟨htri, hpar⟩ => ?_, fun hnot => ?_⟩
  swap
  · by_cases htri : Triangle m n.val k.val
    · rw [hG]
      have h' : ¬(m + n.val + k.val) % 2 = 0 := fun h => hnot ⟨htri, h⟩
      exact Gk_parity v hv hb k m n.val (by omega)
    · exact product_triangle_zero v hv m hm n k htri
  unfold Triangle at htri
  obtain ⟨c, hk | hk⟩ : ∃ c, k.val = 2 * c ∨ k.val = 2 * c + 1 := ⟨k.val / 2, by omega⟩
  · obtain ⟨a, rfl | rfl⟩ : ∃ a, m = 2 * a ∨ m = 2 * a + 1 := ⟨m / 2, by omega⟩
    · -- three even indices: the even component is `K_N(r)`
      obtain ⟨b, hbn⟩ : ∃ b, n.val = 2 * b := ⟨n.val / 2, by omega⟩
      have h1 := even_block v hv hb a (by omega) ⟨b, by omega⟩ ⟨c, by omega⟩
      have hk2 := szwarc_even_kraw hN hp (by linarith) a (by omega)
      unfold evenComp at hk2
      rw [hr_def] at hk2
      rw [← product_normalize (evenRaw v) (evenRaw_a0 v hv hN).ne', hk2] at h1
      have h2 : Geven v a b c = productMatrix v (2 * a) n k := by
        unfold Geven Gk
        rw [dif_pos (by omega), dif_pos ⟨by omega, by omega⟩]
        congr 1 <;> exact Fin.ext (by simp; omega)
      rw [← h2, ← h1]
      have := kraw_triangle_margin N hN r hr0 hr1 a ⟨b, by omega⟩ ⟨c, by omega⟩ (by omega)
        (by unfold Triangle; simp; omega)
      rw [hs_def] at this
      linarith
    · -- two odd indices: `π_n g(m,n;k) = π_k g(m,k;n)`
      obtain ⟨b, hbn⟩ : ∃ b, n.val = 2 * b + 1 := ⟨n.val / 2, by omega⟩
      have hpi := piW_entry v hv (2 * a + 1) n k
      have hodd := odd_block v hv hb hN ⟨b, by omega⟩ (2 * a + 1) hm k
      have hn' : (⟨2 * b + 1, by omega⟩ : Fin (2 * N + 1)) = n := Fin.ext (by simp; omega)
      rw [hn'] at hodd
      rw [hodd, hk, Hodd_oe] at hpi
      have hπb := szwarc_piW_odd hp (by linarith) hN b (by omega)
      rw [hr_def] at hπb
      rw [hbn, hπb] at hpi
      have hlow : (s / 4) ^ (N - 1) / r ^ c ≤ piW v (2 * c) *
          (v.a (2 * c) * Gk (oddRaw v) ⟨b, by omega⟩ a c +
            v.c (2 * c) * Gk (oddRaw v) ⟨b, by omega⟩ a (c - 1)) := by
        have t1 := mul_nonneg (hnn (2 * c) (by omega)).1 (hodd_nn ⟨b, by omega⟩ a c)
        have t2 := mul_nonneg (hnn (2 * c) (by omega)).2 (hodd_nn ⟨b, by omega⟩ a (c - 1))
        have hπ0 : 0 ≤ piW v (2 * c) := (piW_pos v hv (2 * c) (by omega)).le
        have hrc : 0 < r ^ c := pow_pos hr0 c
        by_cases hA : c + 1 ≤ N ∧ c ≤ a + b
        · have hm' := hmg ⟨b, by omega⟩ a c (by omega) (by omega) (by unfold Triangle; simp; omega)
          have hrel : piW v (2 * c) * v.a (2 * c) = ((N - 1).choose c : ℝ) / r ^ c := by
            have e : piW v (2 * c + 1) = piW v (2 * c) * (v.a (2 * c) / v.c (2 * c + 1)) := by
              unfold piW; rw [prod_range_succ]
            have hπc := szwarc_piW_odd hp (by linarith) hN c (by omega)
            rw [hr_def] at hπc
            rw [hπc, szwarc_c_odd] at e
            have hpne : p ≠ 0 := hp.ne'
            have hrc' : r ^ c ≠ 0 := hrc.ne'
            have : piW v (2 * c) * v.a (2 * c) = ((N - 1).choose c : ℝ) / (r ^ c * p) * p := by
              rw [e]; field_simp
            rw [this]; field_simp
          have hch : (1 : ℝ) ≤ ((N - 1).choose c : ℝ) := by
            exact_mod_cast Nat.choose_pos (by omega)
          have hG0 := hodd_nn ⟨b, by omega⟩ a c
          calc (s / 4) ^ (N - 1) / r ^ c ≤ ((N - 1).choose c : ℝ) / r ^ c * Gk (oddRaw v) ⟨b, by omega⟩ a c := by
                rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hrc]
                calc (s / 4) ^ (N - 1) ≤ 1 * Gk (oddRaw v) ⟨b, by omega⟩ a c := by rw [one_mul]; exact hm'
                  _ ≤ _ := mul_le_mul_of_nonneg_right hch hG0
            _ = piW v (2 * c) * v.a (2 * c) * Gk (oddRaw v) ⟨b, by omega⟩ a c := by rw [hrel]
            _ ≤ _ := by rw [mul_add, ← mul_assoc]; exact le_add_of_nonneg_right (mul_nonneg hπ0 t2)
        · have hc1 : 1 ≤ c := by omega
          have hm' := hmg ⟨b, by omega⟩ a (c - 1) (by omega) (by omega) (by unfold Triangle; simp; omega)
          have hrel : piW v (2 * c) * v.c (2 * c) = ((N - 1).choose (c - 1) : ℝ) / r ^ c := by
            have e : piW v (2 * c) = piW v (2 * (c - 1) + 1) * (v.a (2 * (c - 1) + 1) / v.c (2 * c)) := by
              unfold piW; rw [show 2 * c = 2 * (c - 1) + 1 + 1 by omega, prod_range_succ]
            have hcne : v.c (2 * c) ≠ 0 := (hv.2.2.2.2.2.2.2 (2 * c) (by omega) (by omega)).ne'
            have hπc := szwarc_piW_odd hp (by linarith) hN (c - 1) (by omega)
            rw [hr_def] at hπc
            rw [e, hπc, szwarc_a_odd]
            have hpne : p ≠ 0 := hp.ne'
            have hrc' : r ^ (c - 1) ≠ 0 := pow_ne_zero _ hr0.ne'
            have hrr : r = p / (1 - p) := hr_def.symm
            rw [show r ^ c = r ^ (c - 1) * r by rw [← pow_succ]; congr 1; omega]
            field_simp
            rw [hrr]; field_simp
          have hch : (1 : ℝ) ≤ ((N - 1).choose (c - 1) : ℝ) := by
            exact_mod_cast Nat.choose_pos (by omega)
          have hG0 := hodd_nn ⟨b, by omega⟩ a (c - 1)
          calc (s / 4) ^ (N - 1) / r ^ c ≤ ((N - 1).choose (c - 1) : ℝ) / r ^ c *
                Gk (oddRaw v) ⟨b, by omega⟩ a (c - 1) := by
                rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hrc]
                calc (s / 4) ^ (N - 1) ≤ 1 * Gk (oddRaw v) ⟨b, by omega⟩ a (c - 1) := by rw [one_mul]; exact hm'
                  _ ≤ _ := mul_le_mul_of_nonneg_right hch hG0
            _ = piW v (2 * c) * v.c (2 * c) * Gk (oddRaw v) ⟨b, by omega⟩ a (c - 1) := by rw [hrel]
            _ ≤ _ := by rw [mul_add, ← mul_assoc (piW v (2 * c)) (v.c (2 * c))]
                        exact le_add_of_nonneg_left (mul_nonneg hπ0 t1)
      have hchb : ((N - 1).choose b : ℝ) ≤ 2 ^ (N - 1) := by exact_mod_cast Nat.choose_le_two_pow _ _
      have hchb0 : (0 : ℝ) < ((N - 1).choose b : ℝ) := by exact_mod_cast Nat.choose_pos (by omega)
      have hrb : r ^ (N - 1) * r ^ c ≤ r ^ b := by
        rw [← pow_add]; exact pow_le_pow_of_le_one hr0.le hr1.le (by omega)
      have hπn : 0 < ((N - 1).choose b : ℝ) / (r ^ b * p) := by
        have := pow_pos hr0 b; positivity
      have hP : (s / 4) ^ (N - 1) / r ^ c / (((N - 1).choose b : ℝ) / (r ^ b * p)) ≤
          productMatrix v (2 * a + 1) n k := by
        rw [div_le_iff₀ hπn, mul_comm, hpi]; exact hlow
      have := oo_arith hX hp (pow_nonneg hr0.le (N - 1)) (pow_pos hr0 c) (pow_pos hr0 b) hchb0 hchb hrb
      linarith
  · -- odd column
    have hodd := odd_block v hv hb hN ⟨c, by omega⟩ m hm n
    have hk' : (⟨2 * c + 1, by omega⟩ : Fin (2 * N + 1)) = k := Fin.ext (by simp; omega)
    rw [hk'] at hodd
    rw [hodd]
    have hbase : 1 / (N : ℝ) * (s / 4) ^ (N - 1) ≤ Hodd v ⟨c, by omega⟩ m n.val := by
      obtain ⟨a, rfl | rfl⟩ : ∃ a, m = 2 * a ∨ m = 2 * a + 1 := ⟨m / 2, by omega⟩
      · obtain ⟨b, hbn⟩ : ∃ b, n.val = 2 * b + 1 := ⟨n.val / 2, by omega⟩
        rw [hbn, Hodd_eo]
        have t1 := mul_nonneg (hnn (2 * a) (by omega)).1 (hodd_nn ⟨c, by omega⟩ a b)
        have t2 := mul_nonneg (hnn (2 * a) (by omega)).2 (hodd_nn ⟨c, by omega⟩ (a - 1) b)
        by_cases hA : a + 1 ≤ N ∧ a ≤ b + c
        · have hm' := hmg ⟨c, by omega⟩ a b (by omega) (by omega) (by unfold Triangle; simp; omega)
          have hl := ha_lb a hA.1
          calc 1 / (N : ℝ) * (s / 4) ^ (N - 1) ≤ v.a (2 * a) * Gk (oddRaw v) ⟨c, by omega⟩ a b :=
                mul_le_mul hl hm' hX (le_trans (by positivity) hl)
            _ ≤ _ := le_add_of_nonneg_right t2
        · have hm' := hmg ⟨c, by omega⟩ (a - 1) b (by omega) (by omega) (by unfold Triangle; simp; omega)
          have hl := hc_lb a (by omega)
          calc 1 / (N : ℝ) * (s / 4) ^ (N - 1) ≤ v.c (2 * a) * Gk (oddRaw v) ⟨c, by omega⟩ (a - 1) b :=
                mul_le_mul hl hm' hX (le_trans (by positivity) hl)
            _ ≤ _ := le_add_of_nonneg_left t1
      · obtain ⟨b, hbn⟩ : ∃ b, n.val = 2 * b := ⟨n.val / 2, by omega⟩
        rw [hbn, Hodd_oe]
        have t1 := mul_nonneg (hnn (2 * b) (by omega)).1 (hodd_nn ⟨c, by omega⟩ a b)
        have t2 := mul_nonneg (hnn (2 * b) (by omega)).2 (hodd_nn ⟨c, by omega⟩ a (b - 1))
        by_cases hA : b + 1 ≤ N ∧ b ≤ a + c
        · have hm' := hmg ⟨c, by omega⟩ a b (by omega) (by omega) (by unfold Triangle; simp; omega)
          have hl := ha_lb b hA.1
          calc 1 / (N : ℝ) * (s / 4) ^ (N - 1) ≤ v.a (2 * b) * Gk (oddRaw v) ⟨c, by omega⟩ a b :=
                mul_le_mul hl hm' hX (le_trans (by positivity) hl)
            _ ≤ _ := le_add_of_nonneg_right t2
        · have hm' := hmg ⟨c, by omega⟩ a (b - 1) (by omega) (by omega) (by unfold Triangle; simp; omega)
          have hl := hc_lb b (by omega)
          calc 1 / (N : ℝ) * (s / 4) ^ (N - 1) ≤ v.c (2 * b) * Gk (oddRaw v) ⟨c, by omega⟩ a (b - 1) :=
                mul_le_mul hl hm' hX (le_trans (by positivity) hl)
            _ ≤ _ := le_add_of_nonneg_left t1
    linarith

/-! ### Theorem 7.6 and Corollary 7.7 -/

/-- The radius `η = ½ (rs/8)^N (16N)^{-2N}` of Theorem 7.6. -/
noncomputable def symEta (N : ℕ) (p : ℝ) : ℝ :=
  (1 / 2) * (p / (1 - p) * min (p / (1 - p)) (1 - p / (1 - p)) / 8) ^ N / (16 * (N : ℝ)) ^ (2 * N)

/-- **Theorem 7.6** (Symmetric criterion near Szwarc's system). -/
def Stmt_symmetric : Prop :=
  ∀ (N : ℕ), 1 ≤ N → ∀ p : ℝ, 0 < p → p < 1 / 2 → ∀ w : Coefficients (2 * N),
    (∀ k, k ≤ 2 * N → w.b k = 0) → (∀ k, k ≤ 2 * N → w.a k = 1 - w.c k) → w.c 0 = 0 →
    w.c (2 * N) = 1 →
    (∀ k, 1 ≤ k → k + 1 ≤ 2 * N → |w.c k - (szwarcCoefficients N p).c k| ≤ symEta N p) →
    Admissible w ∧ FiniteRealization w ∧ MatrixPositivity w ∧
    (∀ m, m ≤ 2 * N → ∀ n k : Fin (2 * N + 1), Triangle m n.val k.val ∧ (m + n.val + k.val) % 2 = 0 →
      (1 / 2) * (p / (1 - p) * min (p / (1 - p)) (1 - p / (1 - p)) / 8) ^ N ≤ productMatrix w m n k) ∧
    (∀ m, m ≤ 2 * N → ∀ n k : Fin (2 * N + 1), ¬(Triangle m n.val k.val ∧ (m + n.val + k.val) % 2 = 0) →
      productMatrix w m n k = 0)

set_option maxHeartbeats 1000000 in
theorem symmetric_criterion : Stmt_symmetric := by
  intro N hN p hp hp2 w hwb hwa hwc0 hwcN hclose
  set v := szwarcCoefficients N p with hv_def
  have hv := szwarc_admissible N hN p hp (by linarith)
  have hq : 0 < 1 - p := by linarith
  have hr0 : 0 < p / (1 - p) := div_pos hp hq
  have hr1 : p / (1 - p) < 1 := by rw [div_lt_one hq]; linarith
  have hr2 : p / (1 - p) ≤ 2 * p := by rw [div_le_iff₀ hq]; nlinarith
  have hs0 : 0 < min (p / (1 - p)) (1 - p / (1 - p)) := lt_min hr0 (by linarith)
  have hsr : min (p / (1 - p)) (1 - p / (1 - p)) ≤ p / (1 - p) := min_le_left _ _
  set δ := (p / (1 - p) * min (p / (1 - p)) (1 - p / (1 - p)) / 8) ^ N with hδ
  have hx0 : 0 < p / (1 - p) * min (p / (1 - p)) (1 - p / (1 - p)) / 8 := by positivity
  have hx1 : p / (1 - p) * min (p / (1 - p)) (1 - p / (1 - p)) / 8 ≤ p / 4 := by
    have hs1 : min (p / (1 - p)) (1 - p / (1 - p)) ≤ 1 := le_trans hsr hr1.le
    have : p / (1 - p) * min (p / (1 - p)) (1 - p / (1 - p)) ≤ p / (1 - p) * 1 :=
      mul_le_mul_of_nonneg_left hs1 hr0.le
    linarith
  have hδ0 : 0 < δ := pow_pos hx0 N
  have hδx : δ ≤ p / (1 - p) * min (p / (1 - p)) (1 - p / (1 - p)) / 8 := by
    rw [hδ]; exact pow_le_of_le_one hx0.le (by linarith) (by omega)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  set D := (16 * (N : ℝ)) ^ (2 * N) with hD
  have hD1 : 16 * (N : ℝ) ≤ D := by
    rw [hD]; calc 16 * (N : ℝ) = (16 * (N : ℝ)) ^ 1 := (pow_one _).symm
      _ ≤ _ := pow_le_pow_right₀ (by linarith) (by omega)
  have hDpos : 0 < D := by linarith
  have hη : symEta N p = δ / 2 / D := by unfold symEta; rw [← hδ, ← hD]; ring
  have hη0 : 0 ≤ symEta N p := by rw [hη]; positivity
  -- `η ≤ δ / (32 N)` and `δ ≤ 1`
  have hηN : symEta N p ≤ 1 / (32 * N) := by
    rw [hη, div_div, div_le_div_iff₀ (by positivity) (by positivity)]
    have : δ ≤ 1 := by linarith
    nlinarith
  have hηp : symEta N p < p := by
    have h1 : symEta N p ≤ δ / 32 := by
      rw [hη, div_div, div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
    linarith
  -- the coefficient perturbation
  have hvc : ∀ k, k ≤ 2 * N → v.a k = 1 - v.c k := fun k hk => by
    have := hv.2.2.2.2.2.1 k hk; rw [show v.b k = 0 from rfl] at this; linarith
  have hcl : ∀ k, k ≤ 2 * N → |w.c k - v.c k| ≤ symEta N p := by
    intro k hk
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · rw [h0, hwc0, hv.2.2.2.1, sub_zero, abs_zero]; exact hη0
    rcases Nat.lt_or_ge k (2 * N) with h1 | h1
    · exact hclose k h0 (by omega)
    · have hkN : k = 2 * N := by omega
      rw [hkN, hwcN, szwarc_c_even]
      have : (N : ℝ) / N = 1 := div_self (by linarith)
      rw [this, sub_self, abs_zero]; exact hη0
  -- `w` satisfies (basic)
  have hw : Admissible w := by
    refine ⟨by omega, by rw [hwa 0 (by omega), hwc0]; ring, hwb 0 (by omega), hwc0,
      by rw [hwa _ le_rfl, hwcN]; ring, fun i hi => by rw [hwa i hi, hwb i hi]; ring, ?_, ?_⟩
    · intro i hi
      rw [hwa i (by omega)]
      have h := (abs_le.mp (hcl i (by omega))).2
      obtain ⟨n, rfl | rfl⟩ : ∃ n, i = 2 * n ∨ i = 2 * n + 1 := ⟨i / 2, by omega⟩
      · rw [szwarc_c_even] at h
        have hn : (n : ℝ) + 1 ≤ N := by exact_mod_cast (show n + 1 ≤ N by omega)
        have : (n : ℝ) / N ≤ 1 - 1 / N := by
          rw [div_le_iff₀ (by linarith), sub_mul, one_div_mul_cancel (by linarith)]; linarith
        have : 1 / (32 * (N : ℝ)) < 1 / N := by
          apply one_div_lt_one_div_of_lt (by linarith); linarith
        linarith
      · rw [szwarc_c_odd] at h; linarith
    · intro i h0 hi
      rcases Nat.lt_or_ge i (2 * N) with h1 | h1
      · have h := (abs_le.mp (hcl i (by omega))).1
        obtain ⟨n, rfl | rfl⟩ : ∃ n, i = 2 * n ∨ i = 2 * n + 1 := ⟨i / 2, by omega⟩
        · rw [szwarc_c_even] at h
          have hn : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
          have : 1 / (N : ℝ) ≤ (n : ℝ) / N := div_le_div_of_nonneg_right hn (by linarith)
          have : 1 / (32 * (N : ℝ)) < 1 / N := by
            apply one_div_lt_one_div_of_lt (by linarith); linarith
          linarith
        · rw [szwarc_c_odd] at h; linarith
      · rw [show i = 2 * N by omega, hwcN]; norm_num
  -- apply Lemma 7.5 with `α = 1/(2N)` and the margin of Lemma 7.4
  have hα : (0 : ℝ) < 1 / (2 * N) := by positivity
  have hα1 : 1 / (2 * (N : ℝ)) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
  have hαa : ∀ i, i < 2 * N → 1 / (2 * (N : ℝ)) ≤ v.a i := by
    intro i hi
    obtain ⟨n, rfl | rfl⟩ : ∃ n, i = 2 * n ∨ i = 2 * n + 1 := ⟨i / 2, by omega⟩
    · rw [szwarc_a_even]
      have hn : (n : ℝ) + 1 ≤ N := by exact_mod_cast (show n + 1 ≤ N by omega)
      rw [div_le_div_iff₀ (by linarith) (by linarith)]; nlinarith
    · rw [szwarc_a_odd]
      have : 1 / (2 * (N : ℝ)) ≤ 1 / 2 := by
        apply one_div_le_one_div_of_le (by norm_num); linarith
      linarith
  have hmargin := szwarc_margin N hN p hp hp2
  have hcoeff : ∀ i, i ≤ 2 * N → |w.a i - v.a i| ≤ symEta N p ∧ |w.b i - v.b i| ≤ symEta N p ∧
      |w.c i - v.c i| ≤ symEta N p := by
    intro i hi
    have e1 : w.a i - v.a i = -(w.c i - v.c i) := by rw [hwa i hi, hvc i hi]; ring
    have e2 : w.b i - v.b i = 0 := by rw [hwb i hi]; show (0 : ℝ) - 0 = 0; ring
    refine ⟨?_, ?_, hcl i hi⟩
    · rw [e1, abs_neg]; exact hcl i hi
    · rw [e2, abs_zero]; exact hη0
  have hηα : symEta N p ≤ 1 / (2 * (N : ℝ)) / 2 := by
    have e : 1 / (2 * (N : ℝ)) / 2 = 1 / (4 * N) := by field_simp; ring
    rw [e]
    have : 1 / (32 * (N : ℝ)) ≤ 1 / (4 * N) := by
      apply one_div_le_one_div_of_le (by positivity); linarith
    linarith
  have hηδ : symEta N p * (8 / (1 / (2 * (N : ℝ)))) ^ (2 * N) ≤ δ / 2 := by
    have e : 8 / (1 / (2 * (N : ℝ))) = 16 * N := by field_simp; ring
    rw [e, ← hD, hη, div_mul_cancel₀ _ hDpos.ne']
  have hstab := stability (2 * N) v w (1 / (2 * N)) δ (symEta N p)
    (fun m n k => Triangle m n k ∧ (m + n + k) % 2 = 0) hv
    (szwarc_system N hN p hp (by linarith)).2 hα hα1 hαa hδ0
    (fun m hm n k hs => (hmargin m hm n k).1 hs) hw (fun i hi => (hwb i hi).ge) hcoeff hηα hηδ
  have hzero : ∀ m, m ≤ 2 * N → ∀ n k : Fin (2 * N + 1),
      ¬(Triangle m n.val k.val ∧ (m + n.val + k.val) % 2 = 0) → productMatrix w m n k = 0 := by
    intro m hm n k hnot
    by_cases htri : Triangle m n.val k.val
    · have h' : ¬(m + n.val + k.val) % 2 = 0 := fun h => hnot ⟨htri, h⟩
      have := Gk_parity w hw hwb k m n.val (by omega)
      unfold Gk at this; rw [dif_pos ⟨hm, by omega⟩] at this; exact this
    · exact product_triangle_zero w hw m hm n k htri
  refine ⟨hw, finite_realization w hw, ?_, fun m hm n k hs => by have := hstab.2 m hm n k hs; linarith, hzero⟩
  intro m hm n k
  by_cases hs : Triangle m n.val k.val ∧ (m + n.val + k.val) % 2 = 0
  · have := hstab.2 m hm n k hs; linarith
  · rw [hzero m hm n k hs]

/-- The array of Corollary 7.7: (7.2) with `c_1 ↦ p_0 + h`, `a_1 ↦ 1 - p_0 - h`. -/
noncomputable def perturbedSzwarc (N : ℕ) (p h : ℝ) : Coefficients (2 * N) :=
  ⟨fun k => if k = 1 then 1 - p - h else (szwarcCoefficients N p).a k,
   fun k => (szwarcCoefficients N p).b k,
   fun k => if k = 1 then p + h else (szwarcCoefficients N p).c k⟩

/-- `Geometric` only depends on the coefficients with indices `0, …, N`. -/
theorem geometric_congr {K : ℕ} {v w : Coefficients K} (hb : ∀ i, i ≤ K → v.b i = w.b i)
    (hc : ∀ i, i ≤ K → v.c i = w.c i) (hg : Geometric v) : Geometric w := by
  obtain ⟨β, q, hβ, hq, h1, h2, h3⟩ := hg
  refine ⟨β, q, hβ, hq, fun i hi hiK => ?_, fun i hi hiK => ?_, fun i hi hiK => ?_⟩
  · rw [← hb i hiK, ← hc i hiK]; exact h1 i hi hiK
  · rw [← hb i hiK, ← hc i hiK, ← hb (i - 1) (by omega), ← hc (i - 1) (by omega)]; exact h2 i hi hiK
  · rw [← hb (i + 1) (by omega), ← hc (i + 1) (by omega), ← hb i (by omega), ← hc i (by omega),
      ← hb (i - 1) (by omega), ← hc (i - 1) (by omega)]
    exact h3 i hi hiK

/-- **Corollary 7.7** (Symmetric systems outside both families). -/
theorem symmetric_new (N : ℕ) (hN : 2 ≤ N) (p : ℝ) (hp : 0 < p) (hp2 : p < 1 / 2) (h : ℝ)
    (hh : 0 < h) (hhη : h ≤ symEta N p) :
    MatrixPositivity (perturbedSzwarc N p h) ∧
    (∀ p' : ℝ, ¬ ∀ k, k ≤ 2 * N → (perturbedSzwarc N p h).c k = (szwarcCoefficients N p').c k) ∧
    ¬ Geometric (perturbedSzwarc N p h) ∧
    (∀ p' q' : ℝ, 1 ≤ p' → 1 ≤ q' → ¬ ∀ k, k ≤ 2 * N →
      (perturbedSzwarc N p h).b k = (geometricCoefficients (2 * N) p' q').b k ∧
      (perturbedSzwarc N p h).c k = (geometricCoefficients (2 * N) p' q').c k) := by
  have hc3 : (perturbedSzwarc N p h).c 3 = p := by
    show (if (3 : ℕ) = 1 then p + h else (szwarcCoefficients N p).c (2 * 1 + 1)) = p
    rw [if_neg (by omega), szwarc_c_odd]
  have hc1 : (perturbedSzwarc N p h).c 1 = p + h := by
    show (if (1 : ℕ) = 1 then p + h else (szwarcCoefficients N p).c 1) = p + h; rw [if_pos rfl]
  have hbz : ∀ k, (perturbedSzwarc N p h).b k = 0 := fun _ => rfl
  have hnotgeo : ¬ Geometric (perturbedSzwarc N p h) := by
    rintro ⟨β, q, _, _, _, h2, _⟩
    have i2 := h2 2 (by omega) (by omega)
    have i3 := h2 3 (by omega) (by omega)
    simp only [hbz, zero_add, show (2 : ℕ) - 1 = 1 by rfl, show (3 : ℕ) - 1 = 2 by rfl] at i2 i3
    rw [hc1] at i2; rw [hc3] at i3
    linarith
  refine ⟨?_, ?_, hnotgeo, ?_⟩
  · have := symmetric_criterion N (by omega) p hp hp2 (perturbedSzwarc N p h) (fun k _ => hbz k)
      (fun k hk => by
        show (if k = 1 then 1 - p - h else (szwarcCoefficients N p).a k) =
          1 - (if k = 1 then p + h else (szwarcCoefficients N p).c k)
        split_ifs
        · ring
        · have := (szwarc_admissible N (by omega) p hp (by linarith)).2.2.2.2.2.1 k hk
          rw [show (szwarcCoefficients N p).b k = 0 from rfl] at this; linarith)
      (by show (if (0 : ℕ) = 1 then p + h else (szwarcCoefficients N p).c 0) = 0
          rw [if_neg (by omega)]; exact (szwarc_admissible N (by omega) p hp (by linarith)).2.2.2.1)
      (by show (if 2 * N = 1 then p + h else (szwarcCoefficients N p).c (2 * N)) = 1
          rw [if_neg (by omega), szwarc_c_even, div_self (by positivity)])
      (fun k hk1 hk2 => by
        show |(if k = 1 then p + h else (szwarcCoefficients N p).c k) - (szwarcCoefficients N p).c k| ≤ _
        split_ifs with hk
        · subst hk
          rw [show (szwarcCoefficients N p).c 1 = p from szwarc_c_odd 0]
          rw [show p + h - p = h by ring, abs_of_pos hh]; exact hhη
        · rw [sub_self, abs_zero]; unfold symEta
          have : 0 < p / (1 - p) := div_pos hp (by linarith)
          have : 0 < min (p / (1 - p)) (1 - p / (1 - p)) := lt_min this (by
            rw [sub_pos, div_lt_one (by linarith)]; linarith)
          positivity)
    exact this.2.2.1
  · intro p' hall
    have e1 := hall 1 (by omega)
    have e3 := hall 3 (by omega)
    rw [hc1, show (1 : ℕ) = 2 * 0 + 1 by rfl, szwarc_c_odd] at e1
    rw [hc3, show (3 : ℕ) = 2 * 1 + 1 by rfl, szwarc_c_odd] at e3
    linarith
  · intro p' q' hp' hq' hall
    exact hnotgeo (geometric_congr (fun i hi => (hall i hi).1.symm) (fun i hi => (hall i hi).2.symm)
      (geometric_family_hypotheses (2 * N) (by omega) p' q' hp' hq'))

end Szkraw
