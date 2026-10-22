import Szkraw.VRQuadB

/-!
# Theorem 8.11: the weighted `B`-detour for log-concave sequences (paper, eq. `quad-B`)

For a sequence `v` that is log-concave without internal zeros with `v₁ > 0` and `v₀ ≤ ℓ v₁`, and the
Leibniz expressions `Φ_k(base, v) = ρ(base+k) v_k + k Δρ(base+k-1) v_{k-1} + C(k,2) τ v_{k-2}`:
`8(n-1) ρ(ℓ+1)(v₀+v₁) Φ_{n+2}(ℓ, v) ≤ (n+1)(n+2) Φ₂(ℓ, v) Φ_n(ℓ+1, v')`, `v'_k = v_k + v_{k+1}`.
The tail is reduced to the geometric configuration (`FQ_nonneg`) by concavity in `y = v_{n+1}/v_n`.
-/

set_option linter.unusedSectionVars false

namespace Szkraw

/-- The Leibniz expression `Φ_k(base, v)`. -/
noncomputable def PhiQ (r t τ base : ℝ) (k : ℕ) (v : ℕ → ℝ) : ℝ :=
  rhoQ r t τ (base + k) * v k + k * drhoQ t τ (base + k - 1) * v (k - 1) +
    (k : ℝ) * (k - 1) / 2 * τ * v (k - 2)

/-- Concavity of `𝓕` in `y`. -/
theorem FQ_interp (n : ℕ) (r t τ ℓ z q y : ℝ) (hq : q ≠ 0) :
    FQ n r t τ ℓ z q y = (1 - y / q) * FQ n r t τ ℓ z q 0 + y / q * FQ n r t τ ℓ z q q +
      8 * ((n : ℝ) - 1) * rhoQ r t τ (ℓ + 1) * (z + 1) * rhoQ r t τ (ℓ + n + 2) * y * (q - y) := by
  unfold FQ LQ TQ
  split_ifs <;> field_simp <;> ring

/-- `𝓕(y) ≥ 0` on `[0, q]`. -/
theorem FQ_nonneg_y {n : ℕ} (hn : 2 ≤ n) {r t τ ℓ q z y : ℝ} (hr : 0 < r) (ht : 0 ≤ t) (hτ : 0 ≤ τ) (hℓ : 0 ≤ ℓ)
    (hq : 0 < q) (hz : 0 ≤ z) (hzℓ : z ≤ ℓ) (hzq : z * q ≤ 1) (hy : 0 ≤ y) (hyq : y ≤ q) :
    0 ≤ FQ n r t τ ℓ z q y := by
  have hFq := FQ_nonneg hn hr ht hτ hℓ hq hz hzℓ hzq
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hρ1 := (rhoQ_pos hr ht hτ (show (1 : ℝ) ≤ ℓ + 1 by linarith)).le
  have hρn := (rhoQ_pos hr ht hτ (show (1 : ℝ) ≤ ℓ + n + 2 by linarith)).le
  -- `𝓕(0) ≥ 𝓕(q)/(1+q)`
  have hF0 : FQ n r t τ ℓ z q q ≤ (1 + q) * FQ n r t τ ℓ z q 0 := by
    have hA2 : 0 ≤ A2Q r t τ ℓ q + τ * z := by
      unfold A2Q drhoQ
      have := (rhoQ_pos hr ht hτ (show (1 : ℝ) ≤ ℓ + 2 by linarith)).le
      positivity
    have hgap : (1 + q) * FQ n r t τ ℓ z q 0 - FQ n r t τ ℓ z q q =
        ((n : ℝ) + 1) * (n + 2) * (A2Q r t τ ℓ q + τ * z) * ((1 + q) * LQ n r t τ ℓ z q 0 - LQ n r t τ ℓ z q q) +
        8 * ((n : ℝ) - 1) * rhoQ r t τ (ℓ + 1) * (z + 1) * (TQ n r t τ ℓ q - (1 + q) * TQ n r t τ ℓ 0) := by
      unfold FQ; ring
    have hL : 0 ≤ (1 + q) * LQ n r t τ ℓ z q 0 - LQ n r t τ ℓ z q q := by
      unfold LQ
      split_ifs with h2
      · have : 0 ≤ 2 * drhoQ t τ (ℓ + 2) * (1 + 1 / q) * q := by unfold drhoQ; positivity
        have : 0 ≤ τ * (z + 1) / q * q := by positivity
        have e : (1 + q) * (rhoQ r t τ (ℓ + 3) * (1 + 0) + 2 * drhoQ t τ (ℓ + 2) * (1 + 1 / q) + τ * (z + 1) / q) -
            (rhoQ r t τ (ℓ + 3) * (1 + q) + 2 * drhoQ t τ (ℓ + 2) * (1 + 1 / q) + τ * (z + 1) / q) =
            (2 * drhoQ t τ (ℓ + 2) * (1 + 1 / q) + τ * (z + 1) / q) * q := by ring
        have hd : 0 ≤ drhoQ t τ (ℓ + 2) := by unfold drhoQ; positivity
        rw [e]
        exact mul_nonneg (add_nonneg (mul_nonneg (mul_nonneg (by norm_num) hd) (by positivity)) (by positivity)) hq.le
      · have e : (1 + q) * (rhoQ r t τ (ℓ + n + 1) * (1 + 0) + n * drhoQ t τ (ℓ + n) * (1 + 1 / q) +
            (n : ℝ) * (n - 1) / 2 * τ * (1 / q + 1 / q ^ 2)) -
            (rhoQ r t τ (ℓ + n + 1) * (1 + q) + n * drhoQ t τ (ℓ + n) * (1 + 1 / q) +
            (n : ℝ) * (n - 1) / 2 * τ * (1 / q + 1 / q ^ 2)) =
            (n * drhoQ t τ (ℓ + n) * (1 + 1 / q) + (n : ℝ) * (n - 1) / 2 * τ * (1 / q + 1 / q ^ 2)) * q := by ring
        rw [e]
        have hd : 0 ≤ drhoQ t τ (ℓ + n) := by unfold drhoQ; positivity
        have hn1 : 0 ≤ (n : ℝ) - 1 := by linarith
        exact mul_nonneg (add_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hd) (by positivity))
          (by positivity)) hq.le
    have hT : 0 ≤ TQ n r t τ ℓ q - (1 + q) * TQ n r t τ ℓ 0 := by
      unfold TQ drhoQ
      have e : rhoQ r t τ (ℓ + n + 2) * q ^ 2 + (n + 2) * (t + τ * (ℓ + n + 1)) * q + ((n : ℝ) + 2) * (n + 1) / 2 * τ -
          (1 + q) * (rhoQ r t τ (ℓ + n + 2) * 0 ^ 2 + (n + 2) * (t + τ * (ℓ + n + 1)) * 0 + ((n : ℝ) + 2) * (n + 1) / 2 * τ) =
          q * (rhoQ r t τ (ℓ + n + 2) * q + (n + 2) * t + (n + 2) * τ * ℓ + ((n : ℝ) + 2) * (n + 1) / 2 * τ) := by ring
      rw [e]; positivity
    have : 0 ≤ ((n : ℝ) + 1) * (n + 2) * (A2Q r t τ ℓ q + τ * z) * ((1 + q) * LQ n r t τ ℓ z q 0 - LQ n r t τ ℓ z q q) :=
      mul_nonneg (by positivity) hL
    have : 0 ≤ 8 * ((n : ℝ) - 1) * rhoQ r t τ (ℓ + 1) * (z + 1) * (TQ n r t τ ℓ q - (1 + q) * TQ n r t τ ℓ 0) := by
      have : 0 ≤ (n : ℝ) - 1 := by linarith
      exact mul_nonneg (by positivity) hT
    linarith
  have hF00 : 0 ≤ FQ n r t τ ℓ z q 0 := by
    by_contra hc; push Not at hc
    have := mul_neg_of_pos_of_neg (by linarith : (0 : ℝ) < 1 + q) hc
    linarith
  rw [FQ_interp n r t τ ℓ z q y hq.ne']
  have a1 : 0 ≤ 1 - y / q := by rw [sub_nonneg, div_le_one hq]; exact hyq
  have a2 : 0 ≤ y / q := by positivity
  have a3 : 0 ≤ 8 * ((n : ℝ) - 1) * rhoQ r t τ (ℓ + 1) * (z + 1) * rhoQ r t τ (ℓ + n + 2) * y * (q - y) := by
    have : 0 ≤ (n : ℝ) - 1 := by linarith
    have : 0 ≤ q - y := by linarith
    positivity
  nlinarith [mul_nonneg a1 hF00, mul_nonneg a2 hFq]


theorem LCNZ.zero_above {v' : ℕ → ℝ} (hv : LCNZ v') (h1 : 0 < v' 1) {n : ℕ} (hn : 1 ≤ n) (h : v' n = 0) {k : ℕ} (hk : n ≤ k) :
    v' k = 0 := by
  by_contra hc
  have hpos : 0 < v' k := lt_of_le_of_ne (hv.1 k) (Ne.symm hc)
  have := hv.2.2 1 n k hn hk h1 hpos
  rw [h] at this; exact lt_irrefl 0 this

/-- The weighted `B`-detour for a normalized sequence (`v₁ = 1`). -/
theorem quadB_norm {v : ℕ → ℝ} (hv : LCNZ v) (hv1 : v 1 = 1) {n : ℕ} (hn : 2 ≤ n) {r t τ ℓ : ℝ}
    (hr : 0 < r) (ht : 0 ≤ t) (hτ : 0 ≤ τ) (hℓ : 0 ≤ ℓ) (hz : v 0 ≤ ℓ) :
    8 * ((n : ℝ) - 1) * rhoQ r t τ (ℓ + 1) * (v 0 + v 1) * PhiQ r t τ ℓ (n + 2) v ≤
      ((n : ℝ) + 1) * (n + 2) * PhiQ r t τ ℓ 2 v * PhiQ r t τ (ℓ + 1) n (fun k => v k + v (k + 1)) := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hnn := hv.1
  have hd : ∀ x : ℝ, 0 ≤ x → 0 ≤ drhoQ t τ x := fun x hx => by unfold drhoQ; positivity
  have hρ : ∀ x : ℝ, 1 ≤ x → 0 ≤ rhoQ r t τ x := fun x hx => (rhoQ_pos hr ht hτ hx).le
  have hPhi : ∀ (base : ℝ) (k : ℕ) (w : ℕ → ℝ), 0 ≤ base → 1 ≤ k → (∀ i, 0 ≤ w i) → 0 ≤ PhiQ r t τ base k w := by
    intro base k w hb hk hw
    unfold PhiQ
    have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
    have := hρ (base + k) (by linarith)
    have := hd (base + k - 1) (by linarith)
    have : 0 ≤ (k : ℝ) * (k - 1) / 2 := div_nonneg (mul_nonneg (by linarith) (by linarith)) (by norm_num)
    have := hw k; have := hw (k - 1); have := hw (k - 2)
    positivity
  have hRHS : 0 ≤ ((n : ℝ) + 1) * (n + 2) * PhiQ r t τ ℓ 2 v * PhiQ r t τ (ℓ + 1) n (fun k => v k + v (k + 1)) :=
    mul_nonneg (mul_nonneg (by positivity) (hPhi ℓ 2 v hℓ (by norm_num) hnn))
      (hPhi (ℓ + 1) n _ (by linarith) (by omega) fun i => add_nonneg (hnn i) (hnn (i + 1)))
  have hv1p : 0 < v 1 := by rw [hv1]; norm_num
  -- zero cases
  have hzero : v n = 0 → PhiQ r t τ ℓ (n + 2) v = 0 := by
    intro h0
    unfold PhiQ
    rw [show n + 2 - 1 = n + 1 by omega, show n + 2 - 2 = n by omega, h0,
      hv.zero_above hv1p (by omega) h0 (show n ≤ n + 1 by omega), hv.zero_above hv1p (by omega) h0 (show n ≤ n + 2 by omega)]
    ring
  rcases eq_or_lt_of_le (hnn n) with hvn | hvn
  · rw [hzero hvn.symm]; simp only [mul_zero]; exact hRHS
  set q := v 2 with hq
  rcases eq_or_lt_of_le (hnn 2) with hq0 | hq0
  · have : v n = 0 := hv.zero_from hv1p hq0.symm hn
    linarith
  set z := v 0 with hzdef
  have hzq : z * q ≤ 1 := by have := hv.2.1 0; simp only [zero_add] at this; rw [hv1] at this; nlinarith
  set y := v (n + 1) / v n with hy
  have hy0 : 0 ≤ y := div_nonneg (hnn _) (hnn _)
  have hyq : y ≤ q := by
    rw [hy, div_le_iff₀ hvn]
    have := hv.pair (i := 2) (j := n) (by norm_num) (by omega)
    rw [hv1, one_mul, show 2 + n - 1 = n + 1 by omega] at this
    linarith
  have hvn1 : v (n + 1) = y * v n := by rw [hy]; field_simp
  have hvn2 : v (n + 2) ≤ y ^ 2 * v n := by
    have hlc := hv.2.1 n
    rw [show n + 2 = n + 2 from rfl, show n + 1 = n + 1 from rfl] at hlc
    rw [hvn1] at hlc
    have : v (n + 2) * v n ≤ (y ^ 2 * v n) * v n := by nlinarith
    exact le_of_mul_le_mul_right this hvn
  -- upper bound for `Φ_{n+2}(ℓ)`
  have hT : PhiQ r t τ ℓ (n + 2) v ≤ v n * TQ n r t τ ℓ y := by
    unfold PhiQ TQ
    rw [show n + 2 - 1 = n + 1 by omega, show n + 2 - 2 = n by omega, hvn1]
    push_cast
    rw [show ℓ + ((n : ℝ) + 2) - 1 = ℓ + n + 1 by ring, show ℓ + ((n : ℝ) + 2) = ℓ + n + 2 by ring]
    have := mul_le_mul_of_nonneg_left hvn2 (hρ (ℓ + n + 2) (by linarith))
    linear_combination this
  -- lower bound for `Φ_n(ℓ+1)`
  have hL : v n * LQ n r t τ ℓ z q y ≤ PhiQ r t τ (ℓ + 1) n (fun k => v k + v (k + 1)) := by
    unfold PhiQ LQ
    split_ifs with h2
    · subst h2
      simp only [show (2 : ℕ) - 1 = 1 from rfl, show (2 : ℕ) - 2 = 0 from rfl, show (2 : ℕ) + 1 = 3 from rfl,
        show (1 : ℕ) + 1 = 2 from rfl, show (0 : ℕ) + 1 = 1 from rfl]
      rw [hv1, show v 3 = y * v 2 from hvn1]
      push_cast
      rw [show ℓ + 1 + (2 : ℝ) = ℓ + 3 by ring, show ℓ + 3 - 1 = ℓ + 2 by ring]
      have hq' : q ≠ 0 := hq0.ne'
      apply le_of_eq
      field_simp
      ring
    · have hn3 : 3 ≤ n := by omega
      -- `v_{n-1} ≥ v_n / q`, `v_{n-2} ≥ v_{n-1}/q`
      have p1 := hv.pair (i := 2) (j := n - 1) (by norm_num) (by omega)
      rw [hv1, one_mul, show 2 + (n - 1) - 1 = n by omega] at p1
      have p2 := hv.pair (i := 2) (j := n - 2) (by norm_num) (by omega)
      rw [hv1, one_mul, show 2 + (n - 2) - 1 = n - 1 by omega] at p2
      have hm1 : v n / q ≤ v (n - 1) := by rw [div_le_iff₀ hq0]; linarith
      have hm2 : v n / q ^ 2 ≤ v (n - 2) := by
        have : v (n - 1) / q ≤ v (n - 2) := by rw [div_le_iff₀ hq0]; linarith
        have : v n / q ^ 2 = (v n / q) / q := by field_simp
        rw [this]; exact le_trans (div_le_div_of_nonneg_right hm1 hq0.le) ‹_›
      simp only [show n - 1 + 1 = n by omega, show n - 2 + 1 = n - 1 by omega]
      rw [hvn1, show ℓ + 1 + (n : ℝ) = ℓ + n + 1 by ring, show ℓ + n + 1 - 1 = ℓ + n by ring]
      have hρ' := hρ (ℓ + n + 1) (by linarith)
      have hd' := hd (ℓ + n) (by linarith)
      have hc : 0 ≤ (n : ℝ) * (n - 1) / 2 := div_nonneg (mul_nonneg (by linarith) (by linarith)) (by norm_num)
      have k1 : (n : ℝ) * drhoQ t τ (ℓ + n) * (v n * (1 + 1 / q)) ≤ (n : ℝ) * drhoQ t τ (ℓ + n) * (v (n - 1) + v n) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        have : v n * (1 + 1 / q) = v n + v n / q := by field_simp
        rw [this]; linarith
      have k2 : (n : ℝ) * (n - 1) / 2 * τ * (v n * (1 / q + 1 / q ^ 2)) ≤
          (n : ℝ) * (n - 1) / 2 * τ * (v (n - 2) + v (n - 1)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        have : v n * (1 / q + 1 / q ^ 2) = v n / q + v n / q ^ 2 := by field_simp
        rw [this]; linarith
      nlinarith [k1, k2]
  -- combine with `𝓕(y) ≥ 0`
  have hF := FQ_nonneg_y hn hr ht hτ hℓ hq0 (hnn 0) hz hzq hy0 hyq
  have hPhi2 : PhiQ r t τ ℓ 2 v = A2Q r t τ ℓ q + τ * z := by
    unfold PhiQ A2Q
    simp only [show (2 : ℕ) - 1 = 1 from rfl, show (2 : ℕ) - 2 = 0 from rfl]
    rw [hv1]; push_cast
    have : ℓ + 2 - 1 = ℓ + 1 := by ring
    rw [this]; ring
  have hK : 0 ≤ ((n : ℝ) + 1) * (n + 2) * PhiQ r t τ ℓ 2 v := mul_nonneg (by positivity) (hPhi ℓ 2 v hℓ (by norm_num) hnn)
  have hLn : 0 ≤ 8 * ((n : ℝ) - 1) * rhoQ r t τ (ℓ + 1) * (z + 1) := by
    have : 0 ≤ (n : ℝ) - 1 := by linarith
    have := hρ (ℓ + 1) (by linarith)
    have := hnn 0
    positivity
  have c1 := mul_le_mul_of_nonneg_left hL hK
  have c2 := mul_le_mul_of_nonneg_left hT hLn
  have eF : v n * FQ n r t τ ℓ z q y = ((n : ℝ) + 1) * (n + 2) * PhiQ r t τ ℓ 2 v * (v n * LQ n r t τ ℓ z q y) -
      8 * ((n : ℝ) - 1) * rhoQ r t τ (ℓ + 1) * (z + 1) * (v n * TQ n r t τ ℓ y) := by
    unfold FQ; rw [hPhi2]; ring
  have := mul_nonneg hvn.le hF
  rw [hv1] at *
  nlinarith [c1, c2, eF, this]


theorem PhiQ_div (r t τ base : ℝ) (k : ℕ) (v : ℕ → ℝ) (c : ℝ) :
    PhiQ r t τ base k (fun i => v i / c) = PhiQ r t τ base k v / c := by
  unfold PhiQ; ring

/-- **The weighted `B`-detour** (paper, eq. `quad-B`) for a log-concave sequence with `v₀ ≤ ℓ v₁`. -/
theorem quadB_seq {v : ℕ → ℝ} (hv : LCNZ v) (hv1 : 0 < v 1) {n : ℕ} (hn : 2 ≤ n) {r t τ ℓ : ℝ}
    (hr : 0 < r) (ht : 0 ≤ t) (hτ : 0 ≤ τ) (hℓ : 0 ≤ ℓ) (hz : v 0 ≤ ℓ * v 1) :
    8 * ((n : ℝ) - 1) * rhoQ r t τ (ℓ + 1) * (v 0 + v 1) * PhiQ r t τ ℓ (n + 2) v ≤
      ((n : ℝ) + 1) * (n + 2) * PhiQ r t τ ℓ 2 v * PhiQ r t τ (ℓ + 1) n (fun k => v k + v (k + 1)) := by
  set w : ℕ → ℝ := fun i => v i / v 1 with hw
  have hwl : LCNZ w := hv.scale hv1
  have hw1 : w 1 = 1 := by simp [hw, hv1.ne']
  have hwz : w 0 ≤ ℓ := by simp only [hw]; rw [div_le_iff₀ hv1]; exact hz
  have h := quadB_norm hwl hw1 hn hr ht hτ hℓ hwz
  have e1 : PhiQ r t τ ℓ (n + 2) w = PhiQ r t τ ℓ (n + 2) v / v 1 := PhiQ_div _ _ _ _ _ _ _
  have e2 : PhiQ r t τ ℓ 2 w = PhiQ r t τ ℓ 2 v / v 1 := PhiQ_div _ _ _ _ _ _ _
  have e3 : PhiQ r t τ (ℓ + 1) n (fun k => w k + w (k + 1)) =
      PhiQ r t τ (ℓ + 1) n (fun k => v k + v (k + 1)) / v 1 := by
    rw [← PhiQ_div]; congr 1; funext k; simp only [hw]; ring
  have e4 : w 0 + w 1 = (v 0 + v 1) / v 1 := by simp only [hw]; field_simp
  rw [e1, e2, e3, e4] at h
  have hsq : 0 < v 1 ^ 2 := by positivity
  have := mul_le_mul_of_nonneg_left h hsq.le
  have l : v 1 ^ 2 * (8 * ((n : ℝ) - 1) * rhoQ r t τ (ℓ + 1) * ((v 0 + v 1) / v 1) * (PhiQ r t τ ℓ (n + 2) v / v 1)) =
      8 * ((n : ℝ) - 1) * rhoQ r t τ (ℓ + 1) * (v 0 + v 1) * PhiQ r t τ ℓ (n + 2) v := by field_simp
  have rr : v 1 ^ 2 * (((n : ℝ) + 1) * (n + 2) * (PhiQ r t τ ℓ 2 v / v 1) *
      (PhiQ r t τ (ℓ + 1) n (fun k => v k + v (k + 1)) / v 1)) =
      ((n : ℝ) + 1) * (n + 2) * PhiQ r t τ ℓ 2 v * PhiQ r t τ (ℓ + 1) n (fun k => v k + v (k + 1)) := by field_simp
  linarith

end Szkraw
