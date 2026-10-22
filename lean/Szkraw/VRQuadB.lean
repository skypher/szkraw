import Szkraw.VRQuadCert

/-!
# Theorem 8.11: the weighted `B`-detour at the geometric configuration (paper, proof of eq. `quad-B`)

Normalized configuration `u₀ = z`, `u₁ = 1`, `u₂ = q`, `y = u_{n+1}/u_n`. With
`ρ(x) = r + t x + τ x(x-1)/2`, `𝓕(y) = K_n φ₂ 𝓛(y) - L_n ρ(ℓ+1)(z+1) 𝓣(y)`. We show `𝓕(q) ≥ 0` for
`0 ≤ z ≤ min(ℓ, 1/q)`: monotone reduction to `z = min(ℓ, 1/q)`, then the certificate (`z = 1/q`)
or the expansion in `w = 1/q - ℓ` (`z = ℓ`).
-/

namespace Szkraw

/-- `ρ(x) = r + t x + τ C(x,2)` for real `x`. -/
noncomputable def rhoQ (r t τ x : ℝ) : ℝ := r + t * x + τ * (x * (x - 1) / 2)

/-- `Δρ(x) = t + τ x`. -/
noncomputable def drhoQ (t τ x : ℝ) : ℝ := t + τ * x

/-- `A₂ = ρ(ℓ+2) q + 2 Δρ(ℓ+1)`, so that `φ₂(ℓ) = A₂ + τ z` (normalized). -/
noncomputable def A2Q (r t τ ℓ q : ℝ) : ℝ := rhoQ r t τ (ℓ + 2) * q + 2 * drhoQ t τ (ℓ + 1)

/-- `𝓛(y)`, the lower bound for `φ_n(ℓ+1)/u_n` (exact for `n = 2`). -/
noncomputable def LQ (n : ℕ) (r t τ ℓ z q y : ℝ) : ℝ :=
  if n = 2 then rhoQ r t τ (ℓ + 3) * (1 + y) + 2 * drhoQ t τ (ℓ + 2) * (1 + 1 / q) + τ * (z + 1) / q
  else rhoQ r t τ (ℓ + n + 1) * (1 + y) + n * drhoQ t τ (ℓ + n) * (1 + 1 / q) +
    (n : ℝ) * (n - 1) / 2 * τ * (1 / q + 1 / q ^ 2)

/-- `𝓣(y)`, the upper bound for `φ_{n+2}(ℓ)/u_n`. -/
noncomputable def TQ (n : ℕ) (r t τ ℓ y : ℝ) : ℝ :=
  rhoQ r t τ (ℓ + n + 2) * y ^ 2 + (n + 2) * drhoQ t τ (ℓ + n + 1) * y + ((n : ℝ) + 2) * (n + 1) / 2 * τ

/-- `𝓕(y)`. -/
noncomputable def FQ (n : ℕ) (r t τ ℓ z q y : ℝ) : ℝ :=
  ((n : ℝ) + 1) * (n + 2) * (A2Q r t τ ℓ q + τ * z) * LQ n r t τ ℓ z q y -
    8 * ((n : ℝ) - 1) * rhoQ r t τ (ℓ + 1) * (z + 1) * TQ n r t τ ℓ y

/-- Case `z = 1/q`: `𝓕(q) = q(1+q) (K A B - L p C)` with `h = 1 + 1/q`, `s = t + τℓ`. -/
theorem FQ_inv (n : ℕ) (r t τ ℓ q : ℝ) (hq : q ≠ 0) (hq1 : 1 + q ≠ 0) :
    FQ n r t τ ℓ (1 / q) q q = q * (1 + q) * certE n (1 + 1 / q) (rhoQ r t τ (ℓ + 1)) τ (t + τ * ℓ) := by
  unfold FQ LQ TQ A2Q certE rhoQ drhoQ
  split_ifs with h2
  · subst h2; field_simp; ring
  · field_simp; ring


/-- `E_n(w) = K (h₀+w) A B - L h₀ p C` with `h = ℓ + 1 + w`, `s = t + τℓ`, `p = ρ(ℓ+1)`; for `n = 2`
minus `12 A τ w (ℓ+w)²`. -/
noncomputable def EQ (n : ℕ) (r t τ ℓ w : ℝ) : ℝ :=
  let p := rhoQ r t τ (ℓ + 1)
  let s := t + τ * ℓ
  let h := ℓ + 1 + w
  let A := p + (2 * h - 1) * s + τ * ((ℓ + 2) * h - ℓ - 1)
  let B := p + n * h * (s + τ) + (n : ℝ) * (n - 1) / 2 * h ^ 2 * τ
  let C := p + ((n + 2) * h - 1) * s + ((n : ℝ) + 2) * (n + 1) / 2 * h ^ 2 * τ
  ((n : ℝ) + 1) * (n + 2) * h * A * B - 8 * ((n : ℝ) - 1) * (ℓ + 1) * p * C -
    (if n = 2 then 12 * A * τ * w * (ℓ + w) ^ 2 else 0)

/-- Case `z = ℓ`: `𝓕(q) = q² E_n(w)` with `q = 1/(ℓ+w)`. -/
theorem FQ_ell (n : ℕ) (r t τ ℓ w : ℝ) (hw : ℓ + w ≠ 0) :
    FQ n r t τ ℓ ℓ (1 / (ℓ + w)) (1 / (ℓ + w)) = (1 / (ℓ + w)) ^ 2 * EQ n r t τ ℓ w := by
  unfold FQ LQ TQ A2Q EQ rhoQ drhoQ
  split_ifs with h2
  · subst h2; field_simp; ring
  · field_simp; ring


theorem EQ_zero (n : ℕ) (r t τ ℓ : ℝ) :
    EQ n r t τ ℓ 0 = (ℓ + 1) * certE n (ℓ + 1) (rhoQ r t τ (ℓ + 1)) τ (t + τ * ℓ) := by
  unfold EQ certE
  split_ifs <;> simp only [mul_zero, zero_mul, sub_zero] <;> ring

/-- The expansion of `E_n(w)` for `n ≥ 3`. -/
theorem EQ_expand {n : ℕ} (hn : n ≠ 2) (r t τ ℓ w : ℝ) :
    let p := rhoQ r t τ (ℓ + 1)
    let s := t + τ * ℓ
    let h0 := ℓ + 1
    let K := ((n : ℝ) + 1) * (n + 2)
    let Ab := (2 * h0 - 1) * s + h0 ^ 2 * τ
    let Bb := n * h0 * (s + τ) + (n : ℝ) * (n - 1) / 2 * h0 ^ 2 * τ
    let η := 2 * s + (ℓ + 2) * τ
    let θ := n * (s + τ) + n * (n - 1) * τ * h0
    let ε := (n : ℝ) * (n - 1) / 2 * τ
    let a1 := ((n : ℝ) + 2) * (2 * ℓ * (n ^ 2 - n + 6) + 2 * n ^ 2 - 3 * n + 11)
    let a2 := K * (n + 2)
    let b1 := ((n : ℝ) + 2) / 2 * (ℓ ^ 2 * (3 * n ^ 3 - 12 * n ^ 2 - 3 * n + 44) +
      ℓ * (6 * n ^ 3 - 24 * n ^ 2 + 2 * n + 64) + (3 * n ^ 3 - 12 * n ^ 2 + 7 * n + 22))
    let b2 := K / 2 * (3 * n * (n - 3) * (ℓ + 1) + 14 * ℓ + 12)
    EQ n r t τ ℓ w = EQ n r t τ ℓ 0 +
      (K * p ^ 2 + p * (a1 * t + b1 * τ) + K * (Ab * Bb + h0 * (η * Bb + Ab * θ))) * w +
      (p * (a2 * t + b2 * τ) + K * (η * Bb + Ab * θ + h0 * (η * θ + Ab * ε))) * w ^ 2 +
      K * (η * θ + (p + Ab) * ε + h0 * η * ε) * w ^ 3 + K * η * ε * w ^ 4 := by
  intro p s h0 K Ab Bb η θ ε a1 a2 b1 b2
  simp only [EQ, if_neg hn, p, s, h0, K, Ab, Bb, η, θ, ε, a1, a2, b1, b2, rhoQ]
  ring

/-- The expansion of `E_2(w)`. -/
theorem EQ_expand_two (r t τ ℓ w : ℝ) :
    let p := rhoQ r t τ (ℓ + 1)
    let s := t + τ * ℓ
    EQ 2 r t τ ℓ w = EQ 2 r t τ ℓ 0 +
      (12 * p ^ 2 + 4 * (16 * ℓ + 13) * p * t + 8 * (ℓ + 1) * (2 * ℓ + 3) * p * τ +
        48 * (ℓ + 1) * (3 * ℓ + 2) * t ^ 2 + 12 * (36 * ℓ ^ 3 + 92 * ℓ ^ 2 + 76 * ℓ + 21) * t * τ +
        12 * (27 * ℓ ^ 4 + 93 * ℓ ^ 3 + 114 * ℓ ^ 2 + 62 * ℓ + 13) * τ ^ 2) * w +
      (48 * p * t + 12 * (2 * ℓ + 3) * p * τ + 24 * (6 * ℓ + 5) * t ^ 2 +
        12 * (36 * ℓ ^ 2 + 67 * ℓ + 29) * t * τ + 12 * (27 * ℓ ^ 3 + 78 * ℓ ^ 2 + 67 * ℓ + 19) * τ ^ 2) * w ^ 2 +
      12 * (2 * s + (ℓ + 2) * τ) * (2 * t + (3 * ℓ + 5) * τ) * w ^ 3 := by
  intro p s
  simp only [EQ, if_pos rfl, p, s, rhoQ]
  push_cast
  ring


theorem rhoQ_pos {r t τ x : ℝ} (hr : 0 < r) (ht : 0 ≤ t) (hτ : 0 ≤ τ) (hx : 1 ≤ x) : 0 < rhoQ r t τ x := by
  unfold rhoQ
  have : 0 ≤ x * (x - 1) / 2 := div_nonneg (mul_nonneg (by linarith) (by linarith)) (by norm_num)
  have : 0 ≤ t * x := mul_nonneg ht (by linarith)
  nlinarith [mul_nonneg hτ this]

theorem EQ_nonneg {n : ℕ} (hn : 2 ≤ n) {r t τ ℓ w : ℝ} (hr : 0 < r) (ht : 0 ≤ t) (hτ : 0 ≤ τ) (hℓ : 0 ≤ ℓ)
    (hw : 0 ≤ w) : 0 ≤ EQ n r t τ ℓ w := by
  have hp : 0 < rhoQ r t τ (ℓ + 1) := rhoQ_pos hr ht hτ (by linarith)
  have h0 : 0 ≤ EQ n r t τ ℓ 0 := by
    rw [EQ_zero]
    exact mul_nonneg (by linarith) (cert_nonneg hn (by linarith) hp.le hτ (by nlinarith))
  set p := rhoQ r t τ (ℓ + 1) with hpdef
  have hs : 0 ≤ t + τ * ℓ := by positivity
  by_cases h2 : n = 2
  · subst h2
    rw [EQ_expand_two]
    have : 0 ≤ (12 * p ^ 2 + 4 * (16 * ℓ + 13) * p * t + 8 * (ℓ + 1) * (2 * ℓ + 3) * p * τ +
        48 * (ℓ + 1) * (3 * ℓ + 2) * t ^ 2 + 12 * (36 * ℓ ^ 3 + 92 * ℓ ^ 2 + 76 * ℓ + 21) * t * τ +
        12 * (27 * ℓ ^ 4 + 93 * ℓ ^ 3 + 114 * ℓ ^ 2 + 62 * ℓ + 13) * τ ^ 2) * w := by positivity
    have : 0 ≤ (48 * p * t + 12 * (2 * ℓ + 3) * p * τ + 24 * (6 * ℓ + 5) * t ^ 2 +
        12 * (36 * ℓ ^ 2 + 67 * ℓ + 29) * t * τ + 12 * (27 * ℓ ^ 3 + 78 * ℓ ^ 2 + 67 * ℓ + 19) * τ ^ 2) * w ^ 2 := by
      positivity
    have : 0 ≤ 12 * (2 * (t + τ * ℓ) + (ℓ + 2) * τ) * (2 * t + (3 * ℓ + 5) * τ) * w ^ 3 := by positivity
    linarith
  · have hn3 : (3 : ℝ) ≤ n := by exact_mod_cast (show 3 ≤ n by omega)
    rw [EQ_expand h2]
    obtain ⟨k, hk, hkn⟩ : ∃ k : ℝ, 0 ≤ k ∧ (n : ℝ) = k + 3 := ⟨n - 3, by linarith, by ring⟩
    have hP : 0 ≤ 3 * (n : ℝ) ^ 3 - 12 * n ^ 2 - 3 * n + 44 := by rw [hkn]; nlinarith [pow_nonneg hk 2, pow_nonneg hk 3]
    have hQ : 0 ≤ 6 * (n : ℝ) ^ 3 - 24 * n ^ 2 + 2 * n + 64 := by rw [hkn]; nlinarith [pow_nonneg hk 2, pow_nonneg hk 3]
    have hR : 0 ≤ 3 * (n : ℝ) ^ 3 - 12 * n ^ 2 + 7 * n + 22 := by rw [hkn]; nlinarith [pow_nonneg hk 2, pow_nonneg hk 3]
    have hA1 : 0 ≤ 2 * ℓ * ((n : ℝ) ^ 2 - n + 6) + 2 * n ^ 2 - 3 * n + 11 := by nlinarith
    have hB2 : 0 ≤ 3 * (n : ℝ) * (n - 3) * (ℓ + 1) + 14 * ℓ + 12 := by
      have : 0 ≤ (n : ℝ) * (n - 3) := mul_nonneg (by linarith) (by linarith)
      nlinarith
    have hnn : ∀ x : ℝ, 0 ≤ x → 0 ≤ (n : ℝ) * x := fun x hx => mul_nonneg (by linarith) hx
    have hn1 : (0 : ℝ) ≤ (n : ℝ) - 1 := by linarith
    have hAb : 0 ≤ (2 * (ℓ + 1) - 1) * (t + τ * ℓ) + (ℓ + 1) ^ 2 * τ := by
      have : 0 ≤ 2 * (ℓ + 1) - 1 := by linarith
      positivity
    have hBb : 0 ≤ (n : ℝ) * (ℓ + 1) * ((t + τ * ℓ) + τ) + (n : ℝ) * (n - 1) / 2 * (ℓ + 1) ^ 2 * τ := by positivity
    have hη : 0 ≤ 2 * (t + τ * ℓ) + (ℓ + 2) * τ := by positivity
    have hθ : 0 ≤ (n : ℝ) * ((t + τ * ℓ) + τ) + n * (n - 1) * τ * (ℓ + 1) := by positivity
    have hε : 0 ≤ (n : ℝ) * (n - 1) / 2 * τ := by positivity
    have hK : 0 ≤ ((n : ℝ) + 1) * (n + 2) := by positivity
    have t1 : 0 ≤ (((n : ℝ) + 1) * (n + 2) * p ^ 2 +
        p * (((n : ℝ) + 2) * (2 * ℓ * (n ^ 2 - n + 6) + 2 * n ^ 2 - 3 * n + 11) * t +
          ((n : ℝ) + 2) / 2 * (ℓ ^ 2 * (3 * n ^ 3 - 12 * n ^ 2 - 3 * n + 44) +
            ℓ * (6 * n ^ 3 - 24 * n ^ 2 + 2 * n + 64) + (3 * n ^ 3 - 12 * n ^ 2 + 7 * n + 22)) * τ) +
        ((n : ℝ) + 1) * (n + 2) * (((2 * (ℓ + 1) - 1) * (t + τ * ℓ) + (ℓ + 1) ^ 2 * τ) *
          ((n : ℝ) * (ℓ + 1) * ((t + τ * ℓ) + τ) + (n : ℝ) * (n - 1) / 2 * (ℓ + 1) ^ 2 * τ) +
          (ℓ + 1) * ((2 * (t + τ * ℓ) + (ℓ + 2) * τ) *
            ((n : ℝ) * (ℓ + 1) * ((t + τ * ℓ) + τ) + (n : ℝ) * (n - 1) / 2 * (ℓ + 1) ^ 2 * τ) +
            ((2 * (ℓ + 1) - 1) * (t + τ * ℓ) + (ℓ + 1) ^ 2 * τ) *
              ((n : ℝ) * ((t + τ * ℓ) + τ) + n * (n - 1) * τ * (ℓ + 1))))) * w := by
      have : 0 ≤ ℓ ^ 2 * (3 * (n : ℝ) ^ 3 - 12 * n ^ 2 - 3 * n + 44) +
          ℓ * (6 * n ^ 3 - 24 * n ^ 2 + 2 * n + 64) + (3 * n ^ 3 - 12 * n ^ 2 + 7 * n + 22) := by positivity
      positivity
    have t2 : 0 ≤ (p * (((n : ℝ) + 1) * (n + 2) * (n + 2) * t +
        ((n : ℝ) + 1) * (n + 2) / 2 * (3 * n * (n - 3) * (ℓ + 1) + 14 * ℓ + 12) * τ) +
        ((n : ℝ) + 1) * (n + 2) * ((2 * (t + τ * ℓ) + (ℓ + 2) * τ) *
          ((n : ℝ) * (ℓ + 1) * ((t + τ * ℓ) + τ) + (n : ℝ) * (n - 1) / 2 * (ℓ + 1) ^ 2 * τ) +
          ((2 * (ℓ + 1) - 1) * (t + τ * ℓ) + (ℓ + 1) ^ 2 * τ) *
            ((n : ℝ) * ((t + τ * ℓ) + τ) + n * (n - 1) * τ * (ℓ + 1)) +
          (ℓ + 1) * ((2 * (t + τ * ℓ) + (ℓ + 2) * τ) * ((n : ℝ) * ((t + τ * ℓ) + τ) + n * (n - 1) * τ * (ℓ + 1)) +
            ((2 * (ℓ + 1) - 1) * (t + τ * ℓ) + (ℓ + 1) ^ 2 * τ) * ((n : ℝ) * (n - 1) / 2 * τ)))) * w ^ 2 := by
      positivity
    have t3 : 0 ≤ ((n : ℝ) + 1) * (n + 2) * ((2 * (t + τ * ℓ) + (ℓ + 2) * τ) *
        ((n : ℝ) * ((t + τ * ℓ) + τ) + n * (n - 1) * τ * (ℓ + 1)) +
        (p + ((2 * (ℓ + 1) - 1) * (t + τ * ℓ) + (ℓ + 1) ^ 2 * τ)) * ((n : ℝ) * (n - 1) / 2 * τ) +
        (ℓ + 1) * (2 * (t + τ * ℓ) + (ℓ + 2) * τ) * ((n : ℝ) * (n - 1) / 2 * τ)) * w ^ 3 := by positivity
    have t4 : 0 ≤ ((n : ℝ) + 1) * (n + 2) * (2 * (t + τ * ℓ) + (ℓ + 2) * τ) * ((n : ℝ) * (n - 1) / 2 * τ) * w ^ 4 := by
      positivity
    linarith


/-- Monotonicity in `z`: `𝓕(z)(Z+1) ≥ 𝓕(Z)(z+1)` for `0 ≤ z ≤ Z ≤ ℓ`. -/
theorem FQ_mono {n : ℕ} (hn : 2 ≤ n) {r t τ ℓ q z Z : ℝ} (hr : 0 < r) (ht : 0 ≤ t) (hτ : 0 ≤ τ) (hℓ : 0 ≤ ℓ)
    (hq : 0 < q) (hz : 0 ≤ z) (hzZ : z ≤ Z) (hZℓ : Z ≤ ℓ) :
    FQ n r t τ ℓ Z q q * (z + 1) ≤ FQ n r t τ ℓ z q q * (Z + 1) := by
  have hA2 : τ ≤ A2Q r t τ ℓ q := by
    unfold A2Q drhoQ
    have := (rhoQ_pos hr ht hτ (show (1 : ℝ) ≤ ℓ + 2 by linarith)).le
    nlinarith [mul_nonneg this hq.le]
  by_cases h2 : n = 2
  · subst h2
    set G2 := rhoQ r t τ (ℓ + 3) * q * (1 + q) + 2 * drhoQ t τ (ℓ + 2) * (1 + q) with hG2
    have e : FQ 2 r t τ ℓ z q q * (Z + 1) - FQ 2 r t τ ℓ Z q q * (z + 1) =
        ((2 : ℝ) + 1) * (2 + 2) / q * (Z - z) * (G2 * (A2Q r t τ ℓ q - τ) - τ ^ 2 * (z + 1) * (Z + 1)) := by
      have hLz : ∀ x : ℝ, LQ 2 r t τ ℓ x q q = (G2 + τ * (x + 1)) / q := by
        intro x; unfold LQ; rw [if_pos rfl, hG2]; field_simp; ring
      unfold FQ
      rw [hLz z, hLz Z]
      field_simp
      ring
    have hG2b : 2 * τ * (ℓ + 2) ≤ G2 := by
      have h1 := (rhoQ_pos hr ht hτ (show (1 : ℝ) ≤ ℓ + 3 by linarith)).le
      simp only [hG2, drhoQ]
      nlinarith [mul_nonneg (mul_nonneg h1 hq.le) (by linarith : (0 : ℝ) ≤ 1 + q), mul_nonneg ht hq.le,
        mul_nonneg hτ hq.le, mul_nonneg (mul_nonneg hτ hq.le) hℓ]
    have hA2b : τ * (2 * ℓ + 1) ≤ A2Q r t τ ℓ q - τ := by
      unfold A2Q drhoQ
      have := (rhoQ_pos hr ht hτ (show (1 : ℝ) ≤ ℓ + 2 by linarith)).le
      nlinarith [mul_nonneg this hq.le]
    have hprod : τ ^ 2 * (z + 1) * (Z + 1) ≤ G2 * (A2Q r t τ ℓ q - τ) := by
      have k1 : 2 * τ * (ℓ + 2) * (τ * (2 * ℓ + 1)) ≤ G2 * (A2Q r t τ ℓ q - τ) :=
        mul_le_mul hG2b hA2b (by positivity) (le_trans (by positivity) hG2b)
      have k2 : (z + 1) * (Z + 1) ≤ (ℓ + 1) ^ 2 := by nlinarith
      have k3 : τ ^ 2 * ((z + 1) * (Z + 1)) ≤ τ ^ 2 * (ℓ + 1) ^ 2 := mul_le_mul_of_nonneg_left k2 (sq_nonneg τ)
      have k4 : τ ^ 2 * (ℓ + 1) ^ 2 ≤ τ ^ 2 * (2 * (ℓ + 2) * (2 * ℓ + 1)) :=
        mul_le_mul_of_nonneg_left (by nlinarith) (sq_nonneg τ)
      have k5 : 2 * τ * (ℓ + 2) * (τ * (2 * ℓ + 1)) = τ ^ 2 * (2 * (ℓ + 2) * (2 * ℓ + 1)) := by ring
      have k6 : τ ^ 2 * (z + 1) * (Z + 1) = τ ^ 2 * ((z + 1) * (Z + 1)) := by ring
      linarith
    have : 0 ≤ ((2 : ℝ) + 1) * (2 + 2) / q * (Z - z) * (G2 * (A2Q r t τ ℓ q - τ) - τ ^ 2 * (z + 1) * (Z + 1)) :=
      mul_nonneg (mul_nonneg (by positivity) (by linarith)) (by linarith)
    linarith
  · have e : FQ n r t τ ℓ z q q * (Z + 1) - FQ n r t τ ℓ Z q q * (z + 1) =
        ((n : ℝ) + 1) * (n + 2) * LQ n r t τ ℓ z q q * (A2Q r t τ ℓ q - τ) * (Z - z) := by
      unfold FQ LQ
      simp only [if_neg h2]
      ring
    have hL : 0 ≤ LQ n r t τ ℓ z q q := by
      unfold LQ
      rw [if_neg h2]
      have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
      have h1 := (rhoQ_pos hr ht hτ (show (1 : ℝ) ≤ ℓ + n + 1 by linarith)).le
      have : 0 ≤ drhoQ t τ (ℓ + n) := by unfold drhoQ; positivity
      have : 0 ≤ (n : ℝ) - 1 := by linarith
      positivity
    have : 0 ≤ ((n : ℝ) + 1) * (n + 2) * LQ n r t τ ℓ z q q * (A2Q r t τ ℓ q - τ) * (Z - z) :=
      mul_nonneg (mul_nonneg (mul_nonneg (by positivity) hL) (by linarith)) (by linarith)
    linarith

/-- **`𝓕(q) ≥ 0`** for `0 ≤ z ≤ ℓ` and `z q ≤ 1`. -/
theorem FQ_nonneg {n : ℕ} (hn : 2 ≤ n) {r t τ ℓ q z : ℝ} (hr : 0 < r) (ht : 0 ≤ t) (hτ : 0 ≤ τ) (hℓ : 0 ≤ ℓ)
    (hq : 0 < q) (hz : 0 ≤ z) (hzℓ : z ≤ ℓ) (hzq : z * q ≤ 1) : 0 ≤ FQ n r t τ ℓ z q q := by
  have hZ : ∃ Z, z ≤ Z ∧ Z ≤ ℓ ∧ 0 ≤ FQ n r t τ ℓ Z q q := by
    by_cases hc : 1 ≤ ℓ * q
    · -- `Z = 1/q`
      refine ⟨1 / q, by rw [le_div_iff₀ hq]; linarith, by rw [div_le_iff₀ hq]; linarith, ?_⟩
      rw [FQ_inv n r t τ ℓ q hq.ne' (by linarith)]
      refine mul_nonneg (by positivity) (cert_nonneg hn ?_ (rhoQ_pos hr ht hτ (by linarith)).le hτ ?_)
      · have : 0 ≤ 1 / q := by positivity
        linarith
      · have : 1 / q ≤ ℓ := by rw [div_le_iff₀ hq]; linarith
        have : (1 + 1 / q - 1) * τ = τ * (1 / q) := by ring
        rw [this]; nlinarith [mul_le_mul_of_nonneg_left (show 1 / q ≤ ℓ from by rw [div_le_iff₀ hq]; linarith) hτ]
    · -- `Z = ℓ`, `w = 1/q - ℓ`
      push Not at hc
      refine ⟨ℓ, hzℓ, le_rfl, ?_⟩
      set w := 1 / q - ℓ with hw
      have hw0 : 0 ≤ w := by
        rw [hw, sub_nonneg, le_div_iff₀ hq]; linarith
      have hq' : q = 1 / (ℓ + w) := by rw [hw]; field_simp; ring
      have hlw : ℓ + w ≠ 0 := by
        have : 0 < 1 / q := by positivity
        rw [hw]; linarith
      rw [hq', FQ_ell n r t τ ℓ w hlw]
      exact mul_nonneg (by positivity) (EQ_nonneg hn hr ht hτ hℓ hw0)
  obtain ⟨Z, hzZ, hZℓ, hFZ⟩ := hZ
  have hm := FQ_mono hn hr ht hτ hℓ hq hz hzZ hZℓ
  have : 0 ≤ FQ n r t τ ℓ Z q q * (z + 1) := mul_nonneg hFZ (by linarith)
  have hZ1 : 0 < Z + 1 := by linarith
  by_contra hneg
  push Not at hneg
  have := mul_neg_of_neg_of_pos hneg hZ1
  linarith

end Szkraw
