import Szkraw.VRQuadKey

/-!
# Theorem 8.11: the polynomial certificate (paper, eq. `quad-cert`)

For an integer `n ≥ 2` and reals `h ≥ 1`, `p, τ ≥ 0`, `s ≥ (h-1)τ`, with
`A = p + (2h-1)s + h²τ`, `B = p + nh(s+τ) + C(n,2)h²τ`, `C = p + ((n+2)h-1)s + C(n+2,2)h²τ`:
`(n+1)(n+2) A B - 8(n-1) p C ≥ 0`.
-/

namespace Szkraw

/-- `K_n A B - L_n p C` of the certificate, with `n` real. -/
noncomputable def certE (n h p τ s : ℝ) : ℝ :=
  (n + 1) * (n + 2) * (p + (2 * h - 1) * s + h ^ 2 * τ) *
      (p + n * h * (s + τ) + n * (n - 1) / 2 * h ^ 2 * τ) -
    8 * (n - 1) * p * (p + ((n + 2) * h - 1) * s + (n + 2) * (n + 1) / 2 * h ^ 2 * τ)

/-- The value at `s = (h-1)τ`: `a_n p² + C_n(h) p τ + D_n(h) τ²`. -/
noncomputable def certBase (n h p τ : ℝ) : ℝ :=
  (n ^ 2 - 5 * n + 10) * p ^ 2 +
    (h ^ 2 * (n ^ 4 - 4 * n ^ 3 - 21 * n ^ 2 + 12 * n + 60) + h * (10 * n ^ 2 + 14 * n - 60) +
      2 * (n ^ 2 - 5 * n + 10)) / 2 * p * τ +
    h ^ 2 * n * (n + 1) ^ 2 * (n + 2) * (3 * h ^ 2 - 3 * h + 1) / 2 * τ ^ 2

theorem certE_split (n h p τ σ : ℝ) :
    certE n h p τ ((h - 1) * τ + σ) = certBase n h p τ +
      σ ^ 2 * (h * n * (2 * h - 1) * (n + 1) * (n + 2)) +
      σ * p * ((n ^ 2 - 5 * n + 10) * (h * n + 2 * h - 1)) +
      σ * τ * (h * n * (n + 1) * (n + 2) * (2 * h ^ 2 * n + 8 * h ^ 2 - h * n - 7 * h + 2) / 2) := by
  unfold certE certBase; ring

theorem certBase_nonneg {n : ℕ} (hn : 2 ≤ n) {h p τ : ℝ} (hh : 1 ≤ h) (hp : 0 ≤ p) (hτ : 0 ≤ τ) :
    0 ≤ certBase n h p τ := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have ha : 0 < (n : ℝ) ^ 2 - 5 * n + 10 := by nlinarith [sq_nonneg ((n : ℝ) - 5 / 2)]
  have hD : 0 ≤ h ^ 2 * n * (n + 1) ^ 2 * (n + 2) * (3 * h ^ 2 - 3 * h + 1) / 2 := by
    have : 0 ≤ 3 * h ^ 2 - 3 * h + 1 := by nlinarith [sq_nonneg (h - 1 / 2)]
    positivity
  rcases Nat.lt_or_ge n 7 with h7 | h7
  · -- `n ∈ {2,…,6}`: square completion, `4 a_n D_n - C_n²` has positive coefficients in `v = h - 1`
    obtain ⟨v, hv, rfl⟩ : ∃ v : ℝ, 0 ≤ v ∧ h = v + 1 := ⟨h - 1, by linarith, by ring⟩
    have key : ∀ (a C D : ℝ), 0 < a → 0 ≤ 4 * a * D - C ^ 2 → 0 ≤ a * p ^ 2 + C * p * τ + D * τ ^ 2 := by
      intro a C D ha hdisc
      have : 4 * a * (a * p ^ 2 + C * p * τ + D * τ ^ 2) = (2 * a * p + C * τ) ^ 2 + (4 * a * D - C ^ 2) * τ ^ 2 := by
        ring
      have h4 : 0 ≤ 4 * a * (a * p ^ 2 + C * p * τ + D * τ ^ 2) := by
        rw [this]; exact add_nonneg (sq_nonneg _) (mul_nonneg hdisc (sq_nonneg _))
      by_contra hc
      push Not at hc
      have := mul_neg_of_pos_of_neg (by linarith : (0 : ℝ) < 4 * a) hc
      linarith
    unfold certBase
    interval_cases n <;> norm_num <;>
      refine key _ _ _ (by norm_num) ?_ <;> ring_nf <;> positivity
  · -- `n ≥ 7`: all three coefficients are nonnegative
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 7 := ⟨n - 7, by omega⟩
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have hU : 0 ≤ ((k + 7 : ℕ) : ℝ) ^ 4 - 4 * ((k + 7 : ℕ) : ℝ) ^ 3 - 21 * ((k + 7 : ℕ) : ℝ) ^ 2 +
        12 * ((k + 7 : ℕ) : ℝ) + 60 := by
      push_cast; nlinarith [pow_nonneg hk 2, pow_nonneg hk 3, pow_nonneg hk 4]
    have hL : 0 ≤ 10 * ((k + 7 : ℕ) : ℝ) ^ 2 + 14 * ((k + 7 : ℕ) : ℝ) - 60 := by push_cast; nlinarith
    unfold certBase
    have h1 : 0 ≤ (((k + 7 : ℕ) : ℝ) ^ 2 - 5 * ((k + 7 : ℕ) : ℝ) + 10) * p ^ 2 := mul_nonneg ha.le (sq_nonneg _)
    have h2 : 0 ≤ (h ^ 2 * (((k + 7 : ℕ) : ℝ) ^ 4 - 4 * ((k + 7 : ℕ) : ℝ) ^ 3 - 21 * ((k + 7 : ℕ) : ℝ) ^ 2 +
        12 * ((k + 7 : ℕ) : ℝ) + 60) + h * (10 * ((k + 7 : ℕ) : ℝ) ^ 2 + 14 * ((k + 7 : ℕ) : ℝ) - 60) +
        2 * (((k + 7 : ℕ) : ℝ) ^ 2 - 5 * ((k + 7 : ℕ) : ℝ) + 10)) / 2 * p * τ := by
      have : 0 ≤ h := by linarith
      positivity
    have h3 : 0 ≤ h ^ 2 * ((k + 7 : ℕ) : ℝ) * (((k + 7 : ℕ) : ℝ) + 1) ^ 2 * (((k + 7 : ℕ) : ℝ) + 2) *
        (3 * h ^ 2 - 3 * h + 1) / 2 * τ ^ 2 := mul_nonneg hD (sq_nonneg _)
    linarith

/-- **The certificate** (paper, eq. `quad-cert`). -/
theorem cert_nonneg {n : ℕ} (hn : 2 ≤ n) {h p τ s : ℝ} (hh : 1 ≤ h) (hp : 0 ≤ p) (hτ : 0 ≤ τ)
    (hs : (h - 1) * τ ≤ s) : 0 ≤ certE n h p τ s := by
  obtain ⟨σ, hσ, rfl⟩ : ∃ σ, 0 ≤ σ ∧ s = (h - 1) * τ + σ := ⟨s - (h - 1) * τ, by linarith, by ring⟩
  rw [certE_split]
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have h0 := certBase_nonneg hn hh hp hτ
  have c1 : 0 ≤ σ ^ 2 * (h * n * (2 * h - 1) * (n + 1) * (n + 2)) := by
    have : 0 ≤ 2 * h - 1 := by linarith
    have : 0 ≤ h := by linarith
    positivity
  have c2 : 0 ≤ σ * p * (((n : ℝ) ^ 2 - 5 * n + 10) * (h * n + 2 * h - 1)) := by
    have : 0 ≤ (n : ℝ) ^ 2 - 5 * n + 10 := by nlinarith [sq_nonneg ((n : ℝ) - 5 / 2)]
    have : 0 ≤ h * n + 2 * h - 1 := by nlinarith
    positivity
  have c3 : 0 ≤ σ * τ * (h * n * (n + 1) * (n + 2) * (2 * h ^ 2 * n + 8 * h ^ 2 - h * n - 7 * h + 2) / 2) := by
    have : 0 ≤ 2 * h ^ 2 * n + 8 * h ^ 2 - h * n - 7 * h + 2 := by
      nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ h) (by linarith : (0 : ℝ) ≤ 2 * h - 1), sq_nonneg (h - 1)]
    have : 0 ≤ h := by linarith
    positivity
  linarith

end Szkraw
