import Szkraw.ParitySplit
import Szkraw.Parameters
import Szkraw.Normalization

/-!
# Corollary 7.9: identification of the component parameters

Under the hypotheses of Corollary 7.9 the even downward coefficients are `d_n = [n]_q/[N]_q`, the
normalized even component is the array (2.3) with parameters `(N, q, r)`, and for `N ≥ 2` the
normalized odd component is (2.3) with parameters `(N - 1, q, r/q)`, where `r = p_0/(1 - p_0)`.
In the Lean parametrization `geometricCoefficients N p q` of (2.3) the parameter `p` is `1/r`.
-/

namespace Szkraw

variable {N : ℕ} (v : Coefficients (2 * N)) (hv : Admissible v) (hb : ∀ i, i ≤ 2 * N → v.b i = 0)
  {p₀ q : ℝ} (hp : ParitySplit v p₀ q)
include hv hb hp

/-- `d_n = [n]_q / [N]_q`. -/
theorem ps_d_formula : ∀ n, n ≤ N → v.c (2 * n) = qInteger q n / qInteger q N := by
  have hN := hv.1
  have hq := hp.1
  have hQN : 0 < qInteger q N := qInteger_pos q hq N (by omega)
  -- `δ_n = q^{n-1} δ_1` and `d_n = δ_1 [n]_q`
  have hdelta : ∀ n, 1 ≤ n → n ≤ N → v.c (2 * n) - v.c (2 * (n - 1)) = q ^ (n - 1) * v.c 2 := by
    intro n h1 hn
    induction n with
    | zero => omega
    | succ n ih =>
      rw [show n + 1 - 1 = n by omega]
      rcases Nat.eq_zero_or_pos n with h0 | h0
      · subst h0; simp [hv.2.2.2.1]
      · have := hp.2.2.2 n h0 (by omega)
        rw [this, ih h0 (by omega), show q ^ n = q * q ^ (n - 1) by rw [← pow_succ']; congr 1; omega]
        ring
  have hd : ∀ n, n ≤ N → v.c (2 * n) = v.c 2 * qInteger q n := by
    intro n hn
    induction n with
    | zero => simp [qInteger, hv.2.2.2.1]
    | succ n ih =>
      have h1 := hdelta (n + 1) (by omega) hn
      rw [show n + 1 - 1 = n by omega] at h1
      rw [qInteger]
      linarith [ih (by omega)]
  have htop := ps_d_top v hv hb
  rw [hd N le_rfl] at htop
  intro n hn
  rw [hd n hn, eq_div_iff hQN.ne']
  linear_combination qInteger q n * htop

/-- The normalized even component is (2.3) with parameters `(N, q, r)`. -/
theorem ps_even_params :
    ∀ i, i ≤ N → (evenComp v).a i = (geometricCoefficients N ((1 - p₀) / p₀) q).a i ∧
      (evenComp v).b i = (geometricCoefficients N ((1 - p₀) / p₀) q).b i ∧
      (evenComp v).c i = (geometricCoefficients N ((1 - p₀) / p₀) q).c i := by
  have hN := hv.1
  have hq := hp.1
  have hQN : 0 < qInteger q N := qInteger_pos q hq N (by omega)
  have h1 := ps_p0_lt_one v hv hb hp
  have hpos := ps_p0_pos v hv hp
  have hq0 : 1 - p₀ ≠ 0 := by linarith
  have hd := ps_d_formula v hv hb hp
  intro i hi
  obtain ⟨eb, ec⟩ := ps_evenComp v hv hb hp i hi
  refine ⟨?_, ?_, ?_⟩
  · show (evenRaw v).a i / (evenRaw v).a 0 = q ^ i * qInteger q (N - i) / qInteger q N
    have hraw : ∀ n, n ≤ N → (evenRaw v).a n = (1 - v.c (2 * n)) * (1 - p₀) := by
      intro n hn
      show v.a (2 * n) * v.a (2 * n + 1) = _
      rw [ps_a_even v hv hb n hn]
      rcases Nat.lt_or_ge n N with h | h
      · rw [ps_a_odd v hv hb hp n (by omega)]
      · rw [show n = N by omega, ps_d_top v hv hb]; ring
    rw [hraw i hi, hraw 0 (by omega), Nat.mul_zero, hv.2.2.2.1, hd i hi]
    have hsplit := qInteger_add q i (N - i)
    rw [show i + (N - i) = N by omega] at hsplit
    field_simp
    linarith
  · rw [eb, hd i hi]
    show _ = ((1 - p₀) / p₀ - 1) * qInteger q i / ((1 - p₀) / p₀ * qInteger q N)
    field_simp; ring
  · rw [ec, hd i hi]
    show _ = qInteger q i / ((1 - p₀) / p₀ * qInteger q N)
    field_simp

/-- The normalized odd component (`N ≥ 2`) is (2.3) with parameters `(N - 1, q, r/q)`. -/
theorem ps_odd_params (hN2 : 2 ≤ N) :
    ∀ i, i ≤ N - 1 → (oddComp v).a i = (geometricCoefficients (N - 1) (q * (1 - p₀) / p₀) q).a i ∧
      (oddComp v).b i = (geometricCoefficients (N - 1) (q * (1 - p₀) / p₀) q).b i ∧
      (oddComp v).c i = (geometricCoefficients (N - 1) (q * (1 - p₀) / p₀) q).c i := by
  have hq := hp.1
  have hQN : 0 < qInteger q N := qInteger_pos q hq N (by omega)
  have hQN1 : 0 < qInteger q (N - 1) := qInteger_pos q hq (N - 1) (by omega)
  have h1 := ps_p0_lt_one v hv hb hp
  have hpos := ps_p0_pos v hv hp
  have hq0 : 1 - p₀ ≠ 0 := by linarith
  have hqne : q ≠ 0 := by linarith
  have hd := ps_d_formula v hv hb hp
  -- `[N]_q = 1 + q [N-1]_q`
  have hrec : qInteger q N = 1 + q * qInteger q (N - 1) := by
    rw [← qInteger_succ, show N - 1 + 1 = N by omega]
  have hd1 : v.c 2 = 1 / qInteger q N := by
    have := hd 1 (by omega); simp only [Nat.mul_one] at this
    rw [this]; congr 1; simp [qInteger]
  have h1d : 1 - v.c 2 = q * qInteger q (N - 1) / qInteger q N := by
    rw [hd1]; field_simp; linarith
  intro i hi
  obtain ⟨eb, ec⟩ := ps_oddComp v hv hb hp hN2 i hi
  refine ⟨?_, ?_, ?_⟩
  · show (oddRaw v).a i / (oddRaw v).a 0 = q ^ i * qInteger q (N - 1 - i) / qInteger q (N - 1)
    have hraw : ∀ n, n ≤ N - 1 → (oddRaw v).a n = (1 - p₀) * (1 - v.c (2 * (n + 1))) := by
      intro n hn
      show v.a (2 * n + 1) * v.a (2 * n + 2) = _
      rw [ps_a_odd v hv hb hp n (by omega), show 2 * n + 2 = 2 * (n + 1) by ring,
        ps_a_even v hv hb (n + 1) (by omega)]
    rw [hraw i hi, hraw 0 (by omega), show 2 * (0 + 1) = 2 by rfl, hd (i + 1) (by omega), h1d]
    have hsplit := qInteger_add q (i + 1) (N - 1 - i)
    rw [show i + 1 + (N - 1 - i) = N by omega, pow_succ] at hsplit
    field_simp
    linear_combination hsplit
  · rw [eb, hd i (by omega), h1d]
    show _ = (q * (1 - p₀) / p₀ - 1) * qInteger q i / (q * (1 - p₀) / p₀ * qInteger q (N - 1))
    have h2 := hQN.ne'; have h3 := hQN1.ne'; have h4 := hpos.ne'
    field_simp
  · rw [ec, hd i (by omega), h1d]
    show _ = qInteger q i / (q * (1 - p₀) / p₀ * qInteger q (N - 1))
    have h2 := hQN.ne'; have h3 := hQN1.ne'; have h4 := hpos.ne'
    field_simp

end Szkraw
