import Szkraw.QuadDecomp
import Szkraw.Geometric

/-!
# Corollary 7.9 (Parity-split criterion) and Theorem 7.1 (Szwarc's quadratic system)

A symmetric array whose odd downward coefficients are a constant `p_0 ≤ 1/2` and whose even
downward coefficients `d_n = c_{2n}` have geometric increments has nonnegative linearization:
both normalized components satisfy the hypotheses of Theorem 2.1, and Theorem 7.8 applies.
-/

namespace Szkraw

open Finset

variable {N : ℕ}

/-- Hypotheses (i)–(ii) of Corollary 7.9 with parameters `p_0` and `q`. -/
def ParitySplit (v : Coefficients (2 * N)) (p₀ q : ℝ) : Prop :=
  1 ≤ q ∧ (∀ n, 2 * n + 1 ≤ 2 * N → v.c (2 * n + 1) = p₀) ∧
    (∀ n, 1 ≤ n → n ≤ N → 0 < v.c (2 * n) - v.c (2 * (n - 1))) ∧
    (∀ n, 1 ≤ n → n < N → v.c (2 * (n + 1)) - v.c (2 * n) = q * (v.c (2 * n) - v.c (2 * (n - 1))))

section parity

variable (v : Coefficients (2 * N)) (hv : Admissible v) (hb : ∀ i, i ≤ 2 * N → v.b i = 0)
  {p₀ q : ℝ} (hp : ParitySplit v p₀ q)
include hv hb hp

theorem ps_a_odd : ∀ n, 2 * n + 1 ≤ 2 * N → v.a (2 * n + 1) = 1 - p₀ := fun n hn => by
  have := hv.2.2.2.2.2.1 (2 * n + 1) hn
  rw [hb _ hn, hp.2.1 n hn] at this; linarith

omit hp in
theorem ps_a_even : ∀ n, n ≤ N → v.a (2 * n) = 1 - v.c (2 * n) := fun n hn => by
  have := hv.2.2.2.2.2.1 (2 * n) (by omega)
  rw [hb _ (by omega)] at this; linarith

omit hp in
theorem ps_d_top : v.c (2 * N) = 1 := by
  have := ps_a_even v hv hb N le_rfl
  rw [hv.2.2.2.2.1] at this; linarith

/-- The raw even component: `b̂_n = d_n(1-p_0) + (1-d_n)p_0`, `ĉ_n = d_n p_0`. -/
theorem ps_even_b (n : ℕ) (hn : n ≤ N) :
    (evenRaw v).b n = v.c (2 * n) * (1 - p₀) + (1 - v.c (2 * n)) * p₀ := by
  have hN := hv.1
  show v.c (2 * n) * v.a (2 * n - 1) + v.a (2 * n) * v.c (2 * n + 1) = _
  rw [ps_a_even v hv hb n hn]
  rcases Nat.eq_zero_or_pos n with h0 | h0
  · subst h0
    rw [Nat.mul_zero, hv.2.2.2.1, hp.2.1 0 (by omega)]; ring
  rcases Nat.lt_or_ge n N with h1 | h1
  · rw [show 2 * n - 1 = 2 * (n - 1) + 1 by omega, ps_a_odd v hv hb hp (n - 1) (by omega),
      hp.2.1 n (by omega)]
  · have hnN : n = N := by omega
    subst hnN
    rw [show 2 * n - 1 = 2 * (n - 1) + 1 by omega, ps_a_odd v hv hb hp (n - 1) (by omega),
      ps_d_top v hv hb]; ring

omit hb in
theorem ps_even_c (n : ℕ) (hn : n ≤ N) : (evenRaw v).c n = v.c (2 * n) * p₀ := by
  show v.c (2 * n) * v.c (2 * n - 1) = _
  rcases Nat.eq_zero_or_pos n with h0 | h0
  · subst h0; rw [Nat.mul_zero, hv.2.2.2.1]; ring
  · rw [show 2 * n - 1 = 2 * (n - 1) + 1 by omega, hp.2.1 (n - 1) (by omega)]

theorem ps_p0_lt_one : p₀ < 1 := by
  have h := hv.2.2.2.2.2.2.1 1 (by have := hv.1; omega)
  have h2 := ps_a_odd v hv hb hp 0 (by have := hv.1; omega)
  simp only [Nat.mul_zero, zero_add] at h2
  linarith

omit hb in
theorem ps_p0_pos : 0 < p₀ := by
  have h := hv.2.2.2.2.2.2.2 1 (by omega) (by have := hv.1; omega)
  have h2 := hp.2.1 0 (by have := hv.1; omega)
  simp only [Nat.mul_zero, zero_add] at h2
  rw [h2] at h; exact h

/-- The normalized even component has `b̃_n = (1 - r) d_n` and `c̃_n = r d_n`, `r = p_0/(1-p_0)`. -/
theorem ps_evenComp (n : ℕ) (hn : n ≤ N) :
    (evenComp v).b n = (1 - 2 * p₀) / (1 - p₀) * v.c (2 * n) ∧
      (evenComp v).c n = p₀ / (1 - p₀) * v.c (2 * n) := by
  have h1 := ps_p0_lt_one v hv hb hp
  have ha0 : (evenRaw v).a 0 = 1 - p₀ := by
    show v.a (2 * 0) * v.a (2 * 0 + 1) = 1 - p₀
    rw [Nat.mul_zero, hv.2.1, one_mul, ps_a_odd v hv hb hp 0 (by have := hv.1; omega)]
  have hb0 := ps_even_b v hv hb hp 0 (by omega)
  rw [Nat.mul_zero, hv.2.2.2.1] at hb0
  refine ⟨?_, ?_⟩
  · show ((evenRaw v).b n - (evenRaw v).b 0) / (evenRaw v).a 0 = _
    rw [ps_even_b v hv hb hp n hn, hb0, ha0]
    field_simp; ring
  · show (evenRaw v).c n / (evenRaw v).a 0 = _
    rw [ps_even_c v hv hp n hn, ha0]
    field_simp

/-- The normalized even component satisfies the hypotheses of Theorem 2.1. -/
theorem ps_even_geometric (hp0 : p₀ ≤ 1 / 2) : Geometric (evenComp v) := by
  have h1 := ps_p0_lt_one v hv hb hp
  have hpos := ps_p0_pos v hv hp
  have hprof : ∀ n, n ≤ N → (evenComp v).b n + (evenComp v).c n = v.c (2 * n) := by
    intro n hn
    obtain ⟨eb, ec⟩ := ps_evenComp v hv hb hp n hn
    have hne : 1 - p₀ ≠ 0 := by linarith
    rw [eb, ec]; field_simp; ring
  refine ⟨(1 - 2 * p₀) / p₀, q, div_nonneg (by linarith) hpos.le, hp.1, ?_, ?_, ?_⟩
  · intro i hi hiN
    obtain ⟨eb, ec⟩ := ps_evenComp v hv hb hp i hiN
    rw [eb, ec]; field_simp
  · intro i hi hiN
    rw [hprof i hiN, hprof (i - 1) (by omega)]
    exact hp.2.2.1 i hi hiN
  · intro i hi hiN
    rw [hprof (i + 1) (by omega), hprof i (by omega), hprof (i - 1) (by omega)]
    rw [show 2 * (i + 1) = 2 * (i + 1) from rfl]
    exact hp.2.2.2 i hi hiN

omit hb in
/-- `d_{n+1} - d_1 = q d_n` for geometric increments. -/
theorem ps_shift (n : ℕ) (hn : n + 1 ≤ N) : v.c (2 * (n + 1)) - v.c 2 = q * v.c (2 * n) := by
  induction n with
  | zero => rw [Nat.mul_zero, hv.2.2.2.1]; ring
  | succ n ih =>
    have h := hp.2.2.2 (n + 1) (by omega) (by omega)
    rw [show n + 1 - 1 = n by omega] at h
    have := ih (by omega)
    linarith

/-- The normalized odd component (`N ≥ 2`). -/
theorem ps_oddComp (hN : 2 ≤ N) (n : ℕ) (hn : n ≤ N - 1) :
    (oddComp v).b n = ((1 - p₀) * q - p₀) / ((1 - p₀) * (1 - v.c 2)) * v.c (2 * n) ∧
      (oddComp v).c n = p₀ / ((1 - p₀) * (1 - v.c 2)) * v.c (2 * n) := by
  have h1 := ps_p0_lt_one v hv hb hp
  have hd1 : v.c 2 < 1 := by
    have := hv.2.2.2.2.2.2.1 2 (by omega)
    have h2 := ps_a_even v hv hb 1 (by omega)
    simp only [Nat.mul_one] at h2
    linarith
  have hraw_b : ∀ n, n ≤ N - 1 → (oddRaw v).b n =
      (1 - p₀) * v.c (2 * (n + 1)) + p₀ * (1 - v.c (2 * n)) := by
    intro n hn
    show v.a (2 * n + 1) * v.c (2 * n + 2) + v.c (2 * n + 1) * v.a (2 * n) = _
    rw [ps_a_odd v hv hb hp n (by omega), hp.2.1 n (by omega), ps_a_even v hv hb n (by omega),
      show 2 * n + 2 = 2 * (n + 1) by ring]
  have ha0 : (oddRaw v).a 0 = (1 - p₀) * (1 - v.c 2) := by
    show v.a (2 * 0 + 1) * v.a (2 * 0 + 2) = _
    rw [ps_a_odd v hv hb hp 0 (by omega)]
    have := ps_a_even v hv hb 1 (by omega)
    simp only [Nat.mul_one] at this
    simp only [Nat.mul_zero, zero_add]; rw [this]
  have hden : (1 - p₀) * (1 - v.c 2) ≠ 0 := mul_ne_zero (by linarith) (by linarith)
  refine ⟨?_, ?_⟩
  · show ((oddRaw v).b n - (oddRaw v).b 0) / (oddRaw v).a 0 = _
    rw [hraw_b n hn, hraw_b 0 (by omega), ha0]
    have hs := ps_shift v hv hp n (by omega)
    rw [div_mul_eq_mul_div]
    congr 1
    simp only [Nat.mul_zero, zero_add, hv.2.2.2.1, sub_zero, mul_one]
    linear_combination (1 - p₀) * hs
  · show (v.c (2 * n + 1) * v.c (2 * n)) / (oddRaw v).a 0 = _
    rw [hp.2.1 n (by omega), ha0]
    field_simp

/-- The normalized odd component satisfies the hypotheses of Theorem 2.1 (`N ≥ 2`). -/
theorem ps_odd_geometric (hN : 2 ≤ N) (hp0 : p₀ ≤ 1 / 2) : Geometric (oddComp v) := by
  have h1 := ps_p0_lt_one v hv hb hp
  have hpos := ps_p0_pos v hv hp
  have hd1 : v.c 2 < 1 := by
    have := hv.2.2.2.2.2.2.1 2 (by omega)
    have h2 := ps_a_even v hv hb 1 (by omega)
    simp only [Nat.mul_one] at h2
    linarith
  have hD : 0 < (1 - p₀) * (1 - v.c 2) := mul_pos (by linarith) (by linarith)
  have hprof : ∀ n, n ≤ N - 1 → (oddComp v).b n + (oddComp v).c n =
      (1 - p₀) * q / ((1 - p₀) * (1 - v.c 2)) * v.c (2 * n) := by
    intro n hn
    obtain ⟨eb, ec⟩ := ps_oddComp v hv hb hp hN n hn
    rw [eb, ec]; field_simp; ring
  have hq := hp.1
  refine ⟨((1 - p₀) * q - p₀) / p₀, q, ?_, hq, ?_, ?_, ?_⟩
  · apply div_nonneg _ hpos.le; nlinarith
  · intro i hi hiN
    obtain ⟨eb, ec⟩ := ps_oddComp v hv hb hp hN i hiN
    rw [eb, ec]; field_simp
  · intro i hi hiN
    rw [hprof i hiN, hprof (i - 1) (by omega), ← mul_sub]
    apply mul_pos (div_pos (by nlinarith) hD)
    exact hp.2.2.1 i hi (by omega)
  · intro i hi hiN
    rw [hprof (i + 1) (by omega), hprof i (by omega), hprof (i - 1) (by omega), ← mul_sub, ← mul_sub,
      hp.2.2.2 i hi (by omega)]
    ring

end parity

/-- **Corollary 7.9** (Parity-split criterion). -/
def Stmt_parity_split : Prop :=
  ∀ (N : ℕ) (v : Coefficients (2 * N)), 1 ≤ N → Admissible v → (∀ i, i ≤ 2 * N → v.b i = 0) →
    ∀ p₀ q : ℝ, ParitySplit v p₀ q → p₀ ≤ 1 / 2 → MatrixPositivity v

theorem parity_split : Stmt_parity_split := by
  intro N v hN hv hb p₀ q hp hp0
  apply decomp_positivity v hv hb hN
  · exact geometric_matrix_positivity N (evenComp v) (evenComp_admissible v hv hb hN)
      (ps_even_geometric v hv hb hp hp0)
  · rcases Nat.lt_or_ge 1 N with hN2 | hN2
    · exact geometric_matrix_positivity (N - 1) (oddComp v) (oddComp_admissible v hv hb (by omega))
        (ps_odd_geometric v hv hb hp (by omega) hp0)
    · -- `N = 1`: the odd component is `L_0 = 1`
      intro m hm i j
      have hm0 : m = 0 := by omega
      subst hm0
      show 0 ≤ (1 : Matrix (Fin (N - 1 + 1)) (Fin (N - 1 + 1)) ℝ) i j
      rw [Matrix.one_apply]; split_ifs <;> norm_num

/-- Corollary 7.9, sharpness: for `1/2 < p_0 < 1`, `g(2,2;2) < 0`. -/
theorem parity_split_sharp (N : ℕ) (v : Coefficients (2 * N)) (hN : 1 ≤ N) (hv : Admissible v)
    (hb : ∀ i, i ≤ 2 * N → v.b i = 0) (p₀ q : ℝ) (hp : ParitySplit v p₀ q) (hp0 : 1 / 2 < p₀) :
    productMatrix v 2 ⟨2, by omega⟩ ⟨2, by omega⟩ < 0 := by
  have h := even_block v hv hb 1 hN ⟨1, by omega⟩ ⟨1, by omega⟩
  rw [← product_normalize (evenRaw v) (evenRaw_a0 v hv hN).ne'] at h
  have hG : Geven v 1 1 1 = productMatrix v 2 ⟨2, by omega⟩ ⟨2, by omega⟩ := by
    unfold Geven Gk; rw [dif_pos hN, dif_pos ⟨by omega, by omega⟩]
  rw [← hG, ← h]
  -- `p_1(J) = J` for the normalized even component
  have hea := evenComp_admissible v hv hb hN
  have hP1 : productMatrix (normalize (evenRaw v)) 1 = recurrenceMatrix (normalize (evenRaw v)) := by
    show ((normalize (evenRaw v)).a 0)⁻¹ • ((recurrenceMatrix (normalize (evenRaw v)) -
      (normalize (evenRaw v)).b 0 • (1 : Matrix _ _ ℝ)) * 1 - (normalize (evenRaw v)).c 0 • 0) = _
    rw [show (normalize (evenRaw v)).a 0 = 1 from hea.2.1,
      show (normalize (evenRaw v)).b 0 = 0 from hea.2.2.1]
    simp
  rw [hP1]
  unfold recurrenceMatrix
  rw [if_neg (by simp), if_pos rfl]
  obtain ⟨eb, _⟩ := ps_evenComp v hv hb hp 1 hN
  unfold evenComp at eb
  rw [eb]
  have h1 := ps_p0_lt_one v hv hb hp
  have hd := hp.2.2.1 1 le_rfl hN
  simp only [Nat.mul_one, Nat.sub_self, Nat.mul_zero, hv.2.2.2.1, sub_zero] at hd
  apply mul_neg_of_neg_of_pos _ hd
  apply div_neg_of_neg_of_pos (by linarith) (by linarith)

/-! ### Theorem 7.1 -/

/-- Szwarc's array (7.2): `b ≡ 0`, `(a_{2n}, c_{2n}) = ((N-n)/N, n/N)`, `(a_{2n-1}, c_{2n-1}) = (1-p_0, p_0)`. -/
noncomputable def szwarcCoefficients (N : ℕ) (p : ℝ) : Coefficients (2 * N) :=
  ⟨fun k => if k % 2 = 0 then ((N : ℝ) - ((k / 2 : ℕ) : ℝ)) / N else 1 - p,
   fun _ => 0,
   fun k => if k % 2 = 0 then ((k / 2 : ℕ) : ℝ) / N else p⟩

theorem szwarc_admissible (N : ℕ) (hN : 1 ≤ N) (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    Admissible (szwarcCoefficients N p) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  refine ⟨by omega, ?_, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · show (if 0 % 2 = 0 then ((N : ℝ) - ((0 / 2 : ℕ) : ℝ)) / N else 1 - p) = 1
    simp [hN'.ne']
  · show (if 0 % 2 = 0 then ((0 / 2 : ℕ) : ℝ) / N else p) = 0
    simp
  · show (if 2 * N % 2 = 0 then ((N : ℝ) - ((2 * N / 2 : ℕ) : ℝ)) / N else 1 - p) = 0
    rw [if_pos (by omega), show 2 * N / 2 = N by omega]; simp
  · intro i _
    show (if i % 2 = 0 then ((N : ℝ) - ((i / 2 : ℕ) : ℝ)) / N else 1 - p) + 0 +
      (if i % 2 = 0 then ((i / 2 : ℕ) : ℝ) / N else p) = 1
    split_ifs
    · field_simp; ring
    · ring
  · intro i hi
    show 0 < (if i % 2 = 0 then ((N : ℝ) - ((i / 2 : ℕ) : ℝ)) / N else 1 - p)
    split_ifs
    · apply div_pos _ hN'
      have : ((i / 2 : ℕ) : ℝ) < N := by exact_mod_cast (show i / 2 < N by omega)
      linarith
    · linarith
  · intro i hi _
    show 0 < (if i % 2 = 0 then ((i / 2 : ℕ) : ℝ) / N else p)
    split_ifs
    · apply div_pos _ hN'
      exact_mod_cast (show 0 < i / 2 by omega)
    · exact hp

theorem szwarc_parity (N : ℕ) (hN : 1 ≤ N) (p : ℝ) : ParitySplit (szwarcCoefficients N p) p 1 := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hc : ∀ n, (szwarcCoefficients N p).c (2 * n) = (n : ℝ) / N := by
    intro n
    show (if 2 * n % 2 = 0 then ((2 * n / 2 : ℕ) : ℝ) / N else p) = _
    rw [if_pos (by omega), show 2 * n / 2 = n by omega]
  refine ⟨le_rfl, ?_, ?_, ?_⟩
  · intro n _
    show (if (2 * n + 1) % 2 = 0 then (((2 * n + 1) / 2 : ℕ) : ℝ) / N else p) = p
    rw [if_neg (by omega)]
  · intro n hn _
    rw [hc, hc, Nat.cast_sub hn]
    field_simp; norm_num
  · intro n hn _
    rw [hc, hc, hc, Nat.cast_sub (by omega : 1 ≤ n)]
    push_cast
    field_simp; ring

/-- **Theorem 7.1** (Szwarc's quadratic system): for `0 < p_0 ≤ 1/2` the array (7.2) has a positive
finite orthogonality measure, the product identities on its support with nonnegative coefficients,
and coefficient sums one. -/
def Stmt_szwarc : Prop :=
  ∀ (N : ℕ), 1 ≤ N → ∀ p : ℝ, 0 < p → p ≤ 1 / 2 →
    FiniteRealization (szwarcCoefficients N p) ∧ MatrixPositivity (szwarcCoefficients N p)

theorem szwarc_system : Stmt_szwarc := by
  intro N hN p hp hp2
  have hv := szwarc_admissible N hN p hp (by linarith)
  exact ⟨finite_realization _ hv,
    parity_split N _ hN hv (fun _ _ => rfl) p 1 (szwarc_parity N hN p) hp2⟩

/-- **Theorem 7.1**, sharpness: for `1/2 < p_0 < 1`, `g(2,2;2) < 0`. -/
theorem szwarc_sharp (N : ℕ) (hN : 1 ≤ N) (p : ℝ) (hp : 1 / 2 < p) (hp1 : p < 1) :
    productMatrix (szwarcCoefficients N p) 2 ⟨2, by omega⟩ ⟨2, by omega⟩ < 0 :=
  parity_split_sharp N _ hN (szwarc_admissible N hN p (by linarith) hp1) (fun _ _ => rfl) p 1
    (szwarc_parity N hN p) hp

end Szkraw
