import Szkraw.VRAffineMain

/-!
# Proposition 8.10 (quadratic profiles)

`d_i = ν₁ i + ν₂ C(i,2)` with `ν₁ > 0`, `ν₂ ≥ 0`; `ρ(x) = r + t x + τ C(x,2)` with `r > 0`,
`t, τ ≥ 0`; `c_i = ρ(i) d_i`, `b_i = (1 - ρ(i)) d_i`; `b` nondecreasing. On `Ω` the only negative
contribution of the recurrence of Theorem 8.6 is the move `B₁ = C(a,4) φ₄`, and
`φ₂(ℓ) φ₂(ℓ+1) ≥ c_{ℓ+1} φ₄(ℓ)` gives `P² ≥ 4Q`; the resummation (`gkernel_resum`) applies with
`H = 0` and `V₁ = -A₁`.
-/

set_option linter.unusedSectionVars false

namespace Szkraw

open Finset

/-- Iterated shift sums of a padded Newton sequence are the finite differences, on `ℓ + n ≤ N`. -/
theorem iterShift_padNewton (x : ℕ → ℝ) (hx0 : x 0 = 0) (N ℓ n : ℕ) (h : ℓ + n ≤ N) :
    Szkraw.iterShift (padNewton N (newtonCoeff x)) ℓ n = (fwdDiff 1)^[n] x ℓ := by
  have hGN := shift_eq_sum_fwdDiff_iter (1 : ℕ) ((fwdDiff 1)^[n] x) ℓ 0
  simp only [zero_add, smul_eq_mul, mul_one, nsmul_eq_mul] at hGN
  rw [hGN, iterShift_eq]
  refine sum_congr rfl fun k hk => ?_
  rw [mem_range] at hk
  rw [← Function.iterate_add_apply, ← newtonCoeff_eq_iter, add_comm k n]
  unfold padNewton
  by_cases h1 : 1 ≤ n + k
  · rw [if_pos ⟨h1, by omega⟩]
  · have : n + k = 0 := by omega
    rw [this, if_neg (by omega)]
    simp [newtonCoeff, hx0]

theorem fwdDiff_iter_congr {x y : ℕ → ℝ} (n ℓ : ℕ) (h : ∀ i, ℓ ≤ i → i ≤ ℓ + n → x i = y i) :
    (fwdDiff 1)^[n] x ℓ = (fwdDiff 1)^[n] y ℓ := by
  rw [fwdDiff_iter_eq_sum_shift, fwdDiff_iter_eq_sum_shift]
  refine sum_congr rfl fun k hk => ?_
  rw [mem_range] at hk
  simp only [smul_eq_mul, mul_one]
  rw [h (ℓ + k) (by omega) (by omega)]

/-- The quadratic Leibniz rule: for `g(i) = r + t i + τ C(i,2)`,
`Δ^{k+2}(g d)(x) = g(x+k+2) Δ^{k+2}d(x) + (k+2)(t + τ(x+k+1)) Δ^{k+1}d(x) + C(k+2,2) τ Δ^k d(x)`. -/
theorem fwdDiff_quad_mul (r t τ : ℝ) (d : ℕ → ℝ) : ∀ k x : ℕ,
    (fwdDiff 1)^[k + 2] (fun i : ℕ => (r + t * i + τ * (i.choose 2 : ℝ)) * d i) x =
      (r + t * ((x : ℝ) + k + 2) + τ * (((x + k + 2).choose 2 : ℕ) : ℝ)) * (fwdDiff 1)^[k + 2] d x +
      ((k : ℝ) + 2) * (t + τ * ((x : ℝ) + k + 1)) * (fwdDiff 1)^[k + 1] d x +
      ((k : ℝ) + 2) * ((k : ℝ) + 1) / 2 * τ * (fwdDiff 1)^[k] d x
  | 0, x => by
    have c1 : ∀ m : ℕ, (((m + 1).choose 2 : ℕ) : ℝ) = ((m.choose 2 : ℕ) : ℝ) + m := by
      intro m
      rw [show (2 : ℕ) = 1 + 1 from rfl, Nat.choose_succ_succ, Nat.choose_one_right]; push_cast; ring
    simp only [show (0 : ℕ) + 2 = 2 from rfl, show (0 : ℕ) + 1 = 1 from rfl, Function.iterate_succ_apply',
      Function.iterate_zero_apply, fwdDiff]
    rw [show x + 1 + 1 = x + 2 by ring, show x + 0 + 2 = x + 2 by ring, show x + 2 = x + 1 + 1 by ring, c1 (x + 1), c1 x]
    push_cast; ring
  | k + 1, x => by
    rw [fwdDiff_iter_succ (fun i : ℕ => (r + t * i + τ * (i.choose 2 : ℝ)) * d i) (k + 2) x,
      fwdDiff_quad_mul r t τ d k (x + 1), fwdDiff_quad_mul r t τ d k x,
      fwdDiff_iter_succ d (k + 2) x, fwdDiff_iter_succ d (k + 1) x, fwdDiff_iter_succ d k x]
    have c1 : ∀ m : ℕ, (((m + 1).choose 2 : ℕ) : ℝ) = ((m.choose 2 : ℕ) : ℝ) + m := by
      intro m
      rw [show (2 : ℕ) = 1 + 1 from rfl, Nat.choose_succ_succ, Nat.choose_one_right]; push_cast; ring
    rw [show x + (k + 1) + 2 = x + k + 2 + 1 by ring, show x + 1 + k + 2 = x + k + 2 + 1 by ring, c1 (x + k + 2)]
    push_cast; ring

/-! ### The profile `d_i = ν₁ i + ν₂ C(i,2)` -/

section QP

variable (ν1 ν2 : ℝ)

/-- The quadratic profile as a function on `ℕ`. -/
noncomputable def dQ (i : ℕ) : ℝ := ν1 * i + ν2 * (i.choose 2 : ℝ)

theorem dQ_diff1 : (fwdDiff 1)^[1] (dQ ν1 ν2) = fun i : ℕ => ν1 + ν2 * i := by
  funext i
  show dQ ν1 ν2 (i + 1) - dQ ν1 ν2 i = _
  unfold dQ
  rw [show (2 : ℕ) = 1 + 1 from rfl, Nat.choose_succ_succ, Nat.choose_one_right]; push_cast; ring

theorem dQ_diff2 : (fwdDiff 1)^[2] (dQ ν1 ν2) = fun _ : ℕ => ν2 := by
  funext i
  rw [show (2 : ℕ) = 1 + 1 from rfl, Function.iterate_succ_apply', dQ_diff1]
  show (ν1 + ν2 * ((i + 1 : ℕ) : ℝ)) - (ν1 + ν2 * i) = ν2
  push_cast; ring

theorem dQ_diff_high : ∀ k, (fwdDiff 1)^[k + 3] (dQ ν1 ν2) = fun _ : ℕ => (0 : ℝ)
  | 0 => by
    funext i
    rw [show 0 + 3 = 2 + 1 from rfl, Function.iterate_succ_apply', dQ_diff2]
    show ν2 - ν2 = 0; ring
  | k + 1 => by
    funext i
    rw [show k + 1 + 3 = (k + 3) + 1 by ring, Function.iterate_succ_apply', dQ_diff_high k]
    show (0 : ℝ) - 0 = 0; ring

end QP

/-- Hypotheses of Proposition 8.10. -/
def QuadProfileHyp {N : ℕ} (vv : Coefficients N) : Prop :=
  ∃ ν1 ν2 r t τ : ℝ, 0 < ν1 ∧ 0 ≤ ν2 ∧ 0 < r ∧ 0 ≤ t ∧ 0 ≤ τ ∧
    (∀ i, i ≤ N → profile vv i = ν1 * i + ν2 * (i.choose 2 : ℝ)) ∧
    (∀ i, i ≤ N → vv.c i = (r + t * i + τ * (i.choose 2 : ℝ)) * profile vv i) ∧
    (∀ i, i < N → vv.b i ≤ vv.b (i + 1))

/-- Proposition 8.10 (quadratic profiles), matrix-positivity conclusion. -/
def Stmt_quadprofile : Prop :=
  ∀ (N : ℕ) (vv : Coefficients N), Admissible vv → QuadProfileHyp vv → MatrixPositivity vv

section QPproof

variable (ν1 ν2 r t τ : ℝ)

/-- The ratio `ρ(i) = r + t i + τ C(i,2)`. -/
noncomputable def gQ (i : ℕ) : ℝ := r + t * i + τ * (i.choose 2 : ℝ)

/-- `c = ρ d` as a function on `ℕ`. -/
noncomputable def cQ (i : ℕ) : ℝ := gQ r t τ i * dQ ν1 ν2 i

theorem dQ_diff1' (i : ℕ) : (fwdDiff 1)^[1] (dQ ν1 ν2) i = ν1 + ν2 * i := by rw [dQ_diff1]
theorem dQ_diff2' (i : ℕ) : (fwdDiff 1)^[2] (dQ ν1 ν2) i = ν2 := by rw [dQ_diff2]
theorem dQ_diff_high' (k i : ℕ) : (fwdDiff 1)^[k + 3] (dQ ν1 ν2) i = 0 := by rw [dQ_diff_high]

theorem dQ_succ (i : ℕ) : dQ ν1 ν2 (i + 1) = dQ ν1 ν2 i + (ν1 + ν2 * i) := by
  have := dQ_diff1' ν1 ν2 i
  simp only [Function.iterate_one] at this
  have e : fwdDiff 1 (dQ ν1 ν2) i = dQ ν1 ν2 (i + 1) - dQ ν1 ν2 i := rfl
  linarith

/-- `φ₂(x) = ρ(x+2) ν₂ + 2(t + τ(x+1))(ν₁ + ν₂ x) + τ d(x)`. -/
theorem cQ_diff2 (x : ℕ) : (fwdDiff 1)^[2] (cQ ν1 ν2 r t τ) x =
    gQ r t τ (x + 2) * ν2 + 2 * (t + τ * ((x : ℝ) + 1)) * (ν1 + ν2 * x) + τ * dQ ν1 ν2 x := by
  have h := fwdDiff_quad_mul r t τ (dQ ν1 ν2) 0 x
  have e : cQ ν1 ν2 r t τ = fun i : ℕ => (r + t * i + τ * (i.choose 2 : ℝ)) * dQ ν1 ν2 i := rfl
  rw [e, h, dQ_diff2', dQ_diff1']
  simp only [Function.iterate_zero, id]
  unfold gQ; push_cast; ring

/-- `φ₃(x) = 3(t + τ(x+2)) ν₂ + 3τ(ν₁ + ν₂ x)`. -/
theorem cQ_diff3 (x : ℕ) : (fwdDiff 1)^[3] (cQ ν1 ν2 r t τ) x =
    3 * (t + τ * ((x : ℝ) + 2)) * ν2 + 3 * τ * (ν1 + ν2 * x) := by
  have h := fwdDiff_quad_mul r t τ (dQ ν1 ν2) 1 x
  have e : cQ ν1 ν2 r t τ = fun i : ℕ => (r + t * i + τ * (i.choose 2 : ℝ)) * dQ ν1 ν2 i := rfl
  rw [e, show (3 : ℕ) = 1 + 2 from rfl, h, show 1 + 2 = 0 + 3 from rfl, dQ_diff_high', show 1 + 1 = 2 from rfl,
    dQ_diff2', dQ_diff1']
  push_cast; ring

/-- `φ₄ = 6 τ ν₂`. -/
theorem cQ_diff4 (x : ℕ) : (fwdDiff 1)^[4] (cQ ν1 ν2 r t τ) x = 6 * τ * ν2 := by
  have h := fwdDiff_quad_mul r t τ (dQ ν1 ν2) 2 x
  have e : cQ ν1 ν2 r t τ = fun i : ℕ => (r + t * i + τ * (i.choose 2 : ℝ)) * dQ ν1 ν2 i := rfl
  have z4 : (fwdDiff 1)^[2 + 2] (dQ ν1 ν2) x = 0 := dQ_diff_high' ν1 ν2 1 x
  have z3 : (fwdDiff 1)^[2 + 1] (dQ ν1 ν2) x = 0 := dQ_diff_high' ν1 ν2 0 x
  rw [e]
  refine h.trans ?_
  rw [z4, z3, dQ_diff2']
  push_cast; ring

/-- `φ_n = 0` for `n ≥ 5`. -/
theorem cQ_diff_high (k x : ℕ) : (fwdDiff 1)^[k + 5] (cQ ν1 ν2 r t τ) x = 0 := by
  have h := fwdDiff_quad_mul r t τ (dQ ν1 ν2) (k + 3) x
  have e : cQ ν1 ν2 r t τ = fun i : ℕ => (r + t * i + τ * (i.choose 2 : ℝ)) * dQ ν1 ν2 i := rfl
  rw [e, show k + 5 = k + 3 + 2 by ring, h, show k + 3 + 2 = (k + 2) + 3 by ring, dQ_diff_high',
    show k + 3 + 1 = (k + 1) + 3 by ring, dQ_diff_high', dQ_diff_high']
  ring

variable {ν1 ν2 r t τ}

theorem gQ_mono (ht : 0 ≤ t) (hτ : 0 ≤ τ) {i j : ℕ} (hij : i ≤ j) : gQ r t τ i ≤ gQ r t τ j := by
  unfold gQ
  have h1 : (i : ℝ) ≤ j := by exact_mod_cast hij
  have h2 : (i.choose 2 : ℝ) ≤ (j.choose 2 : ℝ) := by exact_mod_cast Nat.choose_le_choose 2 hij
  nlinarith

theorem gQ_pos (hr : 0 < r) (ht : 0 ≤ t) (hτ : 0 ≤ τ) (i : ℕ) : 0 < gQ r t τ i := by
  unfold gQ; positivity

theorem dQ_nonneg (h1 : 0 < ν1) (h2 : 0 ≤ ν2) (i : ℕ) : 0 ≤ dQ ν1 ν2 i := by unfold dQ; positivity

theorem cQ_diff_nonneg (h1 : 0 < ν1) (h2 : 0 ≤ ν2) (hr : 0 < r) (ht : 0 ≤ t) (hτ : 0 ≤ τ) (x n : ℕ) (hn : 2 ≤ n) :
    0 ≤ (fwdDiff 1)^[n] (cQ ν1 ν2 r t τ) x := by
  have hd := dQ_nonneg h1 h2 x
  have hg := (gQ_pos hr ht hτ (x + 2)).le
  rcases Nat.lt_or_ge n 5 with h | h
  · interval_cases n
    · rw [cQ_diff2]; positivity
    · rw [cQ_diff3]; positivity
    · rw [cQ_diff4]; positivity
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 5 := ⟨n - 5, by omega⟩
    rw [cQ_diff_high]

/-- The detour of the `B₁`-move: `φ₂(x) φ₂(x+1) ≥ c_{x+1} φ₄(x)`. -/
theorem phi2_phi2 (h1 : 0 < ν1) (h2 : 0 ≤ ν2) (hr : 0 < r) (ht : 0 ≤ t) (hτ : 0 ≤ τ) (x : ℕ) :
    gQ r t τ (x + 1) * dQ ν1 ν2 (x + 1) * (fwdDiff 1)^[4] (cQ ν1 ν2 r t τ) x ≤
      (fwdDiff 1)^[2] (cQ ν1 ν2 r t τ) x * (fwdDiff 1)^[2] (cQ ν1 ν2 r t τ) (x + 1) := by
  rw [cQ_diff4, cQ_diff2, cQ_diff2, dQ_succ]
  set p1 := gQ r t τ (x + 1)
  have hp2 : p1 ≤ gQ r t τ (x + 2) := gQ_mono ht hτ (by omega)
  have hp3 : p1 ≤ gQ r t τ (x + 1 + 2) := gQ_mono ht hτ (by omega)
  have hp1 : 0 < p1 := gQ_pos hr ht hτ _
  set u0 := dQ ν1 ν2 x
  set v := ν1 + ν2 * (x : ℝ)
  have hu0 : 0 ≤ u0 := dQ_nonneg h1 h2 x
  have hx0 : (0 : ℝ) ≤ x := Nat.cast_nonneg x
  have hv : 0 ≤ v := by positivity
  -- convexity: `u₀ ≤ x v`
  have hconv : u0 ≤ x * v := by
    have hc2 : (x.choose 2 : ℝ) * 2 = (x : ℝ) * ((x : ℝ) - 1) := by
      rcases Nat.eq_zero_or_pos x with hx | hx
      · subst hx; simp
      · have := choose_two_mul x
        have h' : ((x.choose 2 * 2 : ℕ) : ℝ) = ((x * (x - 1) : ℕ) : ℝ) := by rw [this]
        push_cast [Nat.cast_sub (show 1 ≤ x by omega)] at h'; linarith
    simp only [u0, v, dQ]
    nlinarith
  push_cast
  set X := u0 + 2 * ((x : ℝ) + 1) * v
  set Y := u0 + v + 2 * ((x : ℝ) + 2) * (v + ν2)
  have hA : p1 * ν2 + τ * X ≤ gQ r t τ (x + 2) * ν2 + 2 * (t + τ * ((x : ℝ) + 1)) * v + τ * u0 := by
    simp only [X]; nlinarith [mul_le_mul_of_nonneg_right hp2 h2, mul_nonneg ht hv]
  have hB : p1 * ν2 + τ * Y ≤ gQ r t τ (x + 1 + 2) * ν2 + 2 * (t + τ * ((x : ℝ) + 1 + 1)) * (ν1 + ν2 * ((x : ℝ) + 1)) +
      τ * (u0 + v) := by
    simp only [Y, v]; nlinarith [mul_le_mul_of_nonneg_right hp3 h2, mul_nonneg ht (by positivity : (0 : ℝ) ≤ ν1 + ν2 * ((x : ℝ) + 1))]
  have hX : 0 ≤ X := by positivity
  have hY : 0 ≤ Y := by positivity
  have hXY : 6 * (u0 + v) ≤ X + Y := by simp only [X, Y]; nlinarith
  have hAn : 0 ≤ p1 * ν2 + τ * X := by positivity
  have hBn : 0 ≤ p1 * ν2 + τ * Y := by positivity
  have k1 := mul_le_mul hA hB hBn (le_trans hAn hA)
  have k2 : p1 * τ * ν2 * (6 * (u0 + v)) ≤ (p1 * ν2 + τ * X) * (p1 * ν2 + τ * Y) := by
    have := mul_le_mul_of_nonneg_left hXY (by positivity : 0 ≤ p1 * τ * ν2)
    nlinarith [mul_nonneg (mul_nonneg hτ hτ) (mul_nonneg hX hY), sq_nonneg (p1 * ν2)]
  have e : (x : ℝ) + 1 + 1 = (x : ℝ) + 2 := by ring
  rw [e] at k1
  nlinarith [k1, k2]

end QPproof


theorem WtF_zero_of {F : ℕ → ℕ → ℝ} {p q ℓ a : ℕ} (h : ∀ n, p ≤ n → n ≤ a → F ℓ n = 0) : WtF F p q ℓ a = 0 := by
  unfold WtF
  refine sum_eq_zero fun n hn => ?_
  rw [mem_range] at hn
  by_cases hp : p ≤ n
  · rw [h n hp (by omega), mul_zero]
  · rw [if_neg hp]; ring

theorem WtF_nonpos_of {F : ℕ → ℕ → ℝ} {p q ℓ a : ℕ} (h : ∀ n, p ≤ n → n ≤ a → F ℓ n ≤ 0) : WtF F p q ℓ a ≤ 0 := by
  unfold WtF
  refine sum_nonpos fun n hn => ?_
  rw [mem_range] at hn
  by_cases hp : p ≤ n
  · rw [if_pos hp]; exact mul_nonpos_of_nonneg_of_nonpos (by positivity) (h n hp (by omega))
  · rw [if_neg hp]; simp

theorem WtF_ge_single {F : ℕ → ℕ → ℝ} {p q ℓ a : ℕ} (h : ∀ n, p ≤ n → n ≤ a → 0 ≤ F ℓ n) {n0 : ℕ}
    (hp : p ≤ n0) (ha : n0 ≤ a) :
    ((n0 - p + q).choose q : ℝ) * (a.choose n0 : ℝ) * F ℓ n0 ≤ WtF F p q ℓ a := by
  unfold WtF
  have hmem : n0 ∈ range (a + 1) := mem_range.mpr (by omega)
  have := single_le_sum (f := fun n => (if p ≤ n then ((n - p + q).choose q : ℝ) else 0) * (a.choose n : ℝ) * F ℓ n)
    (fun n hn => by
      rw [mem_range] at hn
      by_cases hpn : p ≤ n
      · rw [if_pos hpn]; exact mul_nonneg (by positivity) (h n hpn (by omega))
      · rw [if_neg hpn]; simp) hmem
  simpa [hp] using this

/-- **Proposition 8.10** (quadratic profiles). -/
theorem quadprofile_matrix : Stmt_quadprofile := by
  intro N vv hv hyp
  obtain ⟨ν1, ν2, r, t, τ, h1, h2, hr, ht, hτ, hd, hc, hbmono⟩ := hyp
  have hv' := hv
  obtain ⟨hN, _, hb0, hc0, haN, hsum, hapos, hcpos⟩ := hv'
  set u := padNewton N (newtonCoeff vv.c) with hu_def
  set w := padNewton N (newtonCoeff vv.b) with hw_def
  set ν := padNewton N (newtonCoeff (profile vv)) with hν_def
  set PH : ℕ → ℕ → ℝ := fun ℓ n => (fwdDiff 1)^[n] (cQ ν1 ν2 r t τ) ℓ with hPH
  set FD : ℕ → ℕ → ℝ := fun ℓ n => (fwdDiff 1)^[n] (dQ ν1 ν2) ℓ with hFD
  have hd0 : profile vv 0 = 0 := by simp [profile, hb0, hc0]
  have hcQ : ∀ i, i ≤ N → vv.c i = cQ ν1 ν2 r t τ i := fun i hi => by
    rw [hc i hi, hd i hi]; rfl
  have hdQ : ∀ i, i ≤ N → profile vv i = dQ ν1 ν2 i := hd
  have phi : ∀ ℓ n, ℓ + n ≤ N → Szkraw.iterShift u ℓ n = PH ℓ n := fun ℓ n h => by
    rw [hu_def, iterShift_padNewton vv.c hc0 N ℓ n h]
    exact fwdDiff_iter_congr n ℓ fun i _ hi => hcQ i (by omega)
  have fdef : ∀ ℓ n, ℓ + n ≤ N → Szkraw.iterShift ν ℓ n = FD ℓ n := fun ℓ n h => by
    rw [hν_def, iterShift_padNewton (profile vv) hd0 N ℓ n h]
    exact fwdDiff_iter_congr n ℓ fun i _ hi => hdQ i (by omega)
  have hw_eq : w = fun i => ν i - u i := by
    funext i
    rw [hw_def, hν_def, hu_def]
    unfold padNewton
    split_ifs
    · rw [← newtonCoeff_sub]
      exact newtonCoeff_congr fun j _ => by simp [profile]
    · ring
  have psi : ∀ ℓ n, ℓ + n ≤ N → Szkraw.iterShift w ℓ n = FD ℓ n - PH ℓ n := fun ℓ n h => by
    rw [hw_eq, iterShift_sub, fdef ℓ n h, phi ℓ n h]
  -- values of the differences
  have PH_nn : ∀ ℓ n, 2 ≤ n → 0 ≤ PH ℓ n := fun ℓ n hn => cQ_diff_nonneg h1 h2 hr ht hτ ℓ n hn
  have PH_z : ∀ ℓ n, 5 ≤ n → PH ℓ n = 0 := fun ℓ n hn => by
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 5 := ⟨n - 5, by omega⟩
    exact cQ_diff_high ν1 ν2 r t τ k ℓ
  have FD_z : ∀ ℓ n, 3 ≤ n → FD ℓ n = 0 := fun ℓ n hn => by
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
    exact dQ_diff_high' ν1 ν2 k ℓ
  have FD_nn : ∀ ℓ n, 0 ≤ FD ℓ n := fun ℓ n => by
    rcases Nat.lt_or_ge n 3 with h | h
    · interval_cases n
      · exact dQ_nonneg h1 h2 ℓ
      · simp only [hFD]; rw [dQ_diff1']; positivity
      · simp only [hFD]; rw [dQ_diff2']; exact h2
    · rw [FD_z ℓ n h]
  -- the weights on `Ω` as `WtF`
  have WU : ∀ p q ℓ a, ℓ + a ≤ N → Wt u p q ℓ a = WtF PH p q ℓ a := fun p q ℓ a h => by
    rw [Wt_eq_WtF]; exact WtF_congr fun n hn => phi ℓ n (by omega)
  have WW : ∀ p q ℓ a, ℓ + a ≤ N → Wt w p q ℓ a = WtF (fun ℓ n => FD ℓ n - PH ℓ n) p q ℓ a := fun p q ℓ a h => by
    rw [Wt_eq_WtF]; exact WtF_congr fun n hn => psi ℓ n (by omega)
  have WN : ∀ p q ℓ a, ℓ + a ≤ N → Wt ν p q ℓ a = WtF FD p q ℓ a := fun p q ℓ a h => by
    rw [Wt_eq_WtF]; exact WtF_congr fun n hn => fdef ℓ n (by omega)
  have hwC : ∀ j ℓ a, wC u w j ℓ a = Wt ν (2 * j + 2) (j + 1) ℓ a := fun j ℓ a => by
    unfold wC; rw [Wt_add]; congr 1; funext i; rw [hw_eq]; ring
  -- `u ≥ 0`, `u 1 > 0`
  have hu_nn : ∀ i, 0 ≤ u i := by
    intro i
    rw [hu_def]; unfold padNewton
    split_ifs with hi
    · have e : newtonCoeff vv.c i = PH 0 i := by
        rw [newtonCoeff_eq_iter]; exact fwdDiff_iter_congr i 0 fun j _ hj => hcQ j (by omega)
      rw [e]
      rcases Nat.lt_or_ge i 2 with h | h
      · have : i = 1 := by omega
        subst this
        simp only [hPH, Function.iterate_one]
        show 0 ≤ cQ ν1 ν2 r t τ (0 + 1) - cQ ν1 ν2 r t τ 0
        have : cQ ν1 ν2 r t τ 0 = 0 := by simp [cQ, dQ]
        rw [this, sub_zero]
        exact mul_nonneg (gQ_pos hr ht hτ _).le (dQ_nonneg h1 h2 _)
      · exact PH_nn 0 i h
    · exact le_rfl
  have hu1 : 0 < u 1 := by
    rw [hu_def]; unfold padNewton; rw [if_pos ⟨le_rfl, hN⟩]
    have : newtonCoeff vv.c 1 = vv.c 1 - vv.c 0 := by simp [newtonCoeff, Finset.sum_range_succ]; ring
    rw [this, hc0, sub_zero]; exact hcpos 1 (by norm_num) hN
  have hu0 : u 0 = 0 := padNewton_zero _ _
  have hddc : ∀ i, i ≤ N → dd u i = vv.c i := fun i hi => dd_padNewton vv.c hc0 N i hi
  have hddb : ∀ i, i ≤ N → dd w i = vv.b i := fun i hi => dd_padNewton vv.b hb0 N i hi
  refine matrixPositivity_of_kernel vv hv hu_nn hu1 hu0 hddc hddb (fun k' hk' => ?_)
  have hT : dd w N + dd u N = 1 := by
    rw [hddb N le_rfl, hddc N le_rfl]; have := hsum N le_rfl; rw [haN] at this; linarith
  -- the moves
  have bchain : ∀ ℓ k, ℓ + k ≤ N → vv.b ℓ ≤ vv.b (ℓ + k) := by
    intro ℓ k hk
    induction k with
    | zero => simp
    | succ k ih => exact le_trans (ih (by omega)) (hbmono (ℓ + k) (by omega))
  have hA0 : ∀ ℓ a, ℓ + a ≤ N → 0 ≤ wA w 0 ℓ a := fun ℓ a h => by
    unfold wA; rw [show 2 * 0 + 1 = 1 by ring, Wt_one_zero, hddb _ h, hddb _ (by omega)]
    linarith [bchain ℓ a h]
  have hA1 : ∀ ℓ a, ℓ + a ≤ N → wA w 1 ℓ a ≤ 0 := fun ℓ a h => by
    unfold wA; rw [WW _ _ _ _ h]
    refine WtF_nonpos_of fun n hn _ => ?_
    rw [FD_z ℓ n (by omega)]; linarith [PH_nn ℓ n (by omega)]
  have hAz : ∀ j ℓ a, 2 ≤ j → ℓ + a ≤ N → wA w j ℓ a = 0 := fun j ℓ a hj h => by
    unfold wA; rw [WW _ _ _ _ h]
    refine WtF_zero_of fun n hn _ => ?_
    rw [FD_z ℓ n (by omega), PH_z ℓ n (by omega)]; ring
  have hBnn : ∀ j ℓ a, ℓ + a ≤ N → 0 ≤ wB u j ℓ a := fun j ℓ a h => by
    unfold wB; rw [WU _ _ _ _ h]; exact WtF_nonneg fun n hn _ => PH_nn ℓ n (by omega)
  have hBz : ∀ j ℓ a, 2 ≤ j → ℓ + a ≤ N → wB u j ℓ a = 0 := fun j ℓ a hj h => by
    unfold wB; rw [WU _ _ _ _ h]; exact WtF_zero_of fun n hn _ => PH_z ℓ n (by omega)
  have hB0z : ∀ ℓ a, a < 2 → wB u 0 ℓ a = 0 := fun ℓ a ha => by
    unfold wB; exact Wt_eq_zero _ _ _ _ (by omega)
  have hCnn : ∀ j ℓ a, ℓ + a ≤ N → 0 ≤ wC u w j ℓ a := fun j ℓ a h => by
    rw [hwC, WN _ _ _ _ h]; exact WtF_nonneg fun n _ _ => FD_nn ℓ n
  have hCz : ∀ j ℓ a, 1 ≤ j → ℓ + a ≤ N → wC u w j ℓ a = 0 := fun j ℓ a hj h => by
    rw [hwC, WN _ _ _ _ h]; exact WtF_zero_of fun n hn _ => FD_z ℓ n (by omega)
  set V0 : ℕ → ℕ → ℕ → ℝ := fun j ℓ a => if j = 1 then -wA w 1 ℓ a else 0 with hV0
  have hV0nn : ∀ j ℓ a, ℓ + a ≤ N → 0 ≤ V0 j ℓ a := fun j ℓ a h => by
    simp only [hV0]; split_ifs
    · linarith [hA1 ℓ a h]
    · exact le_rfl
  have hcc : ∀ n, 1 ≤ n → 0 < dd u n := fun n hn => dd_pos_of hu_nn hu1 hn
  have hw : ResumWeights (dd u) (wA w) (wB u) (wC u w) (fun _ _ _ => 0) V0 (wSV u w) N := by
    refine ⟨hcc, fun j ℓ a hj h => ?_, hA0, hBnn, hCnn, fun _ _ _ _ => le_rfl, hV0nn, fun ℓ a h => ?_,
      fun j ℓ a hj h => ?_, fun j ℓ a hj h => ?_, fun j ℓ a hj h => ?_, fun j ℓ a hj h => ?_, fun ℓ a h ha => ?_⟩
    · -- split
      simp only [hV0]
      split_ifs with hj1
      · subst hj1; ring
      · rw [hAz j ℓ a (by omega) h]; ring
    · -- straight weights
      unfold wSV
      rcases Nat.lt_or_ge (ℓ + a) N with hl | hl
      · rw [hddb _ hl.le, hddc _ hl.le]; have := hsum (ℓ + a) hl.le; linarith [hapos (ℓ + a) hl]
      · rw [show ℓ + a = N by omega]; linarith
    · -- domB
      rcases Nat.lt_or_ge a 2 with ha | ha
      · rw [hB0z ℓ a ha, zero_mul]
        unfold wB; rw [Wt_eq_zero _ _ _ _ (by omega), mul_zero]
      rcases Nat.lt_or_ge j 2 with hj2 | hj2
      · have hj1 : j = 1 := by omega
        subst hj1
        rcases Nat.lt_or_ge a 4 with ha4 | ha4
        · unfold wB; rw [Wt_eq_zero _ _ _ _ (by omega), mul_zero]
          exact mul_nonneg (hBnn 0 ℓ a h) (hBnn _ _ _ (by omega))
        -- `B₁ = C(a,4) φ₄`, `B₀ ≥ C(a,2) φ₂`, `B₀' ≥ C(a-2,2) φ₂'`
        have hB1 : wB u 1 ℓ a = (a.choose 4 : ℝ) * PH ℓ 4 := by
          unfold wB; rw [WU _ _ _ _ h]; unfold WtF
          rw [sum_eq_single 4]
          · simp
          · intro n hn hn4
            rw [mem_range] at hn
            by_cases h4 : 4 ≤ n
            · rw [PH_z ℓ n (by omega), mul_zero]
            · rw [if_neg (by omega)]; ring
          · intro hn; exact absurd (mem_range.mpr (by omega)) hn
        have hB0 : (a.choose 2 : ℝ) * PH ℓ 2 ≤ wB u 0 ℓ a := by
          unfold wB; rw [WU _ _ _ _ h]
          have := WtF_ge_single (F := PH) (p := 2) (q := 0) (ℓ := ℓ) (a := a)
            (fun n hn _ => PH_nn ℓ n hn) (n0 := 2) le_rfl ha
          simpa using this
        have hB0' : ((a - 2).choose 2 : ℝ) * PH (ℓ + 1) 2 ≤ wB u 0 (ℓ + 1) (a - 2) := by
          unfold wB; rw [WU _ _ _ _ (by omega)]
          have := WtF_ge_single (F := PH) (p := 2) (q := 0) (ℓ := ℓ + 1) (a := a - 2)
            (fun n hn _ => PH_nn (ℓ + 1) n hn) (n0 := 2) le_rfl (by omega)
          simpa using this
        have hccv : dd u (ℓ + 1) = gQ r t τ (ℓ + 1) * dQ ν1 ν2 (ℓ + 1) := by
          rw [hddc _ (by omega), hcQ _ (by omega)]; rfl
        have hpp := phi2_phi2 h1 h2 hr ht hτ ℓ
        have hch : (a.choose 4 : ℝ) * 6 = (a.choose 2 : ℝ) * ((a - 2).choose 2 : ℝ) := by
          have := Nat.choose_mul (n := a) (k := 4) (s := 2) (by norm_num)
          have h42 : (4 : ℕ).choose 2 = 6 := by decide
          rw [h42, show 4 - 2 = 2 from rfl] at this
          exact_mod_cast this
        have hφ2 := PH_nn ℓ 2 le_rfl
        have hφ2' := PH_nn (ℓ + 1) 2 le_rfl
        have hφ4 := PH_nn ℓ 4 (by norm_num)
        have hC2 : (0 : ℝ) ≤ (a.choose 2 : ℝ) := Nat.cast_nonneg _
        have hC2' : (0 : ℝ) ≤ ((a - 2).choose 2 : ℝ) := Nat.cast_nonneg _
        have hC4 : (0 : ℝ) ≤ (a.choose 4 : ℝ) := Nat.cast_nonneg _
        have hc0' : 0 ≤ dd u (ℓ + 1) := (hcc (ℓ + 1) (by omega)).le
        rw [hB1, show 1 - 1 = 0 from rfl]
        have k1 : (a.choose 2 : ℝ) * PH ℓ 2 * (((a - 2).choose 2 : ℝ) * PH (ℓ + 1) 2) ≤
            wB u 0 ℓ a * wB u 0 (ℓ + 1) (a - 2) :=
          mul_le_mul hB0 hB0' (mul_nonneg hC2' hφ2') (hBnn 0 ℓ a h)
        have k2 : dd u (ℓ + 1) * PH ℓ 4 ≤ PH ℓ 2 * PH (ℓ + 1) 2 := by rw [hccv]; exact hpp
        have k3 : 6 * (a.choose 4 : ℝ) * (dd u (ℓ + 1) * PH ℓ 4) ≤ 6 * (a.choose 4 : ℝ) * (PH ℓ 2 * PH (ℓ + 1) 2) :=
          mul_le_mul_of_nonneg_left k2 (by positivity)
        have k4 : 0 ≤ 2 * (a.choose 4 : ℝ) * (dd u (ℓ + 1) * PH ℓ 4) := by positivity
        have k5 : 6 * (a.choose 4 : ℝ) * (PH ℓ 2 * PH (ℓ + 1) 2) =
            (a.choose 2 : ℝ) * PH ℓ 2 * (((a - 2).choose 2 : ℝ) * PH (ℓ + 1) 2) := by
          linear_combination (PH ℓ 2 * PH (ℓ + 1) 2) * hch
        linarith [k1, k3, k4, k5]
      · rw [hBz j ℓ a hj2 h, mul_zero]
        exact mul_nonneg (hBnn 0 ℓ a h) (hBnn _ _ _ (by omega))
    · -- domC
      rw [hCz j ℓ a hj h, mul_zero]
      rcases Nat.lt_or_ge a 2 with ha | ha
      · rw [hB0z ℓ a ha, zero_mul]
      · exact mul_nonneg (hBnn 0 ℓ a h) (hCnn _ _ _ (by omega))
    · -- domH
      simp
    · -- domV
      have : V0 j ℓ a = 0 := by simp only [hV0]; rw [if_neg (by omega)]
      rw [this, mul_zero]
      rcases Nat.lt_or_ge a 2 with ha | ha
      · rw [hB0z ℓ a ha, zero_mul]
      · exact mul_nonneg (hBnn 0 ℓ a h) (hV0nn _ _ _ (by omega))
    · -- key: `H = 0`
      simp only [mul_zero]
      have := hcc (ℓ + 1) (by omega)
      have hv1 := hV0nn 1 ℓ a h
      refine add_nonneg (add_nonneg (mul_nonneg (hA0 ℓ a h) (hBnn _ _ _ (by omega)))
        (mul_nonneg (hBnn 0 ℓ a h) (hA0 _ _ (by omega)))) (by positivity)
  exact gkernel_resum hN hw (genRec_of hu_nn hu1)
    (fun a => by rw [kerFnV_zero]; split_ifs <;> norm_num) (kerFnV_supp hu_nn hu1 N hk' hT)

end Szkraw
