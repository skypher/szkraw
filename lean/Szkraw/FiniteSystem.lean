import Szkraw.Representation
import Szkraw.RowAction
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.LinearCombination

/-!
# P3, Section 9: every finite system reduces to the normalized recurrence

A finite system is a positive measure `Σ_t w_t δ_{x_t}` on `N + 1` distinct real points, `N ≥ 1`, with its
orthogonal polynomials. With `x_{t₀}` the largest point, an affine change `y = s x + c` (`s > 0`) together with
the positive normalization `R_n(x_{t₀}) = 1` gives an array satisfying (2.1) whose polynomials are the normalized
orthogonal polynomials of the measure (`finite_system_reduction`).

The monic orthogonal polynomials are built by the Stieltjes recursion `P_{n+1} = (X - β_n) P_n - γ_n P_{n-1}`;
`P_n(x_{t₀}) > 0` for `n ≤ N` follows from the Christoffel–Darboux identity at `x_{t₀}`.
-/

namespace Szkraw

open Finset Polynomial

namespace FinSys

variable {N : ℕ} (x w : Fin (N + 1) → ℝ)

/-- `⟨f, g⟩ = Σ_t w_t f(x_t) g(x_t)`. -/
noncomputable def ip (f g : ℝ[X]) : ℝ := ∑ t, w t * f.eval (x t) * g.eval (x t)

/-- The Stieltjes recursion on pairs `(P_{n-1}, P_n)`. -/
noncomputable def stj : ℕ → ℝ[X] × ℝ[X]
  | 0 => (0, 1)
  | n + 1 =>
    ((stj n).2, (X - C (ip x w (X * (stj n).2) (stj n).2 / ip x w (stj n).2 (stj n).2)) * (stj n).2 -
      C (if n = 0 then 0 else ip x w (stj n).2 (stj n).2 / ip x w (stj n).1 (stj n).1) * (stj n).1)

/-- The monic orthogonal polynomial `P_n`. -/
noncomputable def P (n : ℕ) : ℝ[X] := (stj x w n).2
/-- `P_{n-1}` (`0` for `n = 0`). -/
noncomputable def Pm (n : ℕ) : ℝ[X] := (stj x w n).1
/-- `β_n = ⟨X P_n, P_n⟩ / ⟨P_n, P_n⟩`. -/
noncomputable def β (n : ℕ) : ℝ := ip x w (X * P x w n) (P x w n) / ip x w (P x w n) (P x w n)
/-- `γ_n = ⟨P_n, P_n⟩ / ⟨P_{n-1}, P_{n-1}⟩` (`0` for `n = 0`). -/
noncomputable def γ (n : ℕ) : ℝ := if n = 0 then 0 else ip x w (P x w n) (P x w n) / ip x w (Pm x w n) (Pm x w n)

theorem P_zero : P x w 0 = 1 := rfl
theorem Pm_zero : Pm x w 0 = 0 := rfl
theorem Pm_succ (n : ℕ) : Pm x w (n + 1) = P x w n := rfl
theorem P_succ (n : ℕ) : P x w (n + 1) = (X - C (β x w n)) * P x w n - C (γ x w n) * Pm x w n := rfl

/-- `X P_n = P_{n+1} + β_n P_n + γ_n P_{n-1}`. -/
theorem X_mul_P (n : ℕ) : X * P x w n = P x w (n + 1) + C (β x w n) * P x w n + C (γ x w n) * Pm x w n := by
  rw [P_succ]; ring

theorem P_step (n : ℕ) (hm : (P x w n).Monic) (hd : (P x w n).natDegree = n)
    (hPm : (Pm x w n).degree < ((n + 1 : ℕ) : WithBot ℕ)) :
    (P x w (n + 1)).Monic ∧ (P x w (n + 1)).natDegree = n + 1 := by
  have hX : (X - C (β x w n)).Monic := Polynomial.monic_X_sub_C _
  have h1 : ((X - C (β x w n)) * P x w n).Monic := Polynomial.Monic.mul hX hm
  have h2 : ((X - C (β x w n)) * P x w n).natDegree = n + 1 := by
    rw [Polynomial.Monic.natDegree_mul hX hm, natDegree_X_sub_C, hd, add_comm]
  have hCm : (C (γ x w n) * Pm x w n).degree ≤ (Pm x w n).degree := by
    by_cases hg : γ x w n = 0
    · rw [hg, C_0, zero_mul, degree_zero]; exact bot_le
    · rw [degree_C_mul hg]
  have h3 : (C (γ x w n) * Pm x w n).degree < ((X - C (β x w n)) * P x w n).degree := by
    rw [degree_eq_natDegree (Polynomial.Monic.ne_zero h1), h2]
    exact lt_of_le_of_lt hCm hPm
  have hq : (C (γ x w n) * Pm x w n).natDegree < ((X - C (β x w n)) * P x w n).natDegree := by
    by_cases h0 : C (γ x w n) * Pm x w n = 0
    · rw [h0, natDegree_zero, h2]; omega
    · exact natDegree_lt_natDegree h0 h3
  refine ⟨?_, ?_⟩
  · rw [P_succ]; exact Polynomial.Monic.sub_of_left h1 h3
  · rw [P_succ, natDegree_sub_eq_left_of_natDegree_lt hq, h2]

theorem P_monic : ∀ n, (P x w n).Monic ∧ (P x w n).natDegree = n
  | 0 => by simp [P_zero]
  | 1 => P_step x w 0 (by simp [P_zero]) (by simp [P_zero])
      (by rw [Pm_zero, degree_zero]; exact WithBot.bot_lt_coe _)
  | n + 2 => P_step x w (n + 1) (P_monic (n + 1)).1 (P_monic (n + 1)).2
      (by rw [Pm_succ, degree_eq_natDegree (Polynomial.Monic.ne_zero (P_monic n).1), (P_monic n).2]
          exact_mod_cast (show n < n + 1 + 1 by omega))

/-! ### The inner product -/

variable {x w}

theorem ip_comm (f g : ℝ[X]) : ip x w f g = ip x w g f := by
  unfold ip; exact sum_congr rfl fun t _ => by ring

theorem ip_X (f g : ℝ[X]) : ip x w (X * f) g = ip x w f (X * g) := by
  unfold ip; exact sum_congr rfl fun t _ => by simp only [eval_mul, eval_X]; ring

theorem ip_add (f g h : ℝ[X]) : ip x w (f + g) h = ip x w f h + ip x w g h := by
  unfold ip; rw [← sum_add_distrib]; exact sum_congr rfl fun t _ => by simp only [eval_add]; ring

theorem ip_sub (f g h : ℝ[X]) : ip x w (f - g) h = ip x w f h - ip x w g h := by
  unfold ip; rw [← sum_sub_distrib]; exact sum_congr rfl fun t _ => by simp only [eval_sub]; ring

theorem ip_C_mul (a : ℝ) (f g : ℝ[X]) : ip x w (C a * f) g = a * ip x w f g := by
  unfold ip; rw [mul_sum]; exact sum_congr rfl fun t _ => by simp only [eval_mul, eval_C]; ring

theorem ip_zero (g : ℝ[X]) : ip x w 0 g = 0 := by simp [ip]

theorem ip_add' (f g h : ℝ[X]) : ip x w f (g + h) = ip x w f g + ip x w f h := by
  rw [ip_comm, ip_add, ip_comm g, ip_comm h]

theorem ip_C_mul' (a : ℝ) (f g : ℝ[X]) : ip x w f (C a * g) = a * ip x w f g := by
  rw [ip_comm, ip_C_mul, ip_comm]

theorem ip_self_nonneg (hw : ∀ t, 0 < w t) (f : ℝ[X]) : 0 ≤ ip x w f f :=
  sum_nonneg fun t _ => by nlinarith [hw t, sq_nonneg (f.eval (x t))]

/-- A polynomial with `⟨f, f⟩ = 0` vanishes at every node. -/
theorem eval_zero_of_ip_self (hw : ∀ t, 0 < w t) (f : ℝ[X]) (h : ip x w f f = 0) (t : Fin (N + 1)) :
    f.eval (x t) = 0 := by
  have hnn : ∀ s ∈ univ, 0 ≤ w s * f.eval (x s) * f.eval (x s) := fun s _ => by
    nlinarith [hw s, sq_nonneg (f.eval (x s))]
  have := (sum_eq_zero_iff_of_nonneg hnn).1 h t (mem_univ _)
  have hwt := hw t
  have : f.eval (x t) * f.eval (x t) = 0 := by
    rcases mul_eq_zero.1 (show w t * (f.eval (x t) * f.eval (x t)) = 0 by linarith) with h | h
    · linarith
    · exact h
  exact mul_self_eq_zero.1 this

/-- `⟨f, f⟩ > 0` for a nonzero polynomial of degree at most `N`. -/
theorem ip_self_pos (hx : Function.Injective x) (hw : ∀ t, 0 < w t) (f : ℝ[X]) (hf : f ≠ 0)
    (hd : f.natDegree ≤ N) : 0 < ip x w f f := by
  rcases (ip_self_nonneg hw f).lt_or_eq with h | h
  · exact h
  · exact absurd (Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero f hx
      (eval_zero_of_ip_self hw f h.symm) (by simp; omega)) hf

theorem h_pos (hx : Function.Injective x) (hw : ∀ t, 0 < w t) (n : ℕ) (hn : n ≤ N) :
    0 < ip x w (P x w n) (P x w n) :=
  ip_self_pos hx hw _ (Polynomial.Monic.ne_zero (P_monic x w n).1) (by rw [(P_monic x w n).2]; exact hn)

/-! ### Orthogonality -/

theorem ip_Pm_P (n : ℕ) (h : ∀ m < n, ip x w (P x w n) (P x w m) = 0) : ip x w (Pm x w n) (P x w n) = 0 := by
  rcases n with _ | n
  · rw [Pm_zero, ip_zero]
  · rw [Pm_succ, ip_comm]; exact h n (by omega)

/-- `⟨P_n, P_m⟩ = 0` for `m < n ≤ N + 1`. -/
theorem P_orth (hx : Function.Injective x) (hw : ∀ t, 0 < w t) :
    ∀ n, n ≤ N + 1 → ∀ m < n, ip x w (P x w n) (P x w m) = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro hn m hm
  obtain ⟨n, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have IH : ∀ k < n + 1, k ≤ N + 1 → ∀ j < k, ip x w (P x w k) (P x w j) = 0 := fun k hk hkN j hj =>
    ih k hk hkN j hj
  have hhn := h_pos hx hw n (by omega)
  have expand : ip x w (P x w (n + 1)) (P x w m) = ip x w (X * P x w n) (P x w m) -
      β x w n * ip x w (P x w n) (P x w m) - γ x w n * ip x w (Pm x w n) (P x w m) := by
    rw [P_succ, show (X - C (β x w n)) * P x w n - C (γ x w n) * Pm x w n =
      X * P x w n - C (β x w n) * P x w n - C (γ x w n) * Pm x w n by ring, ip_sub, ip_sub, ip_C_mul, ip_C_mul]
  rw [expand]
  rcases Nat.lt_succ_iff_lt_or_eq.1 hm with hm | rfl
  · -- `m < n`
    have e1 : ip x w (X * P x w n) (P x w m) = ip x w (P x w n) (P x w (m + 1)) +
        β x w m * ip x w (P x w n) (P x w m) + γ x w m * ip x w (P x w n) (Pm x w m) := by
      rw [ip_X, X_mul_P, ip_add', ip_add', ip_C_mul', ip_C_mul']
    have o1 : ip x w (P x w n) (P x w m) = 0 := IH n (by omega) (by omega) m hm
    have o3 : ip x w (P x w n) (Pm x w m) = 0 := by
      rcases m with _ | m
      · rw [Pm_zero, ip_comm, ip_zero]
      · rw [Pm_succ]; exact IH n (by omega) (by omega) m (by omega)
    rw [e1, o1, o3]
    rcases Nat.lt_or_ge (m + 1) n with h1 | h1
    · have o5 : ip x w (P x w n) (P x w (m + 1)) = 0 := IH n (by omega) (by omega) _ h1
      have o6 : ip x w (Pm x w n) (P x w m) = 0 := by
        obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
        rw [Pm_succ]; exact IH k (by omega) (by omega) m (by omega)
      rw [o5, o6]; ring
    · obtain rfl : n = m + 1 := by omega
      have hm0 := h_pos hx hw m (by omega)
      have hg : γ x w (m + 1) = ip x w (P x w (m + 1)) (P x w (m + 1)) / ip x w (P x w m) (P x w m) := by
        rw [γ, if_neg (Nat.succ_ne_zero m), Pm_succ]
      rw [Pm_succ, hg]
      field_simp
      ring
  · -- `m = n`
    rw [β, ip_Pm_P m (fun j hj => IH m (by omega) (by omega) j hj)]
    field_simp
    ring


/-! ### Orthogonality to all lower-degree polynomials -/

/-- If `g` is orthogonal to polynomials `F_k` of exact degree `k < n`, it is orthogonal to every polynomial of
degree `< n`. -/
theorem ip_low (n : ℕ) (F : ℕ → ℝ[X]) (hF : ∀ k < n, (F k).natDegree = k ∧ F k ≠ 0) (g : ℝ[X])
    (hg : ∀ k < n, ip x w g (F k) = 0) : ∀ f : ℝ[X], f.natDegree < n → ip x w g f = 0 := by
  intro f
  induction hd : f.natDegree using Nat.strong_induction_on generalizing f with
  | _ d ih =>
  intro hdn
  by_cases hf0 : f = 0
  · rw [hf0, ip_comm, ip_zero]
  obtain ⟨hFd, hF0⟩ := hF d hdn
  set a := f.leadingCoeff / (F d).leadingCoeff with ha
  have hlc0 : (F d).leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hF0
  have hsplit : f = (f - C a * F d) + C a * F d := by ring
  have hdeg : (C a * F d).degree = f.degree := by
    have ha0 : a ≠ 0 := div_ne_zero (leadingCoeff_ne_zero.mpr hf0) hlc0
    rw [degree_C_mul ha0, degree_eq_natDegree hF0, degree_eq_natDegree hf0, hFd, hd]
  have hlc : (C a * F d).leadingCoeff = f.leadingCoeff := by
    rw [leadingCoeff_C_mul_of_isUnit, ha]
    · field_simp
    · exact isUnit_iff_ne_zero.mpr (div_ne_zero (leadingCoeff_ne_zero.mpr hf0) hlc0)
  rw [hsplit, ip_add', ip_C_mul', hg d hdn, mul_zero, add_zero]
  by_cases h0 : f - C a * F d = 0
  · rw [h0, ip_comm, ip_zero]
  · have hlt : (f - C a * F d).degree < f.degree := degree_sub_lt_left hdeg.symm hf0 hlc.symm
    have hlt' : (f - C a * F d).natDegree < d := by
      have := natDegree_lt_natDegree h0 hlt; rwa [hd] at this
    exact ih _ hlt' _ rfl (by omega)

/-- `P_n` is orthogonal to every polynomial of degree `< n`, for `n ≤ N + 1`. -/
theorem P_orth_low (hx : Function.Injective x) (hw : ∀ t, 0 < w t) (n : ℕ) (hn : n ≤ N + 1) (f : ℝ[X])
    (hf : f.natDegree < n) : ip x w (P x w n) f = 0 :=
  ip_low n (P x w) (fun k _ => ⟨(P_monic x w k).2, Polynomial.Monic.ne_zero (P_monic x w k).1⟩) _
    (fun k hk => P_orth hx hw n hn k hk) f hf

/-- `P_{N+1}` vanishes on the support. -/
theorem P_terminal (hx : Function.Injective x) (hw : ∀ t, 0 < w t) (t : Fin (N + 1)) :
    (P x w (N + 1)).eval (x t) = 0 := by
  set Z : ℝ[X] := ∏ s : Fin (N + 1), (X - C (x s)) with hZ
  have hZm : Z.Monic := monic_prod_of_monic _ _ fun s _ => Polynomial.monic_X_sub_C _
  have hZd : Z.natDegree = N + 1 := by
    rw [hZ, natDegree_prod_of_monic _ _ fun s _ => Polynomial.monic_X_sub_C _]
    simp
  have hZe : ∀ t, Z.eval (x t) = 0 := fun t => by
    rw [hZ, eval_prod]; exact prod_eq_zero (mem_univ t) (by simp)
  obtain ⟨hPm, hPd⟩ := P_monic x w (N + 1)
  have hPZ : ip x w (P x w (N + 1)) Z = 0 := by
    unfold ip; exact sum_eq_zero fun s _ => by rw [hZe s, mul_zero]
  have hD : ip x w (P x w (N + 1)) (P x w (N + 1) - Z) = 0 := by
    by_cases h0 : P x w (N + 1) - Z = 0
    · rw [h0, ip_comm, ip_zero]
    · apply P_orth_low hx hw (N + 1) le_rfl
      have hlt : (P x w (N + 1) - Z).degree < (P x w (N + 1)).degree :=
        degree_sub_lt_left (by rw [degree_eq_natDegree hPm.ne_zero, degree_eq_natDegree hZm.ne_zero, hPd, hZd])
          hPm.ne_zero (by rw [hPm.leadingCoeff, hZm.leadingCoeff])
      have := natDegree_lt_natDegree h0 hlt; rwa [hPd] at this
  have hself : ip x w (P x w (N + 1)) (P x w (N + 1)) = 0 := by
    calc ip x w (P x w (N + 1)) (P x w (N + 1)) = ip x w (P x w (N + 1)) ((P x w (N + 1) - Z) + Z) := by
          rw [sub_add_cancel]
      _ = 0 := by rw [ip_add', hD, hPZ, add_zero]
  exact eval_zero_of_ip_self hw _ hself t

/-! ### Christoffel–Darboux and positivity at the top node -/

theorem eval_P_one : ∀ z, (P x w 1).eval z = z - β x w 0 := fun z => by
  simp [P_succ, P_zero, Pm_zero]

/-- The Christoffel–Darboux identity at two nodes. -/
theorem christoffel_darboux (hx : Function.Injective x) (hw : ∀ t, 0 < w t) :
    ∀ m, m ≤ N → ∀ s t : Fin (N + 1),
      (x s - x t) * ∑ k ∈ range (m + 1), (P x w k).eval (x s) * (P x w k).eval (x t) / ip x w (P x w k) (P x w k) =
        ((P x w (m + 1)).eval (x s) * (P x w m).eval (x t) - (P x w m).eval (x s) * (P x w (m + 1)).eval (x t)) /
          ip x w (P x w m) (P x w m)
  | 0, _, s, t => by
    have h0 := h_pos hx hw 0 (by omega)
    rw [Finset.sum_range_one, eval_P_one, eval_P_one]
    simp only [P_zero, eval_one]
    field_simp
    ring
  | m + 1, hm, s, t => by
    have ih := christoffel_darboux hx hw m (by omega) s t
    have hm0 := h_pos hx hw m (by omega)
    have hm1 := h_pos hx hw (m + 1) hm
    have hg : γ x w (m + 1) = ip x w (P x w (m + 1)) (P x w (m + 1)) / ip x w (P x w m) (P x w m) := by
      rw [γ, if_neg (Nat.succ_ne_zero m), Pm_succ]
    have hrec : ∀ z, (P x w (m + 1 + 1)).eval z =
        (z - β x w (m + 1)) * (P x w (m + 1)).eval z - γ x w (m + 1) * (P x w m).eval z := fun z => by
      rw [P_succ, Pm_succ]; simp only [eval_sub, eval_mul, eval_X, eval_C]
    rw [sum_range_succ, mul_add, ih, hrec, hrec, hg]
    field_simp
    ring

/-- `P_n(x_{t₀}) > 0` for `n ≤ N`, where `x_{t₀}` is the largest node. -/
theorem P_top_pos (hN : 1 ≤ N) (hx : Function.Injective x) (hw : ∀ t, 0 < w t) (t0 : Fin (N + 1))
    (htop : ∀ t, x t ≤ x t0) : ∀ n, n ≤ N → 0 < (P x w n).eval (x t0)
  | 0, _ => by simp [P_zero]
  | n + 1, hn => by
    have ih := P_top_pos hN hx hw t0 htop n (by omega)
    have hhn := h_pos hx hw n (by omega)
    set u : ℕ → Fin (N + 1) → ℝ := fun k t => (P x w k).eval (x t) with hu
    set h : ℕ → ℝ := fun k => ip x w (P x w k) (P x w k) with hh
    set K : Fin (N + 1) → ℝ := fun t => ∑ k ∈ range (n + 1), u k t * u k t0 / h k with hK
    have hcd : ∀ t, (x t - x t0) * K t = (u (n + 1) t * u n t0 - u n t * u (n + 1) t0) / h n := fun t =>
      christoffel_darboux hx hw n (by omega) t t0
    -- `Σ_t w_t K_t u_j(t) = Σ_k (u_k(t₀)/h_k) ⟨P_k, P_j⟩`
    have hKu : ∀ j, ∑ t, w t * K t * u j t = ∑ k ∈ range (n + 1), u k t0 / h k * ip x w (P x w k) (P x w j) := by
      intro j
      simp only [hK, hu, ip, mul_sum, sum_mul]
      rw [sum_comm]
      exact sum_congr rfl fun k _ => sum_congr rfl fun t _ => by ring
    have hK1 : ∑ t, w t * K t * u (n + 1) t = 0 := by
      rw [hKu]
      exact sum_eq_zero fun k hk => by
        rw [ip_comm, P_orth hx hw (n + 1) (by omega) k (by simp at hk; omega), mul_zero]
    have hK0 : ∑ t, w t * K t * u n t = u n t0 := by
      rw [hKu, sum_range_succ, sum_eq_zero fun k hk => by
        rw [ip_comm, P_orth hx hw n (by omega) k (by simp at hk; omega), mul_zero]]
      simp only [hh]
      field_simp
      ring
    have hS : ∑ t, w t * (x t0 - x t) * K t ^ 2 = u (n + 1) t0 * u n t0 / h n := by
      calc ∑ t, w t * (x t0 - x t) * K t ^ 2
          = ∑ t, (u (n + 1) t0 * (w t * K t * u n t) - u n t0 * (w t * K t * u (n + 1) t)) / h n :=
            sum_congr rfl fun t _ => by
              rw [show w t * (x t0 - x t) * K t ^ 2 = -((x t - x t0) * K t) * (w t * K t) by ring, hcd t]
              ring
        _ = (u (n + 1) t0 * ∑ t, w t * K t * u n t - u n t0 * ∑ t, w t * K t * u (n + 1) t) / h n := by
            rw [← Finset.sum_div, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
        _ = u (n + 1) t0 * u n t0 / h n := by rw [hK0, hK1]; ring
    -- `K` is the polynomial `Σ_k (u_k(t₀)/h_k) P_k` of degree `≤ n < N`, positive at `x_{t₀}`
    set KP : ℝ[X] := ∑ k ∈ range (n + 1), C (u k t0 / h k) * P x w k with hKP
    have hKPe : ∀ t, KP.eval (x t) = K t := fun t => by
      simp only [hKP, hK, eval_finsetSum, eval_mul, eval_C, hu]
      exact sum_congr rfl fun k _ => by ring
    have hKPd : KP.natDegree ≤ n := by
      apply natDegree_sum_le_of_forall_le
      intro k hk
      refine (natDegree_C_mul_le _ _).trans ?_
      rw [(P_monic x w k).2]; simp at hk; omega
    have hKt0 : 0 < K t0 := by
      simp only [hK]
      rw [sum_range_succ']
      have h0 := h_pos hx hw 0 (by omega)
      have hrest : 0 ≤ ∑ k ∈ range n, u (k + 1) t0 * u (k + 1) t0 / h (k + 1) :=
        sum_nonneg fun k hk => div_nonneg (mul_self_nonneg _) (h_pos hx hw (k + 1) (by simp at hk; omega)).le
      have : u 0 t0 * u 0 t0 / h 0 = 1 / h 0 := by simp [hu, P_zero]
      rw [this]
      exact add_pos_of_nonneg_of_pos hrest (by positivity)
    have hex : ∃ t, t ≠ t0 ∧ K t ≠ 0 := by
      by_contra hno
      simp only [not_exists, not_and, ne_eq, not_not] at hno
      have hz : KP = 0 := by
        apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero KP
          (f := fun t : {t : Fin (N + 1) // t ≠ t0} => x t.1)
          (fun a b hab => Subtype.ext (hx hab))
        · intro t; rw [hKPe]; exact hno t.1 t.2
        · rw [Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_unique]; omega
      have := hKPe t0
      rw [hz, eval_zero] at this
      linarith
    obtain ⟨t1, ht1, hKt1⟩ := hex
    have hlt : x t1 < x t0 := lt_of_le_of_ne (htop t1) (fun h => ht1 (hx h))
    have hSpos : 0 < ∑ t, w t * (x t0 - x t) * K t ^ 2 := by
      apply lt_of_lt_of_le _ (single_le_sum (fun t _ => by
        have := htop t; have := hw t; positivity) (mem_univ t1))
      have := hw t1
      have : 0 < K t1 ^ 2 := by positivity
      have : 0 < x t0 - x t1 := by linarith
      positivity
    rw [hS] at hSpos
    have hprod : 0 < u (n + 1) t0 * u n t0 := by
      have := div_pos_iff.mp hSpos
      rcases this with ⟨h1, _⟩ | ⟨_, h2⟩
      · exact h1
      · exact absurd h2 (not_lt.mpr hhn.le)
    exact pos_of_mul_pos_left hprod ih.le


/-! ### The normalized array -/

section array

variable (x w) (t0 : Fin (N + 1))

/-- `π_n = P_n(x_{t₀})`. -/
noncomputable def ptop (n : ℕ) : ℝ := (P x w n).eval (x t0)
/-- `π_{n-1}` (`1` for `n = 0`). -/
noncomputable def ptopm (n : ℕ) : ℝ := if n = 0 then 1 else ptop x w t0 (n - 1)
/-- The scale `s = 1/π_1 = 1/(x_{t₀} - β_0)`. -/
noncomputable def sc : ℝ := 1 / ptop x w t0 1
/-- The shift `c = -β_0 s`, so that `y = s x + c = R_1(x)`. -/
noncomputable def sh : ℝ := -(β x w 0 * sc x w t0)

/-- The array of the normalized polynomials `R_n = P_n / π_n` in the coordinate `y = s x + c`. -/
noncomputable def arr : Coefficients N where
  a n := if n < N then sc x w t0 * ptop x w t0 (n + 1) / ptop x w t0 n else 0
  b n := sc x w t0 * β x w n + sh x w t0
  c n := sc x w t0 * γ x w n * ptopm x w t0 n / ptop x w t0 n

end array

theorem ptopm_succ (t0 : Fin (N + 1)) (n : ℕ) : ptopm x w t0 (n + 1) = ptop x w t0 n := by simp [ptopm]

/-- `γ_n P_{n-1}(x_{t₀}) = γ_n π_{n-1}` (both sides vanish for `n = 0`). -/
theorem gamma_Pm_top (t0 : Fin (N + 1)) (n : ℕ) :
    γ x w n * (Pm x w n).eval (x t0) = γ x w n * ptopm x w t0 n := by
  rcases n with _ | n
  · simp [γ]
  · rw [Pm_succ, ptopm_succ]; rfl

/-- The polynomials of `arr` are `R_n(s z + c) = P_n(z) / π_n`. -/
theorem arr_eval (hN : 1 ≤ N) (hx : Function.Injective x) (hw : ∀ t, 0 < w t) (t0 : Fin (N + 1))
    (htop : ∀ t, x t ≤ x t0) :
    ∀ n, n ≤ N → ∀ z : ℝ,
      (polynomialPair (arr x w t0) n).2.eval (sc x w t0 * z + sh x w t0) = (P x w n).eval z / ptop x w t0 n ∧
      (polynomialPair (arr x w t0) n).1.eval (sc x w t0 * z + sh x w t0) = (Pm x w n).eval z / ptopm x w t0 n
  | 0, _, z => by simp [polynomialPair, P_zero, Pm_zero, ptop]
  | n + 1, hn, z => by
    obtain ⟨ih2, ih1⟩ := arr_eval hN hx hw t0 htop n (by omega) z
    have hpos := P_top_pos hN hx hw t0 htop
    have hpn : 0 < ptop x w t0 n := hpos n (by omega)
    have hpn1 : 0 < ptop x w t0 (n + 1) := hpos (n + 1) hn
    have hp1 : 0 < ptop x w t0 1 := hpos 1 hN
    have hpm : 0 < ptopm x w t0 n := by
      rcases n with _ | n
      · simp [ptopm]
      · rw [ptopm_succ]; exact hpos n (by omega)
    refine ⟨?_, ?_⟩
    · show (C ((arr x w t0).a n)⁻¹ * ((X - C ((arr x w t0).b n)) * (polynomialPair (arr x w t0) n).2 -
        C ((arr x w t0).c n) * (polynomialPair (arr x w t0) n).1)).eval _ = _
      simp only [eval_mul, eval_C, eval_sub, eval_X, ih2, ih1]
      simp only [arr, if_pos (show n < N by omega), sc, sh, P_succ, eval_sub, eval_mul, eval_X, eval_C]
      field_simp
      ring
    · show (polynomialPair (arr x w t0) n).2.eval _ = _
      rw [ih2, Pm_succ, ptopm_succ]

/-- **P3, Section 9: reduction of finite systems to the normalized recurrence.** Let `Σ_t w_t δ_{x_t}` be a
positive measure on `N + 1 ≥ 2` distinct real points with largest point `x_{t₀}`. Then there are an array `v`
satisfying (2.1) and an affine change `y = s x + c` with `s > 0` and `y(x_{t₀}) = 1` such that the polynomials
`R_n` of `v`, at the points `y_t = s x_t + c`, are orthogonal for the weights `w_t`, satisfy the terminal relation
and the product identity `R_m R_n = Σ_k g(m,n;k) R_k`; and every family `p_n` (`deg p_n = n`) of orthogonal
polynomials of the measure with `p_n(x_{t₀}) = 1` is `p_n(z) = R_n(s z + c)`. -/
theorem finite_system_reduction (hN : 1 ≤ N) (hx : Function.Injective x) (hw : ∀ t, 0 < w t)
    (t0 : Fin (N + 1)) (htop : ∀ t, x t ≤ x t0) :
    ∃ (v : Coefficients N) (s c : ℝ), Admissible v ∧ 0 < s ∧ s * x t0 + c = 1 ∧
      (∀ m n, m ≤ N → n ≤ N → m ≠ n →
        ∑ t, w t * (recurrencePolynomial v m).eval (s * x t + c) * (recurrencePolynomial v n).eval (s * x t + c) = 0) ∧
      (∀ t, (s * x t + c - v.b N) * (recurrencePolynomial v N).eval (s * x t + c) -
        v.c N * (recurrencePolynomial v (N - 1)).eval (s * x t + c) = 0) ∧
      (∀ (m : ℕ) (n t : Fin (N + 1)), m ≤ N →
        (recurrencePolynomial v m).eval (s * x t + c) * (recurrencePolynomial v n.val).eval (s * x t + c) =
          ∑ k : Fin (N + 1), productMatrix v m n k * (recurrencePolynomial v k.val).eval (s * x t + c)) ∧
      (∀ p : ℕ → ℝ[X], (∀ n, n ≤ N → (p n).natDegree = n) →
        (∀ m n, m ≤ N → n ≤ N → m ≠ n → ∑ t, w t * (p m).eval (x t) * (p n).eval (x t) = 0) →
        (∀ n, n ≤ N → (p n).eval (x t0) = 1) →
        ∀ n, n ≤ N → ∀ z, (p n).eval z = (recurrencePolynomial v n).eval (s * z + c)) := by
  have hpos := P_top_pos hN hx hw t0 htop
  have hp1 : 0 < ptop x w t0 1 := hpos 1 hN
  have hR := arr_eval hN hx hw t0 htop
  set v := arr x w t0 with hv
  set s := sc x w t0 with hs
  set c := sh x w t0 with hc
  have hs0 : 0 < s := by simp only [hs, sc]; positivity
  have hP1 : ptop x w t0 1 = x t0 - β x w 0 := eval_P_one _
  have hy0 : s * x t0 + c = 1 := by
    simp only [hs, hc, sc, sh]; rw [hP1] at hp1 ⊢; field_simp; ring
  have hRe : ∀ n, n ≤ N → ∀ z, (recurrencePolynomial v n).eval (s * z + c) = (P x w n).eval z / ptop x w t0 n :=
    fun n hn z => (hR n hn z).1
  -- the recurrence at the top node
  have htopRec : ∀ i, ptop x w t0 (i + 1) =
      (x t0 - β x w i) * ptop x w t0 i - γ x w i * ptopm x w t0 i := fun i => by
    rw [← gamma_Pm_top]; simp only [ptop, P_succ, eval_sub, eval_mul, eval_X, eval_C]
  have hterm0 : ptop x w t0 (N + 1) = 0 := P_terminal hx hw t0
  have hpm : ∀ i, i ≤ N → 0 < ptopm x w t0 i := fun i hi => by
    rcases i with _ | i
    · simp [ptopm]
    · rw [ptopm_succ]; exact hpos i (by omega)
  have hγ : ∀ i, 1 ≤ i → i ≤ N → 0 < γ x w i := fun i h1 hi => by
    obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    rw [γ, if_neg (Nat.succ_ne_zero j), Pm_succ]
    exact div_pos (h_pos hx hw _ hi) (h_pos hx hw j (by omega))
  -- admissibility
  have hadm : Admissible v := by
    refine ⟨hN, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [hv, arr, if_pos (show 0 < N by omega), sc]
      have h0 : ptop x w t0 0 = 1 := by simp [ptop, P_zero]
      rw [h0, div_one, one_div_mul_cancel hp1.ne']
    · simp only [hv, arr, sh, sc]; ring
    · simp [hv, arr, γ]
    · simp [hv, arr]
    · intro i hi
      have hpi : 0 < ptop x w t0 i := hpos i hi
      have hpmi : 0 < ptopm x w t0 i := hpm i hi
      have hrow : s * ptop x w t0 (i + 1) / ptop x w t0 i + (s * β x w i + c) +
          s * γ x w i * ptopm x w t0 i / ptop x w t0 i = 1 := by
        rw [htopRec i, ← hy0]; field_simp; ring
      rcases Nat.lt_or_ge i N with h | h
      · simp only [hv, arr, if_pos h]; rw [← hs, ← hc]; exact hrow
      · obtain rfl : i = N := by omega
        simp only [hv, arr, lt_irrefl, if_false]; rw [← hs, ← hc]
        rw [hterm0, mul_zero, zero_div, zero_add] at hrow
        linarith
    · intro i hi
      simp only [hv, arr, if_pos hi]
      exact div_pos (mul_pos hs0 (hpos (i + 1) hi)) (hpos i hi.le)
    · intro i h1 hi
      simp only [hv, arr]
      exact div_pos (mul_pos (mul_pos hs0 (hγ i h1 hi)) (hpm i hi)) (hpos i hi)
  have hterm_all : ∀ t, (s * x t + c - v.b N) * (recurrencePolynomial v N).eval (s * x t + c) -
      v.c N * (recurrencePolynomial v (N - 1)).eval (s * x t + c) = 0 := by
    intro t
    obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
    rw [hRe (M + 1) le_rfl, show M + 1 - 1 = M by omega, hRe M (by omega)]
    have hterm := P_terminal hx hw t
    rw [P_succ, Pm_succ] at hterm
    simp only [eval_sub, eval_mul, eval_X, eval_C] at hterm
    have hpM : 0 < ptop x w t0 M := hpos M (by omega)
    have hpM1 : 0 < ptop x w t0 (M + 1) := hpos (M + 1) le_rfl
    have key : (s * x t + c - v.b (M + 1)) * ((P x w (M + 1)).eval (x t) / ptop x w t0 (M + 1)) -
        v.c (M + 1) * ((P x w M).eval (x t) / ptop x w t0 M) =
        s / ptop x w t0 (M + 1) * ((x t - β x w (M + 1)) * (P x w (M + 1)).eval (x t) -
          γ x w (M + 1) * (P x w M).eval (x t)) := by
      simp only [hv, arr, ptopm_succ]
      rw [← hs, ← hc]
      field_simp
      ring
    rw [key, hterm, mul_zero]
  refine ⟨v, s, c, hadm, hs0, hy0, ?_, hterm_all, ?_, ?_⟩
  · -- orthogonality
    intro m n hm hn hmn
    have e : ∀ t, w t * (recurrencePolynomial v m).eval (s * x t + c) * (recurrencePolynomial v n).eval (s * x t + c) =
        (w t * (P x w m).eval (x t) * (P x w n).eval (x t)) / (ptop x w t0 m * ptop x w t0 n) := fun t => by
      rw [hRe m hm, hRe n hn]; field_simp
    simp only [e, ← Finset.sum_div]
    have hip : ip x w (P x w m) (P x w n) = 0 := by
      rcases Nat.lt_or_gt_of_ne hmn with h | h
      · rw [ip_comm]; exact P_orth hx hw n (by omega) m h
      · exact P_orth hx hw m (by omega) n h
    rw [show ∑ t, w t * (P x w m).eval (x t) * (P x w n).eval (x t) = ip x w (P x w m) (P x w n) from rfl, hip,
      zero_div]
  · -- product identity at the nodes
    intro m n t hm
    set y := s * x t + c with hy
    set U : ℕ → ℝ := fun j => if j ≤ N then (recurrencePolynomial v j).eval y else 0 with hU
    have hU0 : ∀ j, N < j → U j = 0 := fun j hj => by simp only [hU]; rw [if_neg (by omega)]
    have hval : ∀ j, j ≤ N → U j = (P x w j).eval (x t) / ptop x w t0 j := fun j hj => by
      simp only [hU]; rw [if_pos hj]; exact hRe j hj (x t)
    have hcterm : ∀ i, 1 ≤ i → i ≤ N → v.c i * U (i - 1) =
        s * γ x w i * (Pm x w i).eval (x t) / ptop x w t0 i := fun i h1 hi => by
      obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
      have hpj : 0 < ptop x w t0 j := hpos j (by omega)
      have hpj1 : 0 < ptop x w t0 (j + 1) := hpos (j + 1) hi
      rw [show j + 1 - 1 = j by omega, hval j (by omega), Pm_succ]
      simp only [hv, arr, ptopm_succ]
      rw [← hs]
      field_simp
    have hJ : ∀ i : Fin (N + 1), y * U i.val = ∑ j : Fin (N + 1), recurrenceMatrix v i j • U j.val := by
      intro i
      rw [recurrence_row_action v U hU0 i]
      have hi := i.isLt
      have hpi : 0 < ptop x w t0 i.val := hpos i.val (by omega)
      have hc' : (if i.val = 0 then 0 else v.c i.val • U (i.val - 1)) =
          s * γ x w i.val * (Pm x w i.val).eval (x t) / ptop x w t0 i.val := by
        rcases Nat.eq_zero_or_pos i.val with h0 | h0
        · rw [if_pos h0, h0]; simp [γ]
        · rw [if_neg (by omega), smul_eq_mul]; exact hcterm i.val h0 (by omega)
      rw [hc', hval i.val (by omega)]
      rcases Nat.lt_or_ge i.val N with h | h
      · have hpi1 : 0 < ptop x w t0 (i.val + 1) := hpos (i.val + 1) h
        have hrec := congrArg (eval (x t)) (X_mul_P x w i.val)
        simp only [eval_mul, eval_X, eval_add, eval_C] at hrec
        rw [hval (i.val + 1) h]
        simp only [hv, arr, if_pos h, smul_eq_mul]
        rw [← hs, ← hc, hy]
        have key : s * ptop x w t0 (i.val + 1) / ptop x w t0 i.val *
              ((P x w (i.val + 1)).eval (x t) / ptop x w t0 (i.val + 1)) +
            (s * β x w i.val + c) * ((P x w i.val).eval (x t) / ptop x w t0 i.val) +
            s * γ x w i.val * (Pm x w i.val).eval (x t) / ptop x w t0 i.val =
            (s * ((P x w (i.val + 1)).eval (x t) + β x w i.val * (P x w i.val).eval (x t) +
              γ x w i.val * (Pm x w i.val).eval (x t)) + c * (P x w i.val).eval (x t)) / ptop x w t0 i.val := by
          field_simp
          ring
        rw [key, ← hrec]
        field_simp
      · obtain hN' : i.val = N := by omega
        have ht := hterm_all t
        rw [hN', hU0 (N + 1) (by omega)]
        rw [hRe N le_rfl, hRe (N - 1) (by omega)] at ht
        have hpN : 0 < ptop x w t0 N := hpos N le_rfl
        have hpN1 : 0 < ptop x w t0 (N - 1) := hpos (N - 1) (by omega)
        obtain ⟨M, hM⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
        have hcN : v.c N * ((P x w (N - 1)).eval (x t) / ptop x w t0 (N - 1)) =
            s * γ x w N * (Pm x w N).eval (x t) / ptop x w t0 N := by
          have := hcterm N hN le_rfl
          rw [hval (N - 1) (by omega)] at this
          exact this
        rw [← hcN]
        simp only [smul_eq_mul, hadm.2.2.2.2.1, zero_mul, zero_add]
        rw [hy]
        linear_combination ht
    have h := representation_product v (fun j : Fin (N + 1) => U j.val) y hJ m n
    simp only [Polynomial.coe_aeval_eq_eval, smul_eq_mul] at h
    have hn := n.isLt
    rw [show U n.val = (recurrencePolynomial v n.val).eval y by simp only [hU]; rw [if_pos (by omega)]] at h
    rw [h]
    exact sum_congr rfl fun k _ => by
      have := k.isLt
      simp only [hU]; rw [if_pos (by omega)]
  · -- uniqueness of the normalized orthogonal polynomials
    intro p hpd hporth hp1' n hn z
    have hne : ∀ k, k ≤ N → p k ≠ 0 := fun k hk h => by
      have := hp1' k hk; rw [h, eval_zero] at this; exact zero_ne_one this
    have hp0 := hne n hn
    set a := (p n).leadingCoeff with ha_def
    have ha : a ≠ 0 := leadingCoeff_ne_zero.mpr hp0
    have hPn := P_monic x w n
    have hq : p n - C a * P x w n = 0 := by
      by_contra hq0
      have hdeg : (C a * P x w n).degree = (p n).degree := by
        rw [degree_C_mul ha, degree_eq_natDegree (Polynomial.Monic.ne_zero hPn.1), degree_eq_natDegree hp0,
          hPn.2, hpd n hn]
      have hlc : (C a * P x w n).leadingCoeff = (p n).leadingCoeff := by
        rw [leadingCoeff_mul, leadingCoeff_C, hPn.1.leadingCoeff, mul_one]
      have hlt := degree_sub_lt_left hdeg.symm hp0 hlc.symm
      have hnd : (p n - C a * P x w n).natDegree < n := by
        have := natDegree_lt_natDegree hq0 hlt; rwa [hpd n hn] at this
      have h1 : ip x w (p n) (p n - C a * P x w n) = 0 :=
        ip_low n p (fun k hk => ⟨hpd k (by omega), hne k (by omega)⟩) (p n)
          (fun k hk => hporth n k hn (by omega) (by omega)) _ hnd
      have h2 : ip x w (P x w n) (p n - C a * P x w n) = 0 := P_orth_low hx hw n (by omega) _ hnd
      have hself : ip x w (p n - C a * P x w n) (p n - C a * P x w n) = 0 := by
        rw [ip_sub, ip_C_mul, h1, h2, mul_zero, sub_zero]
      exact hq0 (Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero _ hx
        (eval_zero_of_ip_self hw _ hself) (by simp; omega))
    have hpn : p n = C a * P x w n := sub_eq_zero.mp hq
    have hpN : 0 < ptop x w t0 n := hpos n hn
    have ha' : a * ptop x w t0 n = 1 := by
      have := hp1' n hn; rw [hpn, eval_mul, eval_C] at this; exact this
    rw [hRe n hn z, hpn, eval_mul, eval_C]
    field_simp
    linear_combination (P x w n).eval z * ha'

end FinSys

end Szkraw
