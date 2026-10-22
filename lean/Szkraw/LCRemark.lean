import Szkraw.LCGraded
import Szkraw.LCAssembly
import Szkraw.Reversal

/-!
# The remark after Theorem 8.1: nonnegative two-parameter and Bernstein coefficients

The kernel of Theorem 8.1 is a polynomial in `t` with nonnegative coefficients. Hence every
linearization coefficient of `y p_i = a_i p_{i+1} + u d_i p_i + v d_i p_{i-1}` is
`Σ_j h_j u^{D-2j} v^j` with `h_j ≥ 0` (`D = m + n - k`), and for the arrays of Theorem 8.1 every
`g(m,n;k)` has nonnegative Bernstein coefficients in `r`.
-/

namespace Szkraw

open Finset

/-! ### The graded kernel -/

/-- Levels `0, …, L` of the graded kernel. -/
noncomputable def kerLevelsG (u : ℕ → ℝ) (T : ℝ) (k : ℕ) : ℕ → (ℕ → ℕ → ℕ → ℝ)
  | 0 => fun ℓ a p => if ℓ = 0 ∧ a = k ∧ p = 0 then 1 else 0
  | L + 1 => fun ℓ a p =>
      if ℓ ≤ L then kerLevelsG u T k L ℓ a p
      else ((T - dd u (L + a)) * kerLevelsG u T k L L a p +
        ∑ j ∈ range (L + 1), (-1 : ℝ) ^ j * grpG u (kerLevelsG u T k L) j L a p) / dd u (L + 1)

/-- The coefficient of `t^p` in the kernel with `ω(0,a) = [a = k]`. -/
noncomputable def kerFnG (u : ℕ → ℝ) (T : ℝ) (k ℓ a p : ℕ) : ℝ := kerLevelsG u T k ℓ ℓ a p

variable {u : ℕ → ℝ} {T : ℝ} {k : ℕ}

theorem kerLevelsG_eq (L : ℕ) : ∀ ℓ a p, ℓ ≤ L → kerLevelsG u T k L ℓ a p = kerFnG u T k ℓ a p := by
  induction L with
  | zero => intro ℓ a p h; rw [Nat.le_zero.mp h]; rfl
  | succ L ih =>
    intro ℓ a p h
    by_cases hl : ℓ ≤ L
    · show (if ℓ ≤ L then kerLevelsG u T k L ℓ a p else _) = _
      rw [if_pos hl, ih ℓ a p hl]
    · have : ℓ = L + 1 := by omega
      subst this; rfl

theorem grpG_congr {Ω₁ Ω₂ : ℕ → ℕ → ℕ → ℝ} {ℓ : ℕ} (h : ∀ ℓ' a p, ℓ' ≤ ℓ → Ω₁ ℓ' a p = Ω₂ ℓ' a p)
    (j a p : ℕ) : grpG u Ω₁ j ℓ a p = grpG u Ω₂ j ℓ a p := by
  unfold grpG moveAG moveBG moveCG
  rw [h _ _ _ (Nat.sub_le _ _), h _ _ _ (Nat.sub_le _ _)]
  split_ifs
  · rw [h _ _ _ (by omega)]
  · rfl

theorem kerFnG_rec (hu : LCNZ u) (hu1 : 0 < u 1) : KernelRecG u (kerFnG u T k) T := by
  intro ℓ a p
  have hd : dd u (ℓ + 1) ≠ 0 := ne_of_gt (dd_pos hu hu1 (by omega))
  have e : kerFnG u T k (ℓ + 1) a p =
      ((T - dd u (ℓ + a)) * kerLevelsG u T k ℓ ℓ a p +
        ∑ j ∈ range (ℓ + 1), (-1 : ℝ) ^ j * grpG u (kerLevelsG u T k ℓ) j ℓ a p) / dd u (ℓ + 1) := by
    show (if ℓ + 1 ≤ ℓ then _ else _) = _
    rw [if_neg (by omega)]
  rw [e, mul_div_cancel₀ _ hd]
  have hg : ∀ j, grpG u (kerLevelsG u T k ℓ) j ℓ a p = grpG u (kerFnG u T k) j ℓ a p :=
    fun j => grpG_congr (fun ℓ' a' p' h => kerLevelsG_eq ℓ ℓ' a' p' h) j a p
  simp only [hg]
  rfl

theorem kerFnG_zero (a p : ℕ) : kerFnG u T k 0 a p = if a = k ∧ p = 0 then 1 else 0 := by
  show (if 0 = 0 ∧ a = k ∧ p = 0 then (1 : ℝ) else 0) = _
  simp

/-- Support: `Ω(ℓ,a,p) = 0` for `ℓ + a > N`. -/
theorem kerFnG_supp (hu : LCNZ u) (hu1 : 0 < u 1) (N : ℕ) (hk : k ≤ N) (hT : T = dd u N) :
    ∀ ℓ a p, N < ℓ + a → kerFnG u T k ℓ a p = 0 := by
  intro ℓ
  induction ℓ using Nat.strong_induction_on with
  | _ ℓ ih =>
    intro a p ha
    rcases ℓ with _ | ℓ
    · rw [kerFnG_zero, if_neg (by omega)]
    · have hrec := kerFnG_rec (T := T) (k := k) hu hu1 ℓ a p
      have hd : dd u (ℓ + 1) ≠ 0 := ne_of_gt (dd_pos hu hu1 (by omega))
      have h1 : (T - dd u (ℓ + a)) * kerFnG u T k ℓ a p = 0 := by
        by_cases h : ℓ + a = N
        · rw [hT, h, sub_self, zero_mul]
        · rw [ih ℓ (by omega) a p (by omega), mul_zero]
      have h2 : ∀ j ∈ range (ℓ + 1), (-1 : ℝ) ^ j * grpG u (kerFnG u T k) j ℓ a p = 0 := by
        intro j hj
        rw [Finset.mem_range] at hj
        unfold grpG moveAG moveBG moveCG
        rw [ih (ℓ - j) (by omega) _ _ (by omega), ih (ℓ - j) (by omega) _ _ (by omega)]
        split_ifs
        · rw [ih (ℓ - j - 1) (by omega) _ _ (by omega)]; ring
        · ring
      rw [h1, sum_eq_zero h2, add_zero] at hrec
      exact (mul_eq_zero.mp hrec).resolve_left hd

/-- Degree and parity: `Ω(ℓ,a,p) = 0` unless `k + p ≤ a + 2ℓ` with `a + 2ℓ + k + p` even. -/
theorem kerFnG_deg (hu : LCNZ u) (hu1 : 0 < u 1) :
    ∀ ℓ a p, ¬(k + p ≤ a + 2 * ℓ ∧ (a + 2 * ℓ + k + p) % 2 = 0) → kerFnG u T k ℓ a p = 0 := by
  intro ℓ
  induction ℓ using Nat.strong_induction_on with
  | _ ℓ ih =>
    intro a p hc
    rcases ℓ with _ | ℓ
    · rw [kerFnG_zero, if_neg (by omega)]
    · have hrec := kerFnG_rec (T := T) (k := k) hu hu1 ℓ a p
      have hd : dd u (ℓ + 1) ≠ 0 := ne_of_gt (dd_pos hu hu1 (by omega))
      have h1 : kerFnG u T k ℓ a p = 0 := ih ℓ (by omega) a p (by omega)
      have h2 : ∀ j ∈ range (ℓ + 1), (-1 : ℝ) ^ j * grpG u (kerFnG u T k) j ℓ a p = 0 := by
        intro j hj
        rw [Finset.mem_range] at hj
        unfold grpG moveAG moveBG moveCG
        have hA : tau p * Wt u (2 * j + 1) j (ℓ - j) (a + 2 * j + 1) *
            kerFnG u T k (ℓ - j) (a + 2 * j + 1) (p - 1) = 0 := by
          unfold tau
          split_ifs with hp
          · rw [ih (ℓ - j) (by omega) _ _ (by omega), mul_zero]
          · ring
        rw [hA, ih (ℓ - j) (by omega) _ _ (by omega)]
        split_ifs
        · rw [ih (ℓ - j - 1) (by omega) _ _ (by omega)]; ring
        · ring
      rw [h1, mul_zero, sum_eq_zero h2, add_zero] at hrec
      exact (mul_eq_zero.mp hrec).resolve_left hd

/-! ### The kernel at a real `t` is the polynomial `Σ_p Ω_p t^p` -/

/-- Two solutions of (8.1) with the same initial level coincide. -/
theorem kernel_unique (hu : LCNZ u) (hu1 : 0 < u 1) {t : ℝ} {ω₁ ω₂ : ℕ → ℕ → ℝ}
    (h1 : KernelRec u t ω₁ T) (h2 : KernelRec u t ω₂ T) (h0 : ∀ a, ω₁ 0 a = ω₂ 0 a) :
    ∀ ℓ a, ω₁ ℓ a = ω₂ ℓ a := by
  have claim : ∀ ℓ, ∀ ℓ' ≤ ℓ, ∀ a, ω₁ ℓ' a = ω₂ ℓ' a := by
    intro ℓ
    induction ℓ with
    | zero => intro ℓ' h a; rw [Nat.le_zero.mp h]; exact h0 a
    | succ ℓ ih =>
      intro ℓ' h a
      rcases Nat.lt_or_ge ℓ' (ℓ + 1) with h' | h'
      · exact ih ℓ' (by omega) a
      have e : ℓ' = ℓ + 1 := by omega
      subst e
      have hd : dd u (ℓ + 1) ≠ 0 := ne_of_gt (dd_pos hu hu1 (by omega))
      have r1 := h1 ℓ a
      have r2 := h2 ℓ a
      have hg : ∀ j, grp u t ω₁ j ℓ a = grp u t ω₂ j ℓ a :=
        fun j => grp_congr (fun ℓ' a' h => ih ℓ' h a') j a
      simp only [hg, ih ℓ le_rfl a] at r1
      rw [← r2] at r1
      exact mul_left_cancel₀ hd r1
  exact fun ℓ a => claim ℓ ℓ le_rfl a

/-- `ω_t(ℓ,a) = Σ_{p ≤ 2N+1} Ω(ℓ,a,p) t^p`. -/
noncomputable def polyKer (u : ℕ → ℝ) (T : ℝ) (k N : ℕ) (t : ℝ) (ℓ a : ℕ) : ℝ :=
  ∑ p ∈ range (2 * N + 2), kerFnG u T k ℓ a p * t ^ p

theorem kerFnG_top (hu : LCNZ u) (hu1 : 0 < u 1) (N : ℕ) (hk : k ≤ N) (hT : T = dd u N) :
    ∀ ℓ a p, 2 * N < p → kerFnG u T k ℓ a p = 0 := by
  intro ℓ a p hp
  by_cases h : N < ℓ + a
  · exact kerFnG_supp hu hu1 N hk hT ℓ a p h
  · exact kerFnG_deg hu hu1 ℓ a p (by omega)

theorem polyKer_rec (hu : LCNZ u) (hu1 : 0 < u 1) (N : ℕ) (hk : k ≤ N) (hT : T = dd u N) (t : ℝ) :
    KernelRec u t (polyKer u T k N t) T := by
  intro ℓ a
  have htop := kerFnG_top hu hu1 N hk hT
  have hrec := kerFnG_rec (T := T) (k := k) hu hu1
  unfold polyKer
  -- multiply the graded recurrence by `t^p` and sum
  have lhs : dd u (ℓ + 1) * ∑ p ∈ range (2 * N + 2), kerFnG u T k (ℓ + 1) a p * t ^ p =
      ∑ p ∈ range (2 * N + 2), ((T - dd u (ℓ + a)) * kerFnG u T k ℓ a p +
        ∑ j ∈ range (ℓ + 1), (-1 : ℝ) ^ j * grpG u (kerFnG u T k) j ℓ a p) * t ^ p := by
    rw [mul_sum]; apply sum_congr rfl; intro p _; rw [← hrec ℓ a p]; ring
  rw [lhs]
  simp only [add_mul, sum_add_distrib, mul_sum, sum_mul]
  congr 1
  · apply sum_congr rfl; intro p _; ring
  · rw [sum_comm]
    apply sum_congr rfl; intro j hj
    rw [Finset.mem_range] at hj
    unfold grp moveA moveB moveC grpG moveAG moveBG moveCG
    simp only [add_mul, mul_add, sum_add_distrib]
    -- the `A`-moves: shift the degree
    have hA : ∑ p ∈ range (2 * N + 2), (-1 : ℝ) ^ j * (tau p * Wt u (2 * j + 1) j (ℓ - j) (a + 2 * j + 1) *
          kerFnG u T k (ℓ - j) (a + 2 * j + 1) (p - 1)) * t ^ p =
        (-1 : ℝ) ^ j * (t * Wt u (2 * j + 1) j (ℓ - j) (a + 2 * j + 1) *
          ∑ p ∈ range (2 * N + 2), kerFnG u T k (ℓ - j) (a + 2 * j + 1) p * t ^ p) := by
      rw [sum_range_succ' _ (2 * N + 1), sum_range_succ (fun p => kerFnG u T k (ℓ - j) (a + 2 * j + 1) p * t ^ p)]
      rw [htop _ _ (2 * N + 1) (by omega)]
      simp only [tau, show ¬(1 ≤ 0) by omega, if_false, mul_zero, zero_mul, add_zero, zero_mul]
      rw [mul_sum, mul_sum]
      apply sum_congr rfl; intro p _
      rw [if_pos (by omega), Nat.add_sub_cancel, pow_succ]; ring
    rw [hA]
    congr 1
    · congr 1
      simp only [Finset.mul_sum]; exact sum_congr rfl (fun p _ => by ring)
    · split_ifs
      · simp only [Finset.mul_sum]; exact sum_congr rfl (fun p _ => by ring)
      · simp

theorem kerFn_eq_poly (hu : LCNZ u) (hu1 : 0 < u 1) (N : ℕ) (hk : k ≤ N) (hT : T = dd u N) (t : ℝ) :
    ∀ ℓ a, kerFn u t T k ℓ a = polyKer u T k N t ℓ a := by
  apply kernel_unique hu hu1 (kerFn_rec hu hu1) (polyKer_rec hu hu1 N hk hT t)
  intro a
  rw [kerFn_zero]
  unfold polyKer
  rw [Finset.sum_eq_single 0]
  · rw [kerFnG_zero]
    by_cases h : a = k
    · rw [if_pos h, if_pos ⟨h, rfl⟩]; simp
    · rw [if_neg h, if_neg (fun h' => h h'.1)]; simp
  · intro p _ hp; rw [kerFnG_zero, if_neg (fun h' => hp h'.2), zero_mul]
  · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h

/-! ### The product identity for the two-parameter array -/

/-- Hypotheses on the profile in Theorem 8.1. -/
structure LCProfile (N : ℕ) (d : ℕ → ℝ) : Prop where
  hN : 1 ≤ N
  d0 : d 0 = 0
  dN : d N = 1
  pos : ∀ i, 1 ≤ i → i ≤ N → 0 < d i
  lt1 : ∀ i, i < N → d i < 1
  lc : LogConcaveNoInternalZeros N (newtonCoeff d)

/-- The array `z p_i = (1 - d_i) p_{i+1} + x d_i p_i + y d_i p_{i-1}`. -/
def twoParam (N : ℕ) (d : ℕ → ℝ) (x y : ℝ) : Coefficients N :=
  ⟨fun i => 1 - d i, fun i => x * d i, fun i => y * d i⟩

/-- `ê_i = Π_{j<i} (1 - d_j)/(ρ d_{j+1})`. -/
noncomputable def ehat (d : ℕ → ℝ) (ρ : ℝ) (i : ℕ) : ℝ := ∏ j ∈ range i, ((1 - d j) / (ρ * d (j + 1)))

theorem profile_facts {N : ℕ} {d : ℕ → ℝ} (hd : LCProfile N d) :
    LCNZ (padNewton N (newtonCoeff d)) ∧ 0 < padNewton N (newtonCoeff d) 1 ∧
      padNewton N (newtonCoeff d) 0 = 0 ∧ (∀ i, i ≤ N → dd (padNewton N (newtonCoeff d)) i = d i) := by
  refine ⟨padNewton_lcnz hd.lc, ?_, ?_, fun i hi => dd_padNewton d hd.d0 N i hi⟩
  · unfold padNewton; rw [if_pos ⟨le_rfl, hd.hN⟩]; exact hd.lc.1
  · unfold padNewton; rw [if_neg (by omega)]

/-- The product coefficients of `twoParam N d (ρ t) ρ²` through the kernel at `t`. -/
theorem product_twoParam {N : ℕ} {d : ℕ → ℝ} (hd : LCProfile N d) {ρ : ℝ} (hρ : 0 < ρ) (t : ℝ) :
    ∀ m, m ≤ N → ∀ n k : Fin (N + 1), productMatrix (twoParam N d (ρ * t) (ρ ^ 2)) m n k =
      ehat d ρ k / (ehat d ρ m * ehat d ρ n) *
        Lker N (kerFn (padNewton N (newtonCoeff d)) t 1 k) m n := by
  obtain ⟨hu, hu1, hu0, hdd⟩ := profile_facts hd
  set u := padNewton N (newtonCoeff d)
  set w := twoParam N d (ρ * t) (ρ ^ 2)
  have hN := hd.hN
  have hdpos := hd.pos
  have h1d : ∀ i, i < N → 0 < 1 - d i := fun i hi => by linarith [hd.lt1 i hi]
  have hê_succ : ∀ i, ehat d ρ (i + 1) = ehat d ρ i * ((1 - d i) / (ρ * d (i + 1))) :=
    fun i => prod_range_succ _ _
  have hê_pos : ∀ i, i ≤ N → 0 < ehat d ρ i := fun i hi => by
    apply prod_pos; intro j hj; rw [Finset.mem_range] at hj
    exact div_pos (h1d j (by omega)) (mul_pos hρ (hdpos (j + 1) (by omega) (by omega)))
  have hê0 : ehat d ρ 0 = 1 := prod_range_zero _
  have hT : (1 : ℝ) = dd u N := by rw [hdd N le_rfl, hd.dN]
  have hsupp : ∀ k', k' ≤ N → ∀ ℓ a, N < ℓ + a → kerFn u t 1 k' ℓ a = 0 :=
    fun k' hk' => kerFn_supp hu hu1 N hk' hT
  set G : ℕ → ℕ → ℕ → ℝ := fun m n k' =>
    ehat d ρ k' / (ehat d ρ m * ehat d ρ n) * Lker N (kerFn u t 1 k') m n with hG
  have h0 : ∀ n k' : ℕ, n ≤ N → k' ≤ N → G 0 n k' = if n = k' then 1 else 0 := by
    intro n k' hn hk'
    simp only [hG]
    rw [Lker_zero_left N _ n hn, kerFn_zero, hê0, one_mul]
    split_ifs with h
    · subst h; rw [div_self (hê_pos n hn).ne', one_mul]
    · rw [mul_zero]
  have hrecG : ∀ m n k', m + 1 ≤ N → n ≤ N → k' ≤ N →
      w.a m * G (m + 1) n k' =
        (if n + 1 ≤ N then w.a n * G m (n + 1) k' else 0) + w.b n * G m n k' +
        (if 1 ≤ n then w.c n * G m (n - 1) k' else 0) - w.b m * G m n k' -
        (if 1 ≤ m then w.c m * G (m - 1) n k' else 0) := by
    intro m n k' hm hn hk'
    set L := Lker N (kerFn u t 1 k') with hL
    have star := kernel_star hu0 N (kerFn u t 1 k') (kerFn_rec hu hu1) (hsupp k' hk') m n
    unfold Lz Lw at star
    rw [← hL] at star
    have em : ehat d ρ m ≠ 0 := (hê_pos m (by omega)).ne'
    have en : ehat d ρ n ≠ 0 := (hê_pos n hn).ne'
    set E := ehat d ρ k' / (ehat d ρ m * ehat d ρ n) with hE
    have sm : dd u (m + 1) * L (m + 1) n + t * dd u m * L m n +
        (if 1 ≤ m then (1 - dd u (m - 1)) * L (m - 1) n else 0) =
        d (m + 1) * L (m + 1) n + t * d m * L m n +
        (if 1 ≤ m then (1 - d (m - 1)) * L (m - 1) n else 0) := by
      rw [hdd (m + 1) hm, hdd m (by omega)]
      split_ifs
      · rw [hdd (m - 1) (by omega)]
      · rfl
    have sn : dd u (n + 1) * L m (n + 1) + t * dd u n * L m n +
        (if 1 ≤ n then (1 - dd u (n - 1)) * L m (n - 1) else 0) =
        (if n + 1 ≤ N then d (n + 1) * L m (n + 1) else 0) + t * d n * L m n +
        (if 1 ≤ n then (1 - d (n - 1)) * L m (n - 1) else 0) := by
      rw [hdd n hn]
      have e1 : dd u (n + 1) * L m (n + 1) = if n + 1 ≤ N then d (n + 1) * L m (n + 1) else 0 := by
        split_ifs with h
        · rw [hdd (n + 1) h]
        · rw [show n = N by omega, hL, Lker_top N _ (hsupp k' hk') m, mul_zero]
      rw [e1]
      split_ifs
      · rw [hdd (n - 1) (by omega)]
      · rfl
      · rw [hdd (n - 1) (by omega)]
      · rfl
    rw [sm, sn] at star
    have c1 : w.a m * G (m + 1) n k' = ρ * E * (d (m + 1) * L (m + 1) n) := by
      simp only [hG]; rw [← hL]
      exact conv_up (hê_succ m) em en hρ.ne' (hdpos (m + 1) (by omega) hm).ne' (h1d m (by omega)).ne'
    have c2m : w.b m * G m n k' = ρ * E * (t * d m * L m n) := by
      simp only [hG]; rw [← hL]; show ρ * t * d m * _ = _; ring
    have c2n : w.b n * G m n k' = ρ * E * (t * d n * L m n) := by
      simp only [hG]; rw [← hL]; show ρ * t * d n * _ = _; ring
    have c3m : (if 1 ≤ m then w.c m * G (m - 1) n k' else 0) =
        ρ * E * (if 1 ≤ m then (1 - d (m - 1)) * L (m - 1) n else 0) := by
      split_ifs with h
      · simp only [hG]; rw [← hL]
        have hs := hê_succ (m - 1)
        rw [show m - 1 + 1 = m by omega] at hs
        exact conv_down hs rfl (hê_pos (m - 1) (by omega)).ne' en hρ.ne'
          (hdpos m h (by omega)).ne' (h1d (m - 1) (by omega)).ne'
      · ring
    have c1n : (if n + 1 ≤ N then w.a n * G m (n + 1) k' else 0) =
        ρ * E * (if n + 1 ≤ N then d (n + 1) * L m (n + 1) else 0) := by
      split_ifs with h
      · simp only [hG]; rw [← hL, mul_comm (ehat d ρ m) (ehat d ρ (n + 1)), hE,
          mul_comm (ehat d ρ m) (ehat d ρ n)]
        exact conv_up (hê_succ n) en em hρ.ne' (hdpos (n + 1) (by omega) h).ne' (h1d n (by omega)).ne'
      · ring
    have c3n : (if 1 ≤ n then w.c n * G m (n - 1) k' else 0) =
        ρ * E * (if 1 ≤ n then (1 - d (n - 1)) * L m (n - 1) else 0) := by
      split_ifs with h
      · simp only [hG]; rw [← hL, mul_comm (ehat d ρ m) (ehat d ρ (n - 1)), hE,
          mul_comm (ehat d ρ m) (ehat d ρ n)]
        have hs := hê_succ (n - 1)
        rw [show n - 1 + 1 = n by omega] at hs
        exact conv_down hs rfl (hê_pos (n - 1) (by omega)).ne' em hρ.ne'
          (hdpos n h hn).ne' (h1d (n - 1) (by omega)).ne'
      · ring
    rw [c1, c1n, c2n, c3n, c2m, c3m]
    linear_combination (ρ * E) * star
  intro m hm n k
  exact product_eq_of_rec w G (fun i hi => (h1d i hi).ne') h0 hrecG m hm n k

/-! ### Polynomial form in the two parameters -/

/-- The coefficient of `t^p` in `L_{mn}^k`. -/
noncomputable def Lcoef (N : ℕ) (u : ℕ → ℝ) (k m n p : ℕ) : ℝ :=
  Lker N (fun ℓ a => kerFnG u 1 k ℓ a p) m n

theorem ehat_eq (d : ℕ → ℝ) {ρ : ℝ} (_hρ : ρ ≠ 0) (i : ℕ) : ehat d ρ i = ehat d 1 i / ρ ^ i := by
  induction i with
  | zero => simp [ehat]
  | succ i ih =>
    have h1 : ehat d ρ (i + 1) = ehat d ρ i * ((1 - d i) / (ρ * d (i + 1))) := prod_range_succ _ _
    have h2 : ehat d 1 (i + 1) = ehat d 1 i * ((1 - d i) / (1 * d (i + 1))) := prod_range_succ _ _
    rw [h1, h2, ih, pow_succ]
    ring

/-! ### Polynomial dependence on `y` -/

section allY

open Polynomial

variable {N : ℕ} (d : ℕ → ℝ) (x : ℝ)

/-- The recurrence matrix of `twoParam N d x y` with `y` an indeterminate. -/
noncomputable def recPoly : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ[X] := fun i j =>
  if j.val = i.val + 1 then C (1 - d i.val)
  else if j = i then C (x * d i.val)
  else if i.val = j.val + 1 then C (d i.val) * X else 0

/-- `matrixPair (twoParam N d x y)` with `y` an indeterminate. -/
noncomputable def pairPoly : ℕ → Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ[X] ×
    Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ[X]
  | 0 => (0, 1)
  | n + 1 => let t := pairPoly n
      (t.2, C (1 - d n)⁻¹ • ((recPoly d x - C (x * d n) • (1 : Matrix _ _ ℝ[X])) * t.2 -
        (C (d n) * X) • t.1))

theorem recPoly_eval (y : ℝ) (i j : Fin (N + 1)) :
    (recPoly d x i j).eval y = recurrenceMatrix (twoParam N d x y) i j := by
  simp only [recPoly, recurrenceMatrix]
  split_ifs <;> (simp only [eval_C, eval_mul, eval_X, eval_zero, twoParam]; try ring)

theorem pairPoly_eval (y : ℝ) : ∀ n,
    (∀ i j, ((pairPoly (N := N) d x n).1 i j).eval y = (matrixPair (twoParam N d x y) n).1 i j) ∧
    (∀ i j, ((pairPoly (N := N) d x n).2 i j).eval y = (matrixPair (twoParam N d x y) n).2 i j)
  | 0 => by
    refine ⟨fun i j => by simp [pairPoly, matrixPair], fun i j => ?_⟩
    simp only [pairPoly, matrixPair, Matrix.one_apply]
    split_ifs <;> simp
  | n + 1 => by
    obtain ⟨ih1, ih2⟩ := pairPoly_eval y n
    refine ⟨fun i j => ih2 i j, fun i j => ?_⟩
    simp only [pairPoly, matrixPair, Matrix.smul_apply, Matrix.sub_apply, Matrix.mul_apply, smul_eq_mul,
      eval_mul, eval_C, eval_sub, eval_finsetSum, eval_X, ih1, ih2, recPoly_eval, Matrix.one_apply]
    simp only [twoParam]
    congr 1; congr 1
    · apply sum_congr rfl; intro l _
      congr 1
      split_ifs <;> simp
    · ring

/-- For fixed `x`, `g(m,n;k)` of `twoParam N d x y` is a polynomial in `y`. -/
theorem product_poly_y (m : ℕ) (n k : Fin (N + 1)) :
    ∃ P : ℝ[X], ∀ y, productMatrix (twoParam N d x y) m n k = P.eval y :=
  ⟨(pairPoly d x m).2 n k, fun y => ((pairPoly_eval d x y m).2 n k).symm⟩

/-- An identity `g(m,n;k) = Σ_j h_j x^{D-2j} y^j` for `y > 0` holds for all real `y`. -/
theorem product_poly_all (m : ℕ) (n k : Fin (N + 1)) (D : ℕ) (h : ℕ → ℝ)
    (H : ∀ y : ℝ, 0 < y → productMatrix (twoParam N d x y) m n k =
      ∑ j ∈ range (D / 2 + 1), h j * x ^ (D - 2 * j) * y ^ j) (y : ℝ) :
    productMatrix (twoParam N d x y) m n k = ∑ j ∈ range (D / 2 + 1), h j * x ^ (D - 2 * j) * y ^ j := by
  obtain ⟨P, hP⟩ := product_poly_y d x m n k
  set Q : ℝ[X] := ∑ j ∈ range (D / 2 + 1), C (h j * x ^ (D - 2 * j)) * X ^ j
  have hQ : ∀ z, Q.eval z = ∑ j ∈ range (D / 2 + 1), h j * x ^ (D - 2 * j) * z ^ j := fun z => by
    simp [Q, eval_finsetSum]
  have hPQ : P = Q := by
    apply Polynomial.eq_of_infinite_eval_eq
    apply Set.Infinite.mono _ (Set.Ioi_infinite (0 : ℝ))
    intro z hz
    show P.eval z = Q.eval z
    rw [← hP, hQ, H z hz]
  rw [hP, hPQ, hQ]

end allY

section poly

variable {N : ℕ} {d : ℕ → ℝ} (hd : LCProfile N d)
include hd

theorem Lker_poly (k : ℕ) (hk : k ≤ N) (t : ℝ) (m n : ℕ) :
    Lker N (kerFn (padNewton N (newtonCoeff d)) t 1 k) m n =
      ∑ p ∈ range (2 * N + 2), Lcoef N (padNewton N (newtonCoeff d)) k m n p * t ^ p := by
  obtain ⟨hu, hu1, _, hdd⟩ := profile_facts hd
  have hT : (1 : ℝ) = dd (padNewton N (newtonCoeff d)) N := by rw [hdd N le_rfl, hd.dN]
  have he := kerFn_eq_poly hu hu1 N hk hT t
  simp only [Lcoef, Lker, he, polyKer, sum_mul]
  conv_rhs => rw [Finset.sum_comm]
  apply sum_congr rfl; intro r _
  conv_rhs => rw [Finset.sum_comm]
  apply sum_congr rfl; intro a _
  apply sum_congr rfl; intro p _
  ring

theorem Lcoef_nonneg (k : ℕ) (hk : k ≤ N) (m n p : ℕ) : 0 ≤ Lcoef N (padNewton N (newtonCoeff d)) k m n p := by
  obtain ⟨hu, hu1, _, hdd⟩ := profile_facts hd
  have hT : (1 : ℝ) = dd (padNewton N (newtonCoeff d)) N := by rw [hdd N le_rfl, hd.dN]
  have hTb : ∀ n ≤ N, dd (padNewton N (newtonCoeff d)) n ≤ 1 := by
    intro n hn
    rw [hdd n hn]
    rcases Nat.lt_or_ge n N with h | h
    · exact (hd.lt1 n h).le
    · rw [show n = N by omega, hd.dN]
  have hnn := kernel_nonnegG hu hu1 1 N hTb (kerFnG_rec hu hu1)
    (fun a p => by rw [kerFnG_zero]; split_ifs <;> norm_num) (kerFnG_supp hu hu1 N hk hT)
  exact Lker_nonneg N _ (fun r a => hnn r a p) m n

theorem Lcoef_zero (k : ℕ) (m n p : ℕ) (h : ¬(k + p ≤ m + n ∧ (m + n + k + p) % 2 = 0)) :
    Lcoef N (padNewton N (newtonCoeff d)) k m n p = 0 := by
  obtain ⟨hu, hu1, _, _⟩ := profile_facts hd
  unfold Lcoef Lker
  apply sum_eq_zero; intro r _; apply sum_eq_zero; intro a _
  unfold Ecf
  dsimp only
  split_ifs with he
  · obtain ⟨_, _, he3⟩ := he
    have hc : ¬(k + p ≤ a + 2 * r ∧ (a + 2 * r + k + p) % 2 = 0) := by
      intro hc; apply h; constructor <;> omega
    rw [kerFnG_deg hu hu1 r a p hc, zero_mul]
  · rw [mul_zero]

/-- The two-parameter form for `y > 0`, through the kernel at `t = x/√y`. -/
theorem twoParam_poly_pos (m : ℕ) (hm : m ≤ N) (n k : Fin (N + 1)) :
    ∃ h : ℕ → ℝ, (∀ j, 0 ≤ h j) ∧ (m + n.val < k.val → ∀ j, h j = 0) ∧
      ∀ x y : ℝ, 0 < y → productMatrix (twoParam N d x y) m n k =
        ∑ j ∈ range ((m + n.val - k.val) / 2 + 1), h j * x ^ (m + n.val - k.val - 2 * j) * y ^ j := by
  set D := m + n.val - k.val
  set C : ℕ → ℝ := fun p => ehat d 1 k / (ehat d 1 m * ehat d 1 n) * Lcoef N (padNewton N (newtonCoeff d)) k.val m n.val p with hC
  have hepos : ∀ i, i ≤ N → 0 < ehat d 1 i := fun i hi => by
    apply prod_pos; intro j hj; rw [Finset.mem_range] at hj
    have h1 := hd.lt1 j (by omega); have h2 := hd.pos (j + 1) (by omega) (by omega)
    exact div_pos (by linarith) (by linarith)
  have hCnn : ∀ p, 0 ≤ C p := fun p => mul_nonneg
    (div_nonneg (hepos k (by omega)).le (mul_pos (hepos m hm) (hepos n (by omega))).le)
    (Lcoef_nonneg hd k.val (by omega) m n.val p)
  have hCz : ∀ p, ¬(k.val + p ≤ m + n.val ∧ (m + n.val + k.val + p) % 2 = 0) → C p = 0 :=
    fun p hp => by simp only [hC]; rw [Lcoef_zero hd k.val m n.val p hp, mul_zero]
  refine ⟨fun j => if k.val ≤ m + n.val ∧ 2 * j ≤ D then C (D - 2 * j) else 0,
    fun j => by dsimp only; split_ifs; exacts [hCnn _, le_rfl], fun hk j => by
      dsimp only
      split_ifs with h
      · exfalso; omega
      · rfl, ?_⟩
  intro x y hy
  set ρ := Real.sqrt y with hρ_def
  have hρ : 0 < ρ := Real.sqrt_pos.mpr hy
  have hρ2 : ρ ^ 2 = y := Real.sq_sqrt hy.le
  have hw : twoParam N d x y = twoParam N d (ρ * (x / ρ)) (ρ ^ 2) := by
    rw [hρ2, mul_div_cancel₀ _ hρ.ne']
  rw [hw, product_twoParam hd hρ (x / ρ) m hm n k, Lker_poly hd k.val (by omega) (x / ρ) m n.val,
    ehat_eq d hρ.ne', ehat_eq d hρ.ne', ehat_eq d hρ.ne', mul_sum]
  -- each term is `C_p x^p y^{(D-p)/2}`
  have hterm : ∀ p, ehat d 1 ↑k / ρ ^ (k : ℕ) / (ehat d 1 m / ρ ^ m * (ehat d 1 ↑n / ρ ^ (n : ℕ))) *
      (Lcoef N (padNewton N (newtonCoeff d)) k.val m n.val p * (x / ρ) ^ p) =
      if k.val + p ≤ m + n.val ∧ (m + n.val + k.val + p) % 2 = 0 then
        C p * x ^ p * y ^ ((m + n.val - k.val - p) / 2) else 0 := by
    intro p
    split_ifs with hp
    · obtain ⟨j, hj⟩ : ∃ j, m + n.val = k.val + p + 2 * j := ⟨(m + n.val - k.val - p) / 2, by omega⟩
      rw [show (m + n.val - k.val - p) / 2 = j by omega, ← hρ2, ← pow_mul]
      simp only [hC]
      have hm0 := hepos m hm; have hn0 := hepos n.val (by omega)
      have e : ρ ^ m * ρ ^ (n : ℕ) = ρ ^ (k : ℕ) * ρ ^ p * ρ ^ (2 * j) := by
        rw [← pow_add, ← pow_add, ← pow_add, hj]
      have hρ0 : ρ ≠ 0 := hρ.ne'
      have hm1 := hm0.ne'; have hn1 := hn0.ne'
      calc ehat d 1 ↑k / ρ ^ (k : ℕ) / (ehat d 1 m / ρ ^ m * (ehat d 1 ↑n / ρ ^ (n : ℕ))) *
            (Lcoef N (padNewton N (newtonCoeff d)) k.val m n.val p * (x / ρ) ^ p)
          = ehat d 1 ↑k / (ehat d 1 m * ehat d 1 ↑n) * Lcoef N (padNewton N (newtonCoeff d)) k.val m n.val p *
              x ^ p * (ρ ^ m * ρ ^ (n : ℕ) / (ρ ^ (k : ℕ) * ρ ^ p)) := by
            rw [div_pow]; field_simp
        _ = _ := by
            rw [e, mul_div_cancel_left₀ _ (by positivity)]
    · simp only [hC] at hCz
      have := hCz p hp
      have hz : Lcoef N (padNewton N (newtonCoeff d)) k.val m n.val p = 0 := by
        rw [Lcoef_zero hd k.val m n.val p hp]
      rw [hz]; ring
  simp only [hterm]
  -- reindex `p = D - 2j`
  by_cases hkD : k.val ≤ m + n.val
  · have himg : ∑ j ∈ range (D / 2 + 1), (if k.val ≤ m + n.val ∧ 2 * j ≤ D then C (D - 2 * j) else 0) *
        x ^ (D - 2 * j) * y ^ j =
        ∑ p ∈ (range (D / 2 + 1)).image (fun j => D - 2 * j),
          (if k.val + p ≤ m + n.val ∧ (m + n.val + k.val + p) % 2 = 0 then
            C p * x ^ p * y ^ ((m + n.val - k.val - p) / 2) else 0) := by
      rw [sum_image (fun j1 h1 j2 h2 h => by
        simp only [Finset.coe_range, Set.mem_Iio] at h1 h2; omega)]
      apply sum_congr rfl; intro j hj
      rw [Finset.mem_range] at hj
      rw [if_pos ⟨hkD, by omega⟩, if_pos ⟨by omega, by omega⟩,
        show (m + n.val - k.val - (D - 2 * j)) / 2 = j by omega]
    rw [himg]
    symm
    apply sum_subset
    · intro p hp
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hp
      rw [Finset.mem_range] at hj ⊢; omega
    · intro p hp hnot
      split_ifs with hc
      · exfalso; apply hnot
        rw [Finset.mem_image]
        exact ⟨(D - p) / 2, Finset.mem_range.mpr (by omega), by omega⟩
      · rfl
  · rw [sum_eq_zero (fun p _ => by rw [if_neg (by omega)])]
    symm; apply sum_eq_zero; intro j _; rw [if_neg (by omega)]; ring

/-- **Remark after Theorem 8.1**: every linearization coefficient of
`z p_i = (1 - d_i) p_{i+1} + x d_i p_i + y d_i p_{i-1}` is
`Σ_j h_j x^{D-2j} y^j` with `h_j ≥ 0`, `D = m + n - k`, for all real `x` and `y`; it vanishes for
`k > m + n`. -/
theorem twoParam_poly (m : ℕ) (hm : m ≤ N) (n k : Fin (N + 1)) :
    ∃ h : ℕ → ℝ, (∀ j, 0 ≤ h j) ∧ (m + n.val < k.val → ∀ j, h j = 0) ∧
      ∀ x y : ℝ, productMatrix (twoParam N d x y) m n k =
        ∑ j ∈ range ((m + n.val - k.val) / 2 + 1), h j * x ^ (m + n.val - k.val - 2 * j) * y ^ j := by
  obtain ⟨h, hh, hz, H⟩ := twoParam_poly_pos hd m hm n k
  exact ⟨h, hh, hz, fun x y => product_poly_all d x m n k _ h (H x) y⟩

end poly

/-! ### Bernstein coefficients in `r` -/

theorem bern_term (D j : ℕ) (hj : 2 * j ≤ D) (r : ℝ) :
    r ^ j * (1 - r) ^ (D - 2 * j) = ∑ s ∈ range (D + 1),
      (if j ≤ s then ((j.choose (s - j) : ℕ) : ℝ) else 0) * r ^ s * (1 - r) ^ (D - s) := by
  have hsplit : D + 1 = j + (D + 1 - j) := by omega
  rw [hsplit, Finset.sum_range_add]
  have h1 : ∑ s ∈ range j, (if j ≤ s then ((j.choose (s - j) : ℕ) : ℝ) else 0) * r ^ s *
      (1 - r) ^ (j + (D + 1 - j) - 1 - s) = 0 := by
    apply sum_eq_zero; intro s hs; rw [Finset.mem_range] at hs; rw [if_neg (by omega)]; ring
  simp only [show j + (D + 1 - j) - 1 = D by omega] at h1 ⊢
  rw [h1, zero_add]
  have h2 : ∑ i ∈ range (D + 1 - j), (if j ≤ j + i then ((j.choose (j + i - j) : ℕ) : ℝ) else 0) *
      r ^ (j + i) * (1 - r) ^ (D - (j + i)) =
      ∑ i ∈ range (j + 1), ((j.choose i : ℕ) : ℝ) * r ^ (j + i) * (1 - r) ^ (D - (j + i)) := by
    have h3 : ∑ i ∈ range (D + 1 - j), (if j ≤ j + i then ((j.choose (j + i - j) : ℕ) : ℝ) else 0) *
        r ^ (j + i) * (1 - r) ^ (D - (j + i)) =
        ∑ i ∈ range (D + 1 - j), ((j.choose i : ℕ) : ℝ) * r ^ (j + i) * (1 - r) ^ (D - (j + i)) :=
      sum_congr rfl (fun i _ => by rw [if_pos (by omega), show j + i - j = i by omega])
    rw [h3]
    symm
    apply sum_subset (Finset.range_subset_range.mpr (by omega))
    intro i _ hni
    rw [Finset.mem_range] at hni
    rw [Nat.choose_eq_zero_of_lt (by omega)]; simp
  rw [h2]
  calc r ^ j * (1 - r) ^ (D - 2 * j) = r ^ j * (1 - r) ^ (D - 2 * j) * (r + (1 - r)) ^ j := by
        rw [show r + (1 - r) = 1 by ring, one_pow, mul_one]
    _ = r ^ j * (1 - r) ^ (D - 2 * j) * ∑ i ∈ range (j + 1), r ^ i * (1 - r) ^ (j - i) * (j.choose i : ℝ) := by
        rw [add_pow]
    _ = _ := by
        rw [mul_sum]; apply sum_congr rfl; intro i hi
        rw [Finset.mem_range] at hi
        have e : (1 - r) ^ (D - (j + i)) = (1 - r) ^ (D - 2 * j) * (1 - r) ^ (j - i) := by
          rw [← pow_add]; congr 1; omega
        rw [e, pow_add]; ring

/-- **Remark after Theorem 8.1**, Bernstein form: for the arrays of Theorem 8.1 every `g(m,n;k)`,
as a function of `r`, is `Σ_s B_s r^s (1-r)^{D-s}` with `B_s ≥ 0`, as an identity for all real `r` (`B_s / C(D,s)` are the Bernstein
coefficients of degree `D = m + n - k`). -/
theorem logconcave_bernstein {N : ℕ} {d : ℕ → ℝ} (hd : LCProfile N d) (m : ℕ) (hm : m ≤ N)
    (n k : Fin (N + 1)) :
    ∃ B : ℕ → ℝ, (∀ s, 0 ≤ B s) ∧ ∀ r : ℝ,
      productMatrix (twoParam N d (1 - r) r) m n k =
        ∑ s ∈ range (m + n.val - k.val + 1), B s * r ^ s * (1 - r) ^ (m + n.val - k.val - s) := by
  obtain ⟨h, hh, _, hpoly⟩ := twoParam_poly hd m hm n k
  set D := m + n.val - k.val
  refine ⟨fun s => ∑ j ∈ range (D / 2 + 1), h j * (if j ≤ s then ((j.choose (s - j) : ℕ) : ℝ) else 0),
    fun s => sum_nonneg (fun j _ => mul_nonneg (hh j) (by split_ifs <;> positivity)), ?_⟩
  intro r
  rw [hpoly (1 - r) r]
  have e : ∀ j ∈ range (D / 2 + 1), h j * (1 - r) ^ (D - 2 * j) * r ^ j =
      h j * ∑ s ∈ range (D + 1), (if j ≤ s then ((j.choose (s - j) : ℕ) : ℝ) else 0) * r ^ s * (1 - r) ^ (D - s) := by
    intro j hj
    rw [Finset.mem_range] at hj
    rw [← bern_term D j (by omega) r]; ring
  rw [sum_congr rfl e]
  simp only [mul_sum, sum_mul]
  rw [sum_comm]
  apply sum_congr rfl; intro s _
  apply sum_congr rfl; intro j _
  ring

/-- The remark after Theorem 8.1, two-parameter form. -/
def Stmt_lc_twoParam : Prop :=
  ∀ (N : ℕ) (d : ℕ → ℝ), LCProfile N d → ∀ m, m ≤ N → ∀ n k : Fin (N + 1),
    ∃ h : ℕ → ℝ, (∀ j, 0 ≤ h j) ∧ (m + n.val < k.val → ∀ j, h j = 0) ∧
      ∀ x y : ℝ, productMatrix (twoParam N d x y) m n k =
        ∑ j ∈ range ((m + n.val - k.val) / 2 + 1), h j * x ^ (m + n.val - k.val - 2 * j) * y ^ j

theorem lc_twoParam : Stmt_lc_twoParam := fun _ _ hd m hm n k => twoParam_poly hd m hm n k

/-- The remark after Theorem 8.1, Bernstein form. -/
def Stmt_lc_bernstein : Prop :=
  ∀ (N : ℕ) (d : ℕ → ℝ), LCProfile N d → ∀ m, m ≤ N → ∀ n k : Fin (N + 1),
    ∃ B : ℕ → ℝ, (∀ s, 0 ≤ B s) ∧ ∀ r : ℝ,
      productMatrix (twoParam N d (1 - r) r) m n k =
        ∑ s ∈ range (m + n.val - k.val + 1), B s * r ^ s * (1 - r) ^ (m + n.val - k.val - s)

theorem lc_bernstein : Stmt_lc_bernstein := fun _ _ hd m hm n k => logconcave_bernstein hd m hm n k

/-- The arrays of Theorem 8.1 are `twoParam N d (1 - r) r` with a profile satisfying `LCProfile`. -/
theorem constantRatio_twoParam {N : ℕ} (v : Coefficients N) (hv : Admissible v) {r : ℝ} (hr0 : 0 < r)
    (hc : ∀ i, i ≤ N → v.c i = r * profile v i)
    (hlc : LogConcaveNoInternalZeros N (newtonCoeff (profile v))) :
    LCProfile N (profile v) ∧ ∀ m, m ≤ N → productMatrix v m = productMatrix (twoParam N (profile v) (1 - r) r) m := by
  obtain ⟨hN, _, hb0, hc0, haN, hsum, hapos, hcpos⟩ := hv
  have ha_eq : ∀ i, i ≤ N → v.a i = 1 - profile v i := fun i hi => by
    have := hsum i hi; unfold profile; linarith
  refine ⟨⟨hN, by unfold profile; rw [hb0, hc0]; ring, ?_, ?_, ?_, hlc⟩, ?_⟩
  · have := ha_eq N le_rfl; rw [haN] at this; linarith
  · intro i h1 h2
    have h := hcpos i (by omega) h2
    rw [hc i h2] at h
    exact pos_of_mul_pos_right h hr0.le
  · intro i hi; have := ha_eq i hi.le; linarith [hapos i hi]
  · intro m hm
    apply product_congr v _ _ _ _ m (by omega)
    · intro i hi; exact ha_eq i hi
    · intro i hi; show v.b i = (1 - r) * profile v i
      have := hc i hi; unfold profile at this ⊢; linarith
    · intro i hi; exact hc i hi

end Szkraw
