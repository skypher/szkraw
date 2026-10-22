import Szkraw.KernelPoly
import Szkraw.LogConcaveStatement
import Szkraw.FiniteRealization
import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.FieldSimp

/-!
# Assembly of Theorem 8.1 (F8)

The kernel `ω` is defined by recurrence (8.1) with `ω(0,a) = [a = k]`. It has the support
property and is nonnegative (F7). Its coefficient array `L` satisfies `ℒ_z L = ℒ_w L` (F4).
After rescaling, `L` gives an array that satisfies the matrix recurrence defining
`productMatrix`, so `g(m,n;k) ≥ 0`.
-/

namespace Szkraw

open Finset

/-! ### The kernel defined by recurrence (8.1) -/

/-- Levels `0, …, L` of the kernel (course-of-values recursion on the level). -/
noncomputable def kerLevels (u : ℕ → ℝ) (t T : ℝ) (k : ℕ) : ℕ → (ℕ → ℕ → ℝ)
  | 0 => fun ℓ a => if ℓ = 0 ∧ a = k then 1 else 0
  | L + 1 => fun ℓ a =>
      if ℓ ≤ L then kerLevels u t T k L ℓ a
      else ((T - dd u (L + a)) * kerLevels u t T k L L a +
        ∑ j ∈ range (L + 1), (-1 : ℝ) ^ j * grp u t (kerLevels u t T k L) j L a) / dd u (L + 1)

/-- The kernel `ω` with `ω(0,a) = [a = k]`. -/
noncomputable def kerFn (u : ℕ → ℝ) (t T : ℝ) (k ℓ a : ℕ) : ℝ := kerLevels u t T k ℓ ℓ a

variable {u : ℕ → ℝ} {t T : ℝ} {k : ℕ}

theorem kerLevels_eq (L : ℕ) : ∀ ℓ a, ℓ ≤ L → kerLevels u t T k L ℓ a = kerFn u t T k ℓ a := by
  induction L with
  | zero => intro ℓ a h; rw [Nat.le_zero.mp h]; rfl
  | succ L ih =>
    intro ℓ a h
    by_cases hl : ℓ ≤ L
    · show (if ℓ ≤ L then kerLevels u t T k L ℓ a else _) = _
      rw [if_pos hl, ih ℓ a hl]
    · have : ℓ = L + 1 := by omega
      subst this; rfl

theorem grp_congr {ω₁ ω₂ : ℕ → ℕ → ℝ} {ℓ : ℕ} (h : ∀ ℓ' a, ℓ' ≤ ℓ → ω₁ ℓ' a = ω₂ ℓ' a) (j a : ℕ) :
    grp u t ω₁ j ℓ a = grp u t ω₂ j ℓ a := by
  unfold grp moveA moveB moveC
  rw [h _ _ (Nat.sub_le _ _), h _ _ (Nat.sub_le _ _)]
  split_ifs
  · rw [h _ _ (by omega)]
  · rfl

theorem kerFn_rec (hu : LCNZ u) (hu1 : 0 < u 1) : KernelRec u t (kerFn u t T k) T := by
  intro ℓ a
  have hd : dd u (ℓ + 1) ≠ 0 := ne_of_gt (dd_pos hu hu1 (by omega))
  have e : kerFn u t T k (ℓ + 1) a =
      ((T - dd u (ℓ + a)) * kerLevels u t T k ℓ ℓ a +
        ∑ j ∈ range (ℓ + 1), (-1 : ℝ) ^ j * grp u t (kerLevels u t T k ℓ) j ℓ a) / dd u (ℓ + 1) := by
    show (if ℓ + 1 ≤ ℓ then _ else _) = _
    rw [if_neg (by omega)]
  rw [e, mul_div_cancel₀ _ hd]
  have hg : ∀ j, grp u t (kerLevels u t T k ℓ) j ℓ a = grp u t (kerFn u t T k) j ℓ a :=
    fun j => grp_congr (fun ℓ' a' h => kerLevels_eq ℓ ℓ' a' h) j a
  simp only [hg]
  rfl

theorem kerFn_zero (a : ℕ) : kerFn u t T k 0 a = if a = k then 1 else 0 := by
  show (if 0 = 0 ∧ a = k then (1 : ℝ) else 0) = _
  simp

/-- Support: `ω(ℓ,a) = 0` for `ℓ + a > N`, when `k ≤ N` and `T = D_N`. -/
theorem kerFn_supp (hu : LCNZ u) (hu1 : 0 < u 1) (N : ℕ) (hk : k ≤ N) (hT : T = dd u N) :
    ∀ ℓ a, N < ℓ + a → kerFn u t T k ℓ a = 0 := by
  intro ℓ
  induction ℓ using Nat.strong_induction_on with
  | _ ℓ ih =>
    intro a ha
    rcases ℓ with _ | ℓ
    · rw [kerFn_zero, if_neg (by omega)]
    · have hrec := kerFn_rec (t := t) (T := T) (k := k) hu hu1 ℓ a
      have hd : dd u (ℓ + 1) ≠ 0 := ne_of_gt (dd_pos hu hu1 (by omega))
      have h1 : (T - dd u (ℓ + a)) * kerFn u t T k ℓ a = 0 := by
        by_cases h : ℓ + a = N
        · rw [hT, h, sub_self, zero_mul]
        · rw [ih ℓ (by omega) a (by omega), mul_zero]
      have h2 : ∀ j ∈ range (ℓ + 1), (-1 : ℝ) ^ j * grp u t (kerFn u t T k) j ℓ a = 0 := by
        intro j hj
        rw [Finset.mem_range] at hj
        unfold grp moveA moveB moveC
        rw [ih (ℓ - j) (by omega) _ (by omega), ih (ℓ - j) (by omega) _ (by omega)]
        split_ifs
        · rw [ih (ℓ - j - 1) (by omega) _ (by omega)]; ring
        · ring
      rw [h1, sum_eq_zero h2, add_zero] at hrec
      exact (mul_eq_zero.mp hrec).resolve_left hd

/-! ### Newton's forward formula -/

open fwdDiff in
theorem newton_forward (d : ℕ → ℝ) (i : ℕ) :
    d i = ∑ k ∈ range (i + 1), (i.choose k : ℝ) * newtonCoeff d k := by
  have h1 := shift_eq_sum_fwdDiff_iter (1 : ℕ) d i 0
  have h2 : ∀ k, (fwdDiff 1)^[k] d 0 = newtonCoeff d k := by
    intro k
    rw [fwdDiff_iter_eq_sum_shift]
    unfold newtonCoeff
    apply sum_congr rfl
    intro j _
    simp [zsmul_eq_mul]
  simp only [zero_add, smul_eq_mul, mul_one, nsmul_eq_mul, h2] at h1
  exact h1

/-- `D_i = Σ_h C(i,h) ν̃_h` equals the profile for `i ≤ N` (padded Newton sequence, `d 0 = 0`). -/
theorem dd_padNewton (d : ℕ → ℝ) (hd0 : d 0 = 0) (N i : ℕ) (hi : i ≤ N) :
    dd (padNewton N (newtonCoeff d)) i = d i := by
  unfold dd
  rw [iterShift_eq, newton_forward d i]
  apply sum_congr rfl
  intro h hh
  rw [Finset.mem_range] at hh
  rw [zero_add]
  unfold padNewton
  by_cases h0 : h = 0
  · subst h0
    have : newtonCoeff d 0 = 0 := by simp [newtonCoeff, hd0]
    rw [if_neg (by omega), this]
  · rw [if_pos ⟨by omega, by omega⟩]

/-! ### Uniqueness for the matrix recurrence -/

section matrix

variable {N : ℕ} (v : Coefficients N)

theorem J_entry (n l : Fin (N + 1)) :
    recurrenceMatrix v n l = (if l.val = n.val + 1 then v.a n else 0) +
      (if l.val = n.val then v.b n else 0) + (if l.val + 1 = n.val then v.c n else 0) := by
  unfold recurrenceMatrix
  have e : (l = n) ↔ l.val = n.val := Fin.val_inj.symm
  by_cases h1 : l.val = n.val + 1
  · rw [if_pos h1, if_pos h1, if_neg (by omega), if_neg (by omega)]; ring
  · rw [if_neg h1, if_neg h1]
    by_cases h2 : l.val = n.val
    · rw [if_pos (e.mpr h2), if_pos h2, if_neg (by omega)]; ring
    · rw [if_neg (fun h => h2 (e.mp h)), if_neg h2]
      by_cases h3 : n.val = l.val + 1
      · rw [if_pos h3, if_pos (by omega)]; ring
      · rw [if_neg h3, if_neg (by omega)]; ring

theorem J_mul_apply (P : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (F : ℕ → ℝ) (n k : Fin (N + 1))
    (hF : ∀ l : Fin (N + 1), P l k = F l.val) :
    (recurrenceMatrix v * P) n k = (if n.val + 1 ≤ N then v.a n * F (n + 1) else 0) +
      v.b n * F n + (if 1 ≤ n.val then v.c n * F (n - 1) else 0) := by
  rw [Matrix.mul_apply]
  simp_rw [hF, J_entry, add_mul, sum_add_distrib]
  rw [Fin.sum_univ_eq_sum_range (fun l => (if l = n.val + 1 then v.a n else 0) * F l) (N + 1),
    Fin.sum_univ_eq_sum_range (fun l => (if l = n.val then v.b n else 0) * F l) (N + 1),
    Fin.sum_univ_eq_sum_range (fun l => (if l + 1 = n.val then v.c n else 0) * F l) (N + 1)]
  have s1 : ∑ l ∈ range (N + 1), (if l = n.val + 1 then v.a n else 0) * F l =
      if n.val + 1 ≤ N then v.a n * F (n + 1) else 0 := by
    simp_rw [ite_mul, zero_mul]
    rw [Finset.sum_ite_eq' (range (N + 1)) (n.val + 1) (fun l => v.a n * F l)]
    simp only [Finset.mem_range]
    split_ifs <;> first | rfl | omega
  have s2 : ∑ l ∈ range (N + 1), (if l = n.val then v.b n else 0) * F l = v.b n * F n := by
    simp_rw [ite_mul, zero_mul]
    rw [Finset.sum_ite_eq' (range (N + 1)) n.val (fun l => v.b n * F l)]
    rw [if_pos (Finset.mem_range.mpr n.isLt)]
  have s3 : ∑ l ∈ range (N + 1), (if l + 1 = n.val then v.c n else 0) * F l =
      if 1 ≤ n.val then v.c n * F (n - 1) else 0 := by
    have e : ∀ l, (if l + 1 = n.val then v.c n else 0) * F l =
        if l = n.val - 1 then (if 1 ≤ n.val then v.c n * F l else 0) else 0 := by
      intro l
      by_cases h : l + 1 = n.val
      · rw [if_pos h, if_pos (by omega), if_pos (by omega)]
      · rw [if_neg h]
        by_cases h' : l = n.val - 1
        · rw [if_pos h', if_neg (by omega)]; ring
        · rw [if_neg h']; ring
    simp_rw [e]
    rw [Finset.sum_ite_eq' (range (N + 1)) (n.val - 1)]
    rw [if_pos (Finset.mem_range.mpr (by omega))]
  rw [s1, s2, s3]

/-- Any array satisfying the entry recurrence of `p_m(J)` with `p_0(J) = 1` is `productMatrix`. -/
theorem product_eq_of_rec (G : ℕ → ℕ → ℕ → ℝ) (ha : ∀ i, i < N → v.a i ≠ 0)
    (h0 : ∀ n k : ℕ, n ≤ N → k ≤ N → G 0 n k = if n = k then 1 else 0)
    (hrec : ∀ m n k, m + 1 ≤ N → n ≤ N → k ≤ N →
      v.a m * G (m + 1) n k =
        (if n + 1 ≤ N then v.a n * G m (n + 1) k else 0) + v.b n * G m n k +
        (if 1 ≤ n then v.c n * G m (n - 1) k else 0) - v.b m * G m n k -
        (if 1 ≤ m then v.c m * G (m - 1) n k else 0)) :
    ∀ m, m ≤ N → ∀ n k : Fin (N + 1), productMatrix v m n k = G m n k := by
  have claim : ∀ m, m ≤ N → (∀ n k : Fin (N + 1), productMatrix v m n k = G m n k) ∧
      (∀ n k : Fin (N + 1), (matrixPair v m).1 n k = if m = 0 then 0 else G (m - 1) n k) := by
    intro m
    induction m with
    | zero =>
      intro _
      refine ⟨fun n k => ?_, fun n k => ?_⟩
      · show (1 : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) n k = _
        rw [Matrix.one_apply, h0 n k (by omega) (by omega)]
        simp only [Fin.val_inj]
      · show (0 : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) n k = _
        simp
    | succ m ih =>
      intro hm
      obtain ⟨ihP, ihQ⟩ := ih (by omega)
      refine ⟨fun n k => ?_, fun n k => ?_⟩
      · have hdef : productMatrix v (m + 1) = (v.a m)⁻¹ •
            ((recurrenceMatrix v - v.b m • (1 : Matrix _ _ ℝ)) * productMatrix v m -
              v.c m • (matrixPair v m).1) := rfl
        rw [hdef]
        simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.sub_mul, Matrix.smul_mul,
          Matrix.one_mul, smul_eq_mul]
        rw [J_mul_apply v _ (fun l => G m l k) n k (fun l => ihP l k), ihP n k, ihQ n k]
        have hr := hrec m n k hm (by omega) (by omega)
        have ham := ha m (by omega)
        have e : v.c m * (if m = 0 then (0 : ℝ) else G (m - 1) n k) =
            if 1 ≤ m then v.c m * G (m - 1) n k else 0 := by
          split_ifs <;> first | omega | ring
        rw [inv_mul_eq_iff_eq_mul₀ ham, hr, e]
      · show productMatrix v m n k = _
        rw [ihP n k, if_neg (by omega), Nat.add_sub_cancel]
  exact fun m hm => (claim m hm).1

end matrix

/-! ### Facts about the kernel array -/

theorem Lker_zero_left (N : ℕ) (ω : ℕ → ℕ → ℝ) (n : ℕ) (hn : n ≤ N) : Lker N ω 0 n = ω 0 n := by
  unfold Lker
  rw [Finset.sum_eq_single 0]
  · rw [Finset.sum_eq_single n]
    · unfold Ecf; rw [if_pos (by omega)]; simp
    · intro a _ ha; unfold Ecf; rw [if_neg (by omega), mul_zero]
    · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h
  · intro r _ hr; apply sum_eq_zero; intro a _; unfold Ecf; rw [if_neg (by omega), mul_zero]
  · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h

theorem Lker_top (N : ℕ) (ω : ℕ → ℕ → ℝ) (hsupp : ∀ r a, N < r + a → ω r a = 0) (m : ℕ) :
    Lker N ω m (N + 1) = 0 := by
  unfold Lker
  apply sum_eq_zero; intro r _; apply sum_eq_zero; intro a _
  unfold Ecf
  split_ifs with h
  · rw [hsupp r a (by omega), zero_mul]
  · rw [mul_zero]

theorem Lker_nonneg (N : ℕ) (ω : ℕ → ℕ → ℝ) (h : ∀ r a, 0 ≤ ω r a) (m n : ℕ) : 0 ≤ Lker N ω m n := by
  unfold Lker
  exact sum_nonneg fun r _ => sum_nonneg fun a _ => mul_nonneg (h r a) (Ecf_nonneg _ _ _ _ _ _)

/-! ### Rescaling algebra -/

theorem conv_up {e0 e1 em ek ρ x y L : ℝ} (h : e1 = e0 * ((1 - x) / (ρ * y)))
    (h0 : e0 ≠ 0) (hm : em ≠ 0) (hρ : ρ ≠ 0) (hy : y ≠ 0) (hx : 1 - x ≠ 0) :
    (1 - x) * (ek / (e1 * em) * L) = ρ * (ek / (e0 * em)) * (y * L) := by
  subst h; field_simp

theorem conv_down {e0 e1 em ek ρ r x y L : ℝ} (h : e1 = e0 * ((1 - x) / (ρ * y))) (hr : ρ ^ 2 = r)
    (h0 : e0 ≠ 0) (hm : em ≠ 0) (hρ : ρ ≠ 0) (hy : y ≠ 0) (hx : 1 - x ≠ 0) :
    (r * y) * (ek / (e0 * em) * L) = ρ * (ek / (e1 * em)) * ((1 - x) * L) := by
  subst h hr; field_simp

theorem conv_mid {E ρ r x L : ℝ} (hρ : ρ ≠ 0) :
    ((1 - r) * x) * (E * L) = ρ * E * ((1 - r) / ρ * x * L) := by
  field_simp

/-! ### Theorem 8.1 -/

/-- **Theorem 8.1** (log-concave Newton criterion), matrix form. -/
theorem logconcave_matrix : Stmt_logconcave_matrix := by
  intro N v hv hcr
  obtain ⟨hN, _, hb0, hc0, haN, hsum, hapos, hcpos⟩ := hv
  obtain ⟨r, hr0, hr1, hc, hlc⟩ := hcr
  set d := profile v with hd
  set u := padNewton N (newtonCoeff d) with hu_def
  have hu : LCNZ u := padNewton_lcnz hlc
  have hu1 : 0 < u 1 := by
    rw [hu_def]; unfold padNewton; rw [if_pos ⟨le_rfl, hN⟩]; exact hlc.1
  have hu0 : u 0 = 0 := by rw [hu_def]; unfold padNewton; rw [if_neg (by omega)]
  have hd0 : d 0 = 0 := by rw [hd]; unfold profile; rw [hb0, hc0]; ring
  have hdd : ∀ i, i ≤ N → dd u i = d i := fun i hi => dd_padNewton d hd0 N i hi
  have ha_eq : ∀ i, i ≤ N → v.a i = 1 - d i := fun i hi => by
    have := hsum i hi; rw [hd]; unfold profile; linarith
  have hb_eq : ∀ i, i ≤ N → v.b i = (1 - r) * d i := fun i hi => by
    have := hc i hi; rw [hd] at this ⊢; unfold profile at this ⊢; linarith
  have hdN : d N = 1 := by have := ha_eq N le_rfl; rw [haN] at this; linarith
  have hdpos : ∀ i, 1 ≤ i → i ≤ N → 0 < d i := fun i h1 h2 => by
    have h := hcpos i (by omega) h2
    rw [hc i h2] at h
    exact pos_of_mul_pos_right h hr0.le
  have h1d : ∀ i, i < N → 0 < 1 - d i := fun i hi => by
    rw [← ha_eq i (by omega)]; exact hapos i hi
  have hdle : ∀ i, i ≤ N → d i ≤ 1 := fun i hi => by
    rcases Nat.lt_or_ge i N with h | h
    · linarith [h1d i h]
    · rw [show i = N by omega, hdN]
  -- parameters
  set ρ := Real.sqrt r with hρ_def
  have hρ : 0 < ρ := Real.sqrt_pos.mpr hr0
  have hρ2 : ρ ^ 2 = r := Real.sq_sqrt hr0.le
  set t := (1 - r) / ρ with ht_def
  have ht : 0 ≤ t := div_nonneg (by linarith) hρ.le
  -- normalization `ê`
  set ê : ℕ → ℝ := fun i => ∏ j ∈ range i, ((1 - d j) / (ρ * d (j + 1))) with hê_def
  have hê_succ : ∀ i, ê (i + 1) = ê i * ((1 - d i) / (ρ * d (i + 1))) := fun i => prod_range_succ _ _
  have hê_pos : ∀ i, i ≤ N → 0 < ê i := fun i hi => by
    apply prod_pos; intro j hj; rw [Finset.mem_range] at hj
    exact div_pos (h1d j (by omega)) (mul_pos hρ (hdpos (j + 1) (by omega) (by omega)))
  have hê0 : ê 0 = 1 := prod_range_zero _
  -- the kernel for each `k ≤ N`
  have hT : ∀ k' : ℕ, (1 : ℝ) = dd u N := fun _ => by rw [hdd N le_rfl, hdN]
  have hsupp : ∀ k', k' ≤ N → ∀ ℓ a, N < ℓ + a → kerFn u t 1 k' ℓ a = 0 :=
    fun k' hk' => kerFn_supp hu hu1 N hk' (hT k')
  have hnn : ∀ k', k' ≤ N → ∀ ℓ a, 0 ≤ kerFn u t 1 k' ℓ a := fun k' hk' =>
    kernel_nonneg hu hu1 ht 1 N (fun n hn => by rw [hdd n hn]; exact hdle n hn)
      (kerFn_rec hu hu1) (fun a => by rw [kerFn_zero]; split_ifs <;> norm_num) (hsupp k' hk')
  -- the candidate array
  set G : ℕ → ℕ → ℕ → ℝ := fun m n k' => ê k' / (ê m * ê n) * Lker N (kerFn u t 1 k') m n with hG
  have h0 : ∀ n k' : ℕ, n ≤ N → k' ≤ N → G 0 n k' = if n = k' then 1 else 0 := by
    intro n k' hn hk'
    simp only [hG]
    rw [Lker_zero_left N _ n hn, kerFn_zero, hê0, one_mul]
    split_ifs with h
    · subst h; rw [div_self (hê_pos n hn).ne', one_mul]
    · rw [mul_zero]
  have hrecG : ∀ m n k', m + 1 ≤ N → n ≤ N → k' ≤ N →
      v.a m * G (m + 1) n k' =
        (if n + 1 ≤ N then v.a n * G m (n + 1) k' else 0) + v.b n * G m n k' +
        (if 1 ≤ n then v.c n * G m (n - 1) k' else 0) - v.b m * G m n k' -
        (if 1 ≤ m then v.c m * G (m - 1) n k' else 0) := by
    intro m n k' hm hn hk'
    set L := Lker N (kerFn u t 1 k') with hL
    have star := kernel_star hu0 N (kerFn u t 1 k') (kerFn_rec hu hu1) (hsupp k' hk') m n
    unfold Lz Lw at star
    rw [← hL] at star
    have em : ê m ≠ 0 := (hê_pos m (by omega)).ne'
    have en : ê n ≠ 0 := (hê_pos n hn).ne'
    set E := ê k' / (ê m * ê n) with hE
    -- the `m`-side of the star relation
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
    -- conversions
    have c1 : v.a m * G (m + 1) n k' = ρ * E * (d (m + 1) * L (m + 1) n) := by
      simp only [hG]; rw [← hL, ha_eq m (by omega)]
      exact conv_up (hê_succ m) em en hρ.ne' (hdpos (m + 1) (by omega) hm).ne' (h1d m (by omega)).ne'
    have c2m : v.b m * G m n k' = ρ * E * (t * d m * L m n) := by
      simp only [hG]; rw [← hL, hb_eq m (by omega)]; exact conv_mid hρ.ne'
    have c2n : v.b n * G m n k' = ρ * E * (t * d n * L m n) := by
      simp only [hG]; rw [← hL, hb_eq n hn]; exact conv_mid hρ.ne'
    have c3m : (if 1 ≤ m then v.c m * G (m - 1) n k' else 0) =
        ρ * E * (if 1 ≤ m then (1 - d (m - 1)) * L (m - 1) n else 0) := by
      split_ifs with h
      · simp only [hG]; rw [← hL, hc m (by omega)]
        have hs := hê_succ (m - 1)
        rw [show m - 1 + 1 = m by omega] at hs
        exact conv_down hs hρ2 (hê_pos (m - 1) (by omega)).ne' en hρ.ne'
          (hdpos m h (by omega)).ne' (h1d (m - 1) (by omega)).ne'
      · ring
    have c1n : (if n + 1 ≤ N then v.a n * G m (n + 1) k' else 0) =
        ρ * E * (if n + 1 ≤ N then d (n + 1) * L m (n + 1) else 0) := by
      split_ifs with h
      · simp only [hG]; rw [← hL, ha_eq n hn, mul_comm (ê m) (ê (n + 1)), hE, mul_comm (ê m) (ê n)]
        exact conv_up (hê_succ n) en em hρ.ne' (hdpos (n + 1) (by omega) h).ne' (h1d n (by omega)).ne'
      · ring
    have c3n : (if 1 ≤ n then v.c n * G m (n - 1) k' else 0) =
        ρ * E * (if 1 ≤ n then (1 - d (n - 1)) * L m (n - 1) else 0) := by
      split_ifs with h
      · simp only [hG]; rw [← hL, hc n hn, mul_comm (ê m) (ê (n - 1)), hE, mul_comm (ê m) (ê n)]
        have hs := hê_succ (n - 1)
        rw [show n - 1 + 1 = n by omega] at hs
        exact conv_down hs hρ2 (hê_pos (n - 1) (by omega)).ne' em hρ.ne'
          (hdpos n h hn).ne' (h1d (n - 1) (by omega)).ne'
      · ring
    rw [c1, c1n, c2n, c3n, c2m, c3m]
    linear_combination (ρ * E) * star
  intro m hm n k
  rw [product_eq_of_rec v G (fun i hi => (hapos i hi).ne') h0 hrecG m hm n k]
  simp only [hG]
  exact mul_nonneg (div_nonneg (hê_pos k (by omega)).le
    (mul_pos (hê_pos m hm) (hê_pos n (by omega))).le)
    (Lker_nonneg N _ (hnn k (by omega)) m n)

/-- **Theorem 8.1**, with the finite realization: the array has a positive finite orthogonality
measure, the terminal relation and the product identities, and nonnegative linearization. -/
theorem logconcave_criterion : Stmt_logconcave := by
  intro N v hv hcr
  exact ⟨finite_realization v hv, logconcave_matrix N v hv hcr⟩

end Szkraw
