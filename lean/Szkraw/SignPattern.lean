import Szkraw.ProfileCounterexamples
import Szkraw.ComboCounterexamples
import Szkraw.LCAssembly
import Szkraw.Krawtchouk

/-!
# P3, open problems: sign conditions on the shape

For `S₁, S₂ ∈ {[0,∞), (-∞,0], {0}, ℝ}` and `ρ_max > 0`, the class `SignClass S₁ S₂ ρ_max` consists of the
admissible arrays (`b_0 = 0`) with `a` nonincreasing, `b` and `c` nondecreasing, `d_{n+2} - 2d_{n+1} + d_n ∈ S₁`,
`ρ_{n+1} - ρ_n ∈ S₂` and `ρ_n ≤ ρ_max`, where `d = b + c` and `ρ_n = c_n/d_n`. Every class contains `K_{N,r}` for
`0 < r ≤ min(1, ρ_max)`; the class `S₁ = S₂ = {0}` consists of these arrays only, so it has property (P); for every
other choice and `ρ_max ≥ 83/400` one of four exact witnesses (`N = 100, 20, 120, 80`) lies in the class and has
`g(N,N;N) < 0` (`sign_pattern`).
-/

namespace Szkraw

open Finset ColCheck

inductive SignSet
  | nonneg
  | nonpos
  | zero
  | all
  deriving DecidableEq

/-- `[0,∞)`, `(-∞,0]`, `{0}`, `ℝ`. -/
def SignSet.mem : SignSet → ℝ → Prop
  | .nonneg, x => 0 ≤ x
  | .nonpos, x => x ≤ 0
  | .zero, x => x = 0
  | .all, _ => True

theorem SignSet.mem_zero (S : SignSet) : S.mem 0 := by cases S <;> simp [SignSet.mem]

theorem SignSet.mem_div {S : SignSet} {x c : ℝ} (hc : 0 < c) (h : S.mem x) : S.mem (x / c) := by
  cases S <;> simp only [SignSet.mem] at h ⊢
  · exact div_nonneg h hc.le
  · exact div_nonpos_of_nonpos_of_nonneg h hc.le
  · rw [h, zero_div]

/-- The class of the sign-pattern discussion of P3. -/
def SignClass {N : ℕ} (S₁ S₂ : SignSet) (ρmax : ℝ) (v : Coefficients N) : Prop :=
  Admissible v ∧ (∀ n, n < N → v.a (n + 1) ≤ v.a n) ∧ (∀ n, n < N → v.b n ≤ v.b (n + 1)) ∧
  (∀ n, n < N → v.c n ≤ v.c (n + 1)) ∧
  (∀ n, n + 2 ≤ N → S₁.mem (profile v (n + 2) - 2 * profile v (n + 1) + profile v n)) ∧
  (∀ n, 1 ≤ n → n + 1 ≤ N → S₂.mem (v.c (n + 1) / profile v (n + 1) - v.c n / profile v n)) ∧
  (∀ n, 1 ≤ n → n ≤ N → v.c n / profile v n ≤ ρmax)

/-! ### Krawtchouk arrays are in every class, and they are all of the class `{0}, {0}` -/

theorem krawCoefficients_admissible (N : ℕ) (hN : 1 ≤ N) (r : ℝ) (hr : 0 < r) :
    Admissible (krawCoefficients N r) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  refine ⟨hN, by simp [krawCoefficients, hN'.ne'], by simp [krawCoefficients], by simp [krawCoefficients],
    by simp [krawCoefficients], fun i _ => by simp only [krawCoefficients]; field_simp; ring,
    fun i hi => ?_, fun i hi _ => ?_⟩
  · simp only [krawCoefficients]
    have : (i : ℝ) < N := by exact_mod_cast hi
    apply div_pos <;> linarith
  · simp only [krawCoefficients]
    have : (0 : ℝ) < i := by exact_mod_cast hi
    positivity

/-- Every class contains `K_{N,r}` for `0 < r ≤ 1`, `r ≤ ρ_max`. -/
theorem kraw_mem_signClass (N : ℕ) (hN : 1 ≤ N) (S₁ S₂ : SignSet) (ρmax r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1)
    (hρ : r ≤ ρmax) : SignClass S₁ S₂ ρmax (krawCoefficients N r) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hρn : ∀ n, 1 ≤ n → (krawCoefficients N r).c n / profile (krawCoefficients N r) n = r := fun n hn => by
    have : (0 : ℝ) < n := by exact_mod_cast hn
    simp only [krawCoefficients, profile]
    field_simp
    ring
  refine ⟨krawCoefficients_admissible N hN r hr, fun n _ => ?_, fun n _ => ?_, fun n _ => ?_, fun n _ => ?_,
    fun n h1 h2 => ?_, fun n h1 h2 => ?_⟩
  · simp only [krawCoefficients]; push_cast
    exact div_le_div_of_nonneg_right (by linarith) hN'.le
  · simp only [krawCoefficients]; push_cast
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith) (by linarith)) hN'.le
  · simp only [krawCoefficients]; push_cast
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith) hr.le) hN'.le
  · have : profile (krawCoefficients N r) (n + 2) - 2 * profile (krawCoefficients N r) (n + 1) +
        profile (krawCoefficients N r) n = 0 := by
      simp only [profile, krawCoefficients]; push_cast; field_simp; ring
    rw [this]; exact S₁.mem_zero
  · rw [hρn (n + 1) (by omega), hρn n h1, sub_self]; exact S₂.mem_zero
  · rw [hρn n h1]; exact hρ

/-- The class `S₁ = S₂ = {0}` consists of the arrays `K_{N,r}`, `0 < r ≤ min(1, ρ_max)`, and has property (P). -/
theorem signClass_zero_zero {N : ℕ} (hN : 1 ≤ N) (ρmax : ℝ) (v : Coefficients N)
    (hv : SignClass .zero .zero ρmax v) :
    (∃ r, 0 < r ∧ r ≤ 1 ∧ r ≤ ρmax ∧ ∀ i, i ≤ N → v.a i = (krawCoefficients N r).a i ∧
      v.b i = (krawCoefficients N r).b i ∧ v.c i = (krawCoefficients N r).c i) ∧ MatrixPositivity v := by
  obtain ⟨hadm, -, hbm, -, h1, h2, hρ⟩ := hv
  obtain ⟨-, ha0, hb0, hc0, haN, hsum, hapos, hcpos⟩ := hadm
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  set d := profile v with hd
  have hd0 : d 0 = 0 := by simp [hd, profile, hb0, hc0]
  have hdN : d N = 1 := by have := hsum N le_rfl; rw [haN] at this; simp only [hd, profile]; linarith
  -- `b ≥ 0`
  have hbnn : ∀ n, n ≤ N → 0 ≤ v.b n := by
    intro n hn
    induction n with
    | zero => rw [hb0]
    | succ n ih => exact (ih (by omega)).trans (hbm n (by omega))
  have hdpos : ∀ n, 1 ≤ n → n ≤ N → 0 < d n := fun n h1 h2 => by
    simp only [hd, profile]; linarith [hbnn n h2, hcpos n h1 h2]
  -- linear profile
  have hlin : ∀ n, n ≤ N → d n = n * d 1 := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro hn
      rcases n with _ | _ | n
      · simp [hd0]
      · simp
      · have := h1 n hn
        simp only [SignSet.mem] at this
        rw [show d (n + 2) = 2 * d (n + 1) - d n by linarith, ih (n + 1) (by omega) (by omega),
          ih n (by omega) (by omega)]
        push_cast; ring
  have hd1 : d 1 = 1 / N := by
    have := hlin N le_rfl; rw [hdN] at this; field_simp; linarith
  have hprof : ∀ n, n ≤ N → d n = n / N := fun n hn => by rw [hlin n hn, hd1]; ring
  -- constant ratio
  set r := v.c 1 / d 1 with hr
  have hrc : ∀ n, 1 ≤ n → n ≤ N → v.c n / d n = r := by
    intro n hn1 hnN
    induction n with
    | zero => omega
    | succ n ih =>
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · rfl
      · have := h2 n hn (by omega)
        simp only [SignSet.mem] at this
        rw [← ih hn (by omega)]; linarith
  have hc : ∀ n, n ≤ N → v.c n = r * d n := by
    intro n hn
    rcases Nat.eq_zero_or_pos n with rfl | hn0
    · rw [hc0, hd0, mul_zero]
    · have := hrc n hn0 hn
      rw [div_eq_iff (hdpos n hn0 hn).ne'] at this; linarith
  have hr0 : 0 < r := div_pos (hcpos 1 one_pos hN) (hdpos 1 le_rfl hN)
  have hr1 : r ≤ 1 := by
    rw [hr, div_le_one (hdpos 1 le_rfl hN)]
    simp only [hd, profile]; linarith [hbnn 1 hN]
  have hrρ : r ≤ ρmax := by rw [← hrc 1 le_rfl hN]; exact hρ 1 le_rfl hN
  have hcoef : ∀ i, i ≤ N → v.a i = (krawCoefficients N r).a i ∧ v.b i = (krawCoefficients N r).b i ∧
      v.c i = (krawCoefficients N r).c i := by
    intro i hi
    have hci := hc i hi
    rw [hprof i hi] at hci
    have hbi : v.b i = (1 - r) * (i / N) := by
      have : d i = v.b i + v.c i := rfl
      rw [hprof i hi, hci] at this; linarith
    refine ⟨?_, ?_, ?_⟩ <;> simp only [krawCoefficients]
    · have := hsum i hi; rw [hbi, hci] at this
      have e : v.a i = 1 - (i : ℝ) / N := by linear_combination this
      rw [e]; field_simp
    · rw [hbi]; ring
    · rw [hci]; ring
  refine ⟨⟨r, hr0, hr1, hrρ, hcoef⟩, (logconcave_criterion N v ⟨hN, ha0, hb0, hc0, haN, hsum, hapos, hcpos⟩
    ⟨r, hr0, hr1, fun i hi => hc i hi, ?_⟩).2⟩
  -- Newton coefficients `(1/N, 0, …, 0)`
  have hnu : ∀ k, k ≤ N → newtonCoeff d k = if k = 1 then (1 : ℝ) / N else (0 : ℝ) := fun k hk => by
    rw [newtonCoeff_congr (d' := fun i => (1 / N : ℝ) * (i : ℝ) + 0) (fun i hi => by
      rw [hprof i (by omega)]; ring), newtonCoeff_lin_add, newtonCoeff_lin]
    have : newtonCoeff (fun _ : ℕ => (0 : ℝ)) k = 0 := by simp [newtonCoeff]
    rw [this]; split_ifs <;> ring
  refine ⟨?_, fun k hk1 hkN => ?_, fun k hk2 hkN => ?_, fun k hk1 hkN h0 => ?_⟩
  · rw [hnu 1 hN, if_pos rfl]; exact div_pos one_pos hN'
  · rw [hnu k hkN]; split_ifs
    · exact (div_pos one_pos hN').le
    · exact le_rfl
  · rw [hnu (k + 1) hkN, if_neg (by omega), mul_zero]; exact sq_nonneg _
  · rw [hnu (k + 1) (by omega), if_neg (by omega)]

/-! ### The four witnesses -/

theorem ratioArray_admissible (Dn Rn : ℕ → ℤ) (R : ℤ) (N : ℕ) (hN : 1 ≤ N) (hR : 0 < R) (hD0 : Dn 0 = 0)
    (hlt : ∀ i < N, Dn i < Dn N) (hDpos : ∀ i < N, 0 < Dn (i + 1)) (hRpos : ∀ i < N, 0 < Rn (i + 1)) :
    Admissible (ratioArray Dn Rn R N) := by
  have hDN : (0 : ℝ) < Dn N := by
    have := hDpos (N - 1) (by omega); rw [show N - 1 + 1 = N by omega] at this; exact_mod_cast this
  have hR' : (0 : ℝ) < R := by exact_mod_cast hR
  refine ⟨hN, by simp [ratioArray, hD0], by simp [ratioArray, hD0], by simp [ratioArray, hD0],
    by simp [ratioArray, div_self hDN.ne'], fun i _ => by simp only [ratioArray]; ring,
    fun i hi => ?_, fun i hi hiN => ?_⟩
  · show 0 < 1 - (Dn i : ℝ) / Dn N
    have : (Dn i : ℝ) < Dn N := by exact_mod_cast hlt i hi
    have := (div_lt_one hDN).2 this
    linarith
  · show 0 < (Rn i : ℝ) / R * ((Dn i : ℝ) / Dn N)
    obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    have h1 : (0 : ℝ) < Dn (j + 1) := by exact_mod_cast hDpos j (by omega)
    have h2 : (0 : ℝ) < Rn (j + 1) := by exact_mod_cast hRpos j (by omega)
    positivity

/-- A witness from integer data: the array with profile `Dn/Dn_N` and ratio `Rn/R` lies in `SignClass S₁ S₂ ρ_max`
and has `g(N,N;N) < 0`. -/
theorem ratio_signClass (Dn Rn : ℕ → ℤ) (R : ℤ) (N : ℕ) (S₁ S₂ : SignSet) (ρmax : ℝ) (hN : 1 ≤ N) (hR : 0 < R)
    (hD0 : Dn 0 = 0) (hlt : ∀ i < N, Dn i < Dn N) (hDpos : ∀ i < N, 0 < Dn (i + 1))
    (hRpos : ∀ i < N, 0 < Rn (i + 1)) (hbm : ∀ i < N, (R - Rn i) * Dn i ≤ (R - Rn (i + 1)) * Dn (i + 1))
    (hDm : ∀ i < N, Dn i ≤ Dn (i + 1)) (hcm : ∀ i < N, Rn i * Dn i ≤ Rn (i + 1) * Dn (i + 1))
    (hS₁ : ∀ n, n + 2 ≤ N → S₁.mem ((Dn (n + 2) - 2 * Dn (n + 1) + Dn n : ℤ) : ℝ))
    (hS₂ : ∀ n, 1 ≤ n → n + 1 ≤ N → S₂.mem ((Rn (n + 1) - Rn n : ℤ) : ℝ))
    (hρ : ∀ n, 1 ≤ n → n ≤ N → (Rn n : ℝ) / R ≤ ρmax)
    (hneg : eG (ccol (rA Dn R N) (rB Dn Rn R N) (rC Dn Rn N) N N N).2 N < 0) :
    SignClass S₁ S₂ ρmax (ratioArray Dn Rn R N) ∧
      productMatrix (ratioArray Dn Rn R N) N (Fin.last N) (Fin.last N) < 0 := by
  have hDN : (0 : ℝ) < Dn N := by
    have := hDpos (N - 1) (by omega); rw [show N - 1 + 1 = N by omega] at this; exact_mod_cast this
  have hR' : (0 : ℝ) < R := by exact_mod_cast hR
  have hadm := ratioArray_admissible Dn Rn R N hN hR hD0 hlt hDpos hRpos
  have hprof : ∀ i, profile (ratioArray Dn Rn R N) i = (Dn i : ℝ) / Dn N := fun i => by
    simp only [profile, ratioArray]; ring
  have hcrat : ∀ i, (ratioArray Dn Rn R N).c i = (Rn i : ℝ) / R * profile (ratioArray Dn Rn R N) i :=
    fun i => by rw [hprof]; rfl
  have h := ratio_example Dn Rn R N (fun i => (Dn i : ℝ) / Dn N) (fun i => (Rn i : ℝ) / R) hN hR hD0 hlt hDpos
    hRpos (fun _ _ => rfl) (fun _ _ => rfl) hbm N N N le_rfl (by omega) (by omega) hneg
  obtain ⟨hbmono, hg⟩ := h.2 _ hadm (fun i _ => hprof i) (fun i _ => hcrat i)
  have hρn : ∀ n, 1 ≤ n → n ≤ N → (ratioArray Dn Rn R N).c n / profile (ratioArray Dn Rn R N) n = (Rn n : ℝ) / R :=
    fun n h1 h2 => by
      have : (0 : ℝ) < Dn n := by
        obtain ⟨j, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by omega⟩
        exact_mod_cast hDpos j (by omega)
      rw [hcrat, hprof]; field_simp
  refine ⟨⟨hadm, fun n hn => ?_, hbmono, fun n hn => ?_, fun n hn => ?_, fun n h1 h2 => ?_, fun n h1 h2 => ?_⟩,
    hg⟩
  · show 1 - (Dn (n + 1) : ℝ) / Dn N ≤ 1 - (Dn n : ℝ) / Dn N
    have : (Dn n : ℝ) ≤ Dn (n + 1) := by exact_mod_cast hDm n hn
    have := div_le_div_of_nonneg_right this hDN.le
    linarith
  · show (Rn n : ℝ) / R * ((Dn n : ℝ) / Dn N) ≤ (Rn (n + 1) : ℝ) / R * ((Dn (n + 1) : ℝ) / Dn N)
    have : ((Rn n * Dn n : ℤ) : ℝ) ≤ ((Rn (n + 1) * Dn (n + 1) : ℤ) : ℝ) := by exact_mod_cast hcm n hn
    push_cast at this
    rw [show (Rn n : ℝ) / R * ((Dn n : ℝ) / Dn N) = Rn n * Dn n / (R * Dn N) by field_simp,
      show (Rn (n + 1) : ℝ) / R * ((Dn (n + 1) : ℝ) / Dn N) = Rn (n + 1) * Dn (n + 1) / (R * Dn N) by field_simp]
    exact div_le_div_of_nonneg_right this (by positivity)
  · rw [hprof, hprof, hprof, show (Dn (n + 2) : ℝ) / Dn N - 2 * ((Dn (n + 1) : ℝ) / Dn N) + (Dn n : ℝ) / Dn N =
      ((Dn (n + 2) - 2 * Dn (n + 1) + Dn n : ℤ) : ℝ) / Dn N by push_cast; ring]
    exact SignSet.mem_div hDN (hS₁ n hn)
  · rw [hρn (n + 1) (by omega) h2, hρn n h1 (by omega), show (Rn (n + 1) : ℝ) / R - (Rn n : ℝ) / R =
      ((Rn (n + 1) - Rn n : ℤ) : ℝ) / R by push_cast; ring]
    exact SignSet.mem_div hR' (hS₂ n h1 h2)
  · rw [hρn n h1 h2]; exact hρ n h1 h2

theorem mem_of_nonneg {S : SignSet} (hS : S = .nonneg ∨ S = .all) {x : ℝ} (hx : 0 ≤ x) : S.mem x := by
  rcases hS with rfl | rfl <;> simp [SignSet.mem, hx]

theorem mem_of_nonpos {S : SignSet} (hS : S = .nonpos ∨ S = .all) {x : ℝ} (hx : x ≤ 0) : S.mem x := by
  rcases hS with rfl | rfl <;> simp [SignSet.mem, hx]

/-- Witness for `S₁ ∋` a positive number: ratio `1/5`, eighty unit increments then twenty increments `11/10`. -/
theorem sign_witness_100 (S₁ S₂ : SignSet) (hS₁ : S₁ = .nonneg ∨ S₁ = .all) (ρmax : ℝ) (hρ : 1 / 5 ≤ ρmax) :
    ∃ v : Coefficients 100, SignClass S₁ S₂ ρmax v ∧ productMatrix v 100 (Fin.last 100) (Fin.last 100) < 0 :=
  ⟨_, ratio_signClass (psum (kinkZ 80 1 10)) (fun _ => 1) 5 100 S₁ S₂ ρmax (by norm_num) (by norm_num) rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)
    (fun n hn => mem_of_nonneg hS₁ (by
      have : ∀ n < 99, 0 ≤ psum (kinkZ 80 1 10) (n + 2) - 2 * psum (kinkZ 80 1 10) (n + 1) +
        psum (kinkZ 80 1 10) n := by decide +kernel
      exact_mod_cast this n (by omega)))
    (fun n _ _ => by simp [SignSet.mem_zero]) (fun n _ _ => by norm_num; linarith) (by decide +kernel)⟩

/-- Witness for `S₁ ∋` a negative number: ratio `1/10`, seventeen unit increments then three increments `1/2`. -/
theorem sign_witness_20 (S₁ S₂ : SignSet) (hS₁ : S₁ = .nonpos ∨ S₁ = .all) (ρmax : ℝ) (hρ : 1 / 10 ≤ ρmax) :
    ∃ v : Coefficients 20, SignClass S₁ S₂ ρmax v ∧ productMatrix v 20 (Fin.last 20) (Fin.last 20) < 0 :=
  ⟨_, ratio_signClass (psum (fun j => if j < 17 then 2 else 1)) (fun _ => 1) 10 20 S₁ S₂ ρmax (by norm_num)
    (by norm_num) rfl (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (fun n hn => mem_of_nonpos hS₁ (by
      have : ∀ n < 19, psum (fun j => if j < 17 then 2 else 1) (n + 2) -
        2 * psum (fun j => if j < 17 then 2 else 1) (n + 1) + psum (fun j => if j < 17 then 2 else 1) n ≤ 0 := by
        decide +kernel
      exact_mod_cast this n (by omega)))
    (fun n _ _ => by simp [SignSet.mem_zero]) (fun n _ _ => by norm_num; linarith) (by decide +kernel)⟩

/-- Witness for `S₁ = {0}`, `S₂ ∋` a positive number: `d_n = n/N`, `ρ_n = 1/5 + max(n-102,0)/2400`, `N = 120`. -/
theorem sign_witness_120 (S₂ : SignSet) (hS₂ : S₂ = .nonneg ∨ S₂ = .all) (ρmax : ℝ) (hρ : 83 / 400 ≤ ρmax) :
    ∃ v : Coefficients 120, SignClass .zero S₂ ρmax v ∧ productMatrix v 120 (Fin.last 120) (Fin.last 120) < 0 :=
  ⟨_, ratio_signClass (fun i => i) (fun n => if n ≤ 102 then 480 else 480 + ((n : ℤ) - 102)) 2400 120 .zero S₂ ρmax
    (by norm_num) (by norm_num) rfl (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (fun n _ => by simp only [SignSet.mem]; push_cast; ring)
    (fun (n : ℕ) (h1 : 1 ≤ n) (h2 : n + 1 ≤ 120) => mem_of_nonneg hS₂ (by
      have : ∀ n : ℕ, n < 120 → (0 : ℤ) ≤ (if n + 1 ≤ 102 then 480 else 480 + (((n + 1 : ℕ) : ℤ) - 102)) -
        (if n ≤ 102 then 480 else 480 + ((n : ℤ) - 102)) := by decide +kernel
      have hn : n < 120 := by omega
      have h3 := this n hn
      exact_mod_cast h3))
    (fun (n : ℕ) (h1 : 1 ≤ n) (h2 : n ≤ 120) => by
      have : ∀ n : ℕ, n < 121 → 400 * (if n ≤ 102 then (480 : ℤ) else 480 + ((n : ℤ) - 102)) ≤ 83 * 2400 := by
        decide +kernel
      have h := this n (by omega)
      have h' : (400 : ℝ) * ((if n ≤ 102 then (480 : ℤ) else 480 + ((n : ℤ) - 102) : ℤ) : ℝ) ≤ 83 * 2400 := by
        exact_mod_cast h
      rw [div_le_iff₀ (by norm_num)]; push_cast at h' ⊢; linarith) (by decide +kernel)⟩

/-- Witness for `S₁ = {0}`, `S₂ ∋` a negative number: `d_n = n/N`, `ρ_n = 1/5 - max(n-68,0)/1600`, `N = 80`. -/
theorem sign_witness_80 (S₂ : SignSet) (hS₂ : S₂ = .nonpos ∨ S₂ = .all) (ρmax : ℝ) (hρ : 1 / 5 ≤ ρmax) :
    ∃ v : Coefficients 80, SignClass .zero S₂ ρmax v ∧ productMatrix v 80 (Fin.last 80) (Fin.last 80) < 0 :=
  ⟨_, ratio_signClass (fun i => i) (fun n => if n ≤ 68 then 320 else 320 - ((n : ℤ) - 68)) 1600 80 .zero S₂ ρmax
    (by norm_num) (by norm_num) rfl (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (fun n _ => by simp only [SignSet.mem]; push_cast; ring)
    (fun (n : ℕ) (h1 : 1 ≤ n) (h2 : n + 1 ≤ 80) => mem_of_nonpos hS₂ (by
      have : ∀ n : ℕ, n < 80 → (if n + 1 ≤ 68 then (320 : ℤ) else 320 - (((n + 1 : ℕ) : ℤ) - 68)) -
        (if n ≤ 68 then 320 else 320 - ((n : ℤ) - 68)) ≤ 0 := by decide +kernel
      have hn : n < 80 := by omega
      have h3 := this n hn
      exact_mod_cast h3))
    (fun (n : ℕ) (h1 : 1 ≤ n) (h2 : n ≤ 80) => by
      have : ∀ n : ℕ, n < 81 → 5 * (if n ≤ 68 then (320 : ℤ) else 320 - ((n : ℤ) - 68)) ≤ 1600 := by decide +kernel
      have h := this n (by omega)
      have h' : (5 : ℝ) * ((if n ≤ 68 then (320 : ℤ) else 320 - ((n : ℤ) - 68) : ℤ) : ℝ) ≤ 1600 := by
        exact_mod_cast h
      rw [div_le_iff₀ (by norm_num)]; push_cast at h' ⊢; linarith) (by decide +kernel)⟩

/-- **P3, open problems, sign conditions on the shape.** For `ρ_max ≥ 83/400`, among the classes
`SignClass S₁ S₂ ρ_max`, exactly `S₁ = S₂ = {0}` guarantees property (P) for all `N`; every other class contains an
array with `g(N,N;N) < 0`, and every class contains `K_{N,r}` for `0 < r ≤ min(1, ρ_max)`. -/
theorem sign_pattern (S₁ S₂ : SignSet) (ρmax : ℝ) (hρ : 83 / 400 ≤ ρmax) :
    ((∀ N, 1 ≤ N → ∀ v : Coefficients N, SignClass S₁ S₂ ρmax v → MatrixPositivity v) ↔
      (S₁ = .zero ∧ S₂ = .zero)) ∧
    ((S₁, S₂) ≠ (.zero, .zero) → ∃ N, ∃ v : Coefficients N, SignClass S₁ S₂ ρmax v ∧
      productMatrix v N (Fin.last N) (Fin.last N) < 0) := by
  have hρ5 : 1 / 5 ≤ ρmax := by linarith
  have hρ10 : 1 / 10 ≤ ρmax := by linarith
  have wit : (S₁, S₂) ≠ (.zero, .zero) → ∃ N, ∃ v : Coefficients N, SignClass S₁ S₂ ρmax v ∧
      productMatrix v N (Fin.last N) (Fin.last N) < 0 := by
    intro hne
    cases S₁ with
    | nonneg => exact ⟨_, sign_witness_100 .nonneg S₂ (Or.inl rfl) ρmax hρ5⟩
    | all => exact ⟨_, sign_witness_100 .all S₂ (Or.inr rfl) ρmax hρ5⟩
    | nonpos => exact ⟨_, sign_witness_20 .nonpos S₂ (Or.inl rfl) ρmax hρ10⟩
    | zero =>
      cases S₂ with
      | nonneg => exact ⟨_, sign_witness_120 .nonneg (Or.inl rfl) ρmax hρ⟩
      | all => exact ⟨_, sign_witness_120 .all (Or.inr rfl) ρmax hρ⟩
      | nonpos => exact ⟨_, sign_witness_80 .nonpos (Or.inl rfl) ρmax hρ5⟩
      | zero => exact absurd rfl hne
  refine ⟨⟨fun hP => ?_, ?_⟩, wit⟩
  · by_contra hne
    have hne' : (S₁, S₂) ≠ (.zero, .zero) := fun h => hne (by simp_all)
    obtain ⟨N, v, hv, hg⟩ := wit hne'
    have hN : 1 ≤ N := hv.1.1
    have := hP N hN v hv N le_rfl (Fin.last N) (Fin.last N)
    linarith
  · rintro ⟨rfl, rfl⟩ N hN v hv
    exact (signClass_zero_zero hN ρmax v hv).2

end Szkraw
