import Szkraw.RatioCounterexamples
import Szkraw.Geometric
import Szkraw.Parameters

/-!
# P1, "How sharp is log-concavity?": convex combinations of `K_{N,r}` and `G_{N,q,r}`

`K_{N,r} = geometricCoefficients N p 1` and `G_{N,q,r} = geometricCoefficients N p q` with `p = 1/r` both have
property (P). The combination `(1-λ) K + λ G` is admissible with constant ratio, its increments are proportional to
`1 + t q^(i-N)` with `t = λ N (q-1) q^(N-1) / ((1-λ)(q^N - 1))`, its Newton coefficients are positive, and
`ν₂² < ν₁ ν₃` for `N ≥ 3` (`combo_shape`). At the listed `(r, N, q, t)` it has `g(N,N;N) < 0`, decided by an exact
column of the product table in the kernel.
-/

namespace Szkraw

open Finset ColCheck

/-- The convex combination `(1 - lam) v + lam w` of two arrays. -/
noncomputable def combo {N : ℕ} (lam : ℝ) (v w : Coefficients N) : Coefficients N where
  a i := (1 - lam) * v.a i + lam * w.a i
  b i := (1 - lam) * v.b i + lam * w.b i
  c i := (1 - lam) * v.c i + lam * w.c i

theorem combo_admissible {N : ℕ} {v w : Coefficients N} (hv : Admissible v) (hw : Admissible w) {lam : ℝ}
    (h0 : 0 ≤ lam) (h1 : lam ≤ 1) : Admissible (combo lam v w) := by
  obtain ⟨hN, va0, vb0, vc0, vaN, vsum, vapos, vcpos⟩ := hv
  obtain ⟨-, wa0, wb0, wc0, waN, wsum, wapos, wcpos⟩ := hw
  refine ⟨hN, ?_, ?_, ?_, ?_, fun i hi => ?_, fun i hi => ?_, fun i hi hiN => ?_⟩ <;> simp only [combo]
  · rw [va0, wa0]; ring
  · rw [vb0, wb0]; ring
  · rw [vc0, wc0]; ring
  · rw [vaN, waN]; ring
  · have := vsum i hi; have := wsum i hi; linear_combination (1 - lam) * vsum i hi + lam * wsum i hi
  · have := vapos i hi; have := wapos i hi
    rcases eq_or_lt_of_le h0 with h | h
    · subst h; simpa using vapos i hi
    · nlinarith
  · have := vcpos i hi hiN; have := wcpos i hi hiN
    rcases eq_or_lt_of_le h0 with h | h
    · subst h; simpa using vcpos i hi hiN
    · nlinarith

theorem qInteger_mul (q : ℝ) (n : ℕ) : qInteger q n * (q - 1) = q ^ n - 1 := by
  induction n with
  | zero => simp [qInteger]
  | succ n ih => rw [qInteger, add_mul, ih]; ring

theorem qInteger_one (n : ℕ) : qInteger 1 n = n := by
  induction n with
  | zero => simp [qInteger]
  | succ n ih => rw [qInteger, ih]; push_cast; ring

theorem profile_geometric (N : ℕ) (p q : ℝ) (hp : 0 < p) (i : ℕ) :
    profile (geometricCoefficients N p q) i = qInteger q i / qInteger q N := by
  simp only [profile, geometricCoefficients]
  field_simp
  ring

/-- The weight `lam` of `G` that gives the parameter `t`. -/
noncomputable def comboLam (N : ℕ) (q t : ℝ) : ℝ :=
  let u := t * (q ^ N - 1) / (N * (q - 1) * q ^ (N - 1))
  u / (1 + u)

theorem newtonCoeff_lin (k : ℕ) : newtonCoeff (fun i => (i : ℝ)) k = if k = 1 then 1 else 0 := by
  rcases k with _ | _ | k
  · simp [newtonCoeff]
  · simp [newtonCoeff, Finset.sum_range_succ]
  · have h := congr_fun (fwdDiff_iter_pow_eq_zero_of_lt (R := ℝ) (j := 1) (n := k + 2) (by omega)) 0
    rw [fwdDiff_iter_eq_sum_shift] at h
    simp only [Pi.zero_apply, zero_add, nsmul_eq_mul, mul_one, pow_one, zsmul_eq_mul] at h
    push_cast at h
    simp only [newtonCoeff, show k + 2 ≠ 1 by omega, if_false]
    exact h

theorem newtonCoeff_lin_add (α : ℝ) (g : ℕ → ℝ) (k : ℕ) :
    newtonCoeff (fun i => α * (i : ℝ) + g i) k = α * newtonCoeff (fun i => (i : ℝ)) k + newtonCoeff g k := by
  unfold newtonCoeff
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem combo_profile (N : ℕ) (hN : 1 ≤ N) (p q lam : ℝ) (hp0 : 0 < p) (hq : 1 < q) (i : ℕ) :
    profile (combo lam (geometricCoefficients N p 1) (geometricCoefficients N p q)) i =
      (1 - lam) * (i / N) + lam * ((q ^ i - 1) / (q ^ N - 1)) := by
  have hqN : (0 : ℝ) < q ^ N - 1 := by
    have : 1 < q ^ N := one_lt_pow₀ hq (by omega)
    linarith
  have e1 := profile_geometric N p 1 hp0 i
  have e2 := profile_geometric N p q hp0 i
  simp only [profile] at e1 e2 ⊢
  simp only [combo]
  rw [show (1 - lam) * (geometricCoefficients N p 1).b i + lam * (geometricCoefficients N p q).b i +
      ((1 - lam) * (geometricCoefficients N p 1).c i + lam * (geometricCoefficients N p q).c i) =
      (1 - lam) * ((geometricCoefficients N p 1).b i + (geometricCoefficients N p 1).c i) +
      lam * ((geometricCoefficients N p q).b i + (geometricCoefficients N p q).c i) by ring, e1, e2,
    qInteger_one, qInteger_one]
  congr 2
  rw [div_eq_div_iff (by have := qInteger_pos q hq.le N (by omega); linarith) hqN.ne']
  have a1 := qInteger_mul q i
  have a2 := qInteger_mul q N
  linear_combination (-qInteger q i) * a2 + qInteger q N * a1

/-- **P1, "How sharp is log-concavity?"**, the combination: for `N ≥ 1`, `p = 1/r ≥ 1`, `q > 1` and `0 < λ < 1`,
`(1-λ) K_{N,r} + λ G_{N,q,r}` is admissible with `c_i = r d_i`, its increments are `(1-λ)/N (1 + t q^(i-N))` with
`t = λ N (q-1) q^(N-1) / ((1-λ)(q^N - 1))`, its Newton coefficients `ν_1, …, ν_N` are positive, and
`ν₂² < ν₁ ν₃` if `N ≥ 3`. -/
theorem combo_shape (N : ℕ) (hN : 1 ≤ N) (p q lam : ℝ) (hp : 1 ≤ p) (hq : 1 < q) (h0 : 0 < lam) (h1 : lam < 1) :
    let v := combo lam (geometricCoefficients N p 1) (geometricCoefficients N p q)
    let t := lam * N * (q - 1) * q ^ (N - 1) / ((1 - lam) * (q ^ N - 1))
    Admissible v ∧ (∀ i, i ≤ N → v.c i = p⁻¹ * profile v i) ∧
    (∀ i, 1 ≤ i → i ≤ N → profile v i - profile v (i - 1) = (1 - lam) / N * (1 + t * q ^ ((i : ℤ) - N))) ∧
    (∀ k, 1 ≤ k → k ≤ N → 0 < newtonCoeff (profile v) k) ∧
    (3 ≤ N → newtonCoeff (profile v) 2 ^ 2 < newtonCoeff (profile v) 1 * newtonCoeff (profile v) 3) := by
  intro v t
  have hp0 : 0 < p := by linarith
  have hq1 : (0 : ℝ) < q - 1 := by linarith
  have hqN : (0 : ℝ) < q ^ N - 1 := by
    have : 1 < q ^ N := one_lt_pow₀ hq (by omega)
    linarith
  have hN' : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hprof := combo_profile N hN p q lam hp0 hq
  refine ⟨combo_admissible (geometric_coefficients_admissible N hN p 1 hp le_rfl)
    (geometric_coefficients_admissible N hN p q hp hq.le) h0.le h1.le, fun i _ => ?_, fun i hi hiN => ?_,
    fun k hk hkN => ?_, fun h3 => ?_⟩
  · simp only [profile, v, combo, geometricCoefficients]; field_simp; ring
  · rw [hprof, hprof]
    obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    simp only [t, Nat.add_sub_cancel]
    have hzp : q ^ (((j + 1 : ℕ) : ℤ) - N) = q ^ (j + 1) / q ^ N := by
      rw [zpow_sub₀ (by linarith), zpow_natCast, zpow_natCast]
    rw [hzp]
    have hqN1 : q ^ N = q * q ^ (N - 1) := by rw [← pow_succ', Nat.sub_add_cancel hN]
    have hl : 1 - lam ≠ 0 := by linarith
    have hq0 : q ≠ 0 := by linarith
    have hqN' : q ^ N - 1 ≠ 0 := hqN.ne'
    have hN0 : (N : ℝ) ≠ 0 := hN'.ne'
    push_cast
    field_simp
    rw [hqN1]
    ring
  all_goals
    have hnu : ∀ k, 1 ≤ k → newtonCoeff (profile v) k =
        (1 - lam) / N * (if k = 1 then 1 else 0) + lam / (q ^ N - 1) * (q - 1) ^ k := fun k hk => by
      have e : profile v = fun i : ℕ => (1 - lam) / N * (i : ℝ) + ((-(lam / (q ^ N - 1))) + lam / (q ^ N - 1) * q ^ i) :=
        funext fun i => by rw [hprof]; ring
      rw [e, newtonCoeff_lin_add, newtonCoeff_lin, newtonCoeff_const_geom, zero_pow (by omega)]
      ring
  · rw [hnu k hk]
    have : 0 < lam / (q ^ N - 1) * (q - 1) ^ k := by positivity
    split_ifs
    · have : 0 < (1 - lam) / N := by apply div_pos <;> linarith
      linarith
    · linarith
  · rw [hnu 1 le_rfl, hnu 2 (by norm_num), hnu 3 (by norm_num), if_pos rfl, if_neg (by norm_num),
      if_neg (by norm_num)]
    have : 0 < (1 - lam) / N * (lam / (q ^ N - 1) * (q - 1) ^ 3) := by
      have : 0 < (1 - lam) / N := by apply div_pos <;> linarith
      positivity
    have key : ((1 - lam) / N * 1 + lam / (q ^ N - 1) * (q - 1) ^ 1) * ((1 - lam) / N * 0 +
        lam / (q ^ N - 1) * (q - 1) ^ 3) - ((1 - lam) / N * 0 + lam / (q ^ N - 1) * (q - 1) ^ 2) ^ 2 =
        (1 - lam) / N * (lam / (q ^ N - 1) * (q - 1) ^ 3) := by ring
    linarith

/-- A numeric combination example: `r = pr/qr`, integer `q > 1` and `t > 0`; the integer checks are on the profile
numerators `D_i = i (q-1) q^(N-1) + t (q^i - 1)` of the combination. -/
theorem combo_example (N : ℕ) (hN : 1 ≤ N) (pr qr q t : ℤ) (hq : 1 < q) (ht : 0 < t) (hpr : 0 < pr)
    (hprq : pr ≤ qr)
    (hlt : ∀ i < N, (i * (q - 1) * q ^ (N - 1) + t * (q ^ i - 1) : ℤ) <
      N * (q - 1) * q ^ (N - 1) + t * (q ^ N - 1))
    (hDpos : ∀ i < N, (0 : ℤ) < (i + 1 : ℕ) * (q - 1) * q ^ (N - 1) + t * (q ^ (i + 1) - 1))
    (hbm : ∀ i < N, (qr - pr) * ((i : ℕ) * (q - 1) * q ^ (N - 1) + t * (q ^ i - 1)) ≤
      (qr - pr) * ((i + 1 : ℕ) * (q - 1) * q ^ (N - 1) + t * (q ^ (i + 1) - 1)))
    (hneg : eG (ccol (rA (fun i => i * (q - 1) * q ^ (N - 1) + t * (q ^ i - 1)) qr N)
      (rB (fun i => i * (q - 1) * q ^ (N - 1) + t * (q ^ i - 1)) (fun _ => pr) qr N)
      (rC (fun i => i * (q - 1) * q ^ (N - 1) + t * (q ^ i - 1)) (fun _ => pr) N) N N N).2 N < 0) :
    let r : ℝ := (pr : ℝ) / qr
    let K := geometricCoefficients N r⁻¹ 1
    let G := geometricCoefficients N r⁻¹ q
    let lam := comboLam N q t
    0 < lam ∧ lam < 1 ∧ lam * N * (q - 1) * (q : ℝ) ^ (N - 1) / ((1 - lam) * ((q : ℝ) ^ N - 1)) = t ∧
    MatrixPositivity K ∧ MatrixPositivity G ∧ Admissible (combo lam K G) ∧
    productMatrix (combo lam K G) N (Fin.last N) (Fin.last N) < 0 := by
  intro r K G lam
  have hq' : (1 : ℝ) < q := by exact_mod_cast hq
  have ht' : (0 : ℝ) < t := by exact_mod_cast ht
  have hqr : (0 : ℝ) < qr := by have : 0 < qr := by omega
                                exact_mod_cast this
  have hr0 : 0 < r := div_pos (by exact_mod_cast hpr) hqr
  have hr1 : r ≤ 1 := (div_le_one hqr).2 (by exact_mod_cast hprq)
  have hp : 1 ≤ r⁻¹ := one_le_inv_iff₀.2 ⟨hr0, hr1⟩
  have hq1 : (0 : ℝ) < q - 1 := by linarith
  have hqN : (0 : ℝ) < (q : ℝ) ^ N - 1 := by
    have : 1 < (q : ℝ) ^ N := one_lt_pow₀ hq' (by omega)
    linarith
  have hN' : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hqp : (0 : ℝ) < (q : ℝ) ^ (N - 1) := by positivity
  set u : ℝ := t * ((q : ℝ) ^ N - 1) / (N * (q - 1) * (q : ℝ) ^ (N - 1)) with hu
  have hu0 : 0 < u := by positivity
  have hlam : lam = u / (1 + u) := rfl
  have hl0 : 0 < lam := by rw [hlam]; positivity
  have hl1 : lam < 1 := by rw [hlam, div_lt_one (by linarith)]; linarith
  have hsh := combo_shape N hN r⁻¹ q lam hp hq' hl0 hl1
  refine ⟨hl0, hl1, ?_, geometric_family_matrix_positivity N hN _ 1 hp le_rfl,
    geometric_family_matrix_positivity N hN _ q hp hq'.le, hsh.1, ?_⟩
  · rw [hlam, hu]; field_simp; ring
  · have hprof : ∀ i, i ≤ N → profile (combo lam K G) i =
        (((i * (q - 1) * q ^ (N - 1) + t * (q ^ i - 1) : ℤ) : ℝ)) /
          ((N * (q - 1) * q ^ (N - 1) + t * (q ^ N - 1) : ℤ) : ℝ) := fun i _ => by
      rw [combo_profile N hN r⁻¹ q lam (by positivity) hq' i, hlam, hu]
      push_cast
      field_simp
      ring
    have hc : ∀ i, i ≤ N → (combo lam K G).c i = (pr : ℝ) / qr * profile (combo lam K G) i := fun i hi => by
      rw [hsh.2.1 i hi, inv_inv]
    have h := ratio_example (fun i => i * (q - 1) * q ^ (N - 1) + t * (q ^ i - 1)) (fun _ => pr) qr N
      (fun i => (((i * (q - 1) * q ^ (N - 1) + t * (q ^ i - 1) : ℤ) : ℝ)) /
        ((N * (q - 1) * q ^ (N - 1) + t * (q ^ N - 1) : ℤ) : ℝ)) (fun _ => (pr : ℝ) / qr) hN (by omega)
      (by simp) hlt hDpos (fun _ _ => hpr) (fun i _ => by push_cast; rfl) (fun _ _ => rfl) hbm N N N le_rfl
      (by omega) (by omega) hneg
    exact (h.2 _ hsh.1 hprof hc).2

/-! ### The listed parameters `(r, N, q, t)` -/

/-- `(r, N, q, t) = (4/5, 10, 10, 1)`: `K` and `G` have (P), the combination is admissible and
`g(10,10;10) < 0`. -/
theorem combo_fails_4_5_10 :
    let r : ℝ := ((4 : ℤ) : ℝ) / ((5 : ℤ) : ℝ)
    let lam := comboLam 10 ((10 : ℤ) : ℝ) ((1 : ℤ) : ℝ)
    0 < lam ∧ lam < 1 ∧
    lam * 10 * (((10 : ℤ) : ℝ) - 1) * ((10 : ℤ) : ℝ) ^ (10 - 1) / ((1 - lam) * (((10 : ℤ) : ℝ) ^ 10 - 1)) = ((1 : ℤ) : ℝ) ∧
    MatrixPositivity (geometricCoefficients 10 r⁻¹ 1) ∧ MatrixPositivity (geometricCoefficients 10 r⁻¹ ((10 : ℤ) : ℝ)) ∧
    Admissible (combo lam (geometricCoefficients 10 r⁻¹ 1) (geometricCoefficients 10 r⁻¹ ((10 : ℤ) : ℝ))) ∧
    productMatrix (combo lam (geometricCoefficients 10 r⁻¹ 1) (geometricCoefficients 10 r⁻¹ ((10 : ℤ) : ℝ)))
      10 (Fin.last 10) (Fin.last 10) < 0 :=
  combo_example 10 (by norm_num) 4 5 10 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- `(r, N, q, t) = (3/5, 20, 10, 2)`: `K` and `G` have (P), the combination is admissible and
`g(20,20;20) < 0`. -/
theorem combo_fails_3_5_20 :
    let r : ℝ := ((3 : ℤ) : ℝ) / ((5 : ℤ) : ℝ)
    let lam := comboLam 20 ((10 : ℤ) : ℝ) ((2 : ℤ) : ℝ)
    0 < lam ∧ lam < 1 ∧
    lam * 20 * (((10 : ℤ) : ℝ) - 1) * ((10 : ℤ) : ℝ) ^ (20 - 1) / ((1 - lam) * (((10 : ℤ) : ℝ) ^ 20 - 1)) = ((2 : ℤ) : ℝ) ∧
    MatrixPositivity (geometricCoefficients 20 r⁻¹ 1) ∧ MatrixPositivity (geometricCoefficients 20 r⁻¹ ((10 : ℤ) : ℝ)) ∧
    Admissible (combo lam (geometricCoefficients 20 r⁻¹ 1) (geometricCoefficients 20 r⁻¹ ((10 : ℤ) : ℝ))) ∧
    productMatrix (combo lam (geometricCoefficients 20 r⁻¹ 1) (geometricCoefficients 20 r⁻¹ ((10 : ℤ) : ℝ)))
      20 (Fin.last 20) (Fin.last 20) < 0 :=
  combo_example 20 (by norm_num) 3 5 10 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- `(r, N, q, t) = (1/2, 20, 10, 1)`: `K` and `G` have (P), the combination is admissible and
`g(20,20;20) < 0`. -/
theorem combo_fails_1_2_20 :
    let r : ℝ := ((1 : ℤ) : ℝ) / ((2 : ℤ) : ℝ)
    let lam := comboLam 20 ((10 : ℤ) : ℝ) ((1 : ℤ) : ℝ)
    0 < lam ∧ lam < 1 ∧
    lam * 20 * (((10 : ℤ) : ℝ) - 1) * ((10 : ℤ) : ℝ) ^ (20 - 1) / ((1 - lam) * (((10 : ℤ) : ℝ) ^ 20 - 1)) = ((1 : ℤ) : ℝ) ∧
    MatrixPositivity (geometricCoefficients 20 r⁻¹ 1) ∧ MatrixPositivity (geometricCoefficients 20 r⁻¹ ((10 : ℤ) : ℝ)) ∧
    Admissible (combo lam (geometricCoefficients 20 r⁻¹ 1) (geometricCoefficients 20 r⁻¹ ((10 : ℤ) : ℝ))) ∧
    productMatrix (combo lam (geometricCoefficients 20 r⁻¹ 1) (geometricCoefficients 20 r⁻¹ ((10 : ℤ) : ℝ)))
      20 (Fin.last 20) (Fin.last 20) < 0 :=
  combo_example 20 (by norm_num) 1 2 10 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- `(r, N, q, t) = (2/5, 60, 10, 2)`: `K` and `G` have (P), the combination is admissible and
`g(60,60;60) < 0`. -/
theorem combo_fails_2_5_60 :
    let r : ℝ := ((2 : ℤ) : ℝ) / ((5 : ℤ) : ℝ)
    let lam := comboLam 60 ((10 : ℤ) : ℝ) ((2 : ℤ) : ℝ)
    0 < lam ∧ lam < 1 ∧
    lam * 60 * (((10 : ℤ) : ℝ) - 1) * ((10 : ℤ) : ℝ) ^ (60 - 1) / ((1 - lam) * (((10 : ℤ) : ℝ) ^ 60 - 1)) = ((2 : ℤ) : ℝ) ∧
    MatrixPositivity (geometricCoefficients 60 r⁻¹ 1) ∧ MatrixPositivity (geometricCoefficients 60 r⁻¹ ((10 : ℤ) : ℝ)) ∧
    Admissible (combo lam (geometricCoefficients 60 r⁻¹ 1) (geometricCoefficients 60 r⁻¹ ((10 : ℤ) : ℝ))) ∧
    productMatrix (combo lam (geometricCoefficients 60 r⁻¹ 1) (geometricCoefficients 60 r⁻¹ ((10 : ℤ) : ℝ)))
      60 (Fin.last 60) (Fin.last 60) < 0 :=
  combo_example 60 (by norm_num) 2 5 10 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- `(r, N, q, t) = (1/3, 100, 10, 2)`: `K` and `G` have (P), the combination is admissible and
`g(100,100;100) < 0`. -/
theorem combo_fails_1_3_100 :
    let r : ℝ := ((1 : ℤ) : ℝ) / ((3 : ℤ) : ℝ)
    let lam := comboLam 100 ((10 : ℤ) : ℝ) ((2 : ℤ) : ℝ)
    0 < lam ∧ lam < 1 ∧
    lam * 100 * (((10 : ℤ) : ℝ) - 1) * ((10 : ℤ) : ℝ) ^ (100 - 1) / ((1 - lam) * (((10 : ℤ) : ℝ) ^ 100 - 1)) = ((2 : ℤ) : ℝ) ∧
    MatrixPositivity (geometricCoefficients 100 r⁻¹ 1) ∧ MatrixPositivity (geometricCoefficients 100 r⁻¹ ((10 : ℤ) : ℝ)) ∧
    Admissible (combo lam (geometricCoefficients 100 r⁻¹ 1) (geometricCoefficients 100 r⁻¹ ((10 : ℤ) : ℝ))) ∧
    productMatrix (combo lam (geometricCoefficients 100 r⁻¹ 1) (geometricCoefficients 100 r⁻¹ ((10 : ℤ) : ℝ)))
      100 (Fin.last 100) (Fin.last 100) < 0 :=
  combo_example 100 (by norm_num) 1 3 10 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 4000000 in
/-- `(r, N, q, t) = (3/10, 200, 2, 5)`: `K` and `G` have (P), the combination is admissible and
`g(200,200;200) < 0`. -/
theorem combo_fails_3_10_200 :
    let r : ℝ := ((3 : ℤ) : ℝ) / ((10 : ℤ) : ℝ)
    let lam := comboLam 200 ((2 : ℤ) : ℝ) ((5 : ℤ) : ℝ)
    0 < lam ∧ lam < 1 ∧
    lam * 200 * (((2 : ℤ) : ℝ) - 1) * ((2 : ℤ) : ℝ) ^ (200 - 1) / ((1 - lam) * (((2 : ℤ) : ℝ) ^ 200 - 1)) = ((5 : ℤ) : ℝ) ∧
    MatrixPositivity (geometricCoefficients 200 r⁻¹ 1) ∧ MatrixPositivity (geometricCoefficients 200 r⁻¹ ((2 : ℤ) : ℝ)) ∧
    Admissible (combo lam (geometricCoefficients 200 r⁻¹ 1) (geometricCoefficients 200 r⁻¹ ((2 : ℤ) : ℝ))) ∧
    productMatrix (combo lam (geometricCoefficients 200 r⁻¹ 1) (geometricCoefficients 200 r⁻¹ ((2 : ℤ) : ℝ)))
      200 (Fin.last 200) (Fin.last 200) < 0 :=
  combo_example 200 (by norm_num) 3 10 2 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 4000000 in
/-- `(r, N, q, t) = (2/7, 200, 10, 5)`: `K` and `G` have (P), the combination is admissible and
`g(200,200;200) < 0`. -/
theorem combo_fails_2_7_200 :
    let r : ℝ := ((2 : ℤ) : ℝ) / ((7 : ℤ) : ℝ)
    let lam := comboLam 200 ((10 : ℤ) : ℝ) ((5 : ℤ) : ℝ)
    0 < lam ∧ lam < 1 ∧
    lam * 200 * (((10 : ℤ) : ℝ) - 1) * ((10 : ℤ) : ℝ) ^ (200 - 1) / ((1 - lam) * (((10 : ℤ) : ℝ) ^ 200 - 1)) = ((5 : ℤ) : ℝ) ∧
    MatrixPositivity (geometricCoefficients 200 r⁻¹ 1) ∧ MatrixPositivity (geometricCoefficients 200 r⁻¹ ((10 : ℤ) : ℝ)) ∧
    Admissible (combo lam (geometricCoefficients 200 r⁻¹ 1) (geometricCoefficients 200 r⁻¹ ((10 : ℤ) : ℝ))) ∧
    productMatrix (combo lam (geometricCoefficients 200 r⁻¹ 1) (geometricCoefficients 200 r⁻¹ ((10 : ℤ) : ℝ)))
      200 (Fin.last 200) (Fin.last 200) < 0 :=
  combo_example 200 (by norm_num) 2 7 10 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Szkraw
