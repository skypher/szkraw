import Szkraw.LCAssembly

/-!
# Exact columns of the product table, evaluated in the kernel

For an array with `a_i = A_i/Q`, `b_i = B_i/Q`, `c_i = C_i/Q` (`A, B, C` integer lists, `Q > 0`) and
`S_m = A_0 ⋯ A_{m-1}`, the numbers `H_m(n) = S_m g(m,n;k)` of column `k` are integers with
`H_{m+1}(n) = A_n H_m(n+1) + (B_n - B_m) H_m(n) + C_n H_m(n-1) - C_m A_{m-1} H_{m-1}(n)`. `ccol` computes them
in `O(N)` operations per step, and `productMatrix_eq_col` identifies `g(m,n;k) = H_m(n)/S_m`. A sign check of
one entry by `decide +kernel` then decides the sign of `g(m,n;k)`.
-/

namespace Szkraw
namespace ColCheck

/-- `L_i`, zero outside the list. -/
def eG (L : List ℤ) (i : ℕ) : ℤ := L.getD i 0

/-- One step of the column recurrence: from `H_{m-1}` (`P`) and `H_m` (`X`) to `H_{m+1}`. -/
def cstep (A B C : List ℤ) (m : ℕ) (P X : List ℤ) : List ℤ :=
  List.zipWith (· + ·) (List.zipWith (· * ·) A (X.tail ++ [0]))
    (List.zipWith (· + ·) (List.zipWith (fun b x => (b - eG B m) * x) B X)
      (List.zipWith (· - ·) (List.zipWith (· * ·) C (0 :: X)) (P.map ((eG C m * eG A (m - 1)) * ·))))

/-- `(H_{m-1}, H_m)` for column `k`. -/
def ccol (A B C : List ℤ) (N k : ℕ) : ℕ → List ℤ × List ℤ
  | 0 => (List.replicate (N + 1) 0, (List.range (N + 1)).map fun n => if n = k then 1 else 0)
  | m + 1 => ((ccol A B C N k m).2, cstep A B C m (ccol A B C N k m).1 (ccol A B C N k m).2)

/-! ### List lemmas -/

theorem getD_zipWith (f : ℤ → ℤ → ℤ) (l l' : List ℤ) (n : ℕ) (h : n < l.length) (h' : n < l'.length) :
    (List.zipWith f l l').getD n 0 = f (l.getD n 0) (l'.getD n 0) := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_zipWith, List.getElem?_eq_getElem h,
    List.getElem?_eq_getElem h']

theorem getD_shift_up (X : List ℤ) (n : ℕ) (h : n < X.length) :
    (X.tail ++ [0]).getD n 0 = X.getD (n + 1) 0 := by
  cases X with
  | nil => simp at h
  | cons x xs =>
    simp only [List.tail_cons, List.getD_cons_succ]
    simp only [List.length_cons] at h
    rcases Nat.lt_or_ge n xs.length with hn | hn
    · simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hn]
    · have : n = xs.length := by omega
      subst this
      simp [List.getD_eq_getElem?_getD, List.getElem?_append_right le_rfl]

theorem getD_shift_down (X : List ℤ) (n : ℕ) :
    (0 :: X).getD n 0 = if n = 0 then 0 else X.getD (n - 1) 0 := by
  cases n with
  | zero => simp
  | succ n => simp

theorem getD_map_mul (w : ℤ) (P : List ℤ) (n : ℕ) : (P.map (w * ·)).getD n 0 = w * P.getD n 0 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases P[n]? <;> simp

theorem length_cstep (A B C : List ℤ) (N m : ℕ) (P X : List ℤ) (hA : A.length = N + 1)
    (hB : B.length = N + 1) (hC : C.length = N + 1) (hP : P.length = N + 1) (hX : X.length = N + 1) :
    (cstep A B C m P X).length = N + 1 := by
  simp [cstep, List.length_zipWith, hA, hB, hC, hP, hX]

theorem getD_cstep (A B C : List ℤ) (N m : ℕ) (P X : List ℤ) (hA : A.length = N + 1)
    (hB : B.length = N + 1) (hC : C.length = N + 1) (hP : P.length = N + 1) (hX : X.length = N + 1)
    (n : ℕ) (hn : n ≤ N) :
    (cstep A B C m P X).getD n 0 = eG A n * eG X (n + 1) + (eG B n - eG B m) * eG X n +
      eG C n * (if n = 0 then 0 else eG X (n - 1)) - eG C m * eG A (m - 1) * eG P n := by
  have hl : ∀ l : List ℤ, l.length = N + 1 → n < l.length := fun l h => by omega
  unfold cstep
  rw [getD_zipWith _ _ _ _ (by simp [List.length_zipWith, hA, hX]; omega)
      (by simp [List.length_zipWith, hB, hX, hC, hP]; omega),
    getD_zipWith _ _ _ _ (by simp [hA]; omega) (by simp [hX]; omega),
    getD_zipWith _ _ _ _ (by simp [List.length_zipWith, hB, hX]; omega)
      (by simp [List.length_zipWith, hC, hX, hP]; omega),
    getD_zipWith _ _ _ _ (hl B hB) (hl X hX),
    getD_zipWith _ _ _ _ (by simp [List.length_zipWith, hC, hX]; omega) (by simp [hP]; omega),
    getD_zipWith _ _ _ _ (hl C hC) (by simp [hX]; omega),
    getD_shift_up X n (hl X hX), getD_shift_down, getD_map_mul]
  simp only [eG]
  ring

theorem ccol_length (A B C : List ℤ) (N k : ℕ) (hA : A.length = N + 1) (hB : B.length = N + 1)
    (hC : C.length = N + 1) : ∀ m, (ccol A B C N k m).1.length = N + 1 ∧ (ccol A B C N k m).2.length = N + 1
  | 0 => by simp [ccol]
  | m + 1 => by
    obtain ⟨h1, h2⟩ := ccol_length A B C N k hA hB hC m
    exact ⟨h2, length_cstep A B C N m _ _ hA hB hC h1 h2⟩

/-! ### Identification with the product table -/

section real

variable (A B C : List ℤ) (N : ℕ)

/-- `S_m = A_0 ⋯ A_{m-1}`. -/
noncomputable def S : ℕ → ℝ
  | 0 => 1
  | m + 1 => S m * eG A m

/-- The candidate `g(m,n;k) = H_m(n)/S_m`. -/
noncomputable def G (m n k : ℕ) : ℝ := (eG (ccol A B C N k m).2 n : ℝ) / S A m

variable {A B C N}

theorem S_pos (hApos : ∀ i < N, 0 < eG A i) : ∀ m, m ≤ N → 0 < S A m
  | 0, _ => by simp [S]
  | m + 1, h => by
    have := S_pos hApos m (by omega)
    have hm : (0 : ℝ) < eG A m := by exact_mod_cast hApos m (by omega)
    simp only [S]
    exact mul_pos this hm

theorem G_rec (hA : A.length = N + 1) (hB : B.length = N + 1) (hC : C.length = N + 1)
    (hApos : ∀ i < N, 0 < eG A i) (hC0 : eG C 0 = 0) (Q : ℝ) (hQ : 0 < Q) (v : Coefficients N)
    (ha : ∀ i, i ≤ N → v.a i = eG A i / Q) (hb : ∀ i, i ≤ N → v.b i = eG B i / Q)
    (hc : ∀ i, i ≤ N → v.c i = eG C i / Q) (m n k : ℕ) (hm : m + 1 ≤ N) (hn : n ≤ N) :
    v.a m * G A B C N (m + 1) n k =
      (if n + 1 ≤ N then v.a n * G A B C N m (n + 1) k else 0) + v.b n * G A B C N m n k +
      (if 1 ≤ n then v.c n * G A B C N m (n - 1) k else 0) - v.b m * G A B C N m n k -
      (if 1 ≤ m then v.c m * G A B C N (m - 1) n k else 0) := by
  obtain ⟨h1, h2⟩ := ccol_length A B C N k hA hB hC m
  have hAm : (0 : ℝ) < eG A m := by exact_mod_cast hApos m (by omega)
  have hSm := S_pos hApos m (by omega)
  set X := (ccol A B C N k m).2 with hX
  set P := (ccol A B C N k m).1 with hP
  have hG1 : G A B C N (m + 1) n k =
      ((eG A n * eG X (n + 1) + (eG B n - eG B m) * eG X n +
        eG C n * (if n = 0 then 0 else eG X (n - 1)) - eG C m * eG A (m - 1) * eG P n : ℤ) : ℝ) /
        (S A m * eG A m) := by
    simp only [G, ccol, S]
    rw [show eG (cstep A B C m P X) n = (cstep A B C m P X).getD n 0 from rfl,
      getD_cstep A B C N m P X hA hB hC h1 h2 n hn]
  have hA' : (if n + 1 ≤ N then v.a n * G A B C N m (n + 1) k else 0) =
      (eG A n : ℝ) / Q * ((eG X (n + 1) : ℝ) / S A m) := by
    split_ifs with h
    · rw [ha n hn]; rfl
    · have : eG X (n + 1) = 0 := by
        simp only [eG, List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by omega)]; rfl
      rw [this]; simp
  have hC' : (if 1 ≤ n then v.c n * G A B C N m (n - 1) k else 0) =
      (eG C n : ℝ) / Q * (((if n = 0 then 0 else eG X (n - 1) : ℤ) : ℝ) / S A m) := by
    split_ifs with h h'
    · omega
    · rw [hc n hn]; rfl
    · have : n = 0 := by omega
      subst this; simp [hC0]
    · omega
  have hD' : (if 1 ≤ m then v.c m * G A B C N (m - 1) n k else 0) =
      (eG C m : ℝ) / Q * eG A (m - 1) * ((eG P n : ℝ) / S A m) := by
    split_ifs with h
    · obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      have hSm' := S_pos hApos m' (by omega)
      have hAm' : (0 : ℝ) < eG A m' := by exact_mod_cast hApos m' (by omega)
      rw [hc (m' + 1) (by omega)]
      simp only [Nat.add_sub_cancel, G, hP, ccol, S]
      field_simp
    · have : m = 0 := by omega
      subst this; simp [hC0]
  rw [hG1, ha m (by omega), hb m (by omega), hb n hn, hA', hC', hD']
  have hb' : G A B C N m n k = (eG X n : ℝ) / S A m := rfl
  rw [hb']
  push_cast
  field_simp
  ring

/-- `g(m,n;k) = H_m(n)/S_m` for `m, n, k ≤ N`. -/
theorem productMatrix_eq_col (hA : A.length = N + 1) (hB : B.length = N + 1) (hC : C.length = N + 1)
    (hApos : ∀ i < N, 0 < eG A i) (hC0 : eG C 0 = 0) (Q : ℝ) (hQ : 0 < Q) (v : Coefficients N)
    (ha : ∀ i, i ≤ N → v.a i = eG A i / Q) (hb : ∀ i, i ≤ N → v.b i = eG B i / Q)
    (hc : ∀ i, i ≤ N → v.c i = eG C i / Q) :
    ∀ m, m ≤ N → ∀ n k : Fin (N + 1), productMatrix v m n k = G A B C N m n k := by
  have hva : ∀ i, i < N → v.a i ≠ 0 := by
    intro i hi
    rw [ha i hi.le]
    have : (0 : ℝ) < eG A i := by exact_mod_cast hApos i hi
    positivity
  have h0 : ∀ n k : ℕ, n ≤ N → k ≤ N → G A B C N 0 n k = if n = k then 1 else 0 := by
    intro n k hn _
    simp only [G, S, ccol, div_one, eG, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_range (show n < N + 1 by omega)]
    by_cases h : n = k <;> simp [h]
  exact product_eq_of_rec v (G A B C N) hva h0
    (fun m n k hm hn _ => G_rec hA hB hC hApos hC0 Q hQ v ha hb hc m n k hm hn)

/-- A negative column entry gives a negative product coefficient. -/
theorem productMatrix_neg (hA : A.length = N + 1) (hB : B.length = N + 1) (hC : C.length = N + 1)
    (hApos : ∀ i < N, 0 < eG A i) (hC0 : eG C 0 = 0) (Q : ℝ) (hQ : 0 < Q) (v : Coefficients N)
    (ha : ∀ i, i ≤ N → v.a i = eG A i / Q) (hb : ∀ i, i ≤ N → v.b i = eG B i / Q)
    (hc : ∀ i, i ≤ N → v.c i = eG C i / Q) (m : ℕ) (hm : m ≤ N) (n k : Fin (N + 1))
    (hneg : eG (ccol A B C N k m).2 n < 0) : productMatrix v m n k < 0 := by
  rw [productMatrix_eq_col hA hB hC hApos hC0 Q hQ v ha hb hc m hm n k, G]
  have : ((eG (ccol A B C N k m).2 n : ℤ) : ℝ) < 0 := by exact_mod_cast hneg
  exact div_neg_of_neg_of_pos this (S_pos hApos m hm)

end real

end ColCheck
end Szkraw

namespace Szkraw
namespace ColCheck

/-! ### Arrays given by a profile and a ratio -/

/-- `rA = (R (Dn_N - Dn_i))_{i ≤ N}`. -/
def rA (Dn : ℕ → ℤ) (R : ℤ) (N : ℕ) : List ℤ := (List.range (N + 1)).map fun i => R * (Dn N - Dn i)
/-- `rB = ((R - Rn_i) Dn_i)_{i ≤ N}`. -/
def rB (Dn Rn : ℕ → ℤ) (R : ℤ) (N : ℕ) : List ℤ := (List.range (N + 1)).map fun i => (R - Rn i) * Dn i
/-- `rC = (Rn_i Dn_i)_{i ≤ N}`. -/
def rC (Dn Rn : ℕ → ℤ) (N : ℕ) : List ℤ := (List.range (N + 1)).map fun i => Rn i * Dn i

theorem eG_map_range (f : ℕ → ℤ) (N i : ℕ) (hi : i ≤ N) : eG ((List.range (N + 1)).map f) i = f i := by
  simp [eG, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (show i < N + 1 by omega)]

/-- The array with profile `d_i = Dn_i/Dn_N` and ratio `ρ_i = Rn_i/R`. -/
noncomputable def ratioArray (Dn Rn : ℕ → ℤ) (R : ℤ) (N : ℕ) : Coefficients N where
  a i := 1 - (Dn i : ℝ) / Dn N
  b i := (1 - (Rn i : ℝ) / R) * ((Dn i : ℝ) / Dn N)
  c i := (Rn i : ℝ) / R * ((Dn i : ℝ) / Dn N)

/-- A counterexample given by integer data: the array with profile `d` and ratio `ρ` exists and is admissible,
and every admissible array with this profile and ratio has nondecreasing `b` and `g(m,n;k) < 0`. The
hypotheses `hlt`…`hneg` are integer checks. -/
theorem ratio_example (Dn Rn : ℕ → ℤ) (R : ℤ) (N : ℕ) (d ρ : ℕ → ℝ) (hN : 1 ≤ N) (hR : 0 < R)
    (hD0 : Dn 0 = 0) (hlt : ∀ i < N, Dn i < Dn N) (hDpos : ∀ i < N, 0 < Dn (i + 1))
    (hRpos : ∀ i < N, 0 < Rn (i + 1)) (hd : ∀ i, i ≤ N → d i = (Dn i : ℝ) / Dn N)
    (hρ : ∀ i, i ≤ N → ρ i = (Rn i : ℝ) / R)
    (hbm : ∀ i < N, (R - Rn i) * Dn i ≤ (R - Rn (i + 1)) * Dn (i + 1))
    (m n k : ℕ) (hm : m ≤ N) (hn : n < N + 1) (hk : k < N + 1)
    (hneg : eG (ccol (rA Dn R N) (rB Dn Rn R N) (rC Dn Rn N) N k m).2 n < 0) :
    (∃ v : Coefficients N, Admissible v ∧ (∀ i, i ≤ N → profile v i = d i) ∧
      ∀ i, i ≤ N → v.c i = ρ i * profile v i) ∧
    ∀ v : Coefficients N, Admissible v → (∀ i, i ≤ N → profile v i = d i) →
      (∀ i, i ≤ N → v.c i = ρ i * profile v i) →
      (∀ i, i < N → v.b i ≤ v.b (i + 1)) ∧ productMatrix v m ⟨n, hn⟩ ⟨k, hk⟩ < 0 := by
  have hDN : (0 : ℝ) < Dn N := by
    have := hDpos (N - 1) (by omega); rw [show N - 1 + 1 = N by omega] at this; exact_mod_cast this
  have hR' : (0 : ℝ) < R := by exact_mod_cast hR
  refine ⟨⟨ratioArray Dn Rn R N, ?_, fun i hi => ?_, fun i hi => ?_⟩, fun v hv hpd hpc => ?_⟩
  · refine ⟨hN, by simp [ratioArray, hD0], by simp [ratioArray, hD0], by simp [ratioArray, hD0],
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
  · simp only [profile, ratioArray, hd i hi]; ring
  · simp only [profile, ratioArray, hρ i hi]; ring
  -- the coefficients of `v` on `0 ≤ i ≤ N`
  have hc : ∀ i, i ≤ N → v.c i = (Rn i : ℝ) / R * ((Dn i : ℝ) / Dn N) := fun i hi => by
    rw [hpc i hi, hpd i hi, hρ i hi, hd i hi]
  have hb : ∀ i, i ≤ N → v.b i = (1 - (Rn i : ℝ) / R) * ((Dn i : ℝ) / Dn N) := fun i hi => by
    have h1 : profile v i = v.b i + v.c i := rfl
    rw [hpd i hi, hd i hi, hc i hi] at h1
    linarith
  have ha : ∀ i, i ≤ N → v.a i = 1 - (Dn i : ℝ) / Dn N := fun i hi => by
    have h1 := hv.2.2.2.2.2.1 i hi
    rw [hb i hi, hc i hi] at h1
    linarith
  refine ⟨fun i hi => ?_, ?_⟩
  · rw [hb i hi.le, hb (i + 1) hi]
    have h := hbm i hi
    have h' : ((R - Rn i) * Dn i : ℝ) ≤ (R - Rn (i + 1)) * Dn (i + 1) := by exact_mod_cast h
    have e : ∀ j, (1 - (Rn j : ℝ) / R) * ((Dn j : ℝ) / Dn N) = (R - Rn j) * Dn j / (R * Dn N) := fun j => by
      field_simp
    rw [e, e]
    exact div_le_div_of_nonneg_right h' (by positivity)
  · have hQ : (0 : ℝ) < R * Dn N := by positivity
    apply productMatrix_neg (by simp [rA]) (by simp [rB]) (by simp [rC]) (fun i hi => ?_) ?_ _ hQ v
      (fun i hi => ?_) (fun i hi => ?_) (fun i hi => ?_) m hm ⟨n, hn⟩ ⟨k, hk⟩ hneg
    · unfold rC; rw [eG_map_range _ _ _ (Nat.zero_le _), hD0, mul_zero]
    · unfold rA; rw [eG_map_range _ _ _ hi.le]
      exact mul_pos hR (by linarith [hlt i hi])
    · rw [ha i hi, rA, eG_map_range _ _ _ hi]; push_cast; field_simp
    · rw [hb i hi, rB, eG_map_range _ _ _ hi]; push_cast; field_simp
    · rw [hc i hi, rC, eG_map_range _ _ _ hi]; push_cast; field_simp

end ColCheck
end Szkraw
