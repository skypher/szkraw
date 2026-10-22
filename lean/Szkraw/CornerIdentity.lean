import Szkraw.Thinness
import Szkraw.LCAssembly

/-!
# Lemma 9.2: the corner identity

The first-order change of `g(N,N;N)` at `K_{N,1}` along a direction `v = (δb, δc)` is
`s_N Σ_n (-1)^n C(N,n) F(n)`.

The proof is algebraic. Write `J` for the recurrence matrix of `K_{N,1}`, `E` for that of the
direction, `Π = R_N(J)` (the index reversal) and `X` for the derivative of `R_N^ε(J_ε)`. The
matrix `R_N^ε(J_ε)` commutes with `J_ε` and has first row `e_N^T`, so `[J, X] = [Π, E]` and
`e_0^T X = 0`. An explicit matrix `Z` with `Z J - J Z = e_N e_N^T` on the columns `n ≥ 1` gives
`X_{NN} = tr((Z Π - Π Z) E)`, which is evaluated entry by entry.
-/

namespace Szkraw

open Finset Filter Topology

variable {N : ℕ}

/-- `(P J)_{mn}` for the recurrence matrix `J`. -/
theorem mul_J_apply (v : Coefficients N) (P : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (F : ℕ → ℝ)
    (m n : Fin (N + 1)) (hF : ∀ l : Fin (N + 1), P m l = F l.val) :
    (P * recurrenceMatrix v) m n = (if 1 ≤ n.val then F (n - 1) * v.a (n - 1) else 0) +
      F n * v.b n + (if n.val + 1 ≤ N then F (n + 1) * v.c (n + 1) else 0) := by
  rw [Matrix.mul_apply]
  simp_rw [hF, J_entry, mul_add, sum_add_distrib]
  rw [Fin.sum_univ_eq_sum_range (fun l => F l * if n.val = l + 1 then v.a l else 0) (N + 1),
    Fin.sum_univ_eq_sum_range (fun l => F l * if n.val = l then v.b l else 0) (N + 1),
    Fin.sum_univ_eq_sum_range (fun l => F l * if n.val + 1 = l then v.c l else 0) (N + 1)]
  congr 1; congr 1
  · rcases Nat.eq_zero_or_pos n.val with h0 | hpos
    · rw [if_neg (by omega)]
      exact sum_eq_zero fun l _ => by rw [if_neg (by omega), mul_zero]
    · rw [if_pos (by omega : 1 ≤ n.val), sum_eq_single (n.val - 1)]
      · rw [if_pos (by omega)]
      · intro l _ hl; rw [if_neg (by omega), mul_zero]
      · intro h; exact absurd (mem_range.mpr (by omega)) h
  · rw [sum_eq_single n.val]
    · rw [if_pos rfl]
    · intro l _ hl; rw [if_neg (by omega), mul_zero]
    · intro h; exact absurd (mem_range.mpr n.isLt) h
  · split_ifs with h
    · rw [sum_eq_single (n.val + 1)]
      · rw [if_pos rfl]
      · intro l _ hl; rw [if_neg (by omega), mul_zero]
      · intro h'; exact absurd (mem_range.mpr (by omega)) h'
    · exact sum_eq_zero fun l hl => by rw [mem_range] at hl; rw [if_neg (by omega), mul_zero]

/-! ### The direction in raw coefficients -/

/-- The direction `v = (δb, δc)` as a coefficient array: `δa = -(δb + δc)` inside, with
`δa_0 = δb_0 = δc_0 = 0`, `δa_N = 0` and `δb_N = -δc_N`. -/
def stochDir (N : ℕ) (δb δc : ℕ → ℝ) : Coefficients N where
  a i := if i = 0 then 0 else if i = N then 0 else -(δb i) - δc i
  b i := if i = 0 then 0 else if i = N then -(δc N) else δb i
  c i := if i = 0 then 0 else δc i

variable {δb δc : ℕ → ℝ}

theorem krawDir_recurrence (r ε : ℝ) :
    recurrenceMatrix (krawDir N δb δc r ε) =
      recurrenceMatrix (krawDir N δb δc r 0) + ε • recurrenceMatrix (stochDir N δb δc) := by
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, recurrenceMatrix, krawDir, stochArray,
    stochDir]
  split_ifs <;> ring

/-- At `ε = 0` the coefficients are those of `K_{N,r}`. -/
theorem krawDir_zero_coeff (hN : 1 ≤ N) (r : ℝ) (i : ℕ) (hi : i ≤ N) :
    (krawDir N δb δc r 0).a i = (krawCoefficients N r).a i ∧
      (krawDir N δb δc r 0).b i = (krawCoefficients N r).b i ∧
        (krawDir N δb δc r 0).c i = (krawCoefficients N r).c i := by
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  simp only [krawDir, stochArray, krawCoefficients]
  refine ⟨?_, ?_, ?_⟩
  · split_ifs with h0 h1
    · subst h0; simp [hN0]
    · subst h1; simp
    · field_simp; ring
  · split_ifs with h0 h1
    · subst h0; simp
    · subst h1; field_simp; ring
    · ring
  · split_ifs with h0
    · subst h0; simp
    · ring

/-- At `ε = 0` the recurrence matrix is that of `K_{N,r}`. -/
theorem krawDir_zero_recurrence (hN : 1 ≤ N) (r : ℝ) :
    recurrenceMatrix (krawDir N δb δc r 0) = recurrenceMatrix (krawCoefficients N r) := by
  ext i j
  obtain ⟨ha, hb, hc⟩ := krawDir_zero_coeff (δb := δb) (δc := δc) hN r i.val (by omega)
  unfold recurrenceMatrix
  rw [ha, hb, hc]

/-! ### The derivative `X` -/

/-- `R_N^ε(J_ε)` at `K_{N,1} + ε v`. -/
noncomputable def cornerP (N : ℕ) (δb δc : ℕ → ℝ) (ε : ℝ) : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ :=
  productMatrix (krawDir N δb δc 1 ε) N

/-- The derivative `X` of `R_N^ε(J_ε)` at `ε = 0`. -/
noncomputable def cornerX (N : ℕ) (δb δc : ℕ → ℝ) : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ :=
  fun i j => deriv (fun ε => cornerP N δb δc ε i j) 0

theorem krawDir_one_a_pos (hN : 1 ≤ N) (i : ℕ) (hi : i < N) : 0 < (krawDir N δb δc 1 0).a i := by
  rw [(krawDir_zero_coeff (δb := δb) (δc := δc) hN 1 i hi.le).1]
  simp only [krawCoefficients]
  have : (i : ℝ) < N := by exact_mod_cast hi
  exact div_pos (by linarith) (by linarith)

theorem krawDir_eps_contDiff (i : ℕ) :
    ContDiff ℝ 1 (fun ε => (krawDir N δb δc 1 ε).a i) ∧ ContDiff ℝ 1 (fun ε => (krawDir N δb δc 1 ε).b i) ∧
      ContDiff ℝ 1 (fun ε => (krawDir N δb δc 1 ε).c i) := by
  simp only [krawDir, stochArray]
  refine ⟨?_, ?_, ?_⟩ <;> split_ifs <;> fun_prop

theorem cornerP_hasDerivAt (hN : 1 ≤ N) (i j : Fin (N + 1)) :
    HasDerivAt (fun ε => cornerP N δb δc ε i j) (cornerX N δb δc i j) 0 := by
  have h := productMatrix_contDiffAt (fun ε : ℝ => krawDir N δb δc 1 ε) 0
    (fun i => (krawDir_eps_contDiff i).1.contDiffAt) (fun i => (krawDir_eps_contDiff i).2.1.contDiffAt)
    (fun i => (krawDir_eps_contDiff i).2.2.contDiffAt) N (fun i hi => (krawDir_one_a_pos hN i hi).ne') i j
  exact (h.differentiableAt one_ne_zero).hasDerivAt

/-- `[J, X] = [Π, E]`. -/
theorem cornerX_comm (hN : 1 ≤ N) :
    recurrenceMatrix (krawDir N δb δc 1 0) * cornerX N δb δc - cornerX N δb δc * recurrenceMatrix (krawDir N δb δc 1 0) =
      cornerP N δb δc 0 * recurrenceMatrix (stochDir N δb δc) -
        recurrenceMatrix (stochDir N δb δc) * cornerP N δb δc 0 := by
  set J := recurrenceMatrix (krawDir N δb δc 1 0)
  set E := recurrenceMatrix (stochDir N δb δc)
  have hc : ∀ ε, (J + ε • E) * cornerP N δb δc ε = cornerP N δb δc ε * (J + ε • E) := by
    intro ε
    rw [← krawDir_recurrence]
    exact commute_product (krawDir N δb δc 1 ε) _ rfl N
  ext i j
  have hL : HasDerivAt (fun ε => ((J + ε • E) * cornerP N δb δc ε) i j)
      (∑ l, (E i l * cornerP N δb δc 0 l j + J i l * cornerX N δb δc l j)) 0 := by
    simp only [Matrix.mul_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    apply HasDerivAt.fun_sum; intro l _
    have h1 : HasDerivAt (fun ε : ℝ => J i l + ε * E i l) (E i l) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (E i l)).const_add (J i l)
    exact (h1.mul (cornerP_hasDerivAt (δb := δb) (δc := δc) hN l j)).congr_deriv (by ring)
  have hR : HasDerivAt (fun ε => (cornerP N δb δc ε * (J + ε • E)) i j)
      (∑ l, (cornerX N δb δc i l * J l j + cornerP N δb δc 0 i l * E l j)) 0 := by
    simp only [Matrix.mul_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    apply HasDerivAt.fun_sum; intro l _
    have h1 : HasDerivAt (fun ε : ℝ => J l j + ε * E l j) (E l j) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (E l j)).const_add (J l j)
    exact ((cornerP_hasDerivAt (δb := δb) (δc := δc) hN i l).mul h1).congr_deriv (by ring)
  have he := hL.unique (by simpa only [hc] using hR)
  simp only [Matrix.sub_apply, Matrix.mul_apply]
  rw [sum_add_distrib, sum_add_distrib] at he
  linarith

/-- `e_0^T X = 0`. -/
theorem cornerX_row0 (hN : 1 ≤ N) (k : Fin (N + 1)) : cornerX N δb δc 0 k = 0 := by
  have hev : ∀ᶠ ε in 𝓝 (0 : ℝ), ∀ i ∈ range N, (krawDir N δb δc 1 ε).a i ≠ 0 := by
    refine (eventually_all_finset _).mpr fun i hi => ?_
    exact ((krawDir_eps_contDiff i).1.continuous.continuousAt).eventually_ne
      (krawDir_one_a_pos hN i (mem_range.mp hi)).ne'
  have hconst : (fun ε => cornerP N δb δc ε 0 k) =ᶠ[𝓝 0] fun _ => if k.val = N then (1 : ℝ) else 0 := by
    filter_upwards [hev] with ε hε
    exact row_zero (krawDir N δb δc 1 ε) (fun i hi => hε i (mem_range.mpr hi)) N le_rfl k
  exact (cornerP_hasDerivAt hN 0 k).unique ((hasDerivAt_const (0 : ℝ) _).congr_of_eventuallyEq hconst)

/-! ### `Π` is the index reversal -/

/-- The index reversal `e_n ↦ e_{N-n}`. -/
def revMat (N : ℕ) : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ := fun i j => if i.val + j.val = N then 1 else 0

theorem revMat_mul (P : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (m n : Fin (N + 1)) :
    (revMat N * P) m n = P ⟨N - m.val, by omega⟩ n := by
  rw [Matrix.mul_apply, sum_eq_single ⟨N - m.val, by omega⟩]
  · simp [revMat, show m.val + (N - m.val) = N by omega]
  · intro l _ hl; rw [revMat, if_neg (fun h => hl (Fin.ext (by simp; omega))), zero_mul]
  · intro h; exact absurd (mem_univ _) h

theorem mul_revMat (P : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (m n : Fin (N + 1)) :
    (P * revMat N) m n = P m ⟨N - n.val, by omega⟩ := by
  rw [Matrix.mul_apply, sum_eq_single ⟨N - n.val, by omega⟩]
  · simp [revMat, show N - n.val + n.val = N by omega]
  · intro l _ hl; rw [revMat, if_neg (fun h => hl (Fin.ext (by simp; omega))), mul_zero]
  · intro h; exact absurd (mem_univ _) h

theorem revMat_commute (hN : 1 ≤ N) :
    revMat N * recurrenceMatrix (krawCoefficients N 1) = recurrenceMatrix (krawCoefficients N 1) * revMat N := by
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  ext m n
  rw [revMat_mul, mul_revMat]
  simp only [recurrenceMatrix, krawCoefficients, Fin.ext_iff]
  have hm := m.isLt; have hn := n.isLt
  by_cases h1 : n.val = N - m.val + 1
  · rw [if_pos h1, if_neg (by omega), if_neg (by omega), if_pos (by omega)]
    rw [Nat.cast_sub (by omega)]; field_simp; push_cast [show m.val = N + 1 - n.val by omega]; ring_nf
  · rw [if_neg h1]
    by_cases h2 : n.val = N - m.val
    · rw [if_pos h2, if_neg (by omega), if_pos (by omega)]; ring
    · rw [if_neg h2]
      by_cases h3 : N - m.val = n.val + 1
      · rw [if_pos h3, if_pos (by omega)]
        rw [Nat.cast_sub (by omega)]; ring
      · rw [if_neg h3, if_neg (by omega), if_neg (by omega), if_neg (by omega)]

theorem kraw_one_a_ne (i : ℕ) (hi : i < N) : (krawCoefficients N 1).a i ≠ 0 := by
  simp only [krawCoefficients]
  have : (i : ℝ) < N := by exact_mod_cast hi
  exact (div_pos (by linarith) (by linarith)).ne'

/-- `Π = R_N(J) = ` the index reversal at `K_{N,1}`. -/
theorem cornerP_zero (hN : 1 ≤ N) : cornerP N δb δc 0 = revMat N := by
  rw [cornerP, krawDir_zero hN 1 N (by omega)]
  refine (eq_of_row_zero (krawCoefficients N 1) (kraw_one_a_ne) _ _
    (commute_product _ _ rfl N).symm (revMat_commute hN) fun l => ?_)
  rw [row_zero _ (kraw_one_a_ne) N le_rfl l]
  simp [revMat]

/-! ### The certificate `Z` -/

/-- `Z_{mn} = C(N,n) (-1)^{n+s} / (2 C(N-1,s))` if `m + n = 2s + 1`, and `0` if `m + n` is even. -/
noncomputable def zc (N m n : ℕ) : ℝ :=
  if (m + n) % 2 = 1 then (N.choose n : ℝ) * (-1) ^ (n + (m + n) / 2) / (2 * ((N - 1).choose ((m + n) / 2) : ℝ))
  else 0

theorem zc_val {m n s : ℕ} (h : m + n = 2 * s + 1) :
    zc N m n = (N.choose n : ℝ) * (-1) ^ (n + s) / (2 * ((N - 1).choose s : ℝ)) := by
  rw [zc, if_pos (by omega), show (m + n) / 2 = s by omega]

theorem zc_even {m n : ℕ} (h : (m + n) % 2 = 0) : zc N m n = 0 := by
  rw [zc, if_neg (by omega)]

/-- The certificate as a matrix. -/
noncomputable def zMat (N : ℕ) : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ := fun i j => zc N i j

/-- `Z J - J Z = e_N e_N^T` on the columns `n ≥ 1`. -/
theorem zMat_comm (hN : 1 ≤ N) (m n : Fin (N + 1)) (hn : 1 ≤ n.val) :
    (zMat N * recurrenceMatrix (krawCoefficients N 1) - recurrenceMatrix (krawCoefficients N 1) * zMat N) m n =
      if m.val = N ∧ n.val = N then 1 else 0 := by
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  rw [Matrix.sub_apply, mul_J_apply _ _ (fun l => zc N m l) m n (fun l => rfl),
    J_mul_apply _ _ (fun l => zc N l n) m n (fun l => rfl)]
  simp only [krawCoefficients, sub_self, zero_mul, zero_div, mul_zero, add_zero, one_mul]
  have hm := m.isLt; have hn' := n.isLt
  generalize m.val = a at *
  generalize n.val = b at *
  rw [if_pos hn]
  rcases Nat.even_or_odd (a + b) with ⟨t2, ht2⟩ | ⟨s, hs⟩
  · -- even: `a + b = 2t + 2`
    obtain ⟨t, rfl⟩ : ∃ t, t2 = t + 1 := ⟨t2 - 1, by omega⟩
    obtain ⟨b1, rfl⟩ : ∃ b1, b = b1 + 1 := ⟨b - 1, by omega⟩
    simp only [Nat.add_sub_cancel] at *
    have e1 : zc N a b1 = (N.choose b1 : ℝ) * (-1) ^ (b1 + t) / (2 * ((N - 1).choose t : ℝ)) :=
      zc_val (by omega)
    have e2 : zc N a (b1 + 1 + 1) = -((N.choose (b1 + 1 + 1) : ℝ) * (-1) ^ (b1 + t) /
        (2 * ((N - 1).choose (t + 1) : ℝ))) := by
      rw [zc_val (s := t + 1) (by omega)]; ring
    have e3 : zc N (a + 1) (b1 + 1) = (N.choose (b1 + 1) : ℝ) * (-1) ^ (b1 + t) /
        (2 * ((N - 1).choose (t + 1) : ℝ)) := by
      rw [zc_val (s := t + 1) (by omega)]; ring
    have e4 : ((a : ℝ)) * zc N (a - 1) (b1 + 1) = (a : ℝ) * (-((N.choose (b1 + 1) : ℝ) * (-1) ^ (b1 + t) /
        (2 * ((N - 1).choose t : ℝ)))) := by
      rcases Nat.eq_zero_or_pos a with h0 | hpos
      · subst h0; simp
      · rw [zc_val (s := t) (by omega)]; ring
    by_cases htop : a = N ∧ b1 + 1 = N
    · obtain ⟨haN, hbN⟩ := htop
      have haN' := haN.symm
      subst haN'
      have hb1 : b1 = N - 1 := by omega
      subst hb1
      rw [if_neg (by omega), if_neg (by omega), if_pos (by omega), if_pos ⟨rfl, by omega⟩,
        zc_val (s := N - 1) (by omega), zc_val (s := N - 1) (by omega), show N - 1 + 1 = N by omega,
        Nat.choose_self, Nat.choose_self, Nat.choose_symm (by omega : 1 ≤ N), Nat.choose_one_right,
        Nat.cast_sub (by omega : 1 ≤ N), (Even.neg_one_pow ⟨N - 1, rfl⟩ : (-1 : ℝ) ^ (N - 1 + (N - 1)) = 1),
        (Odd.neg_one_pow ⟨N - 1, by omega⟩ : (-1 : ℝ) ^ (N + (N - 1)) = -1)]
      field_simp
      ring
    · rw [if_neg htop]
      have ht : t + 2 ≤ N := by omega
      have hA : (0 : ℝ) < (N - 1).choose t := by exact_mod_cast Nat.choose_pos (by omega)
      have hB : (0 : ℝ) < (N - 1).choose (t + 1) := by exact_mod_cast Nat.choose_pos (by omega)
      have hAB : ((N - 1).choose (t + 1) : ℝ) * (t + 1) = (N - 1).choose t * ((N : ℝ) - 1 - t) := by
        have h' : ((N - 1).choose (t + 1) : ℝ) * ((t + 1 : ℕ) : ℝ) =
            ((N - 1).choose t : ℝ) * ((N - 1 - t : ℕ) : ℝ) := by
          exact_mod_cast Nat.choose_succ_right_eq (N - 1) t
        rw [Nat.cast_sub (by omega : t ≤ N - 1), Nat.cast_sub (by omega : 1 ≤ N)] at h'
        push_cast at h'; linarith
      have hC1 : (N.choose b1 : ℝ) * ((N : ℝ) - b1) = N.choose (b1 + 1) * ((b1 : ℝ) + 1) := by
        have h' : (N.choose (b1 + 1) : ℝ) * ((b1 + 1 : ℕ) : ℝ) = (N.choose b1 : ℝ) * ((N - b1 : ℕ) : ℝ) := by
          exact_mod_cast Nat.choose_succ_right_eq N b1
        rw [Nat.cast_sub (by omega : b1 ≤ N)] at h'; push_cast at h'; linarith
      have hC2 : (N.choose (b1 + 1 + 1) : ℝ) * ((b1 : ℝ) + 2) = N.choose (b1 + 1) * ((N : ℝ) - b1 - 1) := by
        have h' : (N.choose (b1 + 1 + 1) : ℝ) * ((b1 + 1 + 1 : ℕ) : ℝ) =
            (N.choose (b1 + 1) : ℝ) * ((N - (b1 + 1) : ℕ) : ℝ) := by
          exact_mod_cast Nat.choose_succ_right_eq N (b1 + 1)
        rw [Nat.cast_sub (by omega : b1 + 1 ≤ N)] at h'; push_cast at h'; linarith
      have hsum : (a : ℝ) + b1 + 1 = 2 * t + 2 := by exact_mod_cast (by omega : a + b1 + 1 = 2 * t + 2)
      have g2 : (if b1 + 1 + 1 ≤ N then zc N a (b1 + 1 + 1) * (((b1 + 1 + 1 : ℕ) : ℝ) / N) else 0) =
          zc N a (b1 + 1 + 1) * (((b1 + 1 + 1 : ℕ) : ℝ) / N) := by
        split_ifs with h
        · rfl
        · rw [e2, Nat.choose_eq_zero_of_lt (by omega)]; simp
      have g3 : (if a + 1 ≤ N then ((N : ℝ) - a) / N * zc N (a + 1) (b1 + 1) else 0) =
          ((N : ℝ) - a) / N * zc N (a + 1) (b1 + 1) := by
        split_ifs with h
        · rfl
        · rw [show a = N by omega]; simp
      have g4 : (if 1 ≤ a then (a : ℝ) / N * zc N (a - 1) (b1 + 1) else 0) =
          (a : ℝ) * zc N (a - 1) (b1 + 1) / N := by
        split_ifs with h
        · ring
        · rw [show a = 0 by omega]; simp
      rw [g2, g3, g4, e4, e1, e2, e3]
      set σ : ℝ := (-1) ^ (b1 + t)
      set A : ℝ := ((N - 1).choose t : ℝ)
      set B : ℝ := ((N - 1).choose (t + 1) : ℝ)
      set C0 : ℝ := (N.choose b1 : ℝ)
      set C1 : ℝ := (N.choose (b1 + 1) : ℝ)
      set C2 : ℝ := (N.choose (b1 + 1 + 1) : ℝ)
      have hpoly : C0 * ((N : ℝ) - b1) * B - C2 * ((b1 : ℝ) + 2) * A - ((N : ℝ) - a) * C1 * A + (a : ℝ) * C1 * B = 0 := by
        linear_combination B * hC1 - A * hC2 + 2 * C1 * hAB + C1 * (A + B) * hsum
      have hA0 := hA.ne'; have hB0 := hB.ne'
      have key : C0 * σ / (2 * A) * (((N : ℝ) - b1) / N) + -(C2 * σ / (2 * B)) * (((b1 + 1 + 1 : ℕ) : ℝ) / N) -
          (((N : ℝ) - a) / N * (C1 * σ / (2 * B)) + (a : ℝ) * -(C1 * σ / (2 * A)) / N) =
          σ / (2 * N * A * B) * (C0 * ((N : ℝ) - b1) * B - C2 * ((b1 : ℝ) + 2) * A - ((N : ℝ) - a) * C1 * A +
            (a : ℝ) * C1 * B) := by
        push_cast
        field_simp
        ring
      rw [key, hpoly, mul_zero]
  · -- odd: every term vanishes
    rw [zc_even (show (a + (b - 1)) % 2 = 0 by omega), if_neg (show ¬(a = N ∧ b = N) by omega)]
    have g2 : (if b + 1 ≤ N then zc N a (b + 1) * (((b + 1 : ℕ) : ℝ) / N) else 0) = 0 := by
      split_ifs <;> simp [zc_even (show (a + (b + 1)) % 2 = 0 by omega)]
    have g3 : (if a + 1 ≤ N then ((N : ℝ) - a) / N * zc N (a + 1) b else 0) = 0 := by
      split_ifs <;> simp [zc_even (show (a + 1 + b) % 2 = 0 by omega)]
    have g4 : (if 1 ≤ a then (a : ℝ) / N * zc N (a - 1) b else 0) = 0 := by
      split_ifs with h
      · rw [zc_even (show (a - 1 + b) % 2 = 0 by omega), mul_zero]
      · rfl
    rw [g2, g3, g4]; simp

/-! ### The trace identity -/

/-- `X_{NN} = tr((Z Π - Π Z) E)`. -/
theorem cornerX_trace (hN : 1 ≤ N) :
    cornerX N δb δc (Fin.last N) (Fin.last N) =
      Matrix.trace ((zMat N * revMat N - revMat N * zMat N) * recurrenceMatrix (stochDir N δb δc)) := by
  set J := recurrenceMatrix (krawCoefficients N 1)
  set X := cornerX N δb δc
  set Z := zMat N
  set E := recurrenceMatrix (stochDir N δb δc)
  have hcomm : J * X - X * J = revMat N * E - E * revMat N := by
    have h := cornerX_comm (δb := δb) (δc := δc) hN
    rwa [krawDir_zero_recurrence hN 1, cornerP_zero hN] at h
  have hstep : X (Fin.last N) (Fin.last N) = Matrix.trace ((Z * J - J * Z) * X) := by
    rw [Matrix.trace]
    simp only [Matrix.diag, Matrix.mul_apply]
    have hterm : ∀ m n : Fin (N + 1), (Z * J - J * Z) m n * X n m =
        if m = Fin.last N ∧ n = Fin.last N then X (Fin.last N) (Fin.last N) else 0 := by
      intro m n
      rcases Nat.eq_zero_or_pos n.val with h0 | hpos
      · have : n = 0 := Fin.ext h0
        have hx : X 0 m = 0 := cornerX_row0 hN m
        rw [this, hx, mul_zero, if_neg (fun h => by
          have := congrArg Fin.val h.2; simp at this; omega)]
      · rw [zMat_comm hN m n hpos]
        by_cases h : m = Fin.last N ∧ n = Fin.last N
        · rw [if_pos ⟨by rw [h.1]; rfl, by rw [h.2]; rfl⟩, if_pos h, h.1, h.2, one_mul]
        · rw [if_neg (fun h' => h ⟨Fin.ext h'.1, Fin.ext h'.2⟩), if_neg h, zero_mul]
    simp_rw [hterm]
    rw [sum_eq_single (Fin.last N)]
    · rw [sum_eq_single (Fin.last N)]
      · simp
      · intro n _ hn; rw [if_neg (fun h => hn h.2)]
      · intro h; exact absurd (mem_univ _) h
    · intro m _ hm; exact sum_eq_zero fun n _ => if_neg (fun h => hm h.1)
    · intro h; exact absurd (mem_univ _) h
  rw [hstep]
  calc Matrix.trace ((Z * J - J * Z) * X)
      = Matrix.trace (Z * (J * X - X * J)) := by
        simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.trace_sub, Matrix.mul_assoc]
        rw [Matrix.trace_mul_comm J (Z * X), Matrix.mul_assoc]
    _ = Matrix.trace ((Z * revMat N - revMat N * Z) * E) := by
        rw [hcomm]
        simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.trace_sub, Matrix.mul_assoc]
        rw [Matrix.trace_mul_comm Z (E * revMat N), Matrix.mul_assoc, Matrix.trace_mul_comm E (revMat N * Z),
          Matrix.mul_assoc]

/-! ### Evaluation of `tr((Z Π - Π Z) E)` -/

/-- `W_{ln} = Z_{l,N-n} - Z_{N-l,n}`, the entries of `Z Π - Π Z`. -/
noncomputable def wc (N l n : ℕ) : ℝ := zc N l (N - n) - zc N (N - l) n

theorem W_apply (l n : Fin (N + 1)) :
    (zMat N * revMat N - revMat N * zMat N) l n = wc N l n := by
  rw [Matrix.sub_apply, mul_revMat, revMat_mul]; rfl

theorem neg_one_pow_sub_eq {n M : ℕ} (h : n ≤ M) : (-1 : ℝ) ^ (M - n) = (-1) ^ M * (-1) ^ n := by
  obtain ⟨k, rfl⟩ : ∃ k, M = n + k := ⟨M - n, by omega⟩
  rw [Nat.add_sub_cancel_left, pow_add, mul_comm ((-1 : ℝ) ^ n), mul_assoc, ← pow_add, ← two_mul, pow_mul]
  norm_num

theorem wc_diag_even (hN : N % 2 = 0) {n : ℕ} (hn : n ≤ N) : wc N n n = 0 := by
  rw [wc, zc_even (by omega), zc_even (by omega), sub_zero]

theorem wc_diag_odd {h : ℕ} (hN : N = 2 * h + 1) {n : ℕ} (hn : n ≤ N) :
    wc N n n = -((N.choose n : ℝ) * (-1) ^ (n + h) / ((N - 1).choose h : ℝ)) := by
  rw [wc, zc_val (s := h) (by omega), zc_val (s := h) (by omega), Nat.choose_symm hn, pow_add, pow_add,
    neg_one_pow_sub_eq hn, hN, (Odd.neg_one_pow ⟨h, rfl⟩ : (-1 : ℝ) ^ (2 * h + 1) = -1)]
  ring

theorem wc_up_odd (hN : N % 2 = 1) {n : ℕ} (hn : n + 1 ≤ N) : wc N (n + 1) n = 0 := by
  rw [wc, zc_even (by omega), zc_even (by omega), sub_zero]

theorem wc_up_even {h : ℕ} (hN : N = 2 * h) (h1 : 1 ≤ h) {n : ℕ} (hn : n + 1 ≤ N) :
    wc N (n + 1) n = (N.choose n : ℝ) * (-1) ^ (n + h) / ((N - 1).choose (h - 1) : ℝ) := by
  have hc : (N - 1).choose h = (N - 1).choose (h - 1) := Nat.choose_symm_of_eq_add (by omega)
  rw [wc, zc_val (s := h) (by omega), zc_val (s := h - 1) (by omega), Nat.choose_symm (by omega : n ≤ N), hc]
  simp only [pow_add]
  have e2 : (-1 : ℝ) ^ N = 1 := by rw [hN]; exact Even.neg_one_pow ⟨h, by ring⟩
  have e3 : (-1 : ℝ) ^ h = (-1) ^ (h - 1) * (-1) := by rw [← pow_succ, Nat.sub_add_cancel h1]
  rw [neg_one_pow_sub_eq (by omega : n ≤ N), e2, e3]
  ring

theorem wc_down_odd (hN : N % 2 = 1) {n : ℕ} (hn1 : 1 ≤ n) (hn : n ≤ N) : wc N (n - 1) n = 0 := by
  rw [wc, zc_even (by omega), zc_even (by omega), sub_zero]

theorem wc_down_even {h : ℕ} (hN : N = 2 * h) (h1 : 1 ≤ h) {n : ℕ} (hn1 : 1 ≤ n) (hn : n ≤ N) :
    wc N (n - 1) n = -((N.choose n : ℝ) * (-1) ^ (n + h) / ((N - 1).choose (h - 1) : ℝ)) := by
  have hc : (N - 1).choose h = (N - 1).choose (h - 1) := Nat.choose_symm_of_eq_add (by omega)
  rw [wc, zc_val (s := h - 1) (by omega), zc_val (s := h) (by omega), Nat.choose_symm hn, hc]
  simp only [pow_add]
  have e2 : (-1 : ℝ) ^ N = 1 := by rw [hN]; exact Even.neg_one_pow ⟨h, by ring⟩
  have e3 : (-1 : ℝ) ^ h = (-1) ^ (h - 1) * (-1) := by rw [← pow_succ, Nat.sub_add_cancel h1]
  rw [neg_one_pow_sub_eq hn, e2, e3]
  ring

/-- `s_N = (-1)^{⌊N/2⌋+1} / C(N-1, ⌊(N-1)/2⌋)`. -/
noncomputable def sN (N : ℕ) : ℝ := (-1) ^ (N / 2 + 1) / ((N - 1).choose ((N - 1) / 2) : ℝ)

/-- `F = δb + 2 δc` for even `N` and `F = δb` for odd `N`, with `δb_0 = δc_0 = 0`, `δb_N = -δc_N`. -/
noncomputable def cornerF (N : ℕ) (δb δc : ℕ → ℝ) (n : ℕ) : ℝ :=
  if N % 2 = 0 then (stochDir N δb δc).b n + 2 * (stochDir N δb δc).c n else (stochDir N δb δc).b n

theorem corner_term (hN : 2 ≤ N) (n : ℕ) (hn : n ≤ N) :
    (if n + 1 ≤ N then (stochDir N δb δc).a n * wc N (n + 1) n else 0) + (stochDir N δb δc).b n * wc N n n +
      (if 1 ≤ n then (stochDir N δb δc).c n * wc N (n - 1) n else 0) =
      sN N * ((-1) ^ n * (N.choose n : ℝ) * cornerF N δb δc n) := by
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · subst h0; simp [stochDir, cornerF]
  rcases Nat.even_or_odd' N with ⟨h, hh | hh⟩
  · -- `N = 2h`
    have h1 : 1 ≤ h := by omega
    have hpar : N % 2 = 0 := by omega
    have hs : sN N = (-1) ^ (h + 1) / ((N - 1).choose (h - 1) : ℝ) := by
      rw [sN, show N / 2 = h by omega, show (N - 1) / 2 = h - 1 by omega]
    rw [hs, cornerF, if_pos hpar, wc_diag_even hpar hn, if_pos (show 1 ≤ n by omega),
      wc_down_even hh h1 (by omega) hn]
    by_cases hnN : n = N
    · have e := hnN.symm; subst e
      have gb : (stochDir N δb δc).b N = -(δc N) := by simp [stochDir, show N ≠ 0 by omega]
      have gc : (stochDir N δb δc).c N = δc N := by simp [stochDir, show N ≠ 0 by omega]
      rw [if_neg (show ¬(N + 1 ≤ N) by omega), gb, gc, Nat.choose_self, pow_add, pow_add]
      ring
    · have ga : (stochDir N δb δc).a n = -(δb n) - δc n := by simp [stochDir, show n ≠ 0 by omega, hnN]
      have gb : (stochDir N δb δc).b n = δb n := by simp [stochDir, show n ≠ 0 by omega, hnN]
      have gc : (stochDir N δb δc).c n = δc n := by simp [stochDir, show n ≠ 0 by omega]
      rw [if_pos (show n + 1 ≤ N by omega), wc_up_even hh h1 (by omega), ga, gb, gc, pow_add, pow_add]
      ring
  · -- `N = 2h + 1`
    have hpar : N % 2 = 1 := by omega
    have hs : sN N = (-1) ^ (h + 1) / ((N - 1).choose h : ℝ) := by
      rw [sN, show N / 2 = h by omega, show (N - 1) / 2 = h by omega]
    rw [hs, cornerF, if_neg (show ¬(N % 2 = 0) by omega), wc_diag_odd hh hn, if_pos (show 1 ≤ n by omega),
      wc_down_odd hpar (by omega) hn]
    by_cases hnN : n = N
    · have e := hnN.symm; subst e
      have gb : (stochDir N δb δc).b N = -(δc N) := by simp [stochDir, show N ≠ 0 by omega]
      rw [if_neg (show ¬(N + 1 ≤ N) by omega), gb, Nat.choose_self]
      have e2 : (-1 : ℝ) ^ N = -1 := by rw [hh]; exact Odd.neg_one_pow ⟨h, rfl⟩
      rw [pow_add, pow_add, e2]
      ring
    · have gb : (stochDir N δb δc).b n = δb n := by simp [stochDir, show n ≠ 0 by omega, hnN]
      rw [if_pos (show n + 1 ≤ N by omega), wc_up_odd hpar (by omega), gb, pow_add, pow_add]
      ring

/-- **Lemma 9.2** (Corner identity): for `N ≥ 2` the first-order change of `g(N,N;N)` at `K_{N,1}`
along `v = (δb, δc)` is `s_N Σ_{n=0}^N (-1)^n C(N,n) F(n)`. -/
theorem corner_identity (hN : 2 ≤ N) :
    HasDerivAt (fun ε => productMatrix (krawDir N δb δc 1 ε) N (Fin.last N) (Fin.last N))
      (sN N * ∑ n ∈ range (N + 1), (-1) ^ n * (N.choose n : ℝ) * cornerF N δb δc n) 0 := by
  have h := cornerP_hasDerivAt (δb := δb) (δc := δc) (by omega) (Fin.last N) (Fin.last N)
  suffices hv : cornerX N δb δc (Fin.last N) (Fin.last N) =
      sN N * ∑ n ∈ range (N + 1), (-1) ^ n * (N.choose n : ℝ) * cornerF N δb δc n by
    rw [hv] at h; exact h
  rw [cornerX_trace (by omega), Matrix.trace_mul_comm, Matrix.trace]
  simp only [Matrix.diag]
  rw [mul_sum]
  have e : ∀ n : Fin (N + 1), (recurrenceMatrix (stochDir N δb δc) * (zMat N * revMat N - revMat N * zMat N)) n n =
      (if n.val + 1 ≤ N then (stochDir N δb δc).a n * wc N (n.val + 1) n else 0) +
        (stochDir N δb δc).b n * wc N n n + (if 1 ≤ n.val then (stochDir N δb δc).c n * wc N (n.val - 1) n else 0) :=
    fun n => J_mul_apply _ _ (fun l => wc N l n) n n (fun l => W_apply l n)
  simp_rw [e]
  rw [Fin.sum_univ_eq_sum_range (fun n => (if n + 1 ≤ N then (stochDir N δb δc).a n * wc N (n + 1) n else 0) +
    (stochDir N δb δc).b n * wc N n n + (if 1 ≤ n then (stochDir N δb δc).c n * wc N (n - 1) n else 0)) (N + 1)]
  exact sum_congr rfl fun n hn => corner_term hN n (by rw [mem_range] at hn; omega)

end Szkraw
