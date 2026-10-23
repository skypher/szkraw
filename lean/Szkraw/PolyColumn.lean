import Szkraw.RuleCounterexamples
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Product coefficients along a line of arrays, as quotients of integer polynomials

For an array `v(ε)` with `a_i = A_i(ε)/Q`, `b_i = B_i(ε)/Q`, `c_i = C_i(ε)/Q` (`A_i, B_i, C_i` integer polynomials),
`g(m,n;k)(ε) = H_m(n)(ε)/S_m(ε)` with `S_m = A_0 ⋯ A_{m-1}` and integer polynomials `H_m(n)` given by the column
recurrence (`pcol`). The derivative at `ε = 0` is then `(H'(0) S(0) - H(0) S'(0))/S(0)²`, read off from the first two
coefficients. Used for the first-order derivatives along the rule `β = 1`, `γ = 0` at `r = 4/5` (P3, Section 9).
-/

namespace Szkraw
namespace PolyCol

open Filter Topology

/-! ### Integer polynomials as coefficient lists -/

def padd : List ℤ → List ℤ → List ℤ
  | [], q => q
  | p, [] => p
  | x :: p, y :: q => (x + y) :: padd p q

def pneg (p : List ℤ) : List ℤ := p.map (- ·)

def pmul : List ℤ → List ℤ → List ℤ
  | [], _ => []
  | x :: p, q => padd (q.map (x * ·)) (0 :: pmul p q)

/-- `evP ε [p₀, p₁, …] = p₀ + p₁ ε + ⋯`. -/
noncomputable def evP (ε : ℝ) : List ℤ → ℝ
  | [] => 0
  | x :: p => x + ε * evP ε p

theorem evP_padd (ε : ℝ) : ∀ p q, evP ε (padd p q) = evP ε p + evP ε q
  | [], q => by simp [padd, evP]
  | x :: p, [] => by simp [padd, evP]
  | x :: p, y :: q => by simp only [padd, evP, evP_padd ε p q]; push_cast; ring

theorem evP_map_mul (ε : ℝ) (c : ℤ) : ∀ p, evP ε (p.map (c * ·)) = c * evP ε p
  | [] => by simp [evP]
  | x :: p => by simp only [List.map_cons, evP, evP_map_mul ε c p]; push_cast; ring

theorem evP_pneg (ε : ℝ) (p : List ℤ) : evP ε (pneg p) = -evP ε p := by
  have := evP_map_mul ε (-1) p
  simp only [Int.cast_neg, Int.cast_one, neg_one_mul] at this
  rw [← this, pneg]

theorem evP_pmul (ε : ℝ) : ∀ p q, evP ε (pmul p q) = evP ε p * evP ε q
  | [], q => by simp [pmul, evP]
  | x :: p, q => by
    simp only [pmul, evP_padd, evP_map_mul, evP, evP_pmul ε p q]; push_cast; ring

/-- The derivative of `ε ↦ evP ε p`. -/
noncomputable def dP (ε : ℝ) : List ℤ → ℝ
  | [] => 0
  | _ :: p => evP ε p + ε * dP ε p

theorem evP_hasDerivAt (ε : ℝ) : ∀ p, HasDerivAt (fun e => evP e p) (dP ε p) ε
  | [] => by simpa [evP, dP] using hasDerivAt_const ε (0 : ℝ)
  | x :: p => by
    have h := ((hasDerivAt_id ε).mul (evP_hasDerivAt ε p)).const_add (x : ℝ)
    simp only [id, one_mul] at h
    simpa [evP, dP] using h

theorem dP_zero (p : List ℤ) : dP 0 p = ((p.tail.headD 0 : ℤ) : ℝ) := by
  cases p with
  | nil => simp [dP]
  | cons x p => cases p <;> simp [dP, evP]

theorem evP_zero (p : List ℤ) : evP 0 p = ((p.headD 0 : ℤ) : ℝ) := by
  cases p <;> simp [evP]

/-! ### The polynomial column -/

abbrev PL := List (List ℤ)

/-- Entry `i`, the zero polynomial outside the list. -/
def pget (L : PL) (i : ℕ) : List ℤ := L.getD i []

def pstep (A B C : PL) (N m : ℕ) (P X : PL) : PL :=
  (List.range (N + 1)).map fun n =>
    padd (padd (pmul (pget A n) (pget X (n + 1))) (pmul (padd (pget B n) (pneg (pget B m))) (pget X n)))
      (padd (if n = 0 then [] else pmul (pget C n) (pget X (n - 1)))
        (pneg (pmul (pmul (pget C m) (pget A (m - 1))) (pget P n))))

def pcol (A B C : PL) (N k : ℕ) : ℕ → PL × PL
  | 0 => ([], (List.range (N + 1)).map fun n => if n = k then [1] else [])
  | m + 1 => ((pcol A B C N k m).2, pstep A B C N m (pcol A B C N k m).1 (pcol A B C N k m).2)

/-- `S_m = A_0 ⋯ A_{m-1}`. -/
def pS (A : PL) : ℕ → List ℤ
  | 0 => [1]
  | m + 1 => pmul (pS A m) (pget A m)

theorem pget_map_range (N : ℕ) (f : ℕ → List ℤ) (i : ℕ) :
    pget ((List.range (N + 1)).map f) i = if i ≤ N then f i else [] := by
  unfold pget
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range]
  by_cases h : i ≤ N <;> simp [h, show i < N + 1 ↔ i ≤ N by omega]

section real

variable (A B C : PL) (N : ℕ)

noncomputable def G (ε : ℝ) (m n k : ℕ) : ℝ := evP ε (pget (pcol A B C N k m).2 n) / evP ε (pS A m)

variable {A B C N}

theorem pS_ne (ε : ℝ) (hA : ∀ j < N, evP ε (pget A j) ≠ 0) : ∀ m, m ≤ N → evP ε (pS A m) ≠ 0
  | 0, _ => by simp [pS, evP]
  | m + 1, h => by
    rw [pS, evP_pmul]
    exact mul_ne_zero (pS_ne ε hA m (by omega)) (hA m (by omega))

theorem productMatrix_eq_pcol (ε Q : ℝ) (hQ : Q ≠ 0) (v : Coefficients N)
    (hA : ∀ j < N, evP ε (pget A j) ≠ 0)
    (ha : ∀ i, i ≤ N → v.a i = evP ε (pget A i) / Q) (hb : ∀ i, i ≤ N → v.b i = evP ε (pget B i) / Q)
    (hc : ∀ i, i ≤ N → v.c i = evP ε (pget C i) / Q) :
    ∀ m, m ≤ N → ∀ n k : Fin (N + 1), productMatrix v m n k = G A B C N ε m n k := by
  have hva : ∀ i, i < N → v.a i ≠ 0 := fun i hi => by rw [ha i hi.le]; exact div_ne_zero (hA i hi) hQ
  have h0 : ∀ n k : ℕ, n ≤ N → k ≤ N → G A B C N ε 0 n k = if n = k then 1 else 0 := by
    intro n k hn _
    simp only [G, pcol, pS, pget_map_range, if_pos hn]
    by_cases h : n = k <;> simp [h, evP]
  refine product_eq_of_rec v (G A B C N ε) hva h0 fun m n k hm hn _ => ?_
  have hSm := pS_ne ε hA m (by omega)
  have hAm := hA m (by omega)
  set X := (pcol A B C N k m).2
  set P := (pcol A B C N k m).1
  have hG1 : G A B C N ε (m + 1) n k =
      (evP ε (pget A n) * evP ε (pget X (n + 1)) + (evP ε (pget B n) - evP ε (pget B m)) * evP ε (pget X n) +
        (if n = 0 then 0 else evP ε (pget C n) * evP ε (pget X (n - 1))) -
        evP ε (pget C m) * evP ε (pget A (m - 1)) * evP ε (pget P n)) /
        (evP ε (pS A m) * evP ε (pget A m)) := by
    simp only [G, pcol, pS, pstep, pget_map_range, if_pos hn, evP_padd, evP_pmul, evP_pneg]
    congr 1
    split_ifs <;> (try simp only [evP, evP_pmul]) <;> ring
  rw [hG1, ha m (by omega), hb m (by omega), hb n hn]
  have hX : ∀ j, G A B C N ε m j k = evP ε (pget X j) / evP ε (pS A m) := fun j => rfl
  have hA' : (if n + 1 ≤ N then v.a n * G A B C N ε m (n + 1) k else 0) =
      evP ε (pget A n) / Q * (evP ε (pget X (n + 1)) / evP ε (pS A m)) := by
    split_ifs with h
    · rw [ha n hn, hX]
    · have hl : X.length = N + 1 := by
        cases m with
        | zero => simp [X, pcol]
        | succ m => simp [X, pcol, pstep]
      have : pget X (n + 1) = [] := by
        unfold pget
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
        rfl
      rw [this]; simp [evP]
  have hC' : (if 1 ≤ n then v.c n * G A B C N ε m (n - 1) k else 0) =
      (if n = 0 then 0 else evP ε (pget C n) * evP ε (pget X (n - 1))) / (Q * evP ε (pS A m)) := by
    split_ifs with h h'
    · omega
    · rw [hc n hn, hX]; field_simp
    · simp
    · omega
  have hD' : (if 1 ≤ m then v.c m * G A B C N ε (m - 1) n k else 0) =
      evP ε (pget C m) * evP ε (pget A (m - 1)) * evP ε (pget P n) / (Q * evP ε (pS A m)) := by
    split_ifs with h
    · obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      have hSm' := pS_ne ε hA m' (by omega)
      have hAm' := hA m' (by omega)
      rw [hc (m' + 1) (by omega)]
      simp only [Nat.add_sub_cancel, G, P, pcol, pS, evP_pmul]
      field_simp
    · have : m = 0 := by omega
      subst this
      simp [P, pcol, pget, evP]
  rw [hA', hC', hD', hX]
  field_simp
  ring

/-- The derivative at `0` of `ε ↦ g(m,n;k)(ε)`, when the denominators do not vanish near `0`. -/
theorem productMatrix_hasDerivAt (Q : ℝ) (hQ : Q ≠ 0) (v : ℝ → Coefficients N)
    (hA0 : ∀ j < N, evP 0 (pget A j) ≠ 0)
    (ha : ∀ ε, ∀ i, i ≤ N → (v ε).a i = evP ε (pget A i) / Q)
    (hb : ∀ ε, ∀ i, i ≤ N → (v ε).b i = evP ε (pget B i) / Q)
    (hc : ∀ ε, ∀ i, i ≤ N → (v ε).c i = evP ε (pget C i) / Q) (m : ℕ) (hm : m ≤ N) (n k : Fin (N + 1)) :
    let H := pget (pcol A B C N k m).2 n
    let S := pS A m
    HasDerivAt (fun ε => productMatrix (v ε) m n k)
      ((((H.tail.headD 0 * S.headD 0 - H.headD 0 * S.tail.headD 0 : ℤ)) : ℝ) / ((S.headD 0 : ℤ) : ℝ) ^ 2) 0 := by
  intro H S
  -- near `0` all `A_j(ε)` are nonzero
  have hev : ∀ᶠ ε in 𝓝 (0 : ℝ), ∀ j ∈ Finset.range N, evP ε (pget A j) ≠ 0 := by
    rw [Finset.eventually_all]
    intro j hj
    exact (evP_hasDerivAt 0 (pget A j)).continuousAt.eventually_ne (hA0 j (Finset.mem_range.1 hj))
  have hS0 : evP 0 S ≠ 0 := pS_ne 0 hA0 m hm
  have heq : (fun ε => productMatrix (v ε) m n k) =ᶠ[𝓝 0] fun ε => evP ε H / evP ε S := by
    filter_upwards [hev] with ε hε
    exact productMatrix_eq_pcol ε Q hQ (v ε) (fun j hj => hε j (Finset.mem_range.2 hj)) (ha ε) (hb ε) (hc ε)
      m hm n k
  have hd := (evP_hasDerivAt 0 H).div (evP_hasDerivAt 0 S) hS0
  rw [dP_zero, dP_zero, evP_zero, evP_zero] at hd
  rw [evP_zero] at hS0
  refine (hd.congr_of_eventuallyEq heq).congr_deriv ?_
  push_cast
  ring

end real

end PolyCol
end Szkraw

namespace Szkraw
namespace PolyCol

/-! ### Directions at `K_{N,r}`, `r = p/q`: polynomial numerators over `Q = q N` -/

def dA (N : ℕ) (δb δc : ℕ → ℤ) (p q : ℤ) : PL := (List.range (N + 1)).map fun n : ℕ =>
  if n = 0 then [q * N] else if n = N then [] else [q * N - q * n, -(q * N * (δb n + δc n))]
def dB (N : ℕ) (δb δc : ℕ → ℤ) (p q : ℤ) : PL := (List.range (N + 1)).map fun n : ℕ =>
  if n = 0 then [] else if n = N then [q * N - p * N, -(q * N * δc n)] else [(q - p) * n, q * N * δb n]
def dC (N : ℕ) (δc : ℕ → ℤ) (p q : ℤ) : PL := (List.range (N + 1)).map fun n : ℕ =>
  if n = 0 then [] else [p * n, q * N * δc n]

theorem krawDir_poly {N : ℕ} (hN : 1 ≤ N) {δb δc : ℕ → ℤ} {δb' δc' : ℕ → ℝ} {p q : ℤ} (hq : 0 < q)
    (hb' : ∀ n, δb' n = δb n) (hc' : ∀ n, δc' n = δc n) (ε : ℝ) (i : ℕ) (hi : i ≤ N) :
    let v := krawDir N δb' δc' ((p : ℝ) / q) ε
    v.a i = evP ε (pget (dA N δb δc p q) i) / (q * N) ∧ v.b i = evP ε (pget (dB N δb δc p q) i) / (q * N) ∧
      v.c i = evP ε (pget (dC N δc p q) i) / (q * N) := by
  intro v
  have hq' : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have hQ : (q : ℝ) * N ≠ 0 := mul_ne_zero hq' hN'
  simp only [v, krawDir, stochArray, dA, dB, dC, pget_map_range, if_pos hi, hb', hc']
  refine ⟨?_, ?_, ?_⟩ <;> rw [eq_div_iff hQ] <;> split_ifs with h0 h1 <;> (try subst h0) <;>
    (try subst h1) <;> simp only [evP] <;> push_cast <;> field_simp <;> ring

/-- **P3, Section 9**: at `r = 4/5` the first-order derivative of `g(N,N;N)` along the rule `β = 1`, `γ = 0` is
`512/1875` for `N = 4` and `-71936/5859375` for `N = 8`. -/
theorem rule_deriv_4_5 :
    HasDerivAt (fun ε => productMatrix (krawDir 4 (fun _ => 1) (fun _ => 0) (4 / 5) ε) 4 (Fin.last 4) (Fin.last 4))
      (512 / 1875) 0 ∧
    HasDerivAt (fun ε => productMatrix (krawDir 8 (fun _ => 1) (fun _ => 0) (4 / 5) ε) 8 (Fin.last 8) (Fin.last 8))
      (-71936 / 5859375) 0 := by
  have T : ∀ N : ℕ, 1 ≤ N → (∀ j < N, (pget (dA N (fun _ => 1) (fun _ => 0) 4 5) j).headD 0 ≠ 0) →
      HasDerivAt (fun ε => productMatrix (krawDir N (fun _ => 1) (fun _ => 0) (((4 : ℤ) : ℝ) / ((5 : ℤ) : ℝ)) ε) N
        (Fin.last N) (Fin.last N))
        (let H := pget (pcol (dA N (fun _ => 1) (fun _ => 0) 4 5) (dB N (fun _ => 1) (fun _ => 0) 4 5)
            (dC N (fun _ => 0) 4 5) N N N).2 N
          let S := pS (dA N (fun _ => 1) (fun _ => 0) 4 5) N
          (((H.tail.headD 0 * S.headD 0 - H.headD 0 * S.tail.headD 0 : ℤ)) : ℝ) / ((S.headD 0 : ℤ) : ℝ) ^ 2) 0 := by
    intro N hN h0
    have hQ : ((5 : ℤ) : ℝ) * N ≠ 0 := mul_ne_zero (by norm_num) (by exact_mod_cast (show N ≠ 0 by omega))
    exact productMatrix_hasDerivAt (C := dC N (fun _ => 0) 4 5) _ hQ _
      (fun j hj => by rw [evP_zero]; exact_mod_cast h0 j hj)
      (fun ε i hi => (krawDir_poly (δb := fun _ => 1) (δc := fun _ => 0) hN (by norm_num) (fun _ => by simp)
        (fun _ => by simp) ε i hi).1)
      (fun ε i hi => (krawDir_poly (δb := fun _ => 1) (δc := fun _ => 0) hN (by norm_num) (fun _ => by simp)
        (fun _ => by simp) ε i hi).2.1)
      (fun ε i hi => (krawDir_poly (δb := fun _ => 1) (δc := fun _ => 0) hN (by norm_num) (fun _ => by simp)
        (fun _ => by simp) ε i hi).2.2) N le_rfl (Fin.last N) (Fin.last N)
  have e45 : (((4 : ℤ) : ℝ) / ((5 : ℤ) : ℝ)) = 4 / 5 := by norm_num
  constructor
  · have h := T 4 (by norm_num) (by decide +kernel)
    rw [e45] at h
    refine h.congr_deriv ?_
    dsimp only
    have hY : ((pS (dA 4 (fun _ => 1) (fun _ => 0) 4 5) 4).headD 0 : ℤ) ≠ 0 := by decide +kernel
    rw [div_eq_div_iff (pow_ne_zero 2 (by exact_mod_cast hY)) (by norm_num)]
    norm_cast
  · have h := T 8 (by norm_num) (by decide +kernel)
    rw [e45] at h
    refine h.congr_deriv ?_
    dsimp only
    have hY : ((pS (dA 8 (fun _ => 1) (fun _ => 0) 4 5) 8).headD 0 : ℤ) ≠ 0 := by decide +kernel
    rw [div_eq_div_iff (pow_ne_zero 2 (by exact_mod_cast hY)) (by norm_num)]
    norm_cast

end PolyCol
end Szkraw
