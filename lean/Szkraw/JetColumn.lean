import Szkraw.LCAssembly
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add

/-!
# First-order jets of product coefficients along a path of arrays

Let `ε ↦ v ε` be a path of arrays whose coefficients have derivatives at `0`, with
`Q a_i(0) = α_i`, `Q b_i(0) = β_i`, `Q c_i(0) = γ_i` and `Q a_i'(0) = α'_i`, … for integers `α, β, γ, α', β', γ'`
and `Q > 0`. With `T_m = α_0 ⋯ α_{m-1}`, the integers `V_m(n)` and `W_m(n)` of `jcol` (column `k`) give
`g(m,n;k) = V_m(n)/T_m` at `ε = 0` and `d/dε g(m,n;k) = W_m(n)/T_m²` at `ε = 0` (`jet_column`). Used for the rates
`A_z`, `B_z` behind `Λ_N` (P3, Proposition 9.8).
-/

namespace Szkraw
namespace JetCol

open Finset Filter Topology

def eG (L : List ℤ) (i : ℕ) : ℤ := L.getD i 0

/-- `(V_{m-1}, V_m, W_{m-1}, W_m, T_{m-1}, T_m)`. -/
structure St where
  Vp : List ℤ
  V : List ℤ
  Wp : List ℤ
  W : List ℤ
  Tp : ℤ
  T : ℤ

/-- The coefficient data `α, β, γ, α', β', γ'`. -/
structure Dat where
  al : List ℤ
  be : List ℤ
  ga : List ℤ
  dal : List ℤ
  dbe : List ℤ
  dga : List ℤ

def vnew (D : Dat) (N m : ℕ) (s : St) (n : ℕ) : ℤ :=
  eG D.al n * eG s.V (n + 1) + (eG D.be n - eG D.be m) * eG s.V n + eG D.ga n * eG s.V (n - 1) -
    eG D.ga m * eG D.al (m - 1) * eG s.Vp n

/-- `Q T_m² R'(0)`, the derivative of the right-hand side. -/
def rder (D : Dat) (N m : ℕ) (s : St) (n : ℕ) : ℤ :=
  eG D.dal n * s.T * eG s.V (n + 1) + eG D.al n * eG s.W (n + 1) +
    (eG D.dbe n - eG D.dbe m) * s.T * eG s.V n + (eG D.be n - eG D.be m) * eG s.W n +
    eG D.dga n * s.T * eG s.V (n - 1) + eG D.ga n * eG s.W (n - 1) -
    eG D.dga m * eG D.al (m - 1) ^ 2 * s.Tp * eG s.Vp n - eG D.ga m * eG D.al (m - 1) ^ 2 * eG s.Wp n

def step (D : Dat) (N m : ℕ) (s : St) : St :=
  ⟨s.V, (List.range (N + 1)).map (vnew D N m s), s.W,
    (List.range (N + 1)).map fun n => eG D.al m * rder D N m s n - eG D.dal m * s.T * vnew D N m s n,
    s.T, s.T * eG D.al m⟩

def jcol (D : Dat) (N k : ℕ) : ℕ → St
  | 0 => ⟨List.replicate (N + 1) 0, (List.range (N + 1)).map fun n => if n = k then 1 else 0,
      List.replicate (N + 1) 0, List.replicate (N + 1) 0, 1, 1⟩
  | m + 1 => step D N m (jcol D N k m)

theorem eG_map_range (f : ℕ → ℤ) (N i : ℕ) :
    eG ((List.range (N + 1)).map f) i = if i ≤ N then f i else 0 := by
  unfold eG
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range]
  by_cases h : i ≤ N <;> simp [h, show i < N + 1 ↔ i ≤ N by omega]

theorem eG_replicate (N i : ℕ) : eG (List.replicate (N + 1) 0) i = 0 := by
  unfold eG
  simp only [List.getD_eq_getElem?_getD, List.getElem?_replicate]
  split_ifs <;> simp

/-- Entries of the state lists vanish above `N`. -/
theorem jcol_out (D : Dat) (N k : ℕ) : ∀ m, ∀ i, N < i →
    eG (jcol D N k m).V i = 0 ∧ eG (jcol D N k m).W i = 0 ∧ eG (jcol D N k m).Vp i = 0 ∧ eG (jcol D N k m).Wp i = 0
  | 0, i, h => by simp [jcol, eG_map_range, eG_replicate, show ¬ i ≤ N by omega]
  | m + 1, i, h => by
    have ih := jcol_out D N k m i h
    simp only [jcol, step, eG_map_range, if_neg (show ¬ i ≤ N by omega)]
    exact ⟨trivial, trivial, ih.1, ih.2.1⟩

/-! ### Identification with the product table -/

variable {N : ℕ}

theorem T_pos (D : Dat) (k : ℕ) (hal : ∀ i < N, 0 < eG D.al i) :
    ∀ m, m ≤ N → 0 < (jcol D N k m).T ∧ (1 ≤ m → (jcol D N k m).T = (jcol D N k m).Tp * eG D.al (m - 1)) ∧
      0 < (jcol D N k m).Tp
  | 0, _ => by simp [jcol]
  | m + 1, h => by
    obtain ⟨h1, -, h3⟩ := T_pos D k hal m (by omega)
    refine ⟨?_, fun _ => ?_, ?_⟩
    · show 0 < (jcol D N k m).T * eG D.al m
      exact mul_pos h1 (hal m (by omega))
    · show (jcol D N k m).T * eG D.al m = (jcol D N k m).T * eG D.al (m + 1 - 1)
      rw [Nat.add_sub_cancel]
    · exact h1

/-- **Jets of product coefficients**: `g(m,n;k)(0) = V_m(n)/T_m` and `g'(0) = W_m(n)/T_m²`. -/
theorem jet_column (D : Dat) (v : ℝ → Coefficients N) (Q : ℝ) (hQ : 0 < Q)
    (h0a : ∀ i, i ≤ N → (v 0).a i = eG D.al i / Q) (h0b : ∀ i, i ≤ N → (v 0).b i = eG D.be i / Q)
    (h0c : ∀ i, i ≤ N → (v 0).c i = eG D.ga i / Q)
    (hda : ∀ i, i ≤ N → HasDerivAt (fun ε => (v ε).a i) (eG D.dal i / Q) 0)
    (hdb : ∀ i, i ≤ N → HasDerivAt (fun ε => (v ε).b i) (eG D.dbe i / Q) 0)
    (hdc : ∀ i, i ≤ N → HasDerivAt (fun ε => (v ε).c i) (eG D.dga i / Q) 0)
    (hal : ∀ i < N, 0 < eG D.al i) (hg0 : eG D.ga 0 = 0) (hdg0 : eG D.dga 0 = 0) (k : ℕ) :
    ∀ m, m ≤ N → ∀ n : Fin (N + 1), ∀ hk : k < N + 1,
      productMatrix (v 0) m n ⟨k, hk⟩ = (eG (jcol D N k m).V n : ℝ) / (jcol D N k m).T ∧
      HasDerivAt (fun ε => productMatrix (v ε) m n ⟨k, hk⟩)
        ((eG (jcol D N k m).W n : ℝ) / ((jcol D N k m).T : ℝ) ^ 2) 0 ∧
      (matrixPair (v 0) m).1 n ⟨k, hk⟩ = (eG (jcol D N k m).Vp n : ℝ) / (jcol D N k m).Tp ∧
      HasDerivAt (fun ε => (matrixPair (v ε) m).1 n ⟨k, hk⟩)
        ((eG (jcol D N k m).Wp n : ℝ) / ((jcol D N k m).Tp : ℝ) ^ 2) 0 := by
  intro m
  induction m with
  | zero =>
    intro _ n hk
    have hP : ∀ ε, productMatrix (v ε) 0 n ⟨k, hk⟩ = if n.val = k then 1 else 0 := fun ε => by
      show (1 : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) n ⟨k, hk⟩ = _
      rw [Matrix.one_apply]; simp [Fin.ext_iff]
    have hP1 : ∀ ε, (matrixPair (v ε) 0).1 n ⟨k, hk⟩ = 0 := fun ε => rfl
    simp only [jcol, eG_map_range, if_pos (show n.val ≤ N by omega), eG_replicate, Int.cast_zero, zero_div,
      Int.cast_one, div_one, one_pow]
    refine ⟨by rw [hP]; split_ifs <;> simp, ?_, hP1 0, ?_⟩
    · rw [show (fun ε => productMatrix (v ε) 0 n ⟨k, hk⟩) = fun _ => if n.val = k then (1 : ℝ) else 0 from
        funext hP]
      split_ifs <;> simpa using hasDerivAt_const (0 : ℝ) _
    · rw [show (fun ε => (matrixPair (v ε) 0).1 n ⟨k, hk⟩) = fun _ => (0 : ℝ) from funext hP1]
      exact hasDerivAt_const _ _
  | succ m ih =>
    intro hm n hk
    have ihm := fun n => ih (by omega) n hk
    obtain ⟨hT, hTrel, hTp⟩ := T_pos D k hal m (by omega)
    have hT' : (0 : ℝ) < (jcol D N k m).T := by exact_mod_cast hT
    have hTp' : (0 : ℝ) < (jcol D N k m).Tp := by exact_mod_cast hTp
    have hαm : (0 : ℝ) < eG D.al m := by exact_mod_cast hal m (by omega)
    set s := jcol D N k m with hs
    -- the column as a function on `ℕ`
    let F : ℝ → ℕ → ℝ := fun ε l => if h : l ≤ N then productMatrix (v ε) m ⟨l, by omega⟩ ⟨k, hk⟩ else 0
    have hFin : ∀ ε l (h : l ≤ N), F ε l = productMatrix (v ε) m ⟨l, by omega⟩ ⟨k, hk⟩ := fun ε l h => dif_pos h
    have hFout : ∀ ε l, N < l → F ε l = 0 := fun ε l h => dif_neg (by omega)
    have hF : ∀ ε (l : Fin (N + 1)), productMatrix (v ε) m l ⟨k, hk⟩ = F ε l.val := fun ε l => by
      rw [hFin ε l.val (by omega)]
    have Fv : ∀ l, F 0 l = (eG s.V l : ℝ) / s.T := fun l => by
      by_cases h : l ≤ N
      · rw [hFin 0 l h]; exact (ihm ⟨l, by omega⟩).1
      · rw [hFout 0 l (by omega), (jcol_out D N k m l (by omega)).1]; simp
    have Fd : ∀ l, HasDerivAt (fun ε => F ε l) ((eG s.W l : ℝ) / (s.T : ℝ) ^ 2) 0 := fun l => by
      by_cases h : l ≤ N
      · simp only [hFin _ l h]; exact (ihm ⟨l, by omega⟩).2.1
      · simp only [hFout _ l (by omega)]
        rw [(jcol_out D N k m l (by omega)).2.1, Int.cast_zero, zero_div]
        exact hasDerivAt_const (0 : ℝ) (0 : ℝ)
    -- the recurrence at every `ε`
    let X : ℝ → ℝ := fun ε => (if n.val + 1 ≤ N then (v ε).a n * F ε (n + 1) else 0) + (v ε).b n * F ε n +
      (if 1 ≤ n.val then (v ε).c n * F ε (n - 1) else 0) - (v ε).b m * F ε n -
      (v ε).c m * (matrixPair (v ε) m).1 n ⟨k, hk⟩
    have hrec : ∀ ε, productMatrix (v ε) (m + 1) n ⟨k, hk⟩ = ((v ε).a m)⁻¹ * X ε := fun ε => by
      rw [show productMatrix (v ε) (m + 1) = ((v ε).a m)⁻¹ • ((recurrenceMatrix (v ε) - (v ε).b m •
        (1 : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)) * productMatrix (v ε) m - (v ε).c m • (matrixPair (v ε) m).1)
        from rfl]
      simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul, smul_eq_mul]
      rw [J_mul_apply (v ε) _ (F ε) n ⟨k, hk⟩ (fun l => hF ε l), hF ε n]
    -- uniform boundary terms
    have hVN : eG s.V (n + 1) = 0 ∨ n.val + 1 ≤ N := by
      by_cases h : n.val + 1 ≤ N
      · exact Or.inr h
      · exact Or.inl (jcol_out D N k m _ (by omega)).1
    have hWN : n.val + 1 ≤ N ∨ eG s.W (n + 1) = 0 := by
      by_cases h : n.val + 1 ≤ N
      · exact Or.inl h
      · exact Or.inr (jcol_out D N k m _ (by omega)).2.1
    have hprev0 := (ihm n).2.2.1
    have hprevd := (ihm n).2.2.2
    have hγ0 : n.val = 0 → (eG D.ga n : ℝ) = 0 ∧ (eG D.dga n : ℝ) = 0 := fun h => by
      rw [show (n : ℕ) = 0 from h, hg0, hdg0]; simp
    have oV : ¬ n.val + 1 ≤ N → (eG s.V (n + 1) : ℝ) = 0 := fun h => by
      rw [(jcol_out D N k m _ (by omega)).1]; simp
    have oW : ¬ n.val + 1 ≤ N → (eG s.W (n + 1) : ℝ) = 0 := fun h => by
      rw [(jcol_out D N k m _ (by omega)).2.1]; simp
    -- derivative of `X`
    have dT1 : HasDerivAt (fun ε => if n.val + 1 ≤ N then (v ε).a n * F ε (n + 1) else 0)
        ((eG D.dal n : ℝ) / Q * ((eG s.V (n + 1) : ℝ) / s.T) +
          (eG D.al n : ℝ) / Q * ((eG s.W (n + 1) : ℝ) / (s.T : ℝ) ^ 2)) 0 := by
      by_cases h : n.val + 1 ≤ N
      · simp only [if_pos h]
        have := (hda n (by omega)).mul (Fd (n + 1))
        rwa [Fv, h0a n (by omega)] at this
      · simp only [if_neg h, oV h, oW h, zero_div, mul_zero, add_zero]
        exact hasDerivAt_const (0 : ℝ) (0 : ℝ)
    have dT2 : HasDerivAt (fun ε => (v ε).b n * F ε n)
        ((eG D.dbe n : ℝ) / Q * ((eG s.V n : ℝ) / s.T) + (eG D.be n : ℝ) / Q * ((eG s.W n : ℝ) / (s.T : ℝ) ^ 2)) 0 := by
      have := (hdb n (by omega)).mul (Fd n); rwa [Fv, h0b n (by omega)] at this
    have dT3 : HasDerivAt (fun ε => if 1 ≤ n.val then (v ε).c n * F ε (n - 1) else 0)
        ((eG D.dga n : ℝ) / Q * ((eG s.V (n - 1) : ℝ) / s.T) +
          (eG D.ga n : ℝ) / Q * ((eG s.W (n - 1) : ℝ) / (s.T : ℝ) ^ 2)) 0 := by
      by_cases h : 1 ≤ n.val
      · simp only [if_pos h]
        have := (hdc n (by omega)).mul (Fd (n - 1))
        rwa [Fv, h0c n (by omega)] at this
      · obtain ⟨e1, e2⟩ := hγ0 (by omega)
        simp only [if_neg h, e1, e2, zero_div, zero_mul, add_zero]
        exact hasDerivAt_const (0 : ℝ) (0 : ℝ)
    have dT4 : HasDerivAt (fun ε => (v ε).b m * F ε n)
        ((eG D.dbe m : ℝ) / Q * ((eG s.V n : ℝ) / s.T) + (eG D.be m : ℝ) / Q * ((eG s.W n : ℝ) / (s.T : ℝ) ^ 2)) 0 := by
      have := (hdb m (by omega)).mul (Fd n); rwa [Fv, h0b m (by omega)] at this
    have dT5 : HasDerivAt (fun ε => (v ε).c m * (matrixPair (v ε) m).1 n ⟨k, hk⟩)
        ((eG D.dga m : ℝ) / Q * ((eG s.Vp n : ℝ) / s.Tp) +
          (eG D.ga m : ℝ) / Q * ((eG s.Wp n : ℝ) / (s.Tp : ℝ) ^ 2)) 0 := by
      have := (hdc m (by omega)).mul hprevd; rwa [hprev0, h0c m (by omega)] at this
    have hX : HasDerivAt X _ 0 := (((dT1.add dT2).add dT3).sub dT4).sub dT5
    have pA : (if n.val + 1 ≤ N then (v 0).a n * F 0 (n + 1) else 0) =
        (eG D.al n : ℝ) / Q * ((eG s.V (n + 1) : ℝ) / s.T) := by
      split_ifs with h
      · rw [h0a n (by omega), Fv]
      · rw [oV h]; ring
    have pC : (if 1 ≤ n.val then (v 0).c n * F 0 (n - 1) else 0) =
        (eG D.ga n : ℝ) / Q * ((eG s.V (n - 1) : ℝ) / s.T) := by
      split_ifs with h
      · rw [h0c n (by omega), Fv]
      · rw [(hγ0 (by omega)).1]; ring
    have hXv : X 0 = (eG D.al n : ℝ) / Q * ((eG s.V (n + 1) : ℝ) / s.T) +
        (eG D.be n : ℝ) / Q * ((eG s.V n : ℝ) / s.T) + (eG D.ga n : ℝ) / Q * ((eG s.V (n - 1) : ℝ) / s.T) -
        (eG D.be m : ℝ) / Q * ((eG s.V n : ℝ) / s.T) - (eG D.ga m : ℝ) / Q * ((eG s.Vp n : ℝ) / s.Tp) := by
      show (if n.val + 1 ≤ N then (v 0).a n * F 0 (n + 1) else 0) + (v 0).b n * F 0 n +
        (if 1 ≤ n.val then (v 0).c n * F 0 (n - 1) else 0) - (v 0).b m * F 0 n -
        (v 0).c m * (matrixPair (v 0) m).1 n ⟨k, hk⟩ = _
      rw [pA, pC, Fv, hprev0, h0b n (by omega), h0b m (by omega), h0c m (by omega)]
    have ham0 : (v 0).a m = (eG D.al m : ℝ) / Q := h0a m (by omega)
    have hInv : HasDerivAt (fun ε => ((v ε).a m)⁻¹)
        (-((eG D.dal m : ℝ) / Q) / ((eG D.al m : ℝ) / Q) ^ 2) 0 := by
      have := (hda m (by omega)).inv (by rw [ham0]; positivity)
      rwa [ham0] at this
    have hf := hInv.mul hX
    -- the new state
    have eT : ((jcol D N k (m + 1)).T : ℝ) = (s.T : ℝ) * eG D.al m := by
      show (((s.T * eG D.al m : ℤ)) : ℝ) = _; push_cast; rfl
    have eV : (eG (jcol D N k (m + 1)).V n : ℝ) = (vnew D N m s n : ℝ) := by
      show (eG ((List.range (N + 1)).map (vnew D N m s)) n : ℝ) = _
      rw [eG_map_range, if_pos (by omega)]
    have eW : (eG (jcol D N k (m + 1)).W n : ℝ) =
        ((eG D.al m * rder D N m s n - eG D.dal m * s.T * vnew D N m s n : ℤ) : ℝ) := by
      show (eG ((List.range (N + 1)).map fun n => eG D.al m * rder D N m s n - eG D.dal m * s.T *
        vnew D N m s n) n : ℝ) = _
      rw [eG_map_range, if_pos (by omega)]
    -- the previous-row relation
    have hrelT : (m = 0 ∧ (eG D.ga m : ℝ) = 0 ∧ (eG D.dga m : ℝ) = 0) ∨
        (1 ≤ m ∧ (s.T : ℝ) = s.Tp * eG D.al (m - 1)) := by
      rcases Nat.eq_zero_or_pos m with hm0 | hm0
      · left; refine ⟨hm0, ?_, ?_⟩ <;> rw [hm0] <;> simp [hg0, hdg0]
      · right; exact ⟨hm0, by exact_mod_cast hTrel hm0⟩
    have hQ' : Q ≠ 0 := hQ.ne'
    have hTne : (s.T : ℝ) ≠ 0 := hT'.ne'
    have hTpne : (s.Tp : ℝ) ≠ 0 := hTp'.ne'
    have hαne : (eG D.al m : ℝ) ≠ 0 := hαm.ne'
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hrec, hXv, ham0, eV, eT]
      simp only [vnew]; push_cast
      rcases hrelT with ⟨-, e1, -⟩ | ⟨hm1, e1⟩
      · rw [e1]; field_simp; ring
      · have hα1 : (eG D.al (m - 1) : ℝ) ≠ 0 := by
          have : (0 : ℝ) < eG D.al (m - 1) := by exact_mod_cast hal (m - 1) (by omega)
          exact this.ne'
        rw [e1]; field_simp; ring
    · rw [eW, eT]
      refine (hf.congr_of_eventuallyEq (Filter.Eventually.of_forall fun ε => hrec ε)).congr_deriv ?_
      rw [hXv, ham0]
      simp only [vnew, rder]; push_cast
      rcases hrelT with ⟨-, e1, e2⟩ | ⟨hm1, e1⟩
      · rw [e1, e2]; field_simp; ring
      · have hα1 : (eG D.al (m - 1) : ℝ) ≠ 0 := by
          have : (0 : ℝ) < eG D.al (m - 1) := by exact_mod_cast hal (m - 1) (by omega)
          exact this.ne'
        rw [e1]; field_simp; ring
    · show productMatrix (v 0) m n ⟨k, hk⟩ = _
      exact (ihm n).1
    · show HasDerivAt (fun ε => productMatrix (v ε) m n ⟨k, hk⟩) _ 0
      exact (ihm n).2.1

end JetCol
end Szkraw
