import Szkraw.AlgebraProducts
import Szkraw.TowerTrace
import Szkraw.ThreeTerm
import Szkraw.TowerCharacter
import Szkraw.SzwarcMargin
import Mathlib.RingTheory.Adjoin.Basic
import Mathlib.Algebra.Algebra.Operations

/-!
# P3: the remaining sentences of Proposition 3.4 and Corollary 7.7

* Proposition 3.4: the elements `E_0, …, E_N` are linearly independent, their span `B` is the subalgebra generated
  by `E_1`, and every product `E_m E_n` has nonnegative coefficients in this basis (`positive_subalgebra_full`).
* Corollary 7.7, last sentence: Theorem 7.6 admits a relatively open set of symmetric stochastic arrays, with
  `2N - 1` free coefficients `c_1, …, c_{2N-1}`, around each array (eq:qarray) with `0 < p₀ < 1/2`
  (`symmetric_open`).
-/

namespace Szkraw

open Finset
open scoped Pointwise

section subalgebra

variable (p q : ℝ) (N : ℕ)

theorem towerTrace_sum {ι : Type*} (s : Finset ι) (f : ι → (tower p q N).Carrier) :
    towerTrace p q N (∑ i ∈ s, f i) = ∑ i ∈ s, towerTrace p q N (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [tower_trace_zero]
  | insert x s hx ih => rw [Finset.sum_insert hx, Finset.sum_insert hx, tower_trace_add, ih]

variable {p q N}

theorem elementary_ne_zero (hp : 1 ≤ p) (hq : 1 ≤ q) (hN : 1 ≤ N) (k : ℕ) (hk : k ≤ N) :
    elementary p q N k ≠ 0 := by
  intro h
  have h1 := tower_character_elementary p q hp hq N hN k hk
  rw [h, map_zero] at h1
  exact (normalizer_pos p q hp hq N k hk).ne' h1.symm

theorem elementary_linearIndependent (hp : 1 ≤ p) (hq : 1 ≤ q) (hN : 1 ≤ N) :
    LinearIndependent ℝ (fun k : Fin (N + 1) => elementary p q N k) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg m
  have h := congrArg (fun x => towerTrace p q N (elementary p q N m * x)) hg
  simp only [Finset.mul_sum, mul_smul_comm, towerTrace_sum, tower_trace_smul, mul_zero, tower_trace_zero] at h
  rw [Finset.sum_eq_single m (fun k _ hkm => by
    rw [tower_trace_elementary_orthogonal p q N m k (fun h => hkm (Fin.ext h).symm), mul_zero])
    (by simp)] at h
  have hpos := tower_trace_square_pos p q hp hq N _ (elementary_ne_zero hp hq hN m (by omega))
  exact (mul_eq_zero.1 h).resolve_right hpos.ne'

theorem elementary_mem_adjoin (hq : 1 ≤ q) :
    ∀ k, elementary p q N k ∈ Algebra.adjoin ℝ {elementary p q N 1} ∧
      elementary p q N (k + 1) ∈ Algebra.adjoin ℝ {elementary p q N 1}
  | 0 => ⟨by rw [elementary_zero]; exact Subalgebra.one_mem _, Algebra.subset_adjoin rfl⟩
  | k + 1 => by
    obtain ⟨h0, h1⟩ := elementary_mem_adjoin hq k
    refine ⟨h1, ?_⟩
    have h3 := elementary_three_term p q N k
    have hQ : qInteger q (k + 2) ≠ 0 := (qInteger_pos q hq (k + 2) (by omega)).ne'
    have e : elementary p q N (k + 2) = (qInteger q (k + 2))⁻¹ •
        ((tower p q N).sum * elementary p q N (k + 1) - ((p - 1) * qInteger q (k + 1)) • elementary p q N (k + 1) -
          (p * q ^ k * qInteger q (N - k)) • elementary p q N k) := by
      rw [h3]
      rw [show qInteger q (k + 2) • elementary p q N (k + 2) + ((p - 1) * qInteger q (k + 1)) • elementary p q N (k + 1) +
          (p * q ^ k * qInteger q (N - k)) • elementary p q N k -
          ((p - 1) * qInteger q (k + 1)) • elementary p q N (k + 1) -
          (p * q ^ k * qInteger q (N - k)) • elementary p q N k = qInteger q (k + 2) • elementary p q N (k + 2) by abel,
        smul_smul, inv_mul_cancel₀ hQ, one_smul]
    rw [e]
    refine Subalgebra.smul_mem _ (Subalgebra.sub_mem _ (Subalgebra.sub_mem _ (Subalgebra.mul_mem _ ?_ h1)
      (Subalgebra.smul_mem _ h1 _)) (Subalgebra.smul_mem _ h0 _)) _
    rw [← elementary_one]
    exact Algebra.subset_adjoin rfl

/-- **Proposition 3.4** in full: `E_0, …, E_N` are linearly independent, their span is the subalgebra generated
by `E_1`, and every product `E_m E_n` has nonnegative coefficients in this basis. -/
theorem positive_subalgebra_full (hp : 1 ≤ p) (hq : 1 ≤ q) (hN : 1 ≤ N) :
    LinearIndependent ℝ (fun k : Fin (N + 1) => elementary p q N k) ∧
    Subalgebra.toSubmodule (Algebra.adjoin ℝ {elementary p q N 1}) =
      Submodule.span ℝ (Set.range fun k : Fin (N + 1) => elementary p q N k) ∧
    ∀ m n, m ≤ N → n ≤ N → ∃ g : Fin (N + 1) → ℝ, (∀ k, 0 ≤ g k) ∧
      elementary p q N m * elementary p q N n = ∑ k, g k • elementary p q N k.val := by
  set S := Set.range fun k : Fin (N + 1) => elementary p q N k
  have hprod : ∀ m n, m ≤ N → n ≤ N → elementary p q N m * elementary p q N n ∈ Submodule.span ℝ S := by
    intro m n hm hn
    obtain ⟨g, -, hg⟩ := elementary_products p q hp hq N hN m n hm hn
    rw [hg]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  have hSS : S * S ⊆ (Submodule.span ℝ S : Set (tower p q N).Carrier) := by
    rintro _ ⟨_, ⟨m, rfl⟩, _, ⟨n, rfl⟩, rfl⟩
    exact hprod m n (by omega) (by omega)
  have hmul : ∀ x y, x ∈ Submodule.span ℝ S → y ∈ Submodule.span ℝ S → x * y ∈ Submodule.span ℝ S := by
    intro x y hx hy
    have := Submodule.mul_mem_mul hx hy
    rw [Submodule.span_mul_span] at this
    exact (Submodule.span_le.2 hSS) this
  refine ⟨elementary_linearIndependent hp hq hN, le_antisymm ?_ ?_, fun m n hm hn =>
    elementary_products p q hp hq N hN m n hm hn⟩
  · intro x hx
    induction hx using Algebra.adjoin_induction with
    | mem x hx =>
      rw [Set.mem_singleton_iff.1 hx]
      exact Submodule.subset_span ⟨⟨1, by omega⟩, rfl⟩
    | algebraMap r =>
      rw [Algebra.algebraMap_eq_smul_one, ← elementary_zero p q N]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩)
    | add x y _ _ hx hy => exact Submodule.add_mem _ hx hy
    | mul x y _ _ hx hy => exact hmul x y hx hy
  · rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    exact (elementary_mem_adjoin hq k).1

end subalgebra

/-! ### Corollary 7.7: an open set of symmetric arrays -/

/-- The symmetric stochastic array of size `2N` with free coefficients `c_k = u_{k-1}`, `1 ≤ k ≤ 2N - 1`:
`b = 0`, `a = 1 - c`, `c_0 = 0`, `c_{2N} = 1`. -/
noncomputable def symC (N : ℕ) (u : Fin (2 * N - 1) → ℝ) (k : ℕ) : ℝ :=
  if hk : k = 0 then 0 else if h : k < 2 * N then u ⟨k - 1, by omega⟩ else 1

noncomputable def symArray (N : ℕ) (u : Fin (2 * N - 1) → ℝ) : Coefficients (2 * N) where
  a k := 1 - symC N u k
  b _ := 0
  c k := symC N u k

/-- **Corollary 7.7, last sentence**: for `N ≥ 1` and `0 < p₀ < 1/2`, the array (eq:qarray) is the symmetric
array with free coefficients `u⁰`, and an open set `U ∋ u⁰` of free coefficients in `ℝ^(2N-1)` gives arrays that
satisfy the hypothesis of Theorem 7.6, are admissible and have property (P). -/
theorem symmetric_open (N : ℕ) (hN : 1 ≤ N) (p : ℝ) (hp : 0 < p) (hp2 : p < 1 / 2) :
    let u0 : Fin (2 * N - 1) → ℝ := fun i => (szwarcCoefficients N p).c (i.val + 1)
    (∀ k, k ≤ 2 * N → (symArray N u0).a k = (szwarcCoefficients N p).a k ∧
      (symArray N u0).b k = (szwarcCoefficients N p).b k ∧ (symArray N u0).c k = (szwarcCoefficients N p).c k) ∧
    ∃ U : Set (Fin (2 * N - 1) → ℝ), IsOpen U ∧ u0 ∈ U ∧ ∀ u ∈ U,
      (∀ k, 1 ≤ k → k + 1 ≤ 2 * N → |(symArray N u).c k - (szwarcCoefficients N p).c k| ≤ symEta N p) ∧
      Admissible (symArray N u) ∧ MatrixPositivity (symArray N u) := by
  intro u0
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hc0 : (szwarcCoefficients N p).c 0 = 0 := by simp [szwarcCoefficients]
  have hcN : (szwarcCoefficients N p).c (2 * N) = 1 := by
    simp [szwarcCoefficients, Nat.mul_mod_right, Nat.mul_div_cancel_left _ (show 0 < 2 by norm_num),
      div_self hN'.ne', show N ≠ 0 by omega]
  have hac : ∀ k, (szwarcCoefficients N p).a k = 1 - (szwarcCoefficients N p).c k := fun k => by
    simp only [szwarcCoefficients]
    split_ifs <;> field_simp
  have hsc : ∀ (u : Fin (2 * N - 1) → ℝ) (k : ℕ) (h1 : 1 ≤ k) (h2 : k + 1 ≤ 2 * N),
      (symArray N u).c k = u ⟨k - 1, by omega⟩ := fun u k h1 h2 => by
    simp only [symArray, symC, dif_neg (show k ≠ 0 by omega), dif_pos (show k < 2 * N by omega)]
  have hmatch : ∀ k, k ≤ 2 * N → (symArray N u0).c k = (szwarcCoefficients N p).c k := fun k hk => by
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · simp [symArray, symC, hc0]
    · rcases Nat.lt_or_ge k (2 * N) with hlt | hge
      · rw [hsc u0 k hk0 hlt]; simp only [u0]; congr 1; omega
      · have : k = 2 * N := by omega
        subst this
        simp [symArray, symC, hcN, show N ≠ 0 by omega]
  have hη : 0 < symEta N p := by
    unfold symEta
    have h1 : 0 < p / (1 - p) := div_pos hp (by linarith)
    have h2 : 0 < 1 - p / (1 - p) := by
      have : p / (1 - p) < 1 := by rw [div_lt_one (by linarith)]; linarith
      linarith
    have h3 : 0 < min (p / (1 - p)) (1 - p / (1 - p)) := lt_min h1 h2
    positivity
  refine ⟨fun k hk => ⟨by show 1 - (symArray N u0).c k = _; rw [hac, hmatch k hk], rfl, hmatch k hk⟩,
    Metric.ball u0 (symEta N p), Metric.isOpen_ball, Metric.mem_ball_self hη, fun u hu => ?_⟩
  have hclose : ∀ k, 1 ≤ k → k + 1 ≤ 2 * N →
      |(symArray N u).c k - (szwarcCoefficients N p).c k| ≤ symEta N p := by
    intro k h1 h2
    rw [hsc u k h1 h2, ← hmatch k (by omega), hsc u0 k h1 h2]
    have := (dist_le_pi_dist u u0 ⟨k - 1, by omega⟩).trans (Metric.mem_ball.1 hu).le
    rwa [Real.dist_eq] at this
  have h := symmetric_criterion N hN p hp hp2 (symArray N u) (fun k _ => rfl) (fun k _ => rfl)
    (by simp [symArray, symC]) (by simp [symArray, symC, show 2 * N ≠ 0 by omega]) hclose
  exact ⟨hclose, h.1, h.2.2.1⟩

end Szkraw
