import Szkraw.ParitySplit
import Mathlib.LinearAlgebra.Dimension.OrzechProperty
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.Tactic.Module

/-!
# Lemmas 7.2 and 7.3: edge idempotents and the three-term action

`A` is a commutative `ℝ`-algebra with elements `y_1, …, y_N` satisfying `y_j^2 = (1-r) y_j + r`
whose squarefree monomials `y_S` form a basis. Every such algebra is the algebra of Section 7, and
`cube_model` shows that one exists for `r ≠ -1`: the real functions on `{1, -r}^N`. Lemma 7.2 is
stated for every such pair `(A, y)` with a basis `B` of `A` satisfying `B S = y_S`. Lemma 7.3 uses
only the relations.
-/

namespace Szkraw

open Finset

section algebra

variable {N : ℕ} {A : Type*} [CommRing A] [Algebra ℝ A] (r : ℝ) (y : Fin N → A)

/-- The squarefree monomial `y_S = Π_{j ∈ S} y_j`. -/
def ySet (S : Finset (Fin N)) : A := ∏ j ∈ S, y j

/-- The relations `y_j^2 = (1 - r) y_j + r`. -/
def QuadRel : Prop := ∀ j, y j * y j = (1 - r) • y j + algebraMap ℝ A r

/-- The edge idempotent `f_l = (r + y_l)/(1 + r)`. -/
noncomputable def edgeIdem (l : Fin N) : A := (1 + r)⁻¹ • (algebraMap ℝ A r + y l)

/-- The family `f_l y_S`, `S ⊆ {1, …, N} ∖ {l}`. -/
noncomputable def edgeFamily (l : Fin N) (S : {S : Finset (Fin N) // l ∉ S}) : A :=
  edgeIdem r y l * ySet y S.1

/-- Nonnegative coefficients in a basis indexed by subsets. -/
def BasisNonneg (B : Module.Basis (Finset (Fin N)) ℝ A) (u : A) : Prop := ∀ S, 0 ≤ B.repr u S

variable {r y}

theorem edge_mul_y (hy : QuadRel r y) (l : Fin N) :
    y l * edgeIdem r y l = edgeIdem r y l := by
  have h := hy l
  simp only [edgeIdem, Algebra.smul_def, map_sub, map_one] at h ⊢
  linear_combination (algebraMap ℝ A (1 + r)⁻¹) * h

theorem edge_idem (hr : 1 + r ≠ 0) (hy : QuadRel r y) (l : Fin N) :
    edgeIdem r y l * edgeIdem r y l = edgeIdem r y l := by
  have h := edge_mul_y hy l
  have hc : algebraMap ℝ A (1 + r)⁻¹ * (algebraMap ℝ A r + 1) = 1 := by
    rw [← map_one (algebraMap ℝ A), ← map_add, ← map_mul, add_comm r 1, inv_mul_cancel₀ hr]
  have he : algebraMap ℝ A (1 + r)⁻¹ * (algebraMap ℝ A r + y l) = edgeIdem r y l :=
    (Algebra.smul_def _ _).symm
  calc edgeIdem r y l * edgeIdem r y l
      = algebraMap ℝ A (1 + r)⁻¹ * (algebraMap ℝ A r * edgeIdem r y l + y l * edgeIdem r y l) := by
        rw [← add_mul, ← mul_assoc, he]
    _ = edgeIdem r y l := by rw [h]; linear_combination (edgeIdem r y l) * hc

/-- `f_l y_S = f_l y_{S ∖ {l}}`. -/
theorem edge_mul_ySet_erase (hy : QuadRel r y) (l : Fin N) (S : Finset (Fin N)) :
    edgeIdem r y l * ySet y S = edgeIdem r y l * ySet y (S.erase l) := by
  by_cases hl : l ∈ S
  · rw [ySet, ← mul_prod_erase S y hl, ← mul_assoc, mul_comm _ (y l), edge_mul_y hy l]; rfl
  · rw [erase_eq_of_notMem hl]

/-- `(1 + r) f_l y_S = r y_S + y_{S ∪ {l}}` for `l ∉ S`. -/
theorem edge_mul_ySet (l : Fin N) (S : Finset (Fin N)) (hl : l ∉ S) :
    edgeIdem r y l * ySet y S = (1 + r)⁻¹ • (r • ySet y S + ySet y (insert l S)) := by
  rw [edgeIdem, ySet, ySet, prod_insert hl, smul_mul_assoc, add_mul, Algebra.smul_def r]

/-- Splitting a sum over subsets by membership of `l`. -/
theorem sum_split_insert {M : Type*} [AddCommMonoid M] (l : Fin N) (h : Finset (Fin N) → M) :
    ∑ S, h S = ∑ T : {S : Finset (Fin N) // l ∉ S}, (h T.1 + h (insert l T.1)) := by
  rw [sum_add_distrib, ← sum_filter_add_sum_filter_not univ (fun S => l ∉ S)]
  congr 1
  · exact sum_subtype _ (by simp) h
  · rw [← sum_subtype (univ.filter (fun S => l ∉ S)) (by simp) (fun T => h (insert l T))]
    apply sum_nbij' (fun S => S.erase l) (fun T => insert l T)
    · intro S hS; simp
    · intro T hT; simp
    · intro S hS; simp only [mem_filter, mem_univ, true_and, not_not] at hS; exact insert_erase hS
    · intro T hT; simp only [mem_filter, mem_univ, true_and] at hT; exact erase_insert hT
    · intro S hS; simp only [mem_filter, mem_univ, true_and, not_not] at hS; rw [insert_erase hS]

end algebra

section basis

/-! ### Lemma 7.2 -/

variable {N : ℕ} {A : Type*} [CommRing A] [Algebra ℝ A] {r : ℝ} {y : Fin N → A}
  (B : Module.Basis (Finset (Fin N)) ℝ A) (hB : ∀ S, B S = ySet y S)
include hB

theorem repr_edge (l : Fin N) (T T₀ : {S : Finset (Fin N) // l ∉ S}) :
    B.repr (edgeFamily r y l T) (insert l T₀.1) = (1 + r)⁻¹ * if T = T₀ then 1 else 0 := by
  rw [edgeFamily, edge_mul_ySet l T.1 T.2, map_smul, map_add, map_smul, ← hB, ← hB, B.repr_self,
    B.repr_self]
  simp only [Finsupp.smul_apply, Finsupp.add_apply, smul_eq_mul]
  rw [Finsupp.single_apply, Finsupp.single_apply,
    if_neg (fun h => T.2 (by rw [h]; exact mem_insert_self _ _)), mul_zero, zero_add]
  exact congrArg _ (if_congr ⟨fun h => Subtype.ext (by rw [← erase_insert T.2, h, erase_insert T₀.2]),
    fun h => by rw [h]⟩ rfl rfl)

/-- **Lemma 7.2**, basis part: the `f_l y_S` with `l ∉ S` are linearly independent. -/
theorem edge_linearIndependent (hr : 1 + r ≠ 0) (l : Fin N) :
    LinearIndependent ℝ (edgeFamily r y l) := by
  let φ : A →ₗ[ℝ] ({S : Finset (Fin N) // l ∉ S} → ℝ) :=
    LinearMap.pi (fun T => (1 + r) • ((Finsupp.lapply (insert l T.1)) ∘ₗ B.repr.toLinearMap))
  apply LinearIndependent.of_comp φ
  have : φ ∘ edgeFamily r y l = Pi.basisFun ℝ _ := by
    funext T₀ T
    simp only [Function.comp_apply, φ, LinearMap.pi_apply, LinearMap.smul_apply, LinearMap.coe_comp,
      LinearEquiv.coe_coe, Finsupp.lapply_apply, smul_eq_mul, Pi.basisFun_apply]
    rw [repr_edge B hB l T₀ T, ← mul_assoc, mul_inv_cancel₀ hr, one_mul, Pi.single_apply]
    exact if_congr eq_comm rfl rfl
  rw [this]; exact (Pi.basisFun ℝ _).linearIndependent

/-- `f_l u = Σ_S u_S f_l y_{S ∖ {l}}`. -/
theorem edge_mul_expand (hy : QuadRel r y) (l : Fin N) (u : A) :
    edgeIdem r y l * u = ∑ T : {S : Finset (Fin N) // l ∉ S},
      (B.repr u T.1 + B.repr u (insert l T.1)) • edgeFamily r y l T := by
  conv_lhs => rw [← B.sum_repr u]
  rw [mul_sum, sum_split_insert l]
  apply sum_congr rfl; intro T _
  rw [mul_smul_comm, mul_smul_comm, hB, hB, edge_mul_ySet_erase hy l (insert l T.1), erase_insert T.2,
    add_smul]
  rfl

/-- **Lemma 7.2**, basis part: the `f_l y_S` with `l ∉ S` span the ideal `f_l A`. -/
theorem edge_span (hy : QuadRel r y) (l : Fin N) :
    Submodule.span ℝ (Set.range (edgeFamily r y l)) =
      (Ideal.span {edgeIdem r y l}).restrictScalars ℝ := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨_, rfl⟩
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)
  · intro x hx
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp hx
    rw [mul_comm, edge_mul_expand B hB hy l b]
    exact Submodule.sum_mem _ (fun T _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨T, rfl⟩))

/-- **Lemma 7.2**, positivity: `f_l u` has nonnegative coefficients in the basis `f_l y_S` whenever
`u` is nonnegative. -/
theorem edge_nonneg (hy : QuadRel r y) (l : Fin N) (u : A) (hu : BasisNonneg B u) :
    ∃ c : {S : Finset (Fin N) // l ∉ S} → ℝ, (∀ T, 0 ≤ c T) ∧
      edgeIdem r y l * u = ∑ T, c T • edgeFamily r y l T :=
  ⟨fun T => B.repr u T.1 + B.repr u (insert l T.1), fun _ => add_nonneg (hu _) (hu _),
    edge_mul_expand B hB hy l u⟩

/-- **Lemma 7.2** (Edge idempotents): `y_l f_l = f_l`, `f_l^2 = f_l`, the `f_l y_S` with `l ∉ S` form a
basis of the ideal `f_l A`, and `f_l u` has nonnegative coefficients in it whenever `u` is
nonnegative. -/
theorem edge_idempotents (hr : 1 + r ≠ 0) (hy : QuadRel r y) (l : Fin N) :
    y l * edgeIdem r y l = edgeIdem r y l ∧ edgeIdem r y l * edgeIdem r y l = edgeIdem r y l ∧
      LinearIndependent ℝ (edgeFamily r y l) ∧
      Submodule.span ℝ (Set.range (edgeFamily r y l)) = (Ideal.span {edgeIdem r y l}).restrictScalars ℝ ∧
      ∀ u, BasisNonneg B u → ∃ c : {S : Finset (Fin N) // l ∉ S} → ℝ, (∀ T, 0 ≤ c T) ∧
        edgeIdem r y l * u = ∑ T, c T • edgeFamily r y l T :=
  ⟨edge_mul_y hy l, edge_idem hr hy l, edge_linearIndependent B hB hr l, edge_span B hB hy l,
    fun u hu => edge_nonneg B hB hy l u hu⟩

end basis

section cube

/-! ### A model: real functions on `{1, -r}^N` -/

variable (N : ℕ) (r : ℝ)

/-- `y_j` on `{1, -r}^N`, where `true` stands for `-r`. -/
def cubeY (j : Fin N) : (Fin N → Bool) → ℝ := fun ε => if ε j then -r else 1

theorem cube_rel : QuadRel r (cubeY N r) := by
  intro j; funext ε
  simp only [cubeY, Pi.mul_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Algebra.algebraMap_eq_smul_one,
    Pi.one_apply, mul_one]
  split_ifs <;> ring

/-- The indicator of `ε` is a polynomial in the `y_j`. -/
theorem cube_indicator (hr : 1 + r ≠ 0) (ε : Fin N → Bool) :
    (fun ε' => if ε = ε' then (1 : ℝ) else 0) ∈ Submodule.span ℝ (Set.range (ySet (cubeY N r))) := by
  set α : Fin N → ℝ := fun j => if ε j then (1 + r)⁻¹ else r * (1 + r)⁻¹
  set β : Fin N → ℝ := fun j => if ε j then -(1 + r)⁻¹ else (1 + r)⁻¹
  have hind : (fun ε' => if ε = ε' then (1 : ℝ) else 0) =
      ∏ j, (algebraMap ℝ _ (β j) * cubeY N r j + algebraMap ℝ _ (α j)) := by
    funext ε'
    rw [Finset.prod_apply]
    have hj : ∀ j, (algebraMap ℝ ((Fin N → Bool) → ℝ) (β j) * cubeY N r j +
        algebraMap ℝ ((Fin N → Bool) → ℝ) (α j)) ε' = if ε j = ε' j then 1 else 0 := by
      intro j
      simp only [Pi.add_apply, Pi.mul_apply, Algebra.algebraMap_eq_smul_one, Pi.smul_apply, smul_eq_mul,
        Pi.one_apply, mul_one, cubeY, α, β]
      cases ε j <;> cases ε' j <;> simp <;> field_simp <;> ring
    simp only [hj, prod_boole, mem_univ, true_implies]
    exact if_congr funext_iff rfl rfl
  rw [hind, prod_add]
  refine Submodule.sum_mem _ (fun t _ => ?_)
  rw [prod_mul_distrib, ← map_prod, ← map_prod, mul_comm, ← mul_assoc, ← map_mul, ← Algebra.smul_def]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨t, rfl⟩)

/-- The real functions on `{1, -r}^N` with the `y_j` satisfy the relations, and the squarefree
monomials `y_S` form a basis (`r ≠ -1`). -/
theorem cube_model (hr : 1 + r ≠ 0) :
    QuadRel r (cubeY N r) ∧
      ∃ B : Module.Basis (Finset (Fin N)) ℝ ((Fin N → Bool) → ℝ), ∀ S, B S = ySet (cubeY N r) S := by
  refine ⟨cube_rel N r, ?_⟩
  have hspan : ⊤ ≤ Submodule.span ℝ (Set.range (ySet (cubeY N r))) := by
    intro f _
    rw [pi_eq_sum_univ f]
    exact Submodule.sum_mem _ (fun ε _ => Submodule.smul_mem _ _ (cube_indicator N r hr ε))
  have hcard : Fintype.card (Finset (Fin N)) = Module.finrank ℝ ((Fin N → Bool) → ℝ) := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_finset, Fintype.card_fun, Fintype.card_bool,
      Fintype.card_fin]
  exact ⟨basisOfTopLeSpanOfCardEqFinrank _ hspan hcard, fun S => by simp⟩

end cube

section action

/-! ### Lemma 7.3 -/

variable {N : ℕ} {A : Type*} [CommRing A] [Algebra ℝ A] (r : ℝ) (y : Fin N → A)

/-- `Σ_{|S| = m} y_S`. -/
noncomputable def levelSum (m : ℕ) : A := ∑ S ∈ univ.filter (fun S : Finset (Fin N) => S.card = m), ySet y S

/-- `Σ_{l ∉ S, |S| = m} f_l y_S`. -/
noncomputable def edgeSum (l : Fin N) (m : ℕ) : A :=
  ∑ S ∈ univ.filter (fun S : Finset (Fin N) => l ∉ S ∧ S.card = m), edgeIdem r y l * ySet y S

/-- The operator `Y(u; v_1, …, v_N) = (N⁻¹ Σ_l v_l; f_1 u, …, f_N u)` on `V`, a subspace of
`A × A^N`. -/
noncomputable def Yop (w : A × (Fin N → A)) : A × (Fin N → A) :=
  ((N : ℝ)⁻¹ • ∑ l, w.2 l, fun l => edgeIdem r y l * w.1)

/-- `U_{2n} = (C(N,n)⁻¹ Σ_{|S|=n} y_S; 0)` and `U_{2n+1} = (0; (C(N-1,n)⁻¹ Σ_{l∉S,|S|=n} f_l y_S)_l)`. -/
noncomputable def Uvec (k : ℕ) : A × (Fin N → A) :=
  if k % 2 = 0 then ((N.choose (k / 2) : ℝ)⁻¹ • levelSum y (k / 2), 0)
  else (0, fun l => ((N - 1).choose (k / 2) : ℝ)⁻¹ • edgeSum r y l (k / 2))

theorem Uvec_even (n : ℕ) : Uvec r y (2 * n) = ((N.choose n : ℝ)⁻¹ • levelSum y n, 0) := by
  rw [Uvec, if_pos (by omega), show 2 * n / 2 = n by omega]

theorem Uvec_odd (n : ℕ) :
    Uvec r y (2 * n + 1) = (0, fun l => ((N - 1).choose n : ℝ)⁻¹ • edgeSum r y l n) := by
  rw [Uvec, if_neg (by omega), show (2 * n + 1) / 2 = n by omega]

/-- `U_{2N+1} = 0`. -/
theorem Uvec_top : Uvec r y (2 * N + 1) = 0 := by
  rw [Uvec_odd]
  ext l
  · rfl
  · show _ • _ = 0
    rcases Nat.eq_zero_or_pos N with h | h
    · subst h; exact l.elim0
    · rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, inv_zero, zero_smul]

variable {r y}

theorem edgeSum_top (l : Fin N) (m : ℕ) (hm : N ≤ m) : edgeSum r y l m = 0 := by
  apply sum_eq_zero; intro S hS
  simp only [mem_filter, mem_univ, true_and] at hS
  have := card_lt_univ_of_notMem hS.1
  rw [Fintype.card_fin] at this; omega

/-- `Σ_{|S|=n} f_l y_S = Σ_{l∉S,|S|=n} f_l y_S + Σ_{l∉T,|T|+1=n} f_l y_T`. -/
theorem edge_levelSum (hy : QuadRel r y) (l : Fin N) (n : ℕ) :
    edgeIdem r y l * levelSum y n = edgeSum r y l n +
      ∑ T ∈ univ.filter (fun T : Finset (Fin N) => l ∉ T ∧ T.card + 1 = n), edgeIdem r y l * ySet y T := by
  rw [levelSum, mul_sum, ← sum_filter_add_sum_filter_not _ (fun S => l ∉ S), filter_filter, edgeSum]
  congr 1
  · apply sum_congr (by ext S; simp [and_comm]) (fun _ _ => rfl)
  · apply sum_nbij' (fun S => S.erase l) (fun T => insert l T)
    · intro S hS
      simp only [mem_filter, mem_univ, true_and, not_not] at hS ⊢
      exact ⟨notMem_erase l S, by rw [card_erase_of_mem hS.2, ← hS.1]; have := card_pos.mpr ⟨l, hS.2⟩; omega⟩
    · intro T hT
      simp only [mem_filter, mem_univ, true_and, not_not] at hT ⊢
      exact ⟨by rw [card_insert_of_notMem hT.1, hT.2], mem_insert_self l T⟩
    · intro S hS; simp only [mem_filter, mem_univ, true_and, not_not] at hS; exact insert_erase hS.2
    · intro T hT; simp only [mem_filter, mem_univ, true_and] at hT; exact erase_insert hT.1
    · intro S _; exact edge_mul_ySet_erase hy l S

/-- `Σ_l Σ_{l∉S,|S|=n} y_S = (N - n) Σ_{|S|=n} y_S`. -/
theorem count_out (n : ℕ) :
    ∑ l : Fin N, ∑ S ∈ univ.filter (fun S : Finset (Fin N) => l ∉ S ∧ S.card = n), ySet y S =
      ((N - n : ℕ) : ℝ) • levelSum y n := by
  simp_rw [sum_filter]
  rw [sum_comm, levelSum, sum_filter, smul_sum]
  apply sum_congr rfl; intro S _
  split_ifs with h
  · rw [sum_congr rfl (fun l _ => if_congr (and_iff_left h) rfl rfl), ← sum_filter, sum_const,
      ← Nat.cast_smul_eq_nsmul ℝ]
    have : univ.filter (fun l => l ∉ S) = Sᶜ := by ext; simp
    rw [this, card_compl, Fintype.card_fin, h]
  · rw [smul_zero]; exact sum_eq_zero (fun l _ => if_neg (fun h' => h h'.2))

/-- `Σ_l Σ_{l∉S,|S|=n} y_{S ∪ {l}} = (n + 1) Σ_{|T|=n+1} y_T`. -/
theorem count_in (n : ℕ) :
    ∑ l : Fin N, ∑ S ∈ univ.filter (fun S : Finset (Fin N) => l ∉ S ∧ S.card = n), ySet y (insert l S) =
      ((n + 1 : ℕ) : ℝ) • levelSum y (n + 1) := by
  have e : ∀ l : Fin N, ∑ S ∈ univ.filter (fun S : Finset (Fin N) => l ∉ S ∧ S.card = n), ySet y (insert l S) =
      ∑ T ∈ univ.filter (fun T : Finset (Fin N) => l ∈ T ∧ T.card = n + 1), ySet y T := by
    intro l
    apply sum_nbij' (fun S => insert l S) (fun T => T.erase l)
    · intro S hS
      simp only [mem_filter, mem_univ, true_and] at hS ⊢
      exact ⟨mem_insert_self l S, by rw [card_insert_of_notMem hS.1, hS.2]⟩
    · intro T hT
      simp only [mem_filter, mem_univ, true_and] at hT ⊢
      exact ⟨notMem_erase l T, by rw [card_erase_of_mem hT.1, hT.2]; rfl⟩
    · intro S hS; simp only [mem_filter, mem_univ, true_and] at hS; exact erase_insert hS.1
    · intro T hT; simp only [mem_filter, mem_univ, true_and] at hT; exact insert_erase hT.1
    · intro _ _; rfl
  simp_rw [e, sum_filter]
  rw [sum_comm, levelSum, sum_filter, smul_sum]
  apply sum_congr rfl; intro T _
  split_ifs with h
  · rw [sum_congr rfl (fun l _ => if_congr (and_iff_left h) rfl rfl), ← sum_filter, sum_const,
      ← Nat.cast_smul_eq_nsmul ℝ]
    have : univ.filter (fun l => l ∈ T) = T := by ext; simp
    rw [this, h]
  · rw [smul_zero]; exact sum_eq_zero (fun l _ => if_neg (fun h' => h h'.2))

theorem choose_rel1 (hN : 1 ≤ N) (n : ℕ) : ((N - 1).choose n : ℝ) * N = N.choose n * (N - n : ℕ) := by
  have := Nat.choose_mul_succ_eq (N - 1) n
  rw [show N - 1 + 1 = N by omega] at this
  exact_mod_cast this

theorem choose_rel2 (hN : 1 ≤ N) (n : ℕ) : (N : ℝ) * ((N - 1).choose n : ℝ) = N.choose (n + 1) * (n + 1 : ℕ) := by
  have := Nat.add_one_mul_choose_eq (N - 1) n
  rw [show N - 1 + 1 = N by omega] at this
  exact_mod_cast this

/-- **Lemma 7.3** (Three-term action): with the coefficients (7.2), `Y U_k = a_k U_{k+1} + c_k U_{k-1}`
for `0 ≤ k ≤ 2N`, where `U_{2N+1} = 0` (`Uvec_top`) and `c_0 = 0`. -/
theorem three_term_action (hN : 1 ≤ N) {p₀ : ℝ} (hp : p₀ < 1) (hr : r = p₀ / (1 - p₀))
    (hy : QuadRel r y) (k : ℕ) (hk : k ≤ 2 * N) :
    Yop r y (Uvec r y k) = (szwarcCoefficients N p₀).a k • Uvec r y (k + 1) +
      (szwarcCoefficients N p₀).c k • Uvec r y (k - 1) := by
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  have h1p : 1 - p₀ ≠ 0 := by linarith
  have hr1' : (1 + r) * (1 - p₀) = 1 := by rw [hr]; field_simp; ring
  have hr1 : 1 + r ≠ 0 := left_ne_zero_of_mul_eq_one hr1'
  obtain ⟨n, rfl | rfl⟩ := Nat.even_or_odd' k
  · -- even `k = 2n`
    have hn : n ≤ N := by omega
    have ha : (szwarcCoefficients N p₀).a (2 * n) = ((N : ℝ) - n) / N := by
      simp [szwarcCoefficients, show 2 * n / 2 = n by omega]
    have hc : (szwarcCoefficients N p₀).c (2 * n) = (n : ℝ) / N := by
      simp [szwarcCoefficients, show 2 * n / 2 = n by omega]
    rw [ha, hc, Uvec_even, Uvec_odd]
    refine Prod.ext ?_ ?_
    · simp only [Yop, Prod.fst_add, Prod.smul_fst, Pi.zero_apply, sum_const_zero, smul_zero, zero_add]
      rcases Nat.eq_zero_or_pos n with h0 | hpos
      · subst h0; simp
      · rw [show 2 * n - 1 = 2 * (n - 1) + 1 by omega, Uvec_odd, smul_zero]
    funext l
    simp only [Yop, Prod.snd_add, Prod.smul_snd, Pi.add_apply, Pi.smul_apply, smul_smul]
    rw [mul_smul_comm, edge_levelSum hy l n, smul_add]
    congr 1
    · rcases Nat.lt_or_ge n N with hlt | hge
      · congr 1
        have h1 := choose_rel1 hN n
        have h2 : ((N - 1).choose n : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos (by omega)).ne'
        have h3 : (N.choose n : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos (by omega)).ne'
        rw [Nat.cast_sub hlt.le] at h1
        field_simp
        linear_combination h1
      · rw [edgeSum_top l n hge, smul_zero, smul_zero]
    · rcases Nat.eq_zero_or_pos n with h0 | hpos
      · subst h0
        rw [sum_eq_zero (fun T hT => by simp at hT), smul_zero]; simp
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      rw [show 2 * (m + 1) - 1 = 2 * m + 1 by omega, Uvec_odd]
      have hG : ∑ T ∈ univ.filter (fun T : Finset (Fin N) => l ∉ T ∧ T.card + 1 = m + 1),
          edgeIdem r y l * ySet y T = edgeSum r y l m := by
        rw [edgeSum]; exact sum_congr (by ext T; simp) (fun _ _ => rfl)
      simp only [smul_smul]
      rw [hG]
      congr 1
      have h1 := choose_rel2 hN m
      have h2 : ((N - 1).choose m : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos (by omega)).ne'
      have h3 : (N.choose (m + 1) : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos (by omega)).ne'
      field_simp
      push_cast at h1 ⊢
      linear_combination h1
  · -- odd `k = 2n + 1`
    have hn : n < N := by omega
    have ha : (szwarcCoefficients N p₀).a (2 * n + 1) = 1 - p₀ := by
      simp [szwarcCoefficients, Nat.add_mod]
    have hc : (szwarcCoefficients N p₀).c (2 * n + 1) = p₀ := by
      simp [szwarcCoefficients, Nat.add_mod]
    rw [ha, hc, show 2 * n + 1 + 1 = 2 * (n + 1) by ring, Uvec_even, show 2 * n + 1 - 1 = 2 * n by omega,
      Uvec_even, Uvec_odd]
    refine Prod.ext ?_ ?_
    swap
    · funext l; simp [Yop]
    simp only [Yop, Prod.fst_add, Prod.smul_fst]
    have hsum : ∑ l : Fin N, edgeSum r y l n =
        (1 + r)⁻¹ • (r • ((N - n : ℕ) : ℝ) • levelSum y n + ((n + 1 : ℕ) : ℝ) • levelSum y (n + 1)) := by
      simp only [edgeSum]
      have e : ∀ l : Fin N, ∑ S ∈ univ.filter (fun S : Finset (Fin N) => l ∉ S ∧ S.card = n),
          edgeIdem r y l * ySet y S = (1 + r)⁻¹ • (r • ∑ S ∈ univ.filter (fun S : Finset (Fin N) =>
            l ∉ S ∧ S.card = n), ySet y S + ∑ S ∈ univ.filter (fun S : Finset (Fin N) => l ∉ S ∧ S.card = n),
              ySet y (insert l S)) := by
        intro l
        rw [smul_sum, ← sum_add_distrib, smul_sum]
        apply sum_congr rfl; intro S hS
        simp only [mem_filter, mem_univ, true_and] at hS
        rw [edge_mul_ySet l S hS.1]
      simp_rw [e]
      rw [← smul_sum, sum_add_distrib, ← smul_sum, count_out, count_in]
    rw [← smul_sum, hsum]
    have hc1 : ((N - 1).choose n : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos (by omega)).ne'
    have hc2 : (N.choose n : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos (by omega)).ne'
    have hc3 : (N.choose (n + 1) : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos (by omega)).ne'
    have e1 := choose_rel1 hN n
    have e2 := choose_rel2 hN n
    have hpr : (1 + r)⁻¹ = 1 - p₀ := by rw [← mul_eq_one_iff_inv_eq₀ hr1]; exact hr1'
    have hrp : r * (1 - p₀) = p₀ := by rw [hr]; field_simp
    have q1 : ((N - 1).choose n : ℝ)⁻¹ * (N : ℝ)⁻¹ * ((N - n : ℕ) : ℝ) = (N.choose n : ℝ)⁻¹ := by
      field_simp
      linear_combination -e1
    have q2 : ((N - 1).choose n : ℝ)⁻¹ * (N : ℝ)⁻¹ * ((n + 1 : ℕ) : ℝ) = (N.choose (n + 1) : ℝ)⁻¹ := by
      field_simp
      linear_combination -e2
    have k1 : (N : ℝ)⁻¹ * (((N - 1).choose n : ℝ)⁻¹ * ((1 + r)⁻¹ * (r * ((N - n : ℕ) : ℝ)))) =
        p₀ * (N.choose n : ℝ)⁻¹ := by
      calc _ = (1 + r)⁻¹ * r * (((N - 1).choose n : ℝ)⁻¹ * (N : ℝ)⁻¹ * ((N - n : ℕ) : ℝ)) := by ring
        _ = _ := by rw [q1, hpr, mul_comm (1 - p₀) r, hrp]
    have k2 : (N : ℝ)⁻¹ * (((N - 1).choose n : ℝ)⁻¹ * ((1 + r)⁻¹ * ((n + 1 : ℕ) : ℝ))) =
        (1 - p₀) * (N.choose (n + 1) : ℝ)⁻¹ := by
      calc _ = (1 + r)⁻¹ * (((N - 1).choose n : ℝ)⁻¹ * (N : ℝ)⁻¹ * ((n + 1 : ℕ) : ℝ)) := by ring
        _ = _ := by rw [q2, hpr]
    linear_combination (norm := module) k1 • levelSum y n + k2 • levelSum y (n + 1)

end action

end Szkraw
