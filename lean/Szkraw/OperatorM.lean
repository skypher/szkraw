import Szkraw.VRMoves
import Szkraw.VRKernel
import Szkraw.VRAssembly
import Szkraw.LCAssembly

/-!
# P2, Section 6: the operator `M` of the proof of Theorem 4.1 can have a negative entry for cubic ratios

The resummation in the proof of P2's Theorem 4.1 (Theorem 8.9 of `paper.tex`) regards the moves of the kernel
recurrence of Theorem 3.1 (`KernelRecV`) as operators on functions on `Ω`, each divided by `c` at the destination
level: `U` (straight moves), `P` and `Q` (the `B_j` with `j` even and odd), `C = C₊ - C₋` (the `C'_j` with `j` even
and odd) and `A = Σ_j (-1)^j A_j`. With `G = Σ_{m ≤ N} (P/2)^m` and `R = U + P²/4 - Q` it sets
`M = G (R + C + A) G`. Here these operators are built from the weights of `KernelRecV` (`kernelRecV_iff`), and
`opS_eq` shows `R + C + A = T - P + P²/4` for the operator `T = Tmat` of the recurrence.

* `opM_negative_entry`: for the cubic data `N = 6`, `d_i = i/6`, `ρ(x) = 1/5 + C(x,3)/200` (`r = 1/5`, `t = τ = 0`,
  `σ = 1/200`), `c_i = ρ(i) d_i`, `b_i = d_i - c_i`, the entry of `M` from `(ℓ, a) = (0, 6)` to `(2, 2)` is
  `-9/32`. All moves raise `ℓ`, so this entry is the entry of `P²/4 - Q`, and it is negative because the detour
  inequality `4 c_1 B_1(0,6) ≤ B_0(0,6) B_0(1,4)` fails.
* `cubic_data`: `c_i = ρ(i) d_i > 0` for `1 ≤ i ≤ 6` and `b` is nondecreasing on `0, …, 6`.
-/

set_option linter.unusedSectionVars false

namespace Szkraw

open Finset Matrix

namespace OpM

/-! ### Displacements of move operators -/

variable {N : ℕ}

/-- `X` has nonzero entries only at displacements in `D`: `X i k ≠ 0` gives `i = k + (d₁, -d₂)` with `D d₁ d₂`. -/
def Disp (D : ℕ → ℕ → Prop) (X : Matrix (Idx N) (Idx N) ℝ) : Prop :=
  ∀ i k, X i k ≠ 0 → ∃ d1 d2, D d1 d2 ∧ (k.1 : ℕ) + d1 = i.1 ∧ (k.2 : ℕ) = i.2 + d2

variable {D E : ℕ → ℕ → Prop} {X Y : Matrix (Idx N) (Idx N) ℝ}

theorem Disp.mono (h : Disp D X) (hDE : ∀ d1 d2, D d1 d2 → E d1 d2) : Disp E X := fun i k hik => by
  obtain ⟨d1, d2, hd, h1, h2⟩ := h i k hik
  exact ⟨d1, d2, hDE _ _ hd, h1, h2⟩

theorem Disp.add (hX : Disp D X) (hY : Disp D Y) : Disp D (X + Y) := fun i k hik => by
  rw [Matrix.add_apply] at hik
  by_cases hx : X i k = 0
  · rw [hx, zero_add] at hik; exact hY i k hik
  · exact hX i k hx

theorem Disp.neg (hX : Disp D X) : Disp D (-X) := fun i k hik => hX i k (by simpa using hik)

theorem Disp.sub (hX : Disp D X) (hY : Disp D Y) : Disp D (X - Y) := by
  rw [sub_eq_add_neg]; exact hX.add hY.neg

theorem Disp.smul (hX : Disp D X) (c : ℝ) : Disp D (c • X) := fun i k hik => hX i k fun h => by
  apply hik; rw [Matrix.smul_apply, h, smul_zero]

theorem Disp.zero : Disp D (0 : Matrix (Idx N) (Idx N) ℝ) := fun _ _ hik => absurd rfl hik

theorem Disp.sum {α : Type*} {s : Finset α} {F : α → Matrix (Idx N) (Idx N) ℝ} (h : ∀ a ∈ s, Disp D (F a)) :
    Disp D (∑ a ∈ s, F a) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [sum_empty]; exact Disp.zero
  | insert a s ha ih =>
    rw [sum_insert ha]
    exact (h a (mem_insert_self a s)).add (ih fun b hb => h b (mem_insert_of_mem hb))

theorem Disp.mul (hX : Disp D X) (hY : Disp E Y) :
    Disp (fun d1 d2 => ∃ x1 x2 y1 y2, D x1 x2 ∧ E y1 y2 ∧ d1 = x1 + y1 ∧ d2 = x2 + y2) (X * Y) := by
  intro i k hik
  rw [Matrix.mul_apply] at hik
  obtain ⟨p, -, hp⟩ := exists_ne_zero_of_sum_ne_zero hik
  obtain ⟨x1, x2, hdx, hx1, hx2⟩ := hX i p (left_ne_zero_of_mul hp)
  obtain ⟨y1, y2, hdy, hy1, hy2⟩ := hY p k (right_ne_zero_of_mul hp)
  exact ⟨y1 + x1, y2 + x2, ⟨x1, x2, y1, y2, hdx, hdy, by ring, by ring⟩, by omega, by omega⟩

theorem disp_smv (cc : ℕ → ℝ) (d1 d2 : ℕ) (F : ℕ → ℕ → ℝ) :
    Disp (fun e1 e2 => e1 = d1 ∧ e2 = d2) (smv cc N d1 d2 F) := fun i k hik => by
  unfold smv at hik
  split_ifs at hik with h
  · exact ⟨d1, d2, ⟨rfl, rfl⟩, h.2.1, h.2.2⟩
  · exact absurd rfl hik

theorem disp_one : Disp (fun d1 d2 => d1 = 0 ∧ d2 = 0) (1 : Matrix (Idx N) (Idx N) ℝ) := fun i k hik => by
  rw [Matrix.one_apply] at hik
  split_ifs at hik with h
  · subst h; exact ⟨0, 0, ⟨rfl, rfl⟩, rfl, rfl⟩
  · exact absurd rfl hik

theorem Disp.pow_line (hX : Disp (fun d1 d2 => d2 = 2 * d1) X) :
    ∀ m, Disp (fun d1 d2 => d2 = 2 * d1) (X ^ m)
  | 0 => by rw [pow_zero]; exact disp_one.mono fun d1 d2 h => by omega
  | m + 1 => by
    rw [pow_succ]
    exact ((Disp.pow_line hX m).mul hX).mono fun d1 d2 ⟨x1, x2, y1, y2, hx, hy, h1, h2⟩ => by omega

theorem Disp.entry_zero (h : Disp D X) (i k : Idx N)
    (hD : ∀ d1 d2, D d1 d2 → (k.1 : ℕ) + d1 = i.1 → (k.2 : ℕ) = i.2 + d2 → False) : X i k = 0 := by
  by_contra hik
  obtain ⟨d1, d2, hd, h1, h2⟩ := h i k hik
  exact hD d1 d2 hd h1 h2

end OpM

open OpM

/-! ### The operators of the resummation -/

section Ops

variable (N : ℕ) (u v : ℕ → ℝ)

/-! The weights are those of the recurrence of Theorem 3.1 (`wA`, `wB`, `wC`, `wSV` of `VRAssembly.lean`): `A_j`
from `b`, `B_j` from `c`, `C'_j` from both, and the straight weight `a_{ℓ+a} = 1 - b_{ℓ+a} - c_{ℓ+a}`; `u`, `v` are
the Newton sequences of `c`, `b`, and `dd u` is `c`. -/

/-- `U`: the straight moves, divided by `c` at the destination level. -/
noncomputable def opU : Matrix (Idx N) (Idx N) ℝ := smv (dd u) N 1 0 (wSV u v)
/-- `P`: the `B_j` with `j` even. -/
noncomputable def opP : Matrix (Idx N) (Idx N) ℝ :=
  ∑ j ∈ (range (N + 1)).filter Even, smv (dd u) N (j + 1) (2 * j + 2) (wB u j)
/-- `Q`: the `B_j` with `j` odd. -/
noncomputable def opQ : Matrix (Idx N) (Idx N) ℝ :=
  ∑ j ∈ (range (N + 1)).filter Odd, smv (dd u) N (j + 1) (2 * j + 2) (wB u j)
/-- `C₊`: the `C'_j` with `j` even. -/
noncomputable def opCp : Matrix (Idx N) (Idx N) ℝ :=
  ∑ j ∈ (range (N + 1)).filter Even, smv (dd u) N (j + 2) (2 * j + 2) (wC u v j)
/-- `C₋`: the `C'_j` with `j` odd. -/
noncomputable def opCm : Matrix (Idx N) (Idx N) ℝ :=
  ∑ j ∈ (range (N + 1)).filter Odd, smv (dd u) N (j + 2) (2 * j + 2) (wC u v j)
/-- `A = Σ_j (-1)^j A_j`. -/
noncomputable def opA : Matrix (Idx N) (Idx N) ℝ :=
  ∑ j ∈ range (N + 1), (-1 : ℝ) ^ j • smv (dd u) N (j + 1) (2 * j + 1) (wA v j)
/-- `G = Σ_{m ≤ N} (P/2)^m = (I - P/2)^{-1}`. -/
noncomputable def opG : Matrix (Idx N) (Idx N) ℝ := ∑ m ∈ range (N + 1), ((1 / 2 : ℝ) • opP N u) ^ m
/-- `R + C + A` with `R = U + P²/4 - Q`. -/
noncomputable def opS : Matrix (Idx N) (Idx N) ℝ :=
  opU N u v + (1 / 4 : ℝ) • (opP N u * opP N u) - opQ N u + (opCp N u v - opCm N u v) + opA N u v
/-- `M = G (R + C + A) G`. -/
noncomputable def opM : Matrix (Idx N) (Idx N) ℝ := opG N u * opS N u v * opG N u

/-- The recurrence of Theorem 3.1 is the generic recurrence with these weights. -/
theorem kernelRecV_iff (ω : ℕ → ℕ → ℝ) :
    KernelRecV u v ω ↔ GenRec (dd u) (wA v) (wB u) (wC u v) (wSV u v) ω := Iff.rfl

/-- The move operator `T` of the recurrence splits as `U + P - Q + C₊ - C₋ + A`. -/
theorem tmat_split : Tmat (dd u) N (wA v) (wB u) (wC u v) (wSV u v) =
    opU N u v + opP N u - opQ N u + (opCp N u v - opCm N u v) + opA N u v := by
  unfold Tmat opU opP opQ opCp opCm opA
  simp only [smul_add, sum_add_distrib]
  have hB := sign_split_mat (range (N + 1)) fun j => smv (dd u) N (j + 1) (2 * j + 2) (wB u j)
  have hC := sign_split_mat (range (N + 1)) fun j => smv (dd u) N (j + 2) (2 * j + 2) (wC u v j)
  rw [hB, hC]
  abel

/-- `R + C + A = T - P + P²/4`. -/
theorem opS_eq : opS N u v = Tmat (dd u) N (wA v) (wB u) (wC u v) (wSV u v) - opP N u +
    (1 / 4 : ℝ) • (opP N u * opP N u) := by
  rw [tmat_split, opS]; abel

end Ops

/-! ### The cubic data -/

/-- `c_i = ρ(i) d_i` with `d_i = i/6`, `ρ(x) = 1/5 + C(x,3)/200`. -/
noncomputable def cubC (i : ℕ) : ℝ := (1 / 5 + (i.choose 3 : ℝ) / 200) * ((i : ℝ) / 6)
/-- `b_i = d_i - c_i`. -/
noncomputable def cubB (i : ℕ) : ℝ := (i : ℝ) / 6 - cubC i
/-- The Newton sequence of `c` on `1 ≤ k ≤ 6`. -/
noncomputable def cubU : ℕ → ℝ := padNewton 6 (newtonCoeff cubC)
/-- The Newton sequence of `b` on `1 ≤ k ≤ 6`. -/
noncomputable def cubV : ℕ → ℝ := padNewton 6 (newtonCoeff cubB)

/-- The Newton sequences reproduce `c` and `b` on `0, …, 6`. -/
theorem cub_dd (i : ℕ) (hi : i ≤ 6) : dd cubU i = cubC i ∧ dd cubV i = cubB i :=
  ⟨dd_padNewton cubC (by simp [cubC]) 6 i hi, dd_padNewton cubB (by simp [cubB, cubC]) 6 i hi⟩

/-- The cubic data are positive in `c` and nondecreasing in `b`. -/
theorem cubic_data : (∀ i, 1 ≤ i → i ≤ 6 → 0 < cubC i) ∧ (∀ i, i < 6 → cubB i ≤ cubB (i + 1)) := by
  constructor
  · intro i h1 h6
    interval_cases i <;> norm_num [cubC, Nat.choose]
  · intro i h6
    interval_cases i <;> norm_num [cubB, cubC, Nat.choose]

theorem cubU_eq (n : ℕ) :
    cubU n = if n = 1 then 1 / 30 else if n = 3 then 1 / 400 else if n = 4 then 1 / 300 else 0 := by
  unfold cubU padNewton
  by_cases h : 1 ≤ n ∧ n ≤ 6
  · rw [if_pos h]
    obtain ⟨h1, h6⟩ := h
    interval_cases n <;> norm_num [newtonCoeff, sum_range_succ, cubC, Nat.choose]
  · rw [if_neg h]
    have : n ≠ 1 ∧ n ≠ 3 ∧ n ≠ 4 := by omega
    rw [if_neg this.1, if_neg this.2.1, if_neg this.2.2]

/-- The three weights in the entry. -/
theorem cub_weights :
    wB cubU 0 0 6 = 1 / 10 ∧ wB cubU 0 1 4 = 1 / 24 ∧ wB cubU 1 0 6 = 1 / 20 ∧
      dd cubU 1 = 1 / 30 ∧ dd cubU 2 = 1 / 15 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp only [wB, Wt, iterShift_eq, sum_range_succ, sum_range_zero, cubU_eq]; norm_num [Nat.choose]
  · simp only [wB, Wt, iterShift_eq, sum_range_succ, sum_range_zero, cubU_eq]; norm_num [Nat.choose]
  · simp only [wB, Wt, iterShift_eq, sum_range_succ, sum_range_zero, cubU_eq]; norm_num [Nat.choose]
  · rw [(cub_dd 1 (by norm_num)).1]; norm_num [cubC, Nat.choose]
  · rw [(cub_dd 2 (by norm_num)).1]; norm_num [cubC, Nat.choose]

/-! ### The entry of `M` -/

/-- Source `(ℓ, a) = (0, 6)` and destination `(2, 2)`. -/
def srcK : Idx 6 := (⟨0, by norm_num⟩, ⟨6, by norm_num⟩)
def dstI : Idx 6 := (⟨2, by norm_num⟩, ⟨2, by norm_num⟩)
def midP : Idx 6 := (⟨1, by norm_num⟩, ⟨4, by norm_num⟩)

section Entry

variable (u v : ℕ → ℝ)

theorem disp_P : Disp (fun d1 d2 => 1 ≤ d1 ∧ d2 = 2 * d1) (opP 6 u) :=
  Disp.sum fun j _ => (disp_smv _ _ _ _).mono fun d1 d2 h => by omega

theorem disp_X : Disp (fun d1 d2 => 1 ≤ d1 ∧ d2 = 2 * d1) ((1 / 2 : ℝ) • opP 6 u) := (disp_P u).smul _

/-- The displacements of `R + C + A`. -/
def DS (d1 d2 : ℕ) : Prop :=
  (d1 = 1 ∧ d2 = 0) ∨ (2 ≤ d1 ∧ d2 = 2 * d1) ∨ (2 ≤ d1 ∧ d2 + 2 = 2 * d1) ∨ (1 ≤ d1 ∧ d2 + 1 = 2 * d1)

theorem disp_U : Disp (fun d1 d2 => d1 = 1 ∧ d2 = 0) (opU 6 u v) := disp_smv _ _ _ _

theorem disp_Q : Disp (fun d1 d2 => 2 ≤ d1 ∧ d2 = 2 * d1) (opQ 6 u) :=
  Disp.sum fun j hj => (disp_smv _ _ _ _).mono fun d1 d2 h => by
    have := (mem_filter.mp hj).2
    obtain ⟨m, rfl⟩ := this
    omega

theorem disp_C : Disp (fun d1 d2 => 2 ≤ d1 ∧ d2 + 2 = 2 * d1) (opCp 6 u v - opCm 6 u v) :=
  (Disp.sum fun j _ => (disp_smv _ _ _ _).mono fun d1 d2 h => by omega).sub
    (Disp.sum fun j _ => (disp_smv _ _ _ _).mono fun d1 d2 h => by omega)

theorem disp_A : Disp (fun d1 d2 => 1 ≤ d1 ∧ d2 + 1 = 2 * d1) (opA 6 u v) :=
  Disp.sum fun j _ => ((disp_smv _ _ _ _).smul _).mono fun d1 d2 h => by omega

theorem disp_PP : Disp (fun d1 d2 => 2 ≤ d1 ∧ d2 = 2 * d1) (opP 6 u * opP 6 u) :=
  ((disp_P u).mul (disp_P u)).mono fun d1 d2 ⟨x1, x2, y1, y2, hx, hy, h1, h2⟩ => by omega

theorem disp_S : Disp DS (opS 6 u v) := by
  unfold opS
  refine ((((disp_U u v).mono ?_).add (((disp_PP u).smul _).mono ?_)).sub ((disp_Q u).mono ?_)).add
    ((disp_C u v).mono ?_) |>.add ((disp_A u v).mono ?_) <;> intro d1 d2 h <;> unfold DS <;> omega

theorem disp_G1 : Disp (fun d1 d2 => d2 = 2 * d1) (∑ m ∈ range 6, ((1 / 2 : ℝ) • opP 6 u) ^ m) :=
  Disp.sum fun m _ => Disp.pow_line ((disp_X u).mono fun _ _ h => h.2) m

/-- `G = 1 + X G₁ = 1 + G₁ X` with `X = P/2`, `G₁ = Σ_{m < 6} X^m`. -/
theorem opG_split :
    opG 6 u = 1 + ((1 / 2 : ℝ) • opP 6 u) * ∑ m ∈ range 6, ((1 / 2 : ℝ) • opP 6 u) ^ m ∧
    opG 6 u = 1 + (∑ m ∈ range 6, ((1 / 2 : ℝ) • opP 6 u) ^ m) * ((1 / 2 : ℝ) • opP 6 u) := by
  unfold opG
  rw [sum_range_succ', pow_zero, mul_sum, sum_mul]
  constructor
  · rw [add_comm]; congr 1; exact sum_congr rfl fun m _ => pow_succ' _ _
  · rw [add_comm]; congr 1

end Entry

/-- **P2, Section 6**: for the cubic data `N = 6`, `d_i = i/6`, `ρ(x) = 1/5 + C(x,3)/200` (`t = τ = 0`), the
operator `M = G (R + C + A) G` of the proof of Theorem 4.1, built from the moves of the kernel recurrence of
Theorem 3.1 for `c_i = ρ(i) d_i` and `b_i = d_i - c_i`, has the entry `-9/32 < 0` from `(ℓ, a) = (0, 6)` to
`(2, 2)`. -/
theorem opM_negative_entry : opM 6 cubU cubV dstI srcK = -9 / 32 := by
  set X := (1 / 2 : ℝ) • opP 6 cubU with hX
  set G1 := ∑ m ∈ range 6, X ^ m with hG1
  set S := opS 6 cubU cubV with hS
  have hM : opM 6 cubU cubV = S + X * G1 * S + S * G1 * X + X * G1 * S * G1 * X := by
    have h1 := (opG_split cubU).1
    have h2 := (opG_split cubU).2
    rw [← hX, ← hG1] at h1 h2
    calc opM 6 cubU cubV = (1 + X * G1) * S * (1 + G1 * X) := by rw [← h1, ← h2, hS]; rfl
      _ = S + X * G1 * S + S * G1 * X + X * G1 * S * G1 * X := by
        simp only [add_mul, mul_add, one_mul, mul_one, mul_assoc]
        abel
  have dX := disp_X cubU
  have dG := disp_G1 cubU
  have dS := disp_S cubU cubV
  rw [← hX] at dX
  rw [← hX, ← hG1] at dG
  rw [← hS] at dS
  have z1 : (X * G1 * S) dstI srcK = 0 :=
    ((dX.mul dG).mul dS).entry_zero _ _ fun d1 d2 hd h1 h2 => by
      obtain ⟨x1, x2, y1, y2, ⟨a1, a2, b1, b2, ha, hb, rfl, rfl⟩, hy, rfl, rfl⟩ := hd
      simp only [dstI, srcK] at h1 h2
      unfold DS at hy; omega
  have z2 : (S * G1 * X) dstI srcK = 0 :=
    ((dS.mul dG).mul dX).entry_zero _ _ fun d1 d2 hd h1 h2 => by
      obtain ⟨x1, x2, y1, y2, ⟨a1, a2, b1, b2, ha, hb, rfl, rfl⟩, hy, rfl, rfl⟩ := hd
      simp only [dstI, srcK] at h1 h2
      unfold DS at ha; omega
  have z3 : (X * G1 * S * G1 * X) dstI srcK = 0 :=
    ((((dX.mul dG).mul dS).mul dG).mul dX).entry_zero _ _ fun d1 d2 hd h1 h2 => by
      obtain ⟨x1, x2, y1, y2, ⟨a1, a2, b1, b2, ⟨c1, c2, e1, e2, ⟨f1, f2, g1, g2, hf, hg, rfl, rfl⟩, he, rfl, rfl⟩,
        hb, rfl, rfl⟩, hy, rfl, rfl⟩ := hd
      simp only [dstI, srcK] at h1 h2
      unfold DS at he; omega
  rw [hM, Matrix.add_apply, Matrix.add_apply, Matrix.add_apply, z1, z2, z3, add_zero, add_zero, add_zero, hS]
  -- the entry of `R + C + A`
  have zU : opU 6 cubU cubV dstI srcK = 0 :=
    (disp_U cubU cubV).entry_zero _ _ fun d1 d2 hd h1 h2 => by simp only [dstI, srcK] at h1 h2; omega
  have zC : (opCp 6 cubU cubV - opCm 6 cubU cubV) dstI srcK = 0 :=
    (disp_C cubU cubV).entry_zero _ _ fun d1 d2 hd h1 h2 => by simp only [dstI, srcK] at h1 h2; omega
  have zA : opA 6 cubU cubV dstI srcK = 0 :=
    (disp_A cubU cubV).entry_zero _ _ fun d1 d2 hd h1 h2 => by simp only [dstI, srcK] at h1 h2; omega
  have hQ : opQ 6 cubU dstI srcK = wB cubU 1 0 6 / dd cubU 2 := by
    unfold opQ
    rw [Matrix.sum_apply, sum_eq_single 1]
    · simp [smv, dstI, srcK]
    · intro j _ hj
      unfold smv; rw [if_neg]; simp only [dstI, srcK]; omega
    · intro h; exact absurd (mem_filter.mpr ⟨by simp, by decide⟩) h
  have hP1 : opP 6 cubU dstI midP = wB cubU 0 1 4 / dd cubU 2 := by
    unfold opP
    rw [Matrix.sum_apply, sum_eq_single 0]
    · simp [smv, dstI, midP]
    · intro j _ hj
      unfold smv; rw [if_neg]; simp only [dstI, midP]; omega
    · intro h; exact absurd (mem_filter.mpr ⟨by simp, by decide⟩) h
  have hP2 : opP 6 cubU midP srcK = wB cubU 0 0 6 / dd cubU 1 := by
    unfold opP
    rw [Matrix.sum_apply, sum_eq_single 0]
    · simp [smv, midP, srcK]
    · intro j _ hj
      unfold smv; rw [if_neg]; simp only [midP, srcK]; omega
    · intro h; exact absurd (mem_filter.mpr ⟨by simp, by decide⟩) h
  have hPP : (opP 6 cubU * opP 6 cubU) dstI srcK = opP 6 cubU dstI midP * opP 6 cubU midP srcK := by
    rw [Matrix.mul_apply]
    refine sum_eq_single midP (fun p _ hp => ?_) (fun h => absurd (mem_univ _) h)
    by_contra hne
    obtain ⟨x1, x2, hx, hx1, hx2⟩ := disp_P cubU dstI p (left_ne_zero_of_mul hne)
    obtain ⟨y1, y2, hy, hy1, hy2⟩ := disp_P cubU p srcK (right_ne_zero_of_mul hne)
    simp only [dstI, srcK] at hx1 hx2 hy1 hy2
    apply hp
    obtain ⟨⟨p1, hp1⟩, ⟨p2, hp2⟩⟩ := p
    simp only at hx1 hx2 hy1 hy2
    simp only [midP, Prod.mk.injEq, Fin.mk.injEq]
    omega
  obtain ⟨w06, w14, w106, c1, c2⟩ := cub_weights
  simp only [opS, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, zU, zA, hQ, hPP, hP1, hP2]
  have zC' : opCp 6 cubU cubV dstI srcK - opCm 6 cubU cubV dstI srcK = 0 := by rw [← Matrix.sub_apply]; exact zC
  rw [zC', w06, w14, w106, c1, c2]
  norm_num

/-- **P2, Section 6**: for `t = τ = 0` the operator `M` can have negative entries. -/
theorem opM_has_negative_entry : ∃ i k, opM 6 cubU cubV i k < 0 :=
  ⟨dstI, srcK, by rw [opM_negative_entry]; norm_num⟩

end Szkraw
