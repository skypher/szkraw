import Szkraw.ProfileCounterexamples

/-!
# Windowed column of the product table

For the corner `g(N,N;N)` only the entries `H_m(n)` of column `N` with `n ≥ lo_m = max(m, N - m)` matter: the
entries with `n + m < N` vanish (`ccol_triangle`), and `H_N(N)` depends on `H_m(n)` only for `n ≥ m`. `witer`
computes the column on these windows, about a quarter of the table; `witer_eq` identifies its state with the
suffixes of `ccol`, so a kernel check of `witer` decides the sign of `g(N,N;N)`. `witer_add` splits the
computation into chunks that are checked separately against stated intermediate states.
-/

namespace Szkraw

open Finset

namespace ColCheck

/-- The window `[lo_m, N]` at step `m`. -/
def lo (N m : ℕ) : ℕ := max m (N - m)

/-- The window of the previous step (`N` at `m = 0`, where the previous column is zero). -/
def loP (N m : ℕ) : ℕ := if m = 0 then N else lo N (m - 1)

/-- A list on `[lo₁, N]` re-indexed to `[lo₂, N]`: zero-padded in front or shortened. -/
def align (lo1 lo2 : ℕ) (L : List ℤ) : List ℤ :=
  if lo2 ≤ lo1 then List.replicate (lo1 - lo2) 0 ++ L else L.drop (lo2 - lo1)

/-- One step of the column recurrence on aligned lists: coefficients `(A_n, B_n, C_n)`, previous column `P`,
current column `X`, and `X` just below the window. -/
def wrstep (bm k : ℤ) : List (ℤ × ℤ × ℤ) → List ℤ → List ℤ → ℤ → List ℤ
  | t :: cs, p :: P, x :: X, xp => (t.1 * X.headD 0 + ((t.2.1 - bm) * x + (t.2.2 * xp - k * p))) :: wrstep bm k cs P X x
  | _, _, _, _ => []

/-- The windowed state `(lo_{m-1}, H_{m-1}|window, lo_m, H_m|window)`. -/
abbrev WState := ℕ × List ℤ × ℕ × List ℤ

/-- One windowed step from `m` to `m + 1`. -/
def wstep (A B C : List ℤ) (N m : ℕ) (s : WState) : WState :=
  let loN := lo N (m + 1)
  let xp : ℤ := if s.2.2.1 < loN then s.2.2.2.headD 0 else 0
  (s.2.2.1, s.2.2.2, loN,
    wrstep (eG B m) (eG C m * eG A (m - 1)) ((A.zip (B.zip C)).drop loN) (align s.1 loN s.2.1)
      (align s.2.2.1 loN s.2.2.2) xp)

/-- `s` windowed steps starting at step `m₀`. -/
def witer (A B C : List ℤ) (N m0 : ℕ) (s : ℕ) (st : WState) : WState :=
  @Nat.rec (fun _ => WState) st (fun i acc => wstep A B C N (m0 + i) acc) s

/-- The windowed state at `m = 0`: `H_{-1} = 0`, `H_0 = e_N`. -/
def winit (N : ℕ) : WState := (N, [0], N, [1])

theorem witer_add (A B C : List ℤ) (N m0 s t : ℕ) (st : WState) :
    witer A B C N m0 (s + t) st = witer A B C N (m0 + s) t (witer A B C N m0 s st) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    show wstep A B C N (m0 + (s + t)) (witer A B C N m0 (s + t) st) =
      wstep A B C N (m0 + s + t) (witer A B C N (m0 + s) t (witer A B C N m0 s st))
    rw [ih, Nat.add_assoc]

/-! ### Lemmas on the list operations -/

theorem getD_append_replicate (j d : ℕ) (L : List ℤ) :
    (List.replicate d 0 ++ L).getD j 0 = if d ≤ j then L.getD (j - d) 0 else 0 := by
  simp only [List.getD_eq_getElem?_getD]
  split_ifs with h
  · rw [List.getElem?_append_right (by simp; omega)]; simp
  · rw [List.getElem?_append_left (by simp; omega)]; simp [show j < d by omega]

theorem getD_drop (d j : ℕ) (L : List ℤ) : (L.drop d).getD j 0 = L.getD (d + j) 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_drop]

theorem getD_align (lo1 lo2 j : ℕ) (L : List ℤ) :
    (align lo1 lo2 L).getD j 0 = if lo1 ≤ lo2 + j then L.getD (lo2 + j - lo1) 0 else 0 := by
  unfold align
  split_ifs with h1 h2 h2
  · rw [getD_append_replicate, if_pos (by omega)]; congr 1; omega
  · rw [getD_append_replicate, if_neg (by omega)]
  · rw [getD_drop]; congr 1; omega
  · omega

theorem length_align (lo1 lo2 : ℕ) (L : List ℤ) (N : ℕ) (hL : L.length = N + 1 - lo1) (h1 : lo1 ≤ N)
    (h2 : lo2 ≤ N) : (align lo1 lo2 L).length = N + 1 - lo2 := by
  unfold align
  split_ifs <;> simp [hL] <;> omega

theorem length_wrstep (bm k : ℤ) : ∀ (cs : List (ℤ × ℤ × ℤ)) (P X : List ℤ) (xp : ℤ) (L : ℕ),
    cs.length = L → P.length = L → X.length = L → (wrstep bm k cs P X xp).length = L
  | [], _, _, _, L, h, _, _ => by simp [wrstep] at h ⊢; omega
  | _ :: cs, [], _, _, L, h1, h2, _ => by simp at h1 h2; omega
  | _ :: cs, _ :: P, [], _, L, h1, _, h3 => by simp at h1 h3; omega
  | t :: cs, p :: P, x :: X, xp, L, h1, h2, h3 => by
    simp only [wrstep, List.length_cons] at h1 h2 h3 ⊢
    rw [length_wrstep bm k cs P X x (L - 1) (by omega) (by omega) (by omega)]; omega

theorem getD_wrstep (bm k : ℤ) : ∀ (cs : List (ℤ × ℤ × ℤ)) (P X : List ℤ) (xp : ℤ) (i : ℕ),
    i < cs.length → i < P.length → i < X.length →
    (wrstep bm k cs P X xp).getD i 0 =
      (cs.getD i (0, 0, 0)).1 * X.getD (i + 1) 0 + (((cs.getD i (0, 0, 0)).2.1 - bm) * X.getD i 0 +
        ((cs.getD i (0, 0, 0)).2.2 * (if i = 0 then xp else X.getD (i - 1) 0) - k * P.getD i 0))
  | [], _, _, _, i, h, _, _ => by simp at h
  | _ :: _, [], _, _, i, _, h, _ => by simp at h
  | _ :: _, _ :: _, [], _, i, _, _, h => by simp at h
  | t :: cs, p :: P, x :: X, xp, 0, _, _, _ => by
    simp [wrstep, List.getD_eq_getElem?_getD, List.headD_eq_head?_getD]
    cases X <;> simp
  | t :: cs, p :: P, x :: X, xp, i + 1, h1, h2, h3 => by
    simp only [List.length_cons] at h1 h2 h3
    have ih := getD_wrstep bm k cs P X x i (by omega) (by omega) (by omega)
    simp only [wrstep, List.getD_cons_succ, ih]
    rcases i with _ | i
    · simp [List.getD_eq_getElem?_getD]
    · simp [List.getD_eq_getElem?_getD]


/-! ### The windowed state is the suffix of the column -/

theorem list_ext_getD {L M : List ℤ} (h : L.length = M.length) (h' : ∀ i < L.length, L.getD i 0 = M.getD i 0) :
    L = M := by
  apply List.ext_getElem h
  intro i h1 h2
  have := h' i h1
  simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1, List.getElem?_eq_getElem h2] using this

theorem getD_zip3 (A B C : List ℤ) (N n : ℕ) (hA : A.length = N + 1) (hB : B.length = N + 1)
    (hC : C.length = N + 1) (hn : n ≤ N) :
    (A.zip (B.zip C)).getD n (0, 0, 0) = (eG A n, eG B n, eG C n) := by
  have h1 : n < A.length := by omega
  have h2 : n < B.length := by omega
  have h3 : n < C.length := by omega
  have h4 : n < (A.zip (B.zip C)).length := by simp [hA, hB, hC]; omega
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h4, Option.getD_some, List.getElem_zip, eG,
    List.getElem?_eq_getElem h1, List.getElem?_eq_getElem h2, List.getElem?_eq_getElem h3]

section window

variable {A B C : List ℤ} {N : ℕ}

/-- Entries of column `N` vanish below the triangle: `H_m(n) = 0` for `n + m < N`. -/
theorem ccol_triangle (hA : A.length = N + 1) (hB : B.length = N + 1) (hC : C.length = N + 1) :
    ∀ m, (∀ n, n + m < N → eG (ccol A B C N N m).2 n = 0) ∧
      (∀ n, n + m < N + 1 → eG (ccol A B C N N m).1 n = 0)
  | 0 => by
    constructor
    · intro n hn
      simp [ccol, eG, List.getD_eq_getElem?_getD, List.getElem?_map,
        List.getElem?_range (show n < N + 1 by omega), show n ≠ N by omega]
    · intro n hn
      simp only [ccol, eG, List.getD_eq_getElem?_getD, List.getElem?_replicate]
      split_ifs <;> rfl
  | m + 1 => by
    obtain ⟨ih2, ih1⟩ := ccol_triangle hA hB hC m
    obtain ⟨h1, h2⟩ := ccol_length A B C N N hA hB hC m
    refine ⟨fun n hn => ?_, fun n hn => ih2 n (by omega)⟩
    show (cstep A B C m (ccol A B C N N m).1 (ccol A B C N N m).2).getD n 0 = 0
    rw [getD_cstep A B C N m _ _ hA hB hC h1 h2 n (by omega), ih2 (n + 1) (by omega), ih2 n (by omega),
      ih1 n (by omega)]
    rcases n with _ | n
    · simp
    · rw [if_neg (by omega), show n + 1 - 1 = n by omega, ih2 n (by omega)]; ring

theorem lo_le (m : ℕ) (hm : m ≤ N) : lo N m ≤ N := by unfold lo; omega

theorem loP_le (m : ℕ) (hm : m ≤ N) : loP N m ≤ N := by unfold loP lo; split_ifs <;> omega

/-- The aligned current column is the column on the new window. -/
theorem align_X (hA : A.length = N + 1) (hB : B.length = N + 1) (hC : C.length = N + 1) (m j : ℕ)
    (hm : m + 1 ≤ N) :
    (align (lo N m) (lo N (m + 1)) ((ccol A B C N N m).2.drop (lo N m))).getD j 0 =
      eG (ccol A B C N N m).2 (lo N (m + 1) + j) := by
  rw [getD_align]
  split_ifs with h
  · rw [getD_drop]; unfold eG; congr 1; omega
  · have := (ccol_triangle hA hB hC m).1 (lo N (m + 1) + j) (by unfold lo at h ⊢; omega)
    rw [this]

/-- The aligned previous column is the previous column on the new window. -/
theorem align_P (hA : A.length = N + 1) (hB : B.length = N + 1) (hC : C.length = N + 1) (m j : ℕ)
    (hm : m + 1 ≤ N) :
    (align (loP N m) (lo N (m + 1)) ((ccol A B C N N m).1.drop (loP N m))).getD j 0 =
      eG (ccol A B C N N m).1 (lo N (m + 1) + j) := by
  rw [getD_align]
  split_ifs with h
  · rw [getD_drop]; unfold eG; congr 1; omega
  · have := (ccol_triangle hA hB hC m).2 (lo N (m + 1) + j) (by unfold loP lo at h; unfold lo; split_ifs at h <;> omega)
    rw [this]

/-- **The windowed computation.** For column `N`, the state after `m` windowed steps is the pair of suffixes
`(H_{m-1} on [lo_{m-1}, N], H_m on [lo_m, N])` of the column computed by `ccol`. -/
theorem witer_eq (hA : A.length = N + 1) (hB : B.length = N + 1) (hC : C.length = N + 1) (hN : 1 ≤ N) :
    ∀ m, m ≤ N → witer A B C N 0 m (winit N) =
      (loP N m, (ccol A B C N N m).1.drop (loP N m), lo N m, (ccol A B C N N m).2.drop (lo N m))
  | 0, _ => by
    have hd : ((List.range (N + 1)).map fun n => if n = N then (1 : ℤ) else 0).drop N = [1] := by
      rw [List.range_succ, List.map_append, List.drop_left' (by simp)]; simp
    have e1 : loP N 0 = N := by simp [loP]
    have e2 : lo N 0 = N := by simp [lo]
    show winit N = _
    rw [e1, e2]
    simp only [winit, ccol, hd, List.drop_replicate, show N + 1 - N = 1 by omega, List.replicate_one]
  | m + 1, hm => by
    have ih := witer_eq hA hB hC hN m (by omega)
    obtain ⟨h1, h2⟩ := ccol_length A B C N N hA hB hC m
    show wstep A B C N (0 + m) (witer A B C N 0 m (winit N)) = _
    rw [ih, Nat.zero_add]
    have eP : loP N (m + 1) = lo N m := by simp [loP]
    rw [eP]
    simp only [wstep]
    refine Prod.ext rfl (Prod.ext rfl (Prod.ext rfl ?_))
    show wrstep _ _ _ _ _ _ = (cstep A B C m (ccol A B C N N m).1 (ccol A B C N N m).2).drop (lo N (m + 1))
    have hlo := lo_le (N := N) (m + 1) hm
    have hlo0 := lo_le (N := N) m (by omega)
    have hloP := loP_le (N := N) m (by omega)
    have hlen : ((A.zip (B.zip C)).drop (lo N (m + 1))).length = N + 1 - lo N (m + 1) := by
      simp [hA, hB, hC]
    have hPa := length_align (loP N m) (lo N (m + 1)) ((ccol A B C N N m).1.drop (loP N m)) N
      (by simp [h1]) hloP hlo
    have hXa := length_align (lo N m) (lo N (m + 1)) ((ccol A B C N N m).2.drop (lo N m)) N
      (by simp [h2]) hlo0 hlo
    apply list_ext_getD
    · rw [length_wrstep _ _ _ _ _ _ (N + 1 - lo N (m + 1)) hlen hPa hXa, List.length_drop,
        length_cstep A B C N m _ _ hA hB hC h1 h2]
    · intro i hi
      rw [length_wrstep _ _ _ _ _ _ (N + 1 - lo N (m + 1)) hlen hPa hXa] at hi
      rw [getD_wrstep _ _ _ _ _ _ i (by omega) (by omega) (by omega), getD_drop,
        getD_cstep A B C N m _ _ hA hB hC h1 h2 _ (by omega)]
      have hc : ((A.zip (B.zip C)).drop (lo N (m + 1))).getD i (0, 0, 0) =
          (eG A (lo N (m + 1) + i), eG B (lo N (m + 1) + i), eG C (lo N (m + 1) + i)) := by
        simp only [List.getD_eq_getElem?_getD, List.getElem?_drop]
        rw [← List.getD_eq_getElem?_getD, getD_zip3 A B C N _ hA hB hC (by omega)]
      rw [hc, align_X hA hB hC m (i + 1) hm, align_X hA hB hC m i hm, align_P hA hB hC m i hm]
      have hpos : lo N (m + 1) + i ≠ 0 := by unfold lo; omega
      rw [if_neg hpos]
      rcases i with _ | i
      · -- the entry just below the window
        rw [if_pos rfl]
        have hxp : (if lo N m < lo N (m + 1) then ((ccol A B C N N m).2.drop (lo N m)).headD 0 else 0) =
            eG (ccol A B C N N m).2 (lo N (m + 1) + 0 - 1) := by
          split_ifs with h
          · have he : lo N (m + 1) + 0 - 1 = lo N m := by unfold lo at h ⊢; omega
            rw [he]
            unfold eG
            rw [show (ccol A B C N N m).2.getD (lo N m) 0 = ((ccol A B C N N m).2.drop (lo N m)).getD 0 0 by
              rw [getD_drop, Nat.add_zero]]
            cases (ccol A B C N N m).2.drop (lo N m) <;> rfl
          · rw [(ccol_triangle hA hB hC m).1 _ (by unfold lo at h ⊢; omega)]
        rw [hxp]
        dsimp only
        rw [show lo N (m + 1) + (0 + 1) = lo N (m + 1) + 0 + 1 by omega]
        ring
      · rw [if_neg (Nat.succ_ne_zero i), show i + 1 - 1 = i by omega, align_X hA hB hC m i hm,
          show lo N (m + 1) + (i + 1) - 1 = lo N (m + 1) + i by omega,
          show lo N (m + 1) + (i + 1 + 1) = lo N (m + 1) + (i + 1) + 1 by omega]
        dsimp only
        ring

/-- The sign of `H_N(N)` read off the windowed computation. -/
theorem witer_corner (hA : A.length = N + 1) (hB : B.length = N + 1) (hC : C.length = N + 1) (hN : 1 ≤ N) :
    (witer A B C N 0 N (winit N)).2.2.2.headD 0 = eG (ccol A B C N N N).2 N := by
  rw [witer_eq hA hB hC hN N le_rfl]
  have hl : lo N N = N := by unfold lo; omega
  simp only [hl]
  unfold eG
  rw [show (ccol A B C N N N).2.getD N 0 = ((ccol A B C N N N).2.drop N).getD 0 0 by rw [getD_drop, Nat.add_zero]]
  cases (ccol A B C N N N).2.drop N <;> rfl

end window

end ColCheck

end Szkraw

namespace Szkraw.ColCheck

/-! ### The `N = 500` one-kink example of P3 (`r = 1/10`, `m = 450`, `δ = 1/10`) -/

/-- Closed form of the partial sums of the one-kink increments `kinkZ m u w`. -/
def kinkDn (m : ℕ) (u w : ℤ) (i : ℕ) : ℤ := if i ≤ m then w * i else w * m + (w + u) * ((i - m : ℕ) : ℤ)

theorem psum_kinkZ (m : ℕ) (u w : ℤ) : ∀ i, psum (kinkZ m u w) i = kinkDn m u w i
  | 0 => by simp [psum, kinkDn]
  | i + 1 => by
    have h : psum (kinkZ m u w) (i + 1) = psum (kinkZ m u w) i + kinkZ m u w i := by
      simp [psum, List.range_succ, List.map_append, List.sum_append]
    rw [h, psum_kinkZ m u w i]
    unfold kinkDn kinkZ
    split_ifs <;> first
      | (push_cast; ring1)
      | (exfalso; omega)
      | (obtain rfl : i = m := by omega
         rw [show i + 1 - i = 1 by omega]; push_cast; ring1)
      | (rw [show i + 1 - m = i - m + 1 by omega]; push_cast; ring1)

/-- The integer arrays of `incProfile_example` for `kinkZ 450 1 10`, `r = 1/10`, `N = 500`. -/
def k5A : List ℤ := rA (kinkDn 450 1 10) 10 500
def k5B : List ℤ := rB (kinkDn 450 1 10) (fun _ => 1) 10 500
def k5C : List ℤ := rC (kinkDn 450 1 10) (fun _ => 1) 500

end Szkraw.ColCheck
