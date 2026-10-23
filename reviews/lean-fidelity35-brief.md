# Lean statement fidelity, round 35: the negative entry of the operator M (P2, Section 6)

Repository: github.com/skypher/szkraw, commit 4a03165: lean/Szkraw/OperatorM.lean (new); definitions from lean/Szkraw/VRAssembly.lean, VRMoves.lean, VRInduction.lean, VRKernel.lean, LCDetours.lean, LCSequences.lean, LCInduction.lean, LogConcaveStatement.lean (used in the accepted Lean proofs of P2 Theorems 3.1 and 4.1). Axiom audit lean/axioms.log (396 lines, only propext, Classical.choice, Quot.sound).

As in earlier rounds, **do not check proofs**. Check whether the Lean statements say what the passage says: that the operator `opM` is the operator M of the proof of P2 Theorem 4.1, formed for the stated cubic data, and that the stated entry is an entry of it. Check also the new P2 table row, the shortened not-formalized paragraph, and the clause added to the open-problems text. Report MATCH / MISMATCH per item with exact replacement text for any fix.

## Paper passages (P2 at 4a03165)

Notation (Section 2):

The Newton coefficients of a sequence $(u_i)_{0\leq i\leq N}$ are $\Delta^ku(0)=\sum_{i\leq k}(-1)^{k-i}\binom kiu_i$, so that $u_n=\sum_k\binom nk\Delta^ku(0)$. A nonnegative, finitely supported sequence $(u_k)_{k\geq0}$ is \emph{log-concave without internal zeros} if its positive entries form an interval and $u_k^2\geq u_{k-1}u_{k+1}$ for all $k\geq1$. For such a sequence put $f_n(\ell)=\sum_{h\geq0}\binom\ell hu_{n+h}$, and, for integers $p,q\geq0$,
\[
W_{p,q}(\ell,a)=\sum_{n\geq p}\binom{n-p+q}q\binom anf_n(\ell),
\]
with $A_j=W_{2j+1,j}$, $B_j=W_{2j+2,j}$ and $C_j=W_{2j+2,j+1}$ when these are formed from the Newton coefficients of the profile.


Proof of Theorem 3.1 (the kernel recurrence; "holds for every array"):

\]
where $c(\theta)=\sum_k\kappa_k\binom\theta k$ and $b(\theta)=\sum_k\beta_k\binom\theta k$. As in \cite[Section~\ref{P1-sec:lc}]{P1}, $K_k=\sum_{m,n}L_{mn}^kz^mw^n$, with $E_mE_n=\sum_kL_{mn}^kE_k$, satisfies $(\mathcal L_z-\mathcal L_w)K_k=0$, and $K_k=\sum\omega_{\ell,a}S^aZ^\ell$ with $\omega_{0,a}=\mathbf1_{a=k}$ and $\omega_{\ell,a}=0$ for $\ell+a>N$. The computation in the proof of \cite[Lemma~\ref{P1-lem:kernel-rec}]{P1} gives
\[
\frac{(\mathcal L_z-\mathcal L_w)S^aZ^\ell}{z-w}=S^aZ^\ell+\sum_{p\geq0}\binom apS^{a-p}Z^\ell\Bigl(\varphi_p(\ell)(\chi_{p-2}-\chi_p)+\psi_p(\ell)(\chi_{p-1}-\chi_p)\Bigr),
\]
with $\chi_{-2}=-Z^{-1}$ and $\chi_{-1}=0$. Collecting terms as there, with $W_{p,q}$ formed from $\varphi$ and $W^\psi_{p,q}$ from $\psi$, gives
\[
\begin{aligned}
c_{\ell+1}\omega_{\ell+1,a}={}&a_{\ell+a}\,\omega_{\ell,a}+\sum_{j\geq0}(-1)^j\Big(A^\psi_j(\ell-j,a+2j+1)\,\omega_{\ell-j,a+2j+1}+B_j(\ell-j,a+2j+2)\,\omega_{\ell-j,a+2j+2}\\
&+\bigl(C_j+C^\psi_j\bigr)(\ell-j-1,a+2j+2)\,\omega_{\ell-j-1,a+2j+2}\Big),
\end{aligned}
\]
where $A^\psi_j=W^\psi_{2j+1,j}$, $C^\psi_j=W^\psi_{2j+2,j+1}$, and $B_j=W_{2j+2,j}$, $C_j=W_{2j+2,j+1}$. The straight weight is $1-c_{\ell+a}-b_{\ell+a}=a_{\ell+a}$, extended polynomially beyond $N$, and $\beta_0=0$. Up to this point no hypothesis of the theorem has been used: the recurrence holds for every array in the stochastic normalization. Under the hypotheses, all weights are nonnegative on $\Omega$.

Proof of Theorem 4.1, resummation paragraph:

\emph{Resummation.} Regard the moves as operators on functions on $\Omega$, each divided by $c$ at the destination level; all strictly raise $\ell$, and inequalities between operators are entrywise. Let $P$ and $Q$ be the sums of the $B_j$ with $j$ even and odd, $C=C_+-C_-$ with $C_\pm$ the sums of the $C'_j$ with $j$ even and odd, $H_+$ and $H_-$ the sums of the $H_j$ with $j\geq2$ even and $j\geq3$ odd, $V_+$ and $V_-$ the sums of the $V_j$ with $j$ odd and $j\geq2$ even, $A_0$ the operator of $A^\psi_0$, and $U$ the straight moves. The recurrence reads $\omega=\beta+(U+P-Q+C+A)\omega$ with $A=A_0+H_+-H_--H_1+V_+-V_-$ and $\beta=\omega|_{\ell=0}\geq0$. The inequalities above give
\[
P^2\geq4Q,\qquad H_+P\geq6H_-,\qquad V_+P\geq6V_-,\qquad C_+P\geq6C_-,\qquad A_0P+PA_0+2V_1\geq4H_1.
\]
Let $G=(I-P/2)^{-1}=\sum_{m=0}^N(P/2)^m\geq0$. Then $PG=GP=2(G-I)$ and $(I-P/6)G=\frac23G+\frac13I$, so $G(H_+-H_-)G\geq GH_+(I-P/6)G\geq0$, $GCG\geq0$ and $G(V_+-V_-)G\geq\frac23GV_1G$. Hence
\[

Section 6 (open problems), the passage in question (the clause after the script name was added in this round):

In sampled arrays with $t,\tau\geq0$, $r\sigma=u\,t\tau$ and nondecreasing $b$ on log-concave Newton profiles, no negative coefficients were found for the tested values $u\in\{\frac14,1,4,16,64\}$, $r\in\{\frac1{10},\frac13,\frac12,\frac45,\frac{19}{20},\frac{99}{100}\}$ and $4\leq N\leq18$ (full tables), and in the coefficients $g(m,N;k)$ for $u\in\{1,4,16\}$ and $N=24,32,48,64,96$ (\path{runs/varratio/cubic_lc_test.py}); in these samples the operator $M$ of the proof of Theorem~\ref{thm:lc-affine} was nonnegative for $u\leq4$ and $N\leq13$. For $t=\tau=0$, by contrast, $M$ has negative entries; for instance $N=6$, $d_i=i/6$, $r=\frac15$ and $\sigma=\frac1{200}$ give a negative entry (\path{runs/varratio/cubic_diag.py}); this obstructs extending that resummation to such data, and does not contradict Theorem~\ref{thm:lc-affine}, which does not cover them. 

## Lean definitions (existing, used in the accepted proofs)

```lean
def iterShift (u : ℕ → ℝ) : ℕ → ℕ → ℝ
  | 0 => u
  | n + 1 => Szkraw.shiftSum (iterShift u n)
def shiftSum (u : ℕ → ℝ) (i : ℕ) : ℝ := u i + u (i + 1)
-- `dd u ℓ = iterShift u ℓ 0` (value of the sequence with Newton coefficients `u`)
noncomputable def dd (ℓ : ℕ) : ℝ := Szkraw.iterShift u ℓ 0
noncomputable def Wt (u : ℕ → ℝ) (p q ℓ a : ℕ) : ℝ :=
  ∑ n ∈ range (a + 1), (if p ≤ n then ((n - p + q).choose q : ℝ) else 0) *
    (a.choose n : ℝ) * Szkraw.iterShift u ℓ n
noncomputable def newtonCoeff (d : ℕ → ℝ) (k : ℕ) : ℝ :=
  ∑ i ∈ range (k + 1), (-1 : ℝ) ^ (k - i) * (k.choose i : ℝ) * d i

noncomputable def padNewton (N : ℕ) (ν : ℕ → ℝ) (i : ℕ) : ℝ := if 1 ≤ i ∧ i ≤ N then ν i else 0

-- VRAssembly.lean
/-- The weights of the recurrence of Theorem 8.6, in the generic form. -/
noncomputable def wA (v : ℕ → ℝ) (j ℓ a : ℕ) : ℝ := Wt v (2 * j + 1) j ℓ a
noncomputable def wB (u : ℕ → ℝ) (j ℓ a : ℕ) : ℝ := Wt u (2 * j + 2) j ℓ a
noncomputable def wC (u v : ℕ → ℝ) (j ℓ a : ℕ) : ℝ := Wt u (2 * j + 2) (j + 1) ℓ a + Wt v (2 * j + 2) (j + 1) ℓ a
noncomputable def wSV (u v : ℕ → ℝ) (ℓ a : ℕ) : ℝ := 1 - dd v (ℓ + a) - dd u (ℓ + a)

-- VRKernel.lean (the recurrence of Theorem 3.1)
noncomputable def moveAV (j ℓ a : ℕ) : ℝ := Wt v (2 * j + 1) j (ℓ - j) (a + 2 * j + 1) * ω (ℓ - j) (a + 2 * j + 1)
noncomputable def moveBV (j ℓ a : ℕ) : ℝ := Wt u (2 * j + 2) j (ℓ - j) (a + 2 * j + 2) * ω (ℓ - j) (a + 2 * j + 2)
noncomputable def moveCV (j ℓ a : ℕ) : ℝ :=
  if j < ℓ then (Wt u (2 * j + 2) (j + 1) (ℓ - j - 1) (a + 2 * j + 2) +
    Wt v (2 * j + 2) (j + 1) (ℓ - j - 1) (a + 2 * j + 2)) * ω (ℓ - j - 1) (a + 2 * j + 2) else 0

noncomputable def grpV (j ℓ a : ℕ) : ℝ := moveAV v ω j ℓ a + moveBV u ω j ℓ a + moveCV u v ω j ℓ a

/-- The kernel recurrence of Theorem 8.6. -/
def KernelRecV : Prop :=
  ∀ ℓ a, dd u (ℓ + 1) * ω (ℓ + 1) a =
    (1 - dd v (ℓ + a) - dd u (ℓ + a)) * ω ℓ a + ∑ j ∈ range (ℓ + 1), (-1 : ℝ) ^ j * grpV u v ω j ℓ a

-- VRInduction.lean
noncomputable def gmA (j ℓ a : ℕ) : ℝ := A j (ℓ - j) (a + 2 * j + 1) * ω (ℓ - j) (a + 2 * j + 1)
noncomputable def gmB (j ℓ a : ℕ) : ℝ := B j (ℓ - j) (a + 2 * j + 2) * ω (ℓ - j) (a + 2 * j + 2)
noncomputable def gmC (j ℓ a : ℕ) : ℝ :=
  if j < ℓ then C j (ℓ - j - 1) (a + 2 * j + 2) * ω (ℓ - j - 1) (a + 2 * j + 2) else 0

noncomputable def ggrp (j ℓ a : ℕ) : ℝ := gmA A ω j ℓ a + gmB B ω j ℓ a + gmC C ω j ℓ a

/-- The generic kernel recurrence. -/
def GenRec : Prop :=
  ∀ ℓ a, cc (ℓ + 1) * ω (ℓ + 1) a = s ℓ a * ω ℓ a + ∑ j ∈ range (ℓ + 1), (-1 : ℝ) ^ j * ggrp A B C ω j ℓ a

-- VRMoves.lean (`Idx N = Fin (N+1) × Fin (N+1)`, pairs `(ℓ, a)`; `X i k` is the entry from source `k` to destination `i`)
/-- A move of displacement `(d₁, -d₂)` with weight `F` at the source, divided by `cc` at the
destination level; only sources in `Ω = {ℓ + a ≤ N}` count. -/
noncomputable def smv (d1 d2 : ℕ) (F : ℕ → ℕ → ℝ) : Matrix (Idx N) (Idx N) ℝ := fun i k =>
  if (k.1 : ℕ) + k.2 ≤ N ∧ (k.1 : ℕ) + d1 = i.1 ∧ (k.2 : ℕ) = i.2 + d2 then F k.1 k.2 / cc i.1 else 0

/-- The move operator of the generic recurrence. -/
noncomputable def Tmat : Matrix (Idx N) (Idx N) ℝ :=
  smv cc N 1 0 s + ∑ j ∈ range (N + 1), (-1 : ℝ) ^ j •
    (smv cc N (j + 1) (2 * j + 1) (A j) + smv cc N (j + 1) (2 * j + 2) (B j) +
      smv cc N (j + 2) (2 * j + 2) (C j))
```

## New Lean definitions and statements (OperatorM.lean)

```lean
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
    KernelRecV u v ω ↔ GenRec (dd u) (wA v) (wB u) (wC u v) (wSV u v) ω := …

/-- The move operator `T` of the recurrence splits as `U + P - Q + C₊ - C₋ + A`. -/
theorem tmat_split : Tmat (dd u) N (wA v) (wB u) (wC u v) (wSV u v) =
    opU N u v + opP N u - opQ N u + (opCp N u v - opCm N u v) + opA N u v := …

/-- `R + C + A = T - P + P²/4`. -/
theorem opS_eq : opS N u v = Tmat (dd u) N (wA v) (wB u) (wC u v) (wSV u v) - opP N u +
    (1 / 4 : ℝ) • (opP N u * opP N u) := …

/-- `c_i = ρ(i) d_i` with `d_i = i/6`, `ρ(x) = 1/5 + C(x,3)/200`. -/
noncomputable def cubC (i : ℕ) : ℝ := (1 / 5 + (i.choose 3 : ℝ) / 200) * ((i : ℝ) / 6)
/-- `b_i = d_i - c_i`. -/
noncomputable def cubB (i : ℕ) : ℝ := (i : ℝ) / 6 - cubC i
/-- The Newton sequence of `c` on `1 ≤ k ≤ 6`. -/
noncomputable def cubU : ℕ → ℝ := padNewton 6 (newtonCoeff cubC)
/-- The Newton sequence of `b` on `1 ≤ k ≤ 6`. -/
noncomputable def cubV : ℕ → ℝ := padNewton 6 (newtonCoeff cubB)

/-- The Newton sequences reproduce `c` and `b` on `0, …, 6`. -/
theorem cub_dd (i : ℕ) (hi : i ≤ 6) : dd cubU i = cubC i ∧ dd cubV i = cubB i := …

/-- The cubic data are positive in `c` and nondecreasing in `b`. -/
theorem cubic_data : (∀ i, 1 ≤ i → i ≤ 6 → 0 < cubC i) ∧ (∀ i, i < 6 → cubB i ≤ cubB (i + 1)) := …

/-- Source `(ℓ, a) = (0, 6)` and destination `(2, 2)`. -/
def srcK : Idx 6 := (⟨0, by norm_num⟩, ⟨6, by norm_num⟩)
def dstI : Idx 6 := (⟨2, by norm_num⟩, ⟨2, by norm_num⟩)
def midP : Idx 6 := (⟨1, by norm_num⟩, ⟨4, by norm_num⟩)

/-- **P2, Section 6**: for the cubic data `N = 6`, `d_i = i/6`, `ρ(x) = 1/5 + C(x,3)/200` (`t = τ = 0`), the
operator `M = G (R + C + A) G` of the proof of Theorem 4.1, built from the moves of the kernel recurrence of
Theorem 3.1 for `c_i = ρ(i) d_i` and `b_i = d_i - c_i`, has the entry `-9/32 < 0` from `(ℓ, a) = (0, 6)` to
`(2, 2)`. -/
theorem opM_negative_entry : opM 6 cubU cubV dstI srcK = -9 / 32 := …

/-- **P2, Section 6**: for `t = τ = 0` the operator `M` can have negative entries. -/
theorem opM_has_negative_entry : ∃ i k, opM 6 cubU cubV i k < 0 := …
```

Notes. (a) `smv` divides by `cc = dd u = c` at the destination level and counts only sources with `ℓ + a ≤ N`; the move families use the displacements of the recurrence: `A_j` from `(ℓ-j, a+2j+1)`, `B_j` from `(ℓ-j, a+2j+2)`, `C'_j` from `(ℓ-j-1, a+2j+2)`, straight from `(ℓ, a)`. (b) `opA = Σ_j (-1)^j A_j` is the paper's `A = A₀ + H₊ - H₋ - H₁ + V₊ - V₋` with `A_j = H_j - V_j`. (c) The Newton sequences are those of `c`, `b` on `0, …, 6` (`padNewton 6`, as in the accepted proofs); `cub_dd` checks that they reproduce `c`, `b` there. (d) The P2 code `runs/varratio/cubic_diag.py` with arguments `6 1/5 0 0 1/200` reports the minimum entry of M as −0.28125 = −9/32 at destination `(2,2)`, source `(0,6)`.

## P2 changes at 4a03165

New table row:

Section~\ref{sec:open}: a negative entry of the operator $M$ for $N=6$, $t=\tau=0$ & \path{Szkraw.opM_negative_entry}, \path{Szkraw.opM_has_negative_entry}

Removed from the not-formalized paragraph (after "the sampled tests of cubic ratios and of the resummed operator, which are numerical evidence over finitely many arrays"): ", and the negative entry of $M$ for $N=6$, which is checked in exact arithmetic by \path{runs/varratio/cubic_diag.py} but not in Lean; it obstructs extending the resummation used in Theorem~\ref{thm:lc-affine} to those cubic data, rather than contradicting that theorem." Its last clause moved into the Section 6 sentence quoted above.

Questions: (1) Do `opU`, `opP`, `opQ`, `opCp`, `opCm`, `opA`, `opG`, `opS`, `opM` (with `kernelRecV_iff`, `tmat_split`, `opS_eq`) define the operator M of the proof of Theorem 4.1 for an array given by Newton sequences `u` (of `c`) and `v` (of `b`)? (2) Do `cubC`, `cubB`, `cubU`, `cubV` encode "N = 6, d_i = i/6, r = 1/5 and σ = 1/200" with `t = τ = 0`? (3) Do `opM_negative_entry` and `opM_has_negative_entry` formalize "give a negative entry"? (4) Are the table row, the shortened not-formalized paragraph and the moved clause accurate?

Answer per item, then an overall verdict (PASS / PASS WITH MINOR FIXES / FAIL).
