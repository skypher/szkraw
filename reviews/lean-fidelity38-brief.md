# Lean statement fidelity, round 38: the random-set reading of the product theorem (P2, after Proposition 4.3)

Repository: github.com/skypher/szkraw, commit f199058: lean/Szkraw/RandomSets.lean (new); lean/Szkraw/NewtonProduct.lean (accepted for Proposition 4.3 in round 17). Axiom audit lean/axioms.log (409 lines, only propext, Classical.choice, Quot.sound).

As in earlier rounds, **do not check proofs**. Check whether each Lean statement says what the passage says, and whether the P2 table row and the changed not-formalized item are accurate. Report MATCH / MISMATCH per item with exact replacement text for any fix.

## Paper passages (P2)


\begin{proposition}[Products]\label{prop:np}
Let $(\rho_i)_{i\geq0}$ and $(\nu_j)_{j\geq0}$ be nonnegative and log-concave without internal zeros, extended by zero at negative indices, and let $f(x)=\sum_i\rho_i\binom xi$ and $g(x)=\sum_j\nu_j\binom xj$ for $x\in\mathbb Z_{\geq0}$, where the sums are finite. Then the Newton coefficients $\kappa_k=\Delta^k(fg)(0)$ of $fg$ are nonnegative and log-concave without internal zeros.
\end{proposition}

The passage after its proof (the sentences in question):

In the language of random sets: if $S$ and $T$ are independent random subsets of $[n]$ whose laws are invariant under permutations and whose cardinalities are ultra-log-concave of order $n$, then so is $|S\cup T|$, since $\Pr(|S\cup T|=k)=\binom nk\kappa_k$ for $\Pr(S=A)=\rho_{|A|}$ and $\Pr(T=A)=\nu_{|A|}$. This closure theorem is Walkup's Theorem~4 for two sets~\cite{walkup}: his random sets are conditionally uniform, and their fundamental sequences are $\rho$ and $\nu$. He derives it from his Theorem~2, which proves that the double-binomial convolution $h_k=\sum_i\sum_r\binom ki\binom ir\rho_i\nu_{k-r}$, which is $\kappa_k$ after the substitution $j=k-r$, preserves log-concavity; Proposition~\ref{prop:np} expresses it in the Newton basis, and the proof above is self-contained. 

## Lean (accepted)

```lean
def LCNZ (u : ℕ → ℝ) : Prop :=
  (∀ i, 0 ≤ u i) ∧ (∀ i, u i * u (i + 2) ≤ u (i + 1) ^ 2) ∧
  (∀ i j k, i ≤ j → j ≤ k → 0 < u i → 0 < u k → 0 < u j)

def Hn (k i j : ℕ) : ℕ := if j ≤ k then k.choose i * i.choose (k - j) else 0

def nval (ρ : ℕ → ℝ) (x : ℕ) : ℝ := ∑ i ∈ range (x + 1), (x.choose i : ℝ) * ρ i

theorem kap_nat (ρ ν : ℕ → ℝ) (k x : ℕ) (hk : k ≤ x) :
    kap ρ ν k = ∑ i ∈ range (x + 1), ∑ j ∈ range (x + 1), (Hn k i j : ℝ) * (ρ i * ν j) := …

/-- **Proposition 8.14** (Walkup): the Newton coefficients `κ` of the product are nonnegative and
log-concave without internal zeros. -/
theorem kap_LCNZ {ρ ν : ℕ → ℝ} (hρ : LCNZ ρ) (hν : LCNZ ν) : LCNZ (kap ρ ν) := by
  refine ⟨kap_nonneg hρ hν, kap_lc hρ hν, ?_⟩
  intro i j k hij hjk hi hk
  obtain ⟨x1, y1, a1, b1, c1, d1, e1, f1, g1⟩ := kap_witness hρ hν hi
  obtain ⟨x2, y2, a2, b2, c2, d2, e2, f2, g2⟩ := kap_witness hρ hν hk
  set x := min (max x1 x2) (j : ℤ)
  set y := min (max y1 y2) (j : ℤ)
  have hx := extZ_interval hρ f1 f2 (x := x) (by omega) (by omega)
  have hy := extZ_interval hν g1 g2 (x := y) (by omega) (by omega)
  have hi' : (i : ℤ) ≤ j := by exact_mod_cast hij
  have hk' : (j : ℤ) ≤ k := by exact_mod_cast hjk
  exact kap_pos_of hρ hν (x := x) (y := y) (by omega) (by omega) (by omega) (by omega) (by omega) hx hy


/-! ## Identification with the Newton coefficients of the product -/

/-- The product rule in the binomial basis: `Σ_k C(x,k) H_k(i,j) = C(x,i) C(x,j)`. -/
theorem choose_mul_choose_eq_sum (x i j : ℕ) :
    ∑ k ∈ range (x + 1), x.choose k * Hn k i j = x.choose i * x.choose j := by
  by_cases hix : x < i
  · rw [Nat.choose_eq_zero_of_lt hix, zero_mul]
    refine sum_eq_zero (fun k hk => ?_)
    simp only [mem_range] at hk
    unfold Hn; split_ifs
    · rw [Nat.choose_eq_zero_of_lt (show k < i by omega)]; simp
    · simp
  push Not at hix
  obtain ⟨n, rfl⟩ : ∃ n, x = i + n := ⟨x - i, by omega⟩
  -- terms with k < i vanish; write k = i + m
  have hsplit : ∑ k ∈ range (i + n + 1), (i + n).choose k * Hn k i j =
      ∑ m ∈ range (n + 1), (i + n).choose (i + m) * Hn (i + m) i j := by
    rw [show i + n + 1 = i + (n + 1) by ring, sum_range_add]
    have z : ∑ k ∈ range i, (i + n).choose k * Hn k i j = 0 := by
      refine sum_eq_zero (fun k hk => ?_)
      simp only [mem_range] at hk
      unfold Hn; split_ifs
      · rw [Nat.choose_eq_zero_of_lt hk]; simp
      · simp
    rw [z, zero_add]
  rw [hsplit]
  have hterm : ∀ m, (i + n).choose (i + m) * Hn (i + m) i j =
      (i + n).choose i * (n.choose m * (if m ≤ j then i.choose (j - m) else 0)) := by
    intro m
    have cm := Nat.choose_mul (n := i + n) (k := i + m) (s := i) (by omega)
    rw [show i + n - i = n by omega, show i + m - i = m by omega] at cm
    unfold Hn
    by_cases hj : j ≤ i + m
    · rw [if_pos hj]
      by_cases hmj : m ≤ j
      · rw [if_pos hmj]
        have e : i.choose (i + m - j) = i.choose (j - m) := by
          rw [show i + m - j = i - (j - m) by omega, Nat.choose_symm (by omega)]
        rw [e, ← mul_assoc, cm]; ring
      · rw [if_neg hmj, Nat.choose_eq_zero_of_lt (show i < i + m - j by omega)]; simp
    · rw [if_neg hj]
      have hmj : m ≤ j := by omega
      rw [if_pos hmj, Nat.choose_eq_zero_of_lt (show i < j - m by omega)]; simp
  simp only [hterm, ← mul_sum]
  congr 1
  -- Vandermonde
  have vdm : (n + i).choose j = ∑ m ∈ range (j + 1), n.choose m * i.choose (j - m) := by
    rw [Nat.add_choose_eq, Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun a b => n.choose a * i.choose b)]
  rw [show i + n = n + i by ring, vdm]
  have L : ∑ m ∈ range (n + 1), n.choose m * (if m ≤ j then i.choose (j - m) else 0) =
      ∑ m ∈ range (n + j + 1), n.choose m * (if m ≤ j then i.choose (j - m) else 0) := by
    apply sum_subset
    · intro m; simp only [mem_range]; omega
    · intro m _ hm; simp only [mem_range] at hm
      rw [Nat.choose_eq_zero_of_lt (by omega), zero_mul]
  have R : ∑ m ∈ range (j + 1), n.choose m * i.choose (j - m) =
      ∑ m ∈ range (n + j + 1), n.choose m * (if m ≤ j then i.choose (j - m) else 0) := by
    rw [show ∑ m ∈ range (j + 1), n.choose m * i.choose (j - m) =
      ∑ m ∈ range (j + 1), n.choose m * (if m ≤ j then i.choose (j - m) else 0) from
        sum_congr rfl (fun m hm => by simp only [mem_range] at hm; rw [if_pos (by omega)])]
    apply sum_subset
    · intro m; simp only [mem_range]; omega
    · intro m _ hm; simp only [mem_range] at hm
      rw [if_neg (by omega), mul_zero]
  rw [L, R]


/-- Value at `x ∈ ℕ` of the Newton series with coefficients `ρ`. -/
def nval (ρ : ℕ → ℝ) (x : ℕ) : ℝ := ∑ i ∈ range (x + 1), (x.choose i : ℝ) * ρ i

theorem sum_Icc_zero_eq_range (L : ℕ) (f : ℤ → ℝ) :
    ∑ i ∈ Icc (0 : ℤ) L, f i = ∑ n ∈ range (L + 1), f n := by
  symm
  refine Finset.sum_nbij' (fun n : ℕ => (n : ℤ)) (fun i : ℤ => i.toNat) ?_ ?_ ?_ ?_ ?_
  · intro n hn; simp only [mem_range] at hn; simp only [mem_Icc]; omega
  · intro i hi; simp only [mem_Icc] at hi; simp only [mem_range]; omega
  · intro n _; simp
  · intro i hi; simp only [mem_Icc] at hi; omega
  · intro n _; rfl

theorem kap_nat (ρ ν : ℕ → ℝ) (k x : ℕ) (hk : k ≤ x) :
    kap ρ ν k = ∑ i ∈ range (x + 1), ∑ j ∈ range (x + 1), (Hn k i j : ℝ) * (ρ i * ν j) := by
  rw [kap_ext ρ ν k x (by exact_mod_cast hk), sum_Icc_zero_eq_range]
  refine sum_congr rfl (fun i _ => ?_)
  rw [sum_Icc_zero_eq_range]
  refine sum_congr rfl (fun j _ => ?_)
  simp [Hz, extZ]

/-- The Newton series with coefficients `κ = kap ρ ν` is the product of those of `ρ` and `ν`. -/
theorem nval_mul (ρ ν : ℕ → ℝ) (x : ℕ) : nval ρ x * nval ν x = nval (kap ρ ν) x := by
  unfold nval
  have h1 : ∑ k ∈ range (x + 1), (x.choose k : ℝ) * kap ρ ν k =
      ∑ k ∈ range (x + 1), ∑ i ∈ range (x + 1), ∑ j ∈ range (x + 1),
        (x.choose k : ℝ) * (Hn k i j : ℝ) * (ρ i * ν j) := by
    refine sum_congr rfl (fun k hk => ?_)
    simp only [mem_range] at hk
    rw [kap_nat ρ ν k x (by omega), mul_sum]
    refine sum_congr rfl (fun i _ => ?_)
    rw [mul_sum]
    exact sum_congr rfl (fun j _ => by ring)
  rw [h1, sum_comm]
  rw [sum_mul]
  refine sum_congr rfl (fun i _ => ?_)
  rw [sum_comm, mul_sum]
  refine sum_congr rfl (fun j _ => ?_)
  rw [← sum_mul]
  have := choose_mul_choose_eq_sum x i j
  have hc : ∑ k ∈ range (x + 1), (x.choose k : ℝ) * (Hn k i j : ℝ) = (x.choose i : ℝ) * (x.choose j : ℝ) := by
    exact_mod_cast this
  rw [hc]; ring

/-- Newton coefficients are determined by the values on `ℕ`. -/
theorem nval_inj {a b : ℕ → ℝ} (h : ∀ x, nval a x = nval b x) : a = b := by
  funext x
  induction x using Nat.strong_induction_on with
  | _ x ih =>
    have hx := h x
    unfold nval at hx
    rw [sum_range_succ, sum_range_succ, Nat.choose_self, Nat.cast_one, one_mul, one_mul] at hx
    have : ∑ i ∈ range x, (x.choose i : ℝ) * a i = ∑ i ∈ range x, (x.choose i : ℝ) * b i :=
      sum_congr rfl (fun i hi => by rw [ih i (by simpa using hi)])
    linarith

/-- **Proposition 8.14** (Walkup, Theorem 2, in the Newton basis). If `ρ` and `ν` are nonnegative and
log-concave without internal zeros, then the Newton coefficients of the product of their Newton series,
`f(x) g(x) = Σ_k C(x,k) κ_k` on `ℕ`, are nonnegative and log-concave without internal zeros. -/
theorem newton_product_LCNZ {ρ ν κ : ℕ → ℝ} (hρ : LCNZ ρ) (hν : LCNZ ν)
    (hκ : ∀ x, nval ρ x * nval ν x = nval κ x) : LCNZ κ := …
```

(`kap ρ ν` is the Newton-coefficient sequence of the product; `kap_nat` gives its natural-number form with `Hn k i j = C(k,i) C(i,k-j)` for `j ≤ k`.)

## Lean (new)

```lean
/-- `p_0, …, p_n` is ultra-log-concave of order `n`: `p_k / C(n,k)` (`k ≤ n`, extended by zero) is nonnegative and
log-concave without internal zeros. -/
def ULC (n : ℕ) (p : ℕ → ℝ) : Prop := LCNZ (fun k => if k ≤ n then p k / (n.choose k : ℝ) else 0)

/-- The law of `|S|`. -/
noncomputable def cardLaw {n : ℕ} (pS : Finset (Fin n) → ℝ) (i : ℕ) : ℝ := ∑ A ∈ powersetCard i univ, pS A

/-- The law of `|S ∪ T|` for independent `S`, `T`. -/
noncomputable def unionLaw {n : ℕ} (pS pT : Finset (Fin n) → ℝ) (k : ℕ) : ℝ :=
  ∑ A : Finset (Fin n), ∑ B : Finset (Fin n), if (A ∪ B).card = k then pS A * pT B else 0

/-- The law of `|S ∪ T|` for independent `S`, `T`. -/
noncomputable def unionLaw {n : ℕ} (pS pT : Finset (Fin n) → ℝ) (k : ℕ) : ℝ :=
  ∑ A : Finset (Fin n), ∑ B : Finset (Fin n), if (A ∪ B).card = k then pS A * pT B else 0

/-! ### Exchangeable laws depend only on the cardinality -/

theorem perm_invariant_card {n : ℕ} (p : Finset (Fin n) → ℝ)
    (hp : ∀ (σ : Equiv.Perm (Fin n)) (A : Finset (Fin n)), p (A.map σ.toEmbedding) = p A)
    (A B : Finset (Fin n)) (h : A.card = B.card) : p A = p B := …

/-- **The law of `|S ∪ T|`.** For exchangeable laws `Pr(S = A) = ρ_{|A|}`, `Pr(T = B) = ν_{|B|}` on `[n]`,
`Pr(|S ∪ T| = k) = C(n,k) κ_k` for `k ≤ n`, where `κ = kap ρ ν` are the Newton coefficients of the product of the
Newton series of `ρ` and `ν` (`nval_mul`). -/
theorem union_card_law (n : ℕ) (ρ ν : ℕ → ℝ) (k : ℕ) (hk : k ≤ n) :
    ∑ A : Finset (Fin n), ∑ B : Finset (Fin n), (if (A ∪ B).card = k then ρ A.card * ν B.card else 0) =
      (n.choose k : ℝ) * kap ρ ν k := …

/-- **Walkup's double-binomial convolution** `h_k = Σ_i Σ_r C(k,i) C(i,r) ρ_i ν_{k-r}` is `κ_k = kap ρ ν k`
(substitute `j = k - r`). -/
theorem walkup_convolution (ρ ν : ℕ → ℝ) (k : ℕ) :
    ∑ i ∈ range (k + 1), ∑ r ∈ range (i + 1), (k.choose i : ℝ) * (i.choose r : ℝ) * ρ i * ν (k - r) =
      kap ρ ν k := …

/-- **P2, after Proposition 4.3 (random sets, Walkup's Theorem 4 for two sets).** Let `S`, `T` be independent
random subsets of `[n]` whose laws `pS`, `pT` are invariant under permutations, and whose cardinalities are
ultra-log-concave of order `n`. Then `|S ∪ T|` is ultra-log-concave of order `n`. (Nonnegativity of the laws is
implied by the ultra-log-concavity of the cardinalities and is not assumed separately.) -/
theorem random_sets_ulc (n : ℕ) (pS pT : Finset (Fin n) → ℝ)
    (hSinv : ∀ (σ : Equiv.Perm (Fin n)) (A : Finset (Fin n)), pS (A.map σ.toEmbedding) = pS A)
    (hTinv : ∀ (σ : Equiv.Perm (Fin n)) (B : Finset (Fin n)), pT (B.map σ.toEmbedding) = pT B)
    (hSulc : ULC n (cardLaw pS)) (hTulc : ULC n (cardLaw pT)) : ULC n (unionLaw pS pT) := …
```

Notes. (a) A law of a random subset of `[n]` is a function on `Finset (Fin n)`; independence means the joint law of `(S, T)` is the product, as in `unionLaw`. (b) `ULC n p`: `p_k / C(n,k)` for `k ≤ n`, extended by zero, is log-concave without internal zeros; with `Pr(S = A) = ρ_{|A|}`, `|S|` has law `C(n,i) ρ_i`, so `ULC n (cardLaw pS)` is `LCNZ` of `ρ` (extended by zero beyond `n`), the hypothesis of Proposition 4.3. (c) Total mass one is not assumed; nonnegativity of the laws follows from the ULC hypotheses.

## P2 changes at f199058

New table row:

After Proposition~\ref{prop:np}: the law of $|S\cup T|$, ultra-log-concavity of $|S\cup T|$, and the double-binomial convolution $h_k=\kappa_k$ & \path{Szkraw.RandomSets.union_card_law}, \path{Szkraw.RandomSets.random_sets_ulc}, \path{Szkraw.RandomSets.walkup_convolution}

Not-formalized paragraph (the first item was "the random-set interpretation after Proposition~\ref{prop:np} and its identification with Walkup's formulation, a probabilistic reading of an attributed result;"):

Not formalized: the identification of the random-set reading after Proposition~\ref{prop:np} with Walkup's formulation (his conditionally uniform random sets and their fundamental sequences), which concerns the literature; the reported failure of \path{runs/cubic/bdetour_u.py} at $u=9/5$, which concerns one certificate search, not property (P); and, in Section~\ref{sec:open}, the sampled tests of cubic ratios and of the resummed operator, which are numerical evidence over finitely many arrays.

Questions: (1) Do `union_card_law` and `random_sets_ulc` (with `perm_invariant_card`) formalize "if $S$ and $T$ are independent random subsets of $[n]$ whose laws are invariant under permutations and whose cardinalities are ultra-log-concave of order $n$, then so is $|S\cup T|$, since $\Pr(|S\cup T|=k)=\binom nk\kappa_k$"? (2) Does `walkup_convolution` formalize "the double-binomial convolution $h_k=\ldots$, which is $\kappa_k$ after the substitution $j=k-r$"? (3) Are the table row and the changed not-formalized item accurate?

Answer per item, then an overall verdict (PASS / PASS WITH MINOR FIXES / FAIL).
