# Independent review, round 22: Theorem 8.12, Corollary 8.13 (proofs and Lean fidelity), the cubic counterexample, and the new open-problem text

Repository: github.com/skypher/szkraw (paper.tex, lean/Szkraw/VRLowDegree.lean, lean/Szkraw/CubicRatioExample.lean, runs/varratio/). Section and equation numbers refer to paper.tex.

This round has three parts.

**Part 1, mathematics (check the proofs).** Theorem 8.12 and Corollary 8.13 are new and have not been reviewed. Check every step against the recurrence of the proof of Theorem 8.6 and the resummation of the proof of Theorem 8.9 (with H = 0, V_j = B̃_j). In particular check: (a) that f_n = 0 for n ≥ 3 makes every A^ψ_j with j ≥ 1 equal to −B̃_j on Ω and the C-moves of positive index vanish; (b) the two detours and the coefficient quotient jm(m−1)/(2(m−j−1)) ≥ 10; (c) that the resummation's key inequality is trivial with H = 0; (d) the Leibniz formula κ_k = k e_k and the displayed identity for e_k² − e_{k−1}e_{k+1}, the sign of every term, and the no-internal-zeros argument; (e) the claims in the example paragraph (exponential ratios; the sharpness remark; incomparability with Theorem 8.11). Independent exact checks are welcome (runs/varratio/thmQ_check.py is ours).

**Part 2, Lean fidelity (do not check Lean proofs; they compile, axiom audit clean).** For each Lean statement below decide whether it faithfully expresses the paper claim, under the acceptance rule of rounds 1–16: Lean hypotheses equivalent to or weaker than the paper's, Lean conclusion equivalent to or stronger. Where Lean covers less, check that the scope sentence discloses it. Also check the new Lean-table rows and the scope sentence.

**Part 3, text accuracy.** Check that the new open-problem text states exactly what the cited scripts establish (no overclaiming), and that the abstract sentence matches the theorems.

Conventions (unchanged): `Coefficients N` has fields a, b, c : ℕ → ℝ; `Admissible v` is (2.1); `MatrixPositivity v` is nonnegative linearization with `productMatrix v m n k = g(m,n;k)`; `profile v i = v.b i + v.c i`; `newtonCoeff x k = Σ_{i≤k} (−1)^(k−i) C(k,i) x_i`; `LogConcaveNoInternalZeros N ν` means ν_1 > 0, ν_k ≥ 0 and ν_{k−1}ν_{k+1} ≤ ν_k² on the range 1..N, and ν_k = 0 ⇒ ν_{k+1} = 0 for 1 ≤ k < N; `LCNZ ρ` means ρ ≥ 0, ρ_iρ_{i+2} ≤ ρ_{i+1}² for all i ≥ 0, and no internal zeros (0 < ρ_i, 0 < ρ_k, i ≤ j ≤ k ⇒ 0 < ρ_j).

Answer format: Part 1 — PASS / PASS WITH MINOR FIXES / FAIL with every defect and exact fix; Part 2 — a table (paper claim | Lean declaration | MATCH / MATCH, SCOPE NOTED / MISMATCH | reason); Part 3 — list of inaccuracies with exact fixes; overall verdict. Be terse.

## Paper text: Theorem 8.12, its proof, Corollary 8.13, its proof, and the remark

```latex
\paragraph{Ratios of higher degree.}
For profiles of Newton degree at most two the ratio can have any degree, provided the Newton coefficients of $c$ are log-concave; no key inequality is needed.

\begin{theorem}[Low-degree profiles]\label{thm:lc-lowdeg}
Let $d_i=\nu_1i+\nu_2\binom i2$ with $\nu_1>0$, $\nu_2\geq0$ and $d_N=1$, let $c_0=0$, and suppose that the Newton coefficients $\kappa_k=\Delta^kc(0)$, $1\leq k\leq N$, are log-concave without internal zeros. Put $a_i=1-d_i$ and $b_i=d_i-c_i$. If $b$ is nondecreasing, then the system has nonnegative linearization.
\end{theorem}

\begin{proof}
We use the recurrence of the proof of Theorem~\ref{thm:lc-vary}, which holds for every array, with $\varphi_n(\ell)=\Delta^nc(\ell)$, $\psi_n(\ell)=\Delta^nb(\ell)$ and $f_n(\ell)=\Delta^nd(\ell)$ for the polynomial extensions. Since $f_n=0$ for $n\geq3$, every move $A^\psi_j$ with $j\geq1$, which involves only $n\geq2j+1\geq3$, equals $-\widetilde B_j$ with $\widetilde B_j=W_{2j+1,j}$ formed from $\varphi$; the moves $C_j+C^\psi_j=W^f_{2j+2,j+1}$ vanish for $j\geq1$, and $C_0+C^\psi_0=\binom a2\nu_2\geq0$. The weight $A^\psi_0(\ell,a)=b_{\ell+a}-b_\ell$ is nonnegative on $\Omega$, as are the straight weights and all $B_j$ and $\widetilde B_j$, since $(\varphi_n(\ell))_n$ is obtained from $(\kappa_k)$ by the shifts of Lemma~\ref{lem:lc-ineq} and is therefore nonnegative and log-concave without internal zeros. Lemma~\ref{lem:lc-ineq} for $\varphi$ gives, as in Lemma~\ref{lem:detours}, $B_0(\ell,a)B_{j-1}(\ell+1,a-2)\geq4c_{\ell+1}B_j(\ell,a)$ for $j\geq1$, and with $B_0(\ell,a)\geq\binom a2\varphi_2(\ell)$ also $B_0(\ell,a)\widetilde B_{j-1}(\ell+1,a-2)\geq4c_{\ell+1}\widetilde B_j(\ell,a)$ for $j\geq2$, because the coefficient quotients $jm(m-1)/(2(m-j-1))$ on $m\geq2j+1$ are at least $10$. In the resummation of the proof of Theorem~\ref{thm:lc-affine} take $H=0$ and $V_j=\widetilde B_j$; the key inequality is then trivial, and $M\geq0$ gives (P).
\end{proof}

\begin{corollary}\label{cor:lc-lowdeg}
In Theorem~\ref{thm:lc-lowdeg} let $c_i=\rho(i)d_i$ with $\rho(x)=\sum_k\rho_k\binom xk$, where $(\rho_k)_{k\geq0}$ is nonnegative and log-concave without internal zeros and $\rho_0>0$. Then the Newton coefficients of $c$ are log-concave without internal zeros. Hence every such ratio, of any degree, with nondecreasing $b$ gives nonnegative linearization on these profiles.
\end{corollary}

\begin{proof}
Put $s_k=\rho_k+\rho_{k-1}$ ($\rho_{-1}=0$), which is log-concave without internal zeros, and $h=\nu_2/2$. The Leibniz rule gives $\kappa_k=ke_k$ for $k\geq1$, with $e_k=(\nu_1+h(k-1))s_k+h(k-1)s_{k-1}$. Write $\alpha=\nu_1+h(k-1)$ and $\beta=h(k-1)$; then
\[
\begin{aligned}
e_k^2-e_{k-1}e_{k+1}={}&\alpha^2(s_k^2-s_{k-1}s_{k+1})+\beta^2(s_{k-1}^2-s_{k-2}s_k)+(\beta-h)(\alpha+h)(s_{k-1}s_k-s_{k-2}s_{k+1})\\
&+h^2(s_{k-1}s_{k+1}+s_{k-2}s_k+2s_{k-1}s_k),
\end{aligned}
\]
and every term is nonnegative for $k\geq2$ by log-concavity of $s$. So $\kappa_k^2\geq k^2e_{k-1}e_{k+1}\geq\kappa_{k-1}\kappa_{k+1}$. If $\kappa_k=0$ with $k\geq1$, then $s_k=0$, so $\rho_k=0$; as $\rho_0>0$ and $\rho$ has no internal zeros, $\rho_m=0$ for $m\geq k$, and $\kappa_{k+1}=0$.
\end{proof}

For example, on the linear profile $d_i=i/N$ the exponential ratios $\rho(x)=r(1+\varepsilon)^x$, whose Newton coefficients $r\varepsilon^k$ are geometric, give nonnegative linearization whenever $b$ is nondecreasing. Log-concavity cannot be weakened to nonnegativity of the $\rho_k$: the cubic counterexample in Section~\ref{sec:open} has the linear profile $d_i=i/4$ and $\rho=(\frac{19}{20},0,0,\frac1{320})$, whose Newton coefficients have internal zeros. Theorem~\ref{thm:lc-quadratic} and Corollary~\ref{cor:lc-lowdeg} are not comparable: the former admits convex quadratic ratios with $t^2<r\tau$ on every log-concave Newton profile, the latter ratios of every degree on profiles of Newton degree at most two. The diagnostic \path{runs/varratio/thmQ_check.py} checks in exact arithmetic the formula $\kappa_k=ke_k$, the log-concavity of $\kappa$, Lemma~\ref{lem:lc-ineq} for $\varphi$, both detours, $M\geq0$ and (P) on random members with $3\leq N\leq10$, including geometric $(\rho_k)$.
```

## Paper text: the new part of the open problems (Section 10, first paragraph)

```latex
Theorem~\ref{thm:lc-quadratic} does not extend to cubic ratios: for $N=4$, $d_i=i/4$ and $\rho(x)=\frac{19}{20}+\binom x3/320$, whose Newton coefficients $(\frac{19}{20},0,0,\frac1{320})$ are nonnegative, $b=(0,\frac1{80},\frac1{40},\frac9{256},\frac3{80})$ is nondecreasing, but $g(4,4;4)=-14011/30720000$. A bound on $r$ alone does not restore (P) for cubic ratios: on linear profiles with $\kappa=1/80$, which keeps $b$ nondecreasing, $\rho_i=\frac9{10}+\kappa\binom i3/\binom N3$ gives $g(48,48;48)<0$ for $N=48$, and $\rho_i=\frac9{10}+\kappa(i/N)^3$ gives $g(64,64;63)<0$ for $N=64$. Steeper ratios fail at smaller $r$, again with nondecreasing $b$ and nonnegative Newton coefficients of $\rho$: $\rho_i=\frac12+10^{i-N}/100$ gives $g(40,40;40)<0$ for $N=40$, and raising only the last ratio, $\rho_i=r$ for $i<N$ and $\rho_N=r+(1-r)/N$, gives $g(40,40;38)<0$ for $r=\frac12$, $N=40$ and $g(120,120;119)<0$ for $r=\frac25$, $N=120$ (\path{runs/varratio/frontier_examples.py}). Write a cubic ratio as $\rho(x)=r+tx+\tau\binom x2+\sigma\binom x3$. The cubic examples above violate $r\sigma\leq t\tau$, a consequence of log-concavity of $(r,t,\tau,\sigma)$: in the first two $t=\tau=0$, and for $\kappa(i/N)^3$ one has $t\tau=6\kappa^2/N^6<r\sigma=6r\kappa/N^3$. In our exact searches, cubic ratios with $t,\tau,\sigma\geq0$, $r\sigma\leq u\,t\tau$ and nondecreasing $b$ on log-concave Newton profiles kept (P) for $u\leq64$, all tested $r\leq\frac{99}{100}$ and $N\leq18$, and in the coefficients $g(m,N;k)$ for $u\leq16$ and $N=24,32,48,64,96$ (\path{runs/varratio/cubic_lc_test.py}); the operator $M$ of the proof of Theorem~\ref{thm:lc-affine} remained nonnegative for $u\leq4$ and $N\leq13$, whereas for $t=\tau=0$ it has negative entries at every tested $r$. Decide whether $r\sigma\leq u\,t\tau$ suffices for some $u>0$. Corollary~\ref{cor:lc-lowdeg} admits ratios with log-concave Newton coefficients, of any degree, on profiles of Newton degree at most two. Decide whether the same holds on every log-concave Newton profile. In our exact searches ratios with nonnegative log-concave Newton coefficients, including the exponential ratios $r(1+\varepsilon)^x$, on log-concave Newton profiles with nondecreasing $b$ kept (P) for $N\leq16$ and $r\leq\frac{99}{100}$ (full tables), and in the coefficients $g(m,N;k)$ for $N=24$ and $40$, and the operator $M$ was nonnegative for $N\leq10$ (\path{runs/varratio/lcnewton_ratio_test.py}). The proof of Theorem~\ref{thm:lc-lowdeg} used the log-concavity of the Newton coefficients of $c=\rho d$; whether log-concavity of the Newton coefficients is preserved under pointwise products of sequences in general is open, and it held in $13000$ random exact trials with $N\leq16$ (\path{runs/varratio/newton_product_lc.py}). For profiles of higher degree the moves $H_j$ do not vanish, and a key inequality as in the proof of Theorem~\ref{thm:lc-affine} is needed.
```

## New abstract sentence

```latex
On profiles of Newton degree at most two, every ratio whose Newton coefficients are log-concave is admitted, in any degree; a cubic example shows that nonnegative Newton coefficients of the ratio do not suffice.
```

## New Lean-table rows and scope sentence

```latex
Theorem~\ref{thm:lc-lowdeg}: low-degree profiles & \path{Szkraw.lowdeg_matrix}\\[3pt]
Corollary~\ref{cor:lc-lowdeg}: log-concave ratios on low-degree profiles & \path{Szkraw.lowdeg_newton_lc}, \path{Szkraw.lowdeg_ratio_matrix}\\[3pt]
Section~\ref{sec:open}: the cubic counterexample with $N=4$ & \path{Szkraw.cubic_ratio_fails}\\[3pt]
```
Scope sentence: Theorem~\ref{thm:lc-lowdeg} is stated with the Newton coefficients $\kappa_1,\ldots,\kappa_N$ of $c$ log-concave without internal zeros; in Corollary~\ref{cor:lc-lowdeg} the ratio is $\rho(i)=\sum_{k\leq i}\binom ik\rho_k$ with $(\rho_k)$ nonnegative, log-concave and without internal zeros on all $k\geq0$, and $\rho_0>0$, and the Lean statement \path{Szkraw.lowdeg_newton_lc} gives the log-concavity of the Newton coefficients of $c$ as a separate conclusion.
Also changed: "In Section~\ref{sec:open} only the two counterexamples with $N=3$ and the cubic counterexample with $N=4$ are formalized; they are stated with all properties claimed for them, and the remaining computational statements there are not formalized."

## Lean statements

```lean
/-- Hypotheses of Theorem 8.12. -/
def LowDegHyp {N : ℕ} (vv : Coefficients N) : Prop :=
  ∃ ν1 ν2 : ℝ, 0 < ν1 ∧ 0 ≤ ν2 ∧
    (∀ i, i ≤ N → profile vv i = ν1 * i + ν2 * (i.choose 2 : ℝ)) ∧
    LogConcaveNoInternalZeros N (newtonCoeff vv.c) ∧
    (∀ i, i < N → vv.b i ≤ vv.b (i + 1))

/-- Theorem 8.12, matrix-positivity conclusion. -/
def Stmt_lowdeg : Prop :=
  ∀ (N : ℕ) (vv : Coefficients N), Admissible vv → LowDegHyp vv → MatrixPositivity vv

/-- **Theorem 8.12** (profiles of Newton degree at most two). -/
theorem lowdeg_matrix : Stmt_lowdeg  := ...

/-- Hypotheses of Corollary 8.13: a profile of Newton degree at most two and a ratio
`ρ(i) = Σ_k ρ_k C(i,k)` whose Newton coefficients `ρ_k` are nonnegative, log-concave and
without internal zeros, with `ρ_0 > 0`; `b` nondecreasing. -/
def LowDegRatioHyp {N : ℕ} (vv : Coefficients N) : Prop :=
  ∃ (ν1 ν2 : ℝ) (ρ : ℕ → ℝ), 0 < ν1 ∧ 0 ≤ ν2 ∧ LCNZ ρ ∧ 0 < ρ 0 ∧
    (∀ i, i ≤ N → profile vv i = ν1 * i + ν2 * (i.choose 2 : ℝ)) ∧
    (∀ i, i ≤ N → vv.c i = (∑ k ∈ range (i + 1), (i.choose k : ℝ) * ρ k) * profile vv i) ∧
    (∀ i, i < N → vv.b i ≤ vv.b (i + 1))

/-- Corollary 8.13, matrix-positivity conclusion. -/
def Stmt_lowdeg_ratio : Prop :=
  ∀ (N : ℕ) (vv : Coefficients N), Admissible vv → LowDegRatioHyp vv → MatrixPositivity vv

/-- **Lemma (NP), profiles of Newton degree at most two**: the Newton coefficients of `c` are
log-concave without internal zeros. -/
theorem lowdeg_newton_lc {N : ℕ} (vv : Coefficients N) (hv : Admissible vv) {ν1 ν2 : ℝ} {ρ : ℕ → ℝ}
    (h1 : 0 < ν1) (h2 : 0 ≤ ν2) (hρ : LCNZ ρ) (hρ0 : 0 < ρ 0)
    (hd : ∀ i, i ≤ N → profile vv i = ν1 * i + ν2 * (i.choose 2 : ℝ))
    (hc : ∀ i, i ≤ N → vv.c i = (∑ k ∈ range (i + 1), (i.choose k : ℝ) * ρ k) * profile vv i) :
    LogConcaveNoInternalZeros N (newtonCoeff vv.c)  := ...

/-- **Corollary 8.13**: on profiles of Newton degree at most two, every ratio whose Newton
coefficients are nonnegative, log-concave and without internal zeros, with nondecreasing `b`. -/
theorem lowdeg_ratio_matrix : Stmt_lowdeg_ratio  := ...
```

```lean
/-- `d_i = i/4`, `ρ = (19/20, 19/20, 19/20, 61/64, 77/80)`, i.e. `ρ(x) = 19/20 + C(x,3)/320`. -/
noncomputable def cubicEx : Coefficients 4 where
  a i := 1 - (i : ℝ) / 4
  b i := if i = 0 then 0 else if i = 1 then 1 / 80 else if i = 2 then 1 / 40 else if i = 3 then 9 / 256
    else 3 / 80
  c i := if i = 0 then 0 else if i = 1 then 19 / 80 else if i = 2 then 19 / 40 else if i = 3 then 183 / 256
    else 77 / 80

/-- **A cubic ratio fails.** The linear profile `d_i = i/4` (Newton coefficients `(1/4, 0, 0, 0)`,
log-concave without internal zeros) with the ratio `ρ(x) = 19/20 + C(x,3)/320`, whose Newton
coefficients `(19/20, 0, 0, 1/320)` are nonnegative, has nondecreasing `b` and `g(4,4;4) < 0`. -/
theorem cubic_ratio_fails :
    Admissible cubicEx ∧ (∀ i, i ≤ 4 → profile cubicEx i = (i : ℝ) / 4) ∧
      LogConcaveNoInternalZeros 4 (newtonCoeff (profile cubicEx)) ∧
      (∀ i, i ≤ 4 → cubicEx.c i = (19 / 20 + (i.choose 3 : ℝ) / 320) * profile cubicEx i) ∧
      (∀ i, i < 4 → cubicEx.b i ≤ cubicEx.b (i + 1)) ∧
      productMatrix cubicEx 4 4 4 = -14011 / 30720000 ∧ ¬ MatrixPositivity cubicEx := ...
```
