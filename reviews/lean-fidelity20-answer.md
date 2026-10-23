**1. MATCH — P2: `affine_linear_quadratic`.** `QuadHyp` contains exactly the quadratic representations, sign conditions and monotonicity required. Here \(\kappa_2=2\kappa/N^2\), \(\beta_2=-\kappa_2\). The hypothesis `hb` is already assumed in Theorem 4.1; omitting admissibility and restrictions on \(r\) weakens the Lean hypotheses. Proposed change **1** is accurate. [1][2]

**2. MATCH — P1: `lc_violation_fails`.** The statement specifies the correct normalized profile on \(0\le i\le6\), admissibility, \(r=1\), the Newton identity, and \(g(6,6;6)<0\), additionally concluding failure of matrix positivity. Normalizing \(D\) scales every Newton coefficient equally, preserving the factor \(100\). It does **not** formalize the positive \(\mu=1/10\) example. Proposed change **2’s new row** accurately limits its scope. [3]

**3. MATCH — P1/P3: `krawtchouk_range_sharp`.** The geometric parameter is correctly \(p=(1-p_0)/p_0=1/r\), with \(q=1\). The statement gives the specified coefficient and strict negativity for every \(N\ge1\), including \(N=1\), and additionally concludes failure of matrix positivity. The intermediate identification with \(b_1\) follows from the coefficient definitions. Proposed changes **2’s Corollary 3.6 addition** and **3** are accurate. [4][3]

**4. MATCH — proposed `FORMALIZATION.md` changes.** The replacements accurately describe the new coverage. The exact-arithmetic attribution for the positive example is supported by archived `CERTIFIED` outputs for all four specified sizes; it remains distinct from Lean formalization. [5][6]

**Minor documentation fixes:** `productMatrix_one` itself **MATCHES**, but its docstring **MISMATCHES** the indexing convention: replace `g(1,1;i) = b_i` with **`g(1,i;i) = b_i`**. Also qualify the `sharpD` docstring as **“equals \(D(i)/D(6)\) for \(0\le i\le6\), extended by \(1\) for \(i>6\)”**; its unrestricted definition is not the displayed formula beyond the finite array. [3]

**Overall: PASS WITH MINOR FIXES.** No theorem-statement changes are needed.

Sources:
[1] https://raw.githubusercontent.com/skypher/szkraw/f2bd5d5/lean/Szkraw/VRCorollaries.lean
[2] https://raw.githubusercontent.com/skypher/szkraw/f2bd5d5/paper.tex
[3] https://raw.githubusercontent.com/skypher/szkraw/f2bd5d5/lean/Szkraw/LateRemarks.lean
[4] https://raw.githubusercontent.com/skypher/szkraw/f2bd5d5/lean/Szkraw/Krawtchouk.lean
[5] szkraw/papers/FORMALIZATION.md at f2bd5d5085c46d7eadc234dc8b644ec4ab01a08d · skypher/szkraw · GitHub — https://github.com/skypher/szkraw/blob/f2bd5d5/papers/FORMALIZATION.md
[6] https://raw.githubusercontent.com/skypher/szkraw/f2bd5d5/runs/sharp/RESULTS.md

