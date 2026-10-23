# PASS WITH MINOR FIXES

**The \(7/4\) extension and the four stated all-\(r\) examples are justified.** The defects below do not invalidate those results.

## Defects and exact fixes

1. **The sharpness checker’s fallback is not exact.** In `lc_violation_cert.py:45–55`, the empty-generator condition does nothing; sorting roots as floats and rounding their midpoints can miss a negative interval. I reproduced a false certificate using
   \[
   P(r)=(r-\tfrac12-10^{-60})(r-\tfrac12-2\cdot10^{-60}).
   \]
   **Fix:** return `CERTIFIED` only when `nonbern == 0`; otherwise return `FAILS` for an exact negative witness, or `INCONCLUSIVE`. Remove the “exact/Sturm” description unless certified root isolation replaces the fallback. **All four positive examples have `nonbern == 0`, so they are unaffected.** [1]

2. **Qualify the grid report.** `r1_grid.py` uses float64 screening, confirms at most twenty selected candidates at 60 digits, and searches a broader one-jump family; only \(K=2\) is the displayed mixture family. `r1_trend.py` stops at the first successful supplied exponent, not necessarily the smallest unless the list is ordered. **Fix:** describe these as “float64 screening with high-precision confirmation, and high-precision searches in the \(K=2\) subfamily”; archive the parameter lists and outputs; sort the exponent list. Replace “failures occur only in narrow windows” with “the observed failures lay in narrow windows on the tested grids.” Correct the corresponding script descriptions. [2][3]  
   Also clarify that “\(N\le30\)” means a pooled minimum among tested sizes: the research notes give \(10^{5/2}\), not \(10^2\), for \(N=4\). The large-\(N\) grid minima were **not independently rerun** here. [4]

3. **Specify the control’s \(r\), and define the open problem’s factor.** Add **“at \(r=1\)”** to the \(\mu=1/100,\ N=6\) example. Independently,
   \[
   g(6,6;6)=
   -\frac{11421689396209222100480371}
   {11282159504913398311706203653864919}<0.
   \]
   For the quantity actually probed, replace “admissible factor” by
   \[
   V_N=\inf\{\mu^{-1}:0<\mu<1,\ q>1,\ 
   (d^{\mu,q},r=1)\text{ fails (P)}\},
   \]
   with \(\inf\varnothing=\infty\), and ask whether \(V_N\to1\). This avoids presupposing monotonicity in the violation factor. [5]

4. **A stale corner-script comment remains.** `corner_cert.py:5` still says only \(\kappa_{t\sigma}\) can be negative. **Fix:** use the corrected paper wording: “Only \(\kappa_{t\sigma}\) requires an additional check; the quadratic block and existing trade estimates handle the other terms.” The paper itself correctly applies round-25 fix 4. [6]

5. **The code citation is obsolete.** `\bibitem{code}` still pins `e65b421`, which lacks the new certificate scripts. **Fix:** update the revision and tree URL to `19b034643c28286612478a33b67755a8dd4b364f`, or an immutable later revision containing the adopted corrections. [5][7][8]

## Independent checks

**Round 25:** all five fixes are correctly applied in the paper: cutoff \(2\), not \(1\); correct B endpoint/cubic reduction and separate normalization; deletion of the false limit; corrected corner bookkeeping; and continuity for zero tails preserving \(u_0=0\). [9][5]

**Extension:** the proposed sufficient conditions are correct. When \(\kappa_{r\sigma}<0\),
\[
\kappa_{t\tau}t\tau+\kappa_{r\sigma}r\sigma
\ge(\kappa_{t\tau}+u\kappa_{r\sigma})t\tau;
\]
otherwise use \(\kappa_{t\tau}\ge0\).

The corner inherits the combined B-coefficient check at \((0,2)\), plus its nonnegative added form and separate \(t\sigma\) repair. The \(t=\sigma=0\) B block is inherited **as a whole** from Theorem 8.11. The polarization bound for (8.13) requires no trade. Thus no additional restriction prevents the extension. [5]

Coverage matches the baseline: B has symbolic \(n\ge6\), separate \(4,5\), exact \(2,3\); E has symbolic \(n\ge5\), exact \(3,4\). Both cover the small-\(\ell\) cases, both \(z\)-regimes, nonlinear-\(z\) Bernstein checks, and boundary limits. [10][11]

| Check | Result |
|---|---|
| Baseline B / E | 349 / 124 checks pass |
| B at \(u=7/4\) | 51 checks pass |
| E at constant \(3,\ u=7/4\) | 18 checks pass |
| B at \(u=9/5\) | Certificate rejects; not a theorem counterexample |
| \(\mu=1/10,\ q=11/10,\ N=6,8,10,12\) | All Bernstein coefficients nonnegative |
| Control \(\mu=1/100,\ N=6\) | Exact negative \(g(6,6;6)\) at \(r=1\) |

I additionally reconstructed **330 polarized coefficient expressions by direct forward differences**, checked the corner independently, and recovered the geometric ratio limit \(2\). Independent multiplication modulo the terminal polynomial matched **13,800 exact entries**, including products beyond terminal degree.

The sharpness recurrence matches `probe.py`: it divides only by \(r\)-independent \(a_m>0\), \(m<N\), so every entry is in \(\mathbb Q[r]\). The Bernstein conversion is correct. The Newton coefficients and quotient \(1/\mu\) are also correct. [12][1]

The fixed-\(r\) radius statement follows from \(\rho_N(r)\le3(1-r^2)^N\) for sufficiently large \(N\); it does **not** establish pointwise necessity of log-concavity. The cubic open problem and disclosure correctly distinguish the new additions from round 25 and do not claim human or Lean verification. [5]

## PDF citation audit and execution limits

PDF-verified: **Askey**, Part II Theorem 1/Corollary 1; **Koelink**, Theorems 3.1(ii)/7.8; **Miclo 2017**, Proposition 3.3; **Miclo 2015**, Proposition 6/Theorem 31; **Szwarc 2003**, Theorem 1; **Wang–Yeh**, Lemma 2.1/Corollary 2.6. [13]

**UNVERIFIED:** Eagleson 1969, Walkup 1976, and Szwarc’s Inzell survey: their original PDFs could not be opened.

**Execution caveat:** direct checkout was unavailable. Reruns used inspected, locally transcribed operative code—not a byte-verified checkout.

[Detailed review notes](sandbox:/mnt/data/round26/README.md) · [Code and execution logs](sandbox:/mnt/data/round26-checks.zip)

Sources:
[1] https://raw.githubusercontent.com/skypher/szkraw/19b0346/runs/sharp/lc_violation_cert.py
[2] https://raw.githubusercontent.com/skypher/szkraw/19b0346/runs/sharp/r1_grid.py
[3] https://raw.githubusercontent.com/skypher/szkraw/19b0346/runs/sharp/r1_trend.py
[4] https://raw.githubusercontent.com/skypher/szkraw/19b0346/RESEARCH.md
[5] https://raw.githubusercontent.com/skypher/szkraw/19b0346/paper.tex
[6] https://raw.githubusercontent.com/skypher/szkraw/19b0346/runs/cubic/corner_cert.py
[7] https://raw.githubusercontent.com/skypher/szkraw/e65b421f25cec90c8d4097363da80386592ce5ed/paper.tex
[8] https://github.com/skypher/szkraw/commit/19b0346.patch
[9] https://raw.githubusercontent.com/skypher/szkraw/19b0346/REVIEW.md
[10] https://raw.githubusercontent.com/skypher/szkraw/19b0346/runs/cubic/bdetour_u.py
[11] https://raw.githubusercontent.com/skypher/szkraw/19b0346/runs/cubic/edetour_u.py
[12] https://raw.githubusercontent.com/skypher/szkraw/19b0346/probe.py
[13] https://ir.cwi.nl/pub/7741/7741D.pdf
