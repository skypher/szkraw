## PASS WITH MINOR FIXES

No substantive algebraic error found. **Execution limitation:** runs used locally transcribed source retrieved at `911524a`, not a byte-verified checkout; repository cloning failed. No Lean rebuild was performed.

### Issues and exact replacements

1. **State denominator positivity.** In step (vi), replace “whose numerator has nonnegative coefficients” with:
   > whose numerator has nonnegative coefficients and whose denominator is strictly positive for \(p,k\geq0\).

   In the \(\Phi^{\mathrm{loc}}_3\) paragraph, replace “the numerators in \((p,k)\) have nonnegative coefficients” with:
   > the numerators in \((p,k)\) have nonnegative coefficients and the denominators are strictly positive for \(p,k\geq0\).

   The denominators checked satisfy this. [1][2]

2. **Correct the quadratic-term description.** Replace:
   > Bounding the only term quadratic in \(u_0\),

   with:
   > Bounding the only negative term quadratic in \(u_0\),

   Indeed, the exact remainder is
   \[
   u_1\Phi^{\mathrm{loc}}_3-u_1A-u_0B
   =4\binom{a-1}{2}u_0(u_1H_*^+-u_0H_*)
     +\binom a3u_0^2u_1.
   \]
   Thus the stated bound is correct. [3]

3. **Distinguish generator checks from Lean identity checks.** Replace the sentence following the detour-proof bullets with:
   > The scripts \path{runs/lean_plan/gen_cubicB.py} and \path{runs/lean_plan/gen_cubicE.py} check every tail-coefficient sign in exact rational arithmetic and generate the Lean certificates; Lean checks the certificate identities.

   This matches their actual division of work. [4][5]

4. **Complete the \(7/4\) remark’s boundary coverage and attribution.** Replace “There the coefficient forms are certified” with:
   > There the modified coefficient \(\kappa_{t\tau}+\frac74\kappa_{r\sigma}\) is certified

   After that sentence insert:
   > The relevant expressions are affine in \(z\), so these boundary regimes cover the admissible interval for \(q>0\). When \(q=0\), all \(u_k\) with \(k\geq2\) vanish, and the inequality follows directly. For \eqref{eq:cubic-corner}, with \(u_0=0\), the modified tail sums are also nonnegative. Here \path{runs/cubic/bdetour_u.py} supplies the small-\(n\) \(B\) certificate; \path{runs/cubic/edetour_u.py} separately certifies \(E\).

   The older scripts check the modified mixed coefficient, not all coefficients anew. [6][7]

### Independently checked

- **Theorem 5.5:** \(Q_s\) domination, edge-pair counting, and small-window coverage. `edge_exact.py 60` has no failures in the applicable ranges; its reported exceptions are precisely \(R_2\) at \(a=3,4,5\) and \(K_a\) at \(a=3,4\). `forms_iii_v.py` passed; `window_cert.py` certified all **11** windows exactly.
- **Detours:** the quadratic subform and Abel-tail identity; all **six B-generator cases** and **five E-generator cases** passed.
- **Cubic key:** backward-difference and reindexing identities, admissibility of \(\alpha'\), and the exact \(\Phi_3\)-to-\(A,B\) reduction. `phi3_edge.py 40` and `phi3_generic.py` passed; small-index shifted coefficients and denominator positivity were also checked.
- **\(7/4\):** `bdetour_u.py 7/4` passed **51 checks**; `edetour_u.py 3 7/4` passed **18 checks**. Independent modified-tail checks passed for generic B, every E case, and the corner (**7 nonzero tails**). Small-B transfer certificates fail, confirming the need for the regime argument. `bdetour_u.py 9/5` fails as stated—**certificate failure, not a counterexample**.
- Compared the relevant Lean definitions and reductions with the printed expressions; did not repeat the Lean build or axiom audit.

[Execution record and independent-check results](sandbox:/mnt/data/review28/review28_checks.txt)

Sources:
[1] https://raw.githubusercontent.com/skypher/szkraw/911524a/runs/lean_plan/forms_iii_v.py
[2] https://raw.githubusercontent.com/skypher/szkraw/911524a/runs/lean_plan/phi3_generic.py
[3] https://raw.githubusercontent.com/skypher/szkraw/911524a/lean/Szkraw/CubicKeyForms.lean
[4] https://raw.githubusercontent.com/skypher/szkraw/911524a/runs/lean_plan/gen_cubicB.py
[5] https://raw.githubusercontent.com/skypher/szkraw/911524a/runs/lean_plan/gen_cubicE.py
[6] https://raw.githubusercontent.com/skypher/szkraw/911524a/runs/cubic/bdetour_u.py
[7] https://raw.githubusercontent.com/skypher/szkraw/911524a/runs/cubic/edetour_u.py

