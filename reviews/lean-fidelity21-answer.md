## Lean statement — MATCH

`CubicRatioHyp74` changes exactly the bound \(r\sigma\le t\tau\) to \(r\sigma\le\frac74t\tau\). Here `7 / 4` is real division, not natural-number division. All other hypotheses, index ranges, and the `MatrixPositivity` conclusion remain unchanged. Under the accepted conventions, setting \(d=b+c\) recovers \(b=(1-\rho)d\) from \(c=\rho d\), and admissibility gives \(a=1-d\). No small-\(n\), geometric-profile, or boundary-regime restriction appears in the public statement. [1]

The original statement remains a consequence: \(t,\tau\ge0\) gives \(t\tau\le\frac74t\tau\). The original declaration retains its original type and invokes the extended declaration. [1]

## Proposed changes

**1. P2 Lean table — MATCH.**  
The new row correctly identifies the remark’s extension with `Szkraw.cubic_ratio74_matrix`, while retaining `Szkraw.cubic_ratio_matrix` for the original theorem. [1]

**2. P2 introduction — MATCH.**  
The added machine-verification claim is supported by the extended declaration and the checked-in audit. The audit’s final line records `Szkraw.cubic_ratio74_matrix` with only `propext`, `Classical.choice`, and `Quot.sound`. The existing claims about Theorems 5.5 and 5.6 are unchanged. [2]

**3. P2 disclosure — MATCH.**  
Replacing the statement that the extension is not machine-verified is accurate. The revised sentence identifies the extension specifically; it does not claim that every assertion or diagnostic in the surrounding remark is formalized. [2]

**4. P2 remark insertion — MATCH.**  
The certificate description matches the referenced generators: for the modified small-\(n\) coefficient, they use transfers, products, and \(u_j(\ell u_1-u_0)\), rather than the \(u_0=zu_1\) substitution. The general branch multiplies the coefficient by a positive polynomial and uses multipliers with nonnegative coefficients after shifting \(\ell\); smaller values receive separate exact rational certificates. The proposed text correctly includes both the positive scaling and the exceptional smaller values. [3][4]

**5. `papers/FORMALIZATION.md` — MATCH.**  
The table row, relaxed-bound description, and assertion that the original theorem is derived from the extension are accurate. “Multipliers polynomial in \(\ell\)” correctly describes the **scaled certificate identities** detailed in item 4; it need not mean that the unscaled coefficient has polynomial rather than rational multipliers. The use of `\path` and `\eqref` also follows the existing notes section’s LaTeX-source convention. [1][3][5]

## Overall verdict — PASS

No replacement text is required.

Sources:
[1] https://raw.githubusercontent.com/skypher/szkraw/7086f41/lean/Szkraw/CubicMain.lean
[2] https://raw.githubusercontent.com/skypher/szkraw/7086f41/lean/axioms.log
[3] https://raw.githubusercontent.com/skypher/szkraw/7086f41/runs/lean_plan/cert74.py
[4] https://raw.githubusercontent.com/skypher/szkraw/7086f41/runs/lean_plan/gen_cubicB.py
[5] https://raw.githubusercontent.com/skypher/szkraw/7086f41/papers/FORMALIZATION.md

