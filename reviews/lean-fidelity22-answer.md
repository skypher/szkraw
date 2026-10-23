## Lean statement — MATCH

`lc_violation_holds` matches the specified **property (P) plus failure of log-concavity** claim. It covers exactly \(N\in\{6,8,10,12\}\) and every real \(0<r\le1\), asserts existence of an admissible array, and gives the conclusions for every admissible array with the prescribed ratio and profile. The existential clause prevents vacuity. Admissibility and the profile identity force the intended formulas for \(a_i,b_i,c_i\). [1]

Normalization causes no mismatch. Writing \(\widehat\nu_k=\Delta^k(D/D(N))(0)\), the supplied formula for \(D\) gives
\[
\widehat\nu_1=\frac1{D(N)},\qquad
\widehat\nu_k=\frac{10^{-k}}{D(N)}\quad(2\le k\le N).
\]
Consequently, \(\widehat\nu_2>0\) and
\[
\widehat\nu_1\widehat\nu_3=10\widehat\nu_2^2>\widehat\nu_2^2.
\]
Thus this is genuinely a failed log-concavity inequality, not merely failure of the “no internal zeros” condition. The other applicable inequalities hold with equality.

The qualification is that **polynomial dependence and nonnegative Bernstein coefficients are not conclusions of the exported theorem**; its positivity conclusion is `MatrixPositivity v`. [1]

## 1. P1 Lean table — MATCH

The row accurately associates the positive and previously accepted negative examples with their respective declarations. It does not overstate the positive theorem’s conclusion. No replacement needed. [1]

## 2. P1 paragraph — MISMATCH: statement-level attribution

Placing “machine-verified as `Szkraw.lc_violation_holds`” directly after the Bernstein assertion presents that stronger assertion as the named theorem’s conclusion. The supplied certificate description supports the proof-method claim, but the theorem statement itself exports property (P), not a Bernstein representation. Move the attribution to property (P). [1]

**Exact replacement for the full third sentence:**

```latex
For $\mu=\frac1{10}$ and $q=\frac{11}{10}$, the constant-ratio arrays with profile $d_i=D(i)/D(N)$ have property (P) for every $r\in(0,1]$ and $N\in\{6,8,10,12\}$ (machine-verified as \path{Szkraw.lc_violation_holds}). Every coefficient $g(m,n;k)$ is a polynomial in $r$ with nonnegative Bernstein coefficients (\path{runs/sharp/lc_violation_cert.py}).
```

## 3. `papers/FORMALIZATION.md` — MISMATCH: minor coefficient-normalization wording

The summary of the theorem’s hypotheses and conclusions matches. The phrase “computes the Bernstein coefficients … scaled by a positive constant” needs qualification: `evH` uses the **unnormalized** basis \(r^e(1-r)^{m-e}\), whereas the standard Bernstein basis includes \(\binom me\). The source description itself notes these binomial factors. [1]

For the supplied certificate
\[
S_m g(m,n;k)=\sum_{e=0}^{m}H_e r^e(1-r)^{m-e},
\]
the degree-\(m\) Bernstein coefficients of \(g\) are
\[
\beta_e=\frac{H_e}{S_m\binom me}.
\]
Their signs agree with those of \(H_e\), but the normalization involves an index-dependent binomial factor in addition to the common positive scale \(S_m\).

**Replace only the proof-description sentence with:**

```latex
The proof of \path{Szkraw.lc_violation_holds} computes, by an exact integer recurrence, the integer coefficients $H_e$ in a representation $S_m g(m,n;k)=\sum_{e=0}^{m}H_e r^e(1-r)^{m-e}$, where $S_m>0$, and checks their nonnegativity in the Lean kernel (\verb|decide +kernel|). The corresponding degree-$m$ Bernstein coefficients of $g(m,n;k)$ are $H_e/(S_m\binom{m}{e})$, hence are nonnegative.
```

The remainder of the proposed replacement can stand.

## Overall verdict — PASS WITH MINOR FIXES

No change to the Lean theorem statement is needed for the specified positivity/non-log-concavity claim. Move the machine-verification attribution to that conclusion and make the Bernstein normalization explicit.

Sources:
[1] szkraw/lean/Szkraw/LCViolationPos.lean at 1fb1d1e8145d686205bc633bedd3fbd4fa0c34e0 · skypher/szkraw · GitHub — https://github.com/skypher/szkraw/blob/1fb1d1e/lean/Szkraw/LCViolationPos.lean

