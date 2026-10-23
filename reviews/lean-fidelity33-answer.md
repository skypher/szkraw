## 1. `lambda_values` — **MATCH**

The quantified triples are exactly the paper’s \(\mathcal Z_N\): `Fin (N+1)` supplies \(0\le m,n,k\le N\), `Triangle` supplies the triangle inequalities, and the equality to zero selects the vanishing coefficients of \(K_{N,1}\). The definitions of \(A\) and \(B\) have the correct derivative directions and signs. [1][2]

The two clauses characterize the stated maximum: every eligible ratio has positive denominator and is bounded above, and an eligible ratio attains the bound. The witness’s denominator positivity follows from the first clause. Since every listed bound is positive, adjoining \(\{0\}\) does not change the maximum. This identifies the paper’s maximum, **not** the separately defined sum `lamN`. No replacement needed.

## 2. `topmass_rates`, `normK`, and `normalized_direction` — **MATCH**

`topmass_rates` states precisely the two fixed-coordinate derivatives for **lowering** the top mass at \(r=1\). Its broader index quantification does not omit or alter the paper’s relevant indices. [2]

For \(y=sx+t\), the recurrence coefficients transform as
\[
(a,b,c)\longmapsto(sa,\;sb+t,\;sc).
\]
Thus `normK` uses exactly \(s=1-\varepsilon,\ t=\varepsilon\). The product-matrix equality expresses invariance of every product coefficient; `ε ≠ 1` is the required nonsingularity condition. The remaining clauses state the restored initial normalization, row sums, reference array, and all three displayed derivatives. [3][2]

The scope is correctly **the top-mass direction at fixed \(r=1\)**, not the combined derivative along \(r=1-\Lambda\varepsilon\). The unrestricted algebraic identities in \(\varepsilon\) do not assert that every such parameter gives a positive orthogonality measure. No replacement needed.

## 3. `direction_not_uniform` — **MATCH at the symmetric endpoint; MISMATCH for the full later raising remark**

For the displayed normalized direction and its negative, the statement matches Definition 9.3. The ranges \(1\le n<N\) for \(b\) and \(1\le n\le N\) for \(c\) are exact. Using functions on \(\mathbb R\), rather than \([0,1]\), is harmless: only arguments in \([0,1]\) are tested, and interval functions can be extended. The definition imposes no regularity requirement. [4][2]

Consequently, \(\sigma=-1\) correctly covers **raising by an additive mass parameter at \(K_{N,1}\)**.

However, the later raising remark occurs in a paragraph discussing **fixed \(0<r<1\)**. `direction_not_uniform` has no \(r\)-parameter and does not establish that broader claim. Moreover, the referenced raising construction uses a relative increase \(\tau\), corresponding to additive mass \(\tau w_0\); an \(N\)-dependent reparameterization is not automatically covered by negating the displayed direction. [4][5]

No change to the Lean statement is required. The documentation must retain this scope distinction.

## 4. New P3 table row and shortened not-formalized paragraph

**Table row — MATCH**, as a mapping of the claims following Proposition 9.8. All four declarations correspond to the listed endpoint results. It should not be read as covering arbitrary fixed-\(r\) raising non-uniformity. [4]

**Shortened paragraph — MISMATCH by omission**, insofar as it removes the non-uniform-rule caveat for the later fixed-\(r\) raising remark as well. Removing the computed maxima, displayed endpoint derivatives, and endpoint non-uniformity from the unformalized list is justified; removing the broader raising observation is not justified by these statements. [4][2]

**Exact fix:** append this sentence immediately after the sentence listing the remaining unformalized material in `Section~\ref{sec:limits}`:

```latex
The non-uniformity assertion for the raising deformation at fixed $0<r<1$ also remains unformalized; \path{Szkraw.direction_not_uniform} establishes non-uniformity of the additive-mass lowering and raising directions at $r=1$.
```

The repeated `normK` and `normalized_direction` blocks in the supplied excerpt are not duplicated in the pinned source, so they require no repository edit. [2]

## Overall verdict: **PASS WITH MINOR FIXES**

The new endpoint statements faithfully express the maxima, rates, normalization, and non-uniformity claims. The required fix is documentary: preserve the distinction between raising at \(r=1\) and the later raising remark at fixed \(0<r<1\).

Sources:
[1] https://raw.githubusercontent.com/skypher/szkraw/077e5e5/lean/Szkraw/Statements.lean
[2] https://raw.githubusercontent.com/skypher/szkraw/077e5e5/lean/Szkraw/LambdaN.lean
[3] https://raw.githubusercontent.com/skypher/szkraw/077e5e5/lean/Szkraw/AffineInvariance.lean
[4] https://raw.githubusercontent.com/skypher/szkraw/077e5e5/papers/p3.tex
[5] https://raw.githubusercontent.com/skypher/szkraw/077e5e5/lean/Szkraw/RaiseTopMass.lean

