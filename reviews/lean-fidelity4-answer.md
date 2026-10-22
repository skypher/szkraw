Write \(D=m+n-k\) for the **signed** difference.

| Paper claim | Lean declaration | Assessment | Reason |
|---|---|---|---|
| Profile and Newton hypotheses | `LCProfile`, `LogConcaveNoInternalZeros` | MATCH | Paper hypotheses imply these hypotheses. Positivity of \(\nu_1\), nonnegativity, and forward propagation of zeros encode the required initial-interval support. Log-concavity has exactly the stated index range. |
| Two-parameter polynomial with nonnegative coefficients; vanishing for \(D<0\) | `lc_twoParam` | MATCH | `∃ h` precedes `∀ x y`, so coefficients are parameter-independent. For \(D\ge0\), the range and exponents are exact. For \(D<0\), truncated subtraction produces one summand, but the explicit condition forces every `h j` to zero. All-real parameter validity is stronger. |
| Nonnegative Bernstein coefficients and their displayed formula | `lc_bernstein` | MATCH, SCOPE NOTED | For \(D\ge0\), this states the correct unnormalized Bernstein expansion, with coefficients independent of `r`. The explicit relation to `h` is not separately stated, but follows from `lc_twoParam` and uniqueness of Bernstein coordinates. For \(D<0\), vanishing is supplied by `lc_twoParam`, not asserted independently here. |
| Application to every array of Theorem 8.1 | `constantRatio_twoParam` | MATCH, SCOPE NOTED | Establishes `LCProfile` and equality of every relevant product matrix. Omitting `r ≤ 1` weakens the hypotheses, which is acceptable. It does not assert equality of the coefficient functions at indices beyond \(N\); those are outside the paper’s arrays. |
| \(g(N,N;N)=(1-r)^N\) for \(K_{N,r}\) | `corner_value` | MATCH | Exact array, parameter restrictions, \(N\ge1\), matrix entry, and exponent. |
| Remark’s formalization scope | Remark scope sentence and table entry | MATCH, SCOPE NOTED | All-real identities and Bernstein normalization are accurately described. “Identifies the arrays” is valid for the finite arrays and their product matrices, not arbitrary function tails. |
| Lemma 9.1’s formalization scope | Corner-value table entry and final exclusion sentence | MATCH | Correctly includes Lemma 9.1 and excludes the remaining results of Section 9. |

For clarity, the coefficient formula follows from the two identities: for \(0\le s\le D\),
\[
B_s=\sum_{\substack{0\le j\le\lfloor D/2\rfloor\\j\le s\le2j}}
h_j\binom{j}{s-j}.
\]
Thus the paper’s normalized Bernstein coefficient is \(B_s/\binom Ds\). There is **no missing mathematical coverage in the combined remark declarations**.

### Exact fixes

One documentation correction: the `twoParam` docstring uses `y` both as the recurrence variable and as a parameter. Replace it with:
```lean
/-- The array `z p_i = (1 - d_i) p_{i+1} + x d_i p_i + y d_i p_{i-1}`. -/
```

No Lean proposition or paper scope correction is required. Claims about proof structure, compilation, and the axiom audit are outside this statement-only review.

**Overall verdict: PASS WITH MINOR FIXES — documentation only.**
