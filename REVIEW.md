# Independent final mathematical review of the extended criteria

Reviewer: sol_low_ceres, working alone. Owner: root. Final exact source SHA-256: `5a3003d73282d9d9649d5087d6c5650fed57f541fa22477c006656c198b76cc0`. Final PDF SHA-256: `604b05b47bd581d2d3140b1f0e1a19c243ba26130230c5a51a023e76ba39795e`.

Final descriptor-only delta check: I independently hashed both final files. Reversing exactly the disclosed author-line change and the five theorem/corollary descriptor changes in a read-only stream reproduces the previously reviewed source hash `910a38bbfe3b27a92efe7d8ac8016b22df4f8aa84fb122fcfbf889548b8ba1c4`. This exact-byte check establishes that no mathematical or other source text changed. The mathematical and mission PASS below therefore applies to the final source hash above. In particular it covers the relative open neighborhoods and explicit arrays outside the geometric dual q-Krawtchouk family, not only the earlier geometric theorem. No manuscript edits were made by this reviewer.

## Version checks and verdict

I compared the complete source with `reviews/geometric-v1.tex`. Changes are precisely the title, abstract, new perturbation section, and final scope paragraph. The geometric theorem, its proof, its Krawtchouk and dual q-Krawtchouk applications, and its source comparison are unchanged. Their checks in `reviews/geometric-v1-review.md` carry over. I reread the new section in full and checked its consumers against current MISSION.md.

Double-check before verdict: after the first proof replay, I separately repeated the symmetrizing diagonal calculation, terminal annihilation, single-term margin count, matrix subtraction, and constant inequalities below. **PASS** for this exact extended source, including the perturbation theorem, nongeometric examples, and MISSION.md criteria 1–5. No blocking mathematical defect or open assumption was found. This review does not establish historical priority.

## Finite realization and triangle support

For `lem:finite`, π_(i+1)c_(i+1)=π_i a_i makes both off-diagonal entries of DJD⁻¹ equal to √(a_i c_(i+1)). Thus H is symmetric even when b_i is negative. The recurrence gives e₀ᵀR_i(J)=e_iᵀ, and conjugation gives e₀ᵀR_i(H)=π_i^(−1/2)e_iᵀ, exactly as stated. Symmetry converts these row identities to vector cyclicity. The N+1 eigenvalues are distinct with positive spectral masses at e₀. The displayed orthogonality norms π_i⁻¹ follow.

For the terminal polynomial, e₀ᵀQ(J)=e_NᵀJ−b_Ne_Nᵀ−c_Ne_(N−1)ᵀ=0 using a_N=0. Commuting Q(J) past R_i(J) gives e_iᵀQ(J)=0 for every i, hence Q(J)=0. This establishes the terminal relation on the entire spectral support. Multiplication therefore acts on the polynomial basis by rows of J, and its iterates give exactly g(m,n;k)=[R_m(J)]_(n,k), with the orientation needed by the subsequent norm argument.

The triple-product integral vanishes if any index exceeds the sum of the other two, because the product of the two smaller-degree polynomials then has lower degree than the third. This remains valid for original products whose degree sum exceeds N. The allowed indices are exactly |m−n|≤k≤min(m+n,N). Thus the zeros needed for perturbation are exact structural zeros, not entries whose signs are merely assumed stable.

## Reference margin

At q=1, y_i=z_i/p satisfies y_i²=(1−r)y_i+r and U_m=binomial(N,m)⁻¹∑_(|S|=m)y_S. A choice of linear or constant term at every intersection coordinate of S,T contributes a positive coefficient with at most N factors r or 1−r. Since s=min(r,1−r)≤1, its coefficient is at least s^N, also for an empty choice with coefficient one.

For m≥n and m−n≤k≤m, take T⊆S and choose exactly k−(m−n) linear intersection terms; this number lies in [0,n]. For m≤k≤min(m+n,N), choose intersection size m+n−k and union size k, and take every intersection term linear. These constructions realize every triangle index, including m=0, n=0, k=0 and all boundary indices.

Permutation symmetry of the complete product makes the coefficient at each fixed degree-k squarefree monomial equal. A single chosen contribution bounds this common coefficient below by s^N/[binomial(N,m)binomial(N,n)]. Passing to U_k multiplies by binomial(N,k). Since the numerator binomial is ≥1 and the denominator product ≤4^N, the claimed uniform margin (s/4)^N follows. No explicit formula for general product coefficients is used.

## Matrix perturbation and constants

Under the theorem's hypotheses both J and J̃ are entrywise nonnegative with row sums one, including the terminal row. Their maximum absolute row-sum norms are one, and their difference norm is ≤3η. The unchanged geometric theorem and the matrix-product lemma give nonnegative entries and row sums one for each reference B_m, hence norm one. This does not assume positivity of B̃_m.

Subtracting ã_mB̃_(m+1)=(J̃−b̃_mI)B̃_m−c̃_mB̃_(m−1) and the reference identity gives exactly the manuscript formula. In particular the necessary term −(ã_m−a_m)B_(m+1) is present. The forcing terms have total norm at most (3+1+1+1)η=6η; the two difference factors have norms at most 2 and 1. Since a_m≥1/N for m<N and η≤1/(2N), division by ã_m≥1/(2N) gives exactly

e_(m+1)≤4Ne_m+2Ne_(m−1)+12Nη.

The claimed η bound follows from 0<s≤1/2 and η=½(s/(32N))^N. For L=8N, e₀=0≤η and e₁≤3η≤ηL. Thus the first induction step legitimately uses the same bound for e₀. At every step the multiplier is ≤4N+2N/L+12N/L^m≤4N+¼+3/2≤8N for all N,m≥1. This proves e_m≤ηL^m through m=N, without applying the interior recurrence beyond its domain.

The maximum entry error is consequently ≤η(8N)^N=½(s/4)^N. Subtracting this from the reference margin gives the stated lower bound at every triangle index. Outside that triangle the finite-realization lemma gives exact zeros. J̃ has eigenvalue 1, and its spectrum is the orthogonality support, so evaluating product identities there is legitimate. The stochastic recurrence gives R̃_m(1)=1, hence coefficient sum one.

For N=1 there is no subtraction/induction step. The terminal relation is x²=b̃₁x+c̃₁, with b̃₁+c̃₁=1. Here η=s/64, and b̃₁,c̃₁≥s−η=63s/64, exceeding the required s/8. The matrix proof also covers this case via e₁≤3η≤8η. When m=0 or n=0 the unique triangle coefficient is one. All 0<r<1 are included. No division by r or 1−r appears in the perturbation estimate. The symmetric endpoint r=1 is handled by the unchanged geometric criterion, rather than the positive-margin perturbation criterion.

## Nongeometric examples and consumers

At r=1/2 the radius is ½(64N)^(−N); the stated bound on h is half that radius. The change preserves the stochastic row sum and is smaller than a₁=(N−1)/N for every N≥2. All c_i are unchanged, all sign requirements persist, and every coefficient deviation is ≤η. The ratio at index 1 becomes 1+2Nh, while that at index N remains 1. Since these indices differ for N≥2, the array fails the constant-ratio hypothesis for every geometric parametrization, not merely for q=1.

The asymmetric reference has strictly positive free coefficients, including terminal b_N,c_N. A sufficiently small open ball in the affine space with fixed a₀=1,b₀=c₀=0,a_N=0 and row sums one therefore satisfies the sign conditions and strict closeness. This confirms a relative open neighborhood admitting independently varying free coordinates, rather than an exact parametrization of a named family.

| MISSION.md criterion | Exact consumption and verdict |
|---|---|
| 1. Structural coefficient hypotheses without positivity tests | PASS. Closeness consists of explicit scalar comparisons, signs, and stochastic sums; these take O(N) operations for fixed r,N. No product coefficients or matrix positivity inequalities are assumptions. |
| 2. Entire class and finite-support high-degree products | PASS. The matrix estimate applies to every admitted array; the finite realization supplies every product and exact triangle zeros, including degree sums exceeding N. |
| 3. Full positive Krawtchouk range at every size | PASS, carried over from the unchanged geometric theorem and Krawtchouk corollary and their archived review. |
| 4. Meaningful additional class | PASS. Besides the unchanged dual q-Krawtchouk family, the new criterion admits a relative open neighborhood in the free coefficient space and explicit nongeometric examples at every N≥2. The combined criteria do not effectively characterize only a known two-parameter family. |
| 5. Paper proof, boundaries and independent review | PASS for this exact version, using the detailed new checks above and the archived review of unchanged material. |

The abstract and final scope paragraph match these results: the radius is explicit, conservative, size-dependent, and positive around each asymmetric reference. No characterization of all property-(P) systems, radius uniform in N, or positive perturbation radius at the symmetric endpoint is claimed. The geometric algebra's known provenance is retained. The mathematical criteria meet the recorded mission; this review neither asserts nor establishes historical priority for the perturbation argument or a broader historical resolution of Szwarc's intended problem.

# Independent review of Sections 7 and 8 (2026-10-21)

Reviewer: ChatGPT Pro (gpt-6-pro) through pro-cli, job `job_acdafd9c-0fd4-4730-bc5c-1c2892ba8009`, fresh temporary chat. Brief: `reviews/limits-review-brief.md` (paper.tex at commit 693b1e9, SHA-256 `a38a620ae9b945e400a3cbc7b6f853c4ba7824dba32d902a5f395045239f0a38`). Full answer: `reviews/limits-review-answer.md`.

**Verdict: FAIL** for that source. The reviewer re-derived the identities independently and ran its own exact checks. It found the main mathematics sound:
- correct: Theorems 7.1, 7.6, 7.8, 7.10, 7.13, 7.14 and their lemmas and corollaries; Lemma 8.1; Lemma 8.2 (corner identity, re-derived, with exact gradients for N = 2, 3, 4); Theorem 8.4; Proposition 8.8;
- correct with fixable gaps: Corollary 7.9 at N = 1, Lemma 7.12's reversed normalization, Definition 8.3's quantifiers, Lemma 8.5's contour construction, Corollary 8.9's norm and admissibility argument;
- incorrect or overstated: Corollary 8.6 (only the necessary equalities extend to analytic rules); Proposition 8.7(1) (false for weak signs; the reviewer gave admissible directions as a counterexample); the period-4 sign claim away from r = 1 (refuted exactly at r = 4/5); several scope sentences presenting a narrower result as a general disproof; "inequalities alone" after Corollary 7.15; the reversal paragraph (needs N ≥ 3, and Szwarc's array has b ≡ 0); the paragraph applying Lemma 7.5 to arbitrary references; and several computational overstatements.

All defects were corrected in paper.tex (SHA-256 `2af3459bdb7e4d541ab9c697ef210880112030307131ceb7c186054ce0d4d65b`), mostly with the reviewer's replacement text. Two deviations:
- **Fixed-N interior claim:** restricted to the computed sizes N ≤ 10. The reviewer's suggested general argument does not reach odd-parity deep zeros, where both of its directions have zero first-order change.
- **Reviewer-supplied facts, rechecked exactly before use:** the K_{2,1} example (g(2,2;2) = −2ε/(½ − ε)), Szwarc's reversed g'(2,2;2) = (2p₀ − 1)/(Np₀) for N = 3, 4 and p₀ = 1/3, 2/5, and the first-order values 512/1875 (N = 4) and −71936/5859375 (N = 8) at r = 4/5.

RESEARCH.md was narrowed to the same scope. A follow-up review of the corrected source is required before any acceptance claim.

## Follow-up review of the corrected source (2026-10-21)

Reviewer: ChatGPT Pro (gpt-6-pro) through pro-cli, job `job_f304a6a7-9bfa-47bf-8ce0-c39719c41801`. Brief: `reviews/limits-rereview-brief.md` (paper.tex at commit 4381af5, with the first report quoted). Answer: `reviews/limits-rereview-answer.md`.

**Verdict: PASS WITH MINOR FIXES.** The reviewer found no remaining substantive defect in the numbered results of Sections 7 and 8. It marked 32 of the first report's defects fixed and 6 partly fixed. Its independent exact checks reproduced:
- the Szwarc reversal values;
- both first-order values at r = 4/5;
- the corner gradient through N = 20;
- every listed rational counterexample;
- strict first-order directions for 1 ≤ N ≤ 10 with property (P) at both stated sizes.

It also reproduced the two high-precision examples numerically.

It listed eight minor corrections:
1. the parameter range 0 < ε < ½ in the K_{2,1} example;
2. the first computational bullet (failure of period four, not general nonperiodicity);
3. keeping the analytic-domain restriction in the introduction and Section 9;
4. Miclo's small-size exceptions in Section 9;
5. removing the size-scaling inference in Section 9;
6. restating the certificate experiments as numerical findings;
7. normalizing the quadratic profiles and qualifying reproducibility;
8. two wording clarifications (boundary layers; the end of Corollary 8.9's proof).

All eight were applied with the reviewer's wording. Two search reports not reproduced by tracked scripts (a concave-profile scan and a smooth-ratio scan) were removed from the paper and kept in RESEARCH.md.

**Correction of the author's objection.** The author had rejected the first report's fixed-N interior argument. That objection was mistaken. It applies to lowering the mass at both endpoints ±1, which keeps b ≡ 0. The report's argument lowers the mass at the top endpoint only. That one-endpoint construction is exactly the one the author later found independently (RESEARCH.md, "The symmetric endpoint"). It is now in the paper as Lemma 8.7 (lowering the top mass) and Proposition 8.8 (interior points near the symmetric endpoint), replacing the restriction to N ≤ 10.

The new lemma and proposition were written after this review and have not been reviewed. Current paper.tex SHA-256: `82b83184e99b870207e9e682638f51c07b0842df065ddf94d8b7720738714aec`.

## Third review round: minor fixes and the new Lemma 8.7 / Proposition 8.8 (2026-10-21)

Reviewer: ChatGPT Pro (gpt-6-pro) through pro-cli, job `job_1a1000b0-ef7f-4b24-af90-89e8a17924b4`. Brief: `reviews/limits-review3-brief.md` (paper.tex at commit 34952d5, with the second report and the diff quoted). Answer: `reviews/limits-review3-answer.md`.

**Verdict: PASS WITH MINOR FIXES.** All eight corrections from the second round were applied correctly.
- **Lemma 8.7.** The mathematics is correct. The reviewer re-derived it through the exact identity R_n^ε = (1 − εS_n)R_n + εΣ_{j<n}π_jR_j, including the terminal and initial rows and non-probability measures.
- **Proposition 8.8.** The all-N construction is correct. The reviewer checked the reference-zero derivatives and thresholds for N = 1–10 independently, and exact curves with Λ = Λ_N + 1, ε = 10⁻¹⁰ have strictly positive triangle coefficients.
- **Λ_N.** The seven reported values were confirmed.

Required fixes, all applied with the reviewer's wording:
1. state the measure and coordinate conventions of Lemma 8.7 (0 ≤ ε < μ({x₀}), unrescaled π_n^ε, fixed coordinate);
2. define Λ_N with an empty-set convention (Λ₂ = Λ₃ = 0) and state the summation range of the overlap formula;
3. insert the affine normalization y = (1 − ε)x + ε and the smallness conditions before applying Lemma 7.5 (relatively open neighborhood);
4. replace the closing remark: no growth or thickness claim, the fixed-coordinate rates, and the normalized top-mass direction, which the author re-derived before use;
5. fix two Section 9 sentences (triangle support and the N = 1 case; the concave examples no longer supplied).

RESEARCH.md was adjusted to the same scope. Current paper.tex SHA-256: `5b08e105f3c0996b864813771ebc5528e24ffaeedcd10174a08551be2aa37010`.

## Final confirmation round (2026-10-21)

Reviewer: ChatGPT Pro (gpt-6-pro) through pro-cli, job `job_1fc62ef6-f6b5-4834-9b97-20d877ec12af`. Brief: `reviews/limits-review4-brief.md` (paper.tex at commit 8a38efb, with the third report and the diff quoted). Answer: `reviews/limits-review4-answer.md`.

**Verdict: PASS** for Sections 7 and 8, with no further corrections requested. Specifically:
- all third-round fixes are correctly applied, including the two adapted sentences;
- no new error was found;
- the reviewer's fresh exact rational checks for N = 1–10 confirm the thresholds, reference-zero derivatives, initial and terminal conventions, and strict triangle positivity.

Reviewed source: paper.tex at commit 8a38efb, SHA-256 `5b08e105f3c0996b864813771ebc5528e24ffaeedcd10174a08551be2aa37010`.

After the PASS, only the AI-use disclosure sentence changed: it now says Sections 7 and 8 were reviewed in four rounds, instead of "not independently reviewed". The diff against the reviewed commit touches that sentence alone, and no mathematical text changed. Current paper.tex SHA-256: `c7f01cd5d98f0d833a8c50bd2d8f777e277b181b19ae6b6d3b3cca6125bb495c`.

This is an AI review, not human peer review. Under MISSION.md criterion 5, Sections 7 and 8 have now been independently reviewed. Their scope is as corrected during review. The inequality-only form of Szwarc's question remains open apart from the proved obstruction for polynomial and analytic uniform rules.
