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

## Review round 5: Proposition 8.12, Corollary 8.13 and remark (2026-10-21)

Reviewer: ChatGPT Pro (gpt-6-pro) through pro-cli, job `job_2687c28c-65a8-499a-9666-fc9b6135dcef`. Brief: `reviews/limits-review5-brief.md` (paper.tex at commit 9973c6f). Answer: `reviews/limits-review5-answer.md`.

**Verdict: PASS WITH MINOR FIXES.** The statements of Proposition 8.12 and Corollary 8.13 are correct. The reviewer's independent checks:
- 200 exact-rational raised-mass checks by discrete Gram–Schmidt (N = 1–10, five biases, τ ∈ {1/1000, ½, 2, 100}), confirming the stronger normalized bound 2τ max w_n;
- an independent derivation of the terminal-row contour formula (84 cases, N = 1–14);
- the exact counterexample at size exactly 10⁻¹⁵ (r = 4/5, N = 40).

Fixes, applied with the reviewer's text after the author re-derived the normalized coefficient formulas:
1. Proposition 8.12: the final normalization estimate did not hold for arbitrary τ (counterexample to the argument, not the statement: N = 1, r = ½, τ = 4), so it was replaced by the exact normalized formulas with bound ε + t_n ≤ 2τ max w_n.
2. Corollary 8.13: the proof was replaced, with τ* < x strictly, positivity from the exact coefficient formulas, and the limit τ ↓ τ*.
3. The remark now describes the saddle factor as a formal oscillatory envelope, not a proved threshold.
4. One Section 9 sentence now distinguishes an upper bound on ball radii from a construction of positive balls.

Current paper.tex SHA-256: `c0924d406b290f3a2ba6b31083f28e55127cf5568e7dffc7234fef1feffd12b4`. A confirmation round on this exact text follows.

## Confirmation of the round-5 fixes (2026-10-21)

Reviewer: ChatGPT Pro (gpt-6-pro) through pro-cli, job `job_7c82e24a-f063-42c1-9766-5c6929b99d3e`. Brief: `reviews/limits-review6-brief.md`. Answer: `reviews/limits-review6-answer.md`.

**Verdict: PASS** for Proposition 8.12, Corollary 8.13, the remark after it, and both updated Section 9 sentences, with no new error and no further fixes. Reviewed source: paper.tex at commit 0c9d8ff, SHA-256 `c0924d406b290f3a2ba6b31083f28e55127cf5568e7dffc7234fef1feffd12b4`.

After this PASS, only the AI-use disclosure sentence changed ("four rounds" → "six rounds"); the diff against 0c9d8ff touches that one line alone. Current paper.tex SHA-256: `50d3921d72cdd03c6f347916df5e28eecb0efc509bd4ba310bb24638743941ed`.

## Review round 7: terminal-row correction (2026-10-21)

Reviewer: ChatGPT Pro (gpt-6-pro) through pro-cli, job `job_8f5956b2-d2b4-4000-8120-19f6302b831c`. Brief: `reviews/limits-review7-brief.md` (paper.tex at commit b65fcad). Answer: `reviews/limits-review7-answer.md`.

Scope: the remark after Corollary 8.13 (r = ½ is a threshold for the first-order term only; exact terminal-row failures at and below ½) and the replacement Section 9 sentence.

**Verdict: PASS WITH MINOR FIXES.** Independent checks by the reviewer: exact recomputation of the four terminal-row cases by polynomial arithmetic modulo the terminal polynomial, independent of `corner()` (three negative, one positive, as stated); the polynomial dependence on e (degree at most N); and, in each negative case, g₀ + e·g₁ > 0, so the sign reversal is caused by the higher-order terms. Section 9 passes, and no remaining threshold claim at r = ½ for finite perturbations was found in Sections 7–9.

Fix, applied with the reviewer's text: the Taylor-coefficient sentence now states the computed range (orders 1–4, r = ½, N = 30–77, six-size windows, factors 0.503, 0.593, 0.640, 0.676) and that it is a finite-range observation, not an asymptotic statement.

Current paper.tex SHA-256: `dd91e3ee75f5488a94043694aad5f76caa4895aa1acbc05959f644c9d9378be6`.

## Review round 8: round-7 fix and the Section 9 nonconvexity passage (2026-10-21)

Reviewer: ChatGPT Pro (gpt-6-pro) through pro-cli, job `job_411d76f4-e856-42ea-ba9d-d69ef1030fcb`. Brief: `reviews/limits-review8-brief.md` (paper.tex at commit d87857f). Answer: `reviews/limits-review8-answer.md`.

**Item 1 (round-7 fix): PASS.**

**Item 2 (new Section 9 passage: the segment from K(N,r) to the geometric array G(N,q,r) leaves property (P)): PASS WITH MINOR FIXES.** Independent checks by the reviewer: the algebra of the combination (stochastic, b₀ = 0, constant ratio, increments ∝ 1 + t q^{i−N}); all seven exact negative corners, recomputed by an integer-scaled row recurrence independent of the supplied routine; and the 150/300-digit value −1.2454570392…·10²³ at (¼, 500, 3, 10).

Fixes, applied with the reviewer's text:
1. The displayed formula for t was inverted; the correct one is t = λN(q−1)q^{N−1}/((1−λ)(q^N−1)), with q > 1. The script already used the correct relation; its docstring is corrected too.
2. The opening sentence now says that the set with (P) need not be convex.
3. The conclusion is restricted to the seven exactly certified choices and to sufficient criteria for (P); the N = 500 case is not covered by it.
4. The final sentence is worded as an observation on the tested (N,q,t) grid.

Current paper.tex SHA-256: `a2d66cc1076ac8484fe06d21da679f5e853050b95577e9e780d5958958abce57`. A confirmation round on this text follows.

## Confirmation of the round-8 fixes (2026-10-21)

Reviewer: ChatGPT Pro (gpt-6-pro) through pro-cli, job `job_6126ebdb-e696-40f0-a8fd-a19bb54d9019`. Brief: `reviews/limits-review9-brief.md`. Answer: `reviews/limits-review9-answer.md`.

**Verdict: PASS** for the Section 9 nonconvexity passage. All fixes are applied, the t-formula agrees with the script, and no new error was found. Reviewed source: paper.tex at commit 32c4488, SHA-256 `a2d66cc1076ac8484fe06d21da679f5e853050b95577e9e780d5958958abce57` (the reviewer did not recompute the hash; numerical experiments were not rerun in this round, having been recomputed independently in round 8).

After this PASS, only the AI-use disclosure changed ("six rounds" → "nine rounds"); the diff against 32c4488 touches that one line alone. Current paper.tex SHA-256: `f82512701842bc7d901cb4a8a7bc46f4898d9de942fa80198ad4009f4e280c0d`.

## Review round 10: sign-pattern shape criteria (2026-10-22)

Reviewer: ChatGPT Pro (gpt-6-pro) through pro-cli, job `job_019a8793-d8d2-4517-9cb7-ef835978d9b7`. Brief: `reviews/limits-review10-brief.md` (paper.tex at commit 29e89fc). Answer: `reviews/limits-review10-answer.md`.

**Verdict: PASS WITH MINOR FIXES.** Independent checks by the reviewer:
- class membership of all four witnesses (nonzero second differences 1/1020 and −1/37, ratio steps 1/2400 and −1/1600, maxima of ρ as stated);
- completeness of the case split over the 15 sign choices, and that S_1 = S_2 = {0} gives exactly {K_{N,r} : r ≤ min(1, ρ_max)};
- all four negative corners recomputed exactly by an independent method (R_N² reduced modulo the terminal polynomial, not `corner()`), e.g. g(20,20;20) = −165126787294684157855924288177/3893233043700000000000000000000.

Fixes, applied with the reviewer's text:
1. The first two examples' increments are to be normalized to sum to one.
2. The conclusion now reads: for every ρ_max ≥ 83/400, among these classes only S_1 = S_2 = {0} guarantees (P) for all N.
3. Below 83/400 only the cases not excluded by the four examples are called unresolved.

Current paper.tex SHA-256: `8bc78d6849e5bb465b456801ffeba4703b20c4f37537026d34d7399b1e1ae733`. A confirmation round on this text follows.

## Confirmation of the round-10 fixes (2026-10-22)

Reviewer: ChatGPT Pro (gpt-6-pro) through pro-cli, job `job_d679b131-b1ed-41d6-b1fd-8209e2a804af`. Brief: `reviews/limits-review11-brief.md`. Answer: `reviews/limits-review11-answer.md`.

**Verdict: PASS** for the sign-pattern passage: both fixes applied, no new error. Reviewed source: paper.tex at commit b1b3549, SHA-256 `8bc78d6849e5bb465b456801ffeba4703b20c4f37537026d34d7399b1e1ae733` (the reviewer did not recompute the hash).

After this PASS, only the AI-use disclosure changed ("nine rounds" → "eleven rounds"); the diff against b1b3549 touches that one line alone. Current paper.tex SHA-256: `01300c3eebf583c6a3d190609b22d9e41218358e16b51af6f74a9b35344c783c`.

## Round 12: Theorem 7.12 (All products) and Corollary 7.13 (Heavy top step) (2026-10-22)

Reviewer: ChatGPT Pro (gpt-6-pro) through pro-cli, job `job_0cf69d14-bfe6-4545-bcbb-66b3952257dc`. Brief: `reviews/limits-review12-brief.md`. Answer: `reviews/limits-review12-answer.md`. Reviewed source: paper.tex at commit 88c1b4d.

**Verdict: PASS WITH MINOR FIXES.** Theorem 7.12 and Corollary 7.13 are correct, including the truncated cone at i = N. The reviewer independently classified the stencil symbolically for all 1540 cones with 1 ≤ m ≤ n ≤ N ≤ 20 and verified the N = 2 sharpness identity. The fixes concern the surrounding prose:
1. The sentence before Theorem 7.12 said the restriction n + m ≤ N is needed only for (iii). That is false: the extended (ii) is also needed. The reviewer's counterexample: N = 2, σ ≡ 1, a = (1, 3/10, 0), b = (0, 2/5, 2/5), c = (0, 3/10, 3/5) satisfies Theorem 7.10 and the enlarged (iii) but has g(2,2;2) = −2/5, which was rechecked here. The sentence is replaced with the reviewer's text.
2. Section 8: the reference to Theorem 7.12 now mentions its strengthened conditions (i)–(iii), and the Krawtchouk exclusion is qualified by N ≥ 3 (reviewer's text).
3. The compensation remark after Corollary 7.13 now refers to negative weighted contributions (reviewer's text).
Current paper.tex SHA-256: `fde2e1394fb3ecf45b5b407bf0b37e14beac026cf7ceddca6f19067c7213bfc7`. A confirmation round on the fixes follows.

## Round 13: confirmation of the round-12 fixes (2026-10-22)

Reviewer: ChatGPT Pro (gpt-6-pro) through pro-cli, job `job_40cd4f22-24f2-4e5f-85eb-d8368f7e23ed`. Brief: `reviews/limits-review13-brief.md`. Answer: `reviews/limits-review13-answer.md`.

**Verdict: PASS** for Theorem 7.12, Corollary 7.13 and the changed Section 8 sentence: all three fixes are applied correctly and introduce no new error. Reviewed source: commit f52442b, paper.tex SHA-256 `fde2e1394fb3ecf45b5b407bf0b37e14beac026cf7ceddca6f19067c7213bfc7` (the reviewer did not recompute the hash).

After this PASS, only the AI-use disclosure changed ("twelve rounds" → "thirteen rounds"). Current paper.tex SHA-256: `2b4fa0ce51d4607d9c38ab900660f9f4b2732c38e273fa40088a4f69f4853b19`.

## Round 14: Section 8 (Log-concave profiles), Theorem 8.1 (2026-10-22)

Reviewer: ChatGPT Pro (gpt-6-pro) through pro-cli, fresh temporary session, job `job_74fa2ec7-b789-4e94-87ee-107bfad9c9fe`. Brief: `reviews/limits-review14-brief.md`. Answer: `reviews/limits-review14-answer.md`. Reviewed source: commit aadd520. Independence caveat: the key steps of Section 8 (the kernel recurrence and the operator inequality P² ≥ 4Q) came from ChatGPT Pro consultation rounds 3–4 (`reviews/consult-E-answer.md`, `reviews/consult-F-answer.md`). The closed form of the recurrence for every degree and the exact checks were done by Claude.

**Verdict: PASS WITH MINOR FIXES.** The reviewer found no proof-breaking error. It checked line by line:
- the rescaling and the terminal relation;
- the generating-function identity and the kernel equation;
- the support argument, with an explicit triangular formula;
- Lemma 8.2, including the sign bookkeeping of the C_j family;
- Lemma 8.3, including the leading zero and the balanced-product inequalities;
- Lemma 8.4: all coefficients, the quotients and the integer minima 5, 5, 6;
- the matching P² ≥ 4Q (displacements distinct, intermediate nodes in Ω, denominators, powers of t);
- the non-circularity of the induction.
Independent exact tests by the reviewer, by direct linearization and not through (8.1): 36 arrays at N = 20, 24, 30, 32 and r ∈ {1/4, 2/5, 1}, 551,382 coefficients (129,963 deep), none negative. Also at N = 20, 24: kernel recurrence, induction invariant and P² ≥ 4Q checks (11,910 / 12,976 / 2,645 instances), all passing. Negative controls fail as expected: increments ∝ 1 + 10^{i−20} (positive but not log-concave Newton coefficients) give g(20,20;20) ≈ −7.85·10⁻⁶ at r = 1/2; the one-kink profile gives g(20,20;20) ≈ −2.07·10⁻⁵ at r = 2/5.
Fixes applied:
1. The Newton definition range is 1 ≤ k ≤ N, with the zero extension stated.
2. The overbroad sentence on quadratic profiles is replaced by the reviewer's text (ν_2 ≥ 0 is required; d = (0, 3/4, 1) shows why).
3. The mixtures now require q > 1, N ≥ 3, with the exact value ν_2² − ν_1ν_3 = −λ(1−λ)(q−1)²/(N[N]_q), and cite Section 10, not Section 9.
4. The χ_n sum range is written as 0 ≤ j ≤ ⌊n/2⌋.
5. Remark 8.5 spells out the Bernstein degree elevation.
Also changed: the AI-use disclosure ("fourteen rounds", plus the independence sentence). A confirmation round follows.
Current paper.tex SHA-256: `07697127592d9af0c43813e13910c4ffa8b23f8af3ff986555b3edc67d461663`.

## Round 15: confirmation of the round-14 fixes (2026-10-22)

Reviewer: ChatGPT Pro (gpt-6-pro), job `job_29123ec7-c5f1-40ca-b730-4d8ed04eb03f`. Brief: `reviews/limits-review15-brief.md`. Answer: `reviews/limits-review15-answer.md`. Reviewed source: commit fac94b6.

**Verdict: PASS WITH MINOR FIXES.** Fixes 1–5 are correct and there is no new proof-breaking error; Theorem 8.1's argument stays intact. Three small items, applied:
1. the mixture formula's range is now 2 ≤ k ≤ N, consistent with the zero extension;
2. the punctuation slip "equality), The" is now "equality). The";
3. the disclosure now says that for each section the final confirmation round on the corrected text returned PASS (round 14 itself was PASS WITH MINOR FIXES).
A final confirmation round follows.
Current paper.tex SHA-256: `222b12954ff29bd3cc715fec0fbd15432de304f2bcc7a515ab2e73493b5b65ee`.

## Round 16: final confirmation for Section 8 (2026-10-22)

Reviewer: ChatGPT Pro (gpt-6-pro), job `job_9f6db0a3-2434-4879-9bc2-1b081f6ba54f`. Brief: `reviews/limits-review16-brief.md`. Answer: `reviews/limits-review16-answer.md`. Reviewed source: commit c985974.

**Verdict: PASS** for Section 8 (Theorem 8.1, the log-concave Newton criterion): the three round-15 items are applied, nothing else in Section 8 changed, and no error was introduced.

After this PASS, only non-mathematical text changed, at the user's request: the machine-verification sentence of the AI-use disclosure was rewritten in plain words, and the formalization paragraph now says that Sections 7 and 8 are not yet formalized and that formalizing them is planned. Section 8 itself is unchanged.
Current paper.tex SHA-256: `8ac2403ae031c8c0a8ba6827b1cc3195ab9d1eef51a732515f487557bb004ec0`.

## Lean statement fidelity, round 1 (2026-10-22)

Reviewer: ChatGPT Pro (gpt-6-pro), job `job_db9c2283-7f70-48e2-9dde-34a92f92e1a0`. Brief: `reviews/lean-fidelity-brief.md`. Answer: `reviews/lean-fidelity-answer.md`.

The task was to check that each Lean statement listed in the paper's code-and-formalization section says what the paper's statement says. Proofs were not reviewed; they are checked by Lean.

**Verdict: PASS WITH MINOR FIXES** for the supplied declarations. Theorems 7.1, 7.8, 7.10, 7.12, 7.15, 7.16 and 8.1, Corollaries 7.9, 7.11, 7.13 and 7.17, and Lemma 7.14 match; the declared scope exclusions are accurate. No Lean statement needs to change.

Fixes applied:
- The scope sentence for Corollary 7.9 now says that the component statements are for N ≥ 2, and that `parity_split` also covers N = 1.
- The code section now names the three axioms the audit reports.

The reviewer also asked for the Newton-coefficient convention ν_k = Δ^k d(0). The paper already states it at the start of Section 8; the brief's excerpt omitted it.

Open: the types of `geometric_criterion` and `perturbation_criterion` (Theorems 2.1 and 5.3) were not in the brief and remain unreviewed. They go into round 2, together with the new Section 7 formalizations.

## Lean statement fidelity, round 2 (2026-10-22)

Reviewer: ChatGPT Pro (gpt-6-pro), job `job_1d119642-84ec-4f90-8451-15194851b613`. Brief: `reviews/lean-fidelity2-brief.md`. Answer: `reviews/lean-fidelity2-answer.md`.

Scope: Theorem 2.1 (`geometric_criterion`), Theorem 5.3 (`perturbation_criterion`), Lemma 7.4 (`szwarc_margin`), Lemma 7.5 (`stability`), Theorem 7.6 (`symmetric_criterion`) and Corollary 7.7 (`symmetric_new`), and the updated scope text.

**Verdict: PASS WITH MINOR FIXES.** Theorems 2.1, 5.3 and 7.6 and Lemma 7.5 match; Corollary 7.7 matches with its scope noted. No Lean statement needs to change. Fixes applied:
- Lemma 7.4 now defines r = p_0/(1−p_0) in its own statement. Before, it relied on the section's standing convention, which the excerpt did not show.
- The scope sentence for Corollary 7.7 now says that its neighbourhood claim follows from the positive-radius coefficient box of `symmetric_criterion`, and that openness and dimension are not stated separately in Lean.

Declarations added after this brief and still to be reviewed: `szwarc_full`, `realization_symmetric`, `ps_even_params`, `ps_odd_params`.

## Lean statement fidelity, round 3 (2026-10-22)

Reviewer: ChatGPT Pro (gpt-6-pro), job `job_a5dc6254-6cbf-4277-83bd-ca7a7c1647f6`. Brief: `reviews/lean-fidelity3-brief.md`. Answer: `reviews/lean-fidelity3-answer.md`.

Scope:
- Theorem 7.1 in full: `szwarc_full` and `realization_symmetric`;
- the Corollary 7.9 parameter identification: `ps_d_formula`, `ps_even_params`, `ps_odd_params`;
- their scope sentences.

**Verdict: PASS WITH MINOR FIXES.** All declarations match; several are stronger than the paper. Symmetry is proved for every realization, and the parameter lemmas omit the hypothesis p_0 ≤ 1/2. No Lean statement needs to change.

Fix applied: the scope sentence now says "every finite realization of an array satisfying (2.1) with b ≡ 0".

Not yet reviewed: `corner_value` (Lemma 9.1), added after this brief.

## Lean statement fidelity, round 4 (2026-10-22)

Reviewer: ChatGPT Pro (gpt-6-pro), job `job_0b783a78-345b-4053-a9ee-c2f06e58cc9e`. Brief: `reviews/lean-fidelity4-brief.md`. Answer: `reviews/lean-fidelity4-answer.md`.

Scope:
- the remark after Theorem 8.1: `lc_twoParam`, `lc_bernstein`, `constantRatio_twoParam`, `LCProfile`;
- Lemma 9.1: `corner_value`;
- their scope sentences.

**Verdict: PASS WITH MINOR FIXES (documentation only).** All declarations match. The identities for all real parameters are stronger than the paper. The Bernstein coefficients of the paper are B_s/C(D,s), and the reviewer finds no missing coverage in the combined remark declarations. No Lean proposition or paper scope sentence needs to change.

Fix applied: the docstrings of `twoParam` and `twoParam_poly` now write the recurrence variable as z, so that y is used only as a parameter.

## Lean statement fidelity, round 5 (2026-10-22)

Reviewer: ChatGPT Pro (gpt-6-pro), job `job_1f049526-e1f9-4898-bc70-078ed00231a8`. Brief: `reviews/lean-fidelity5-brief.md`. Answer: `reviews/lean-fidelity5-answer.md`.

Scope:
- Lemma 7.2: `edge_idempotents`, `cube_model`;
- Lemma 7.3: `three_term_action`, `Uvec_top`;
- their scope sentences.

**Verdict: PASS WITH MINOR FIXES.** All claims match. The reviewer finds no missing conclusion for either lemma; the parameter ranges are wider than the paper's.

Dispositions:
1. The reviewer asked that the hypothesis `hB : ∀ S, B S = y_S` be included in `edge_idempotents`. It already is: the brief showed the section variable but left out the `include hB` line. `#check @Szkraw.edge_idempotents` lists `hB` as a hypothesis, so only the excerpt was wrong and the Lean statement is unchanged.
2. The Lemma 7.3 scope sentence now states N ≥ 1, p_0 < 1, r = p_0/(1 − p_0), that there is no basis hypothesis, that the identity holds in A × A^N and restricts to V, and that `Uvec_top` states U_{2N+1} = 0 separately.

Not yet reviewed: `thinness` (Proposition 9.10) and `productMatrix_contDiffAt`, added after this brief.

## Lean statement fidelity, round 6 (2026-10-22)

Reviewer: ChatGPT Pro (gpt-6-pro), job `job_5e070c3a-36fa-45f4-9a92-87ab25b36884`. Brief: `reviews/lean-fidelity6-brief.md`. Answer: `reviews/lean-fidelity6-answer.md`.

Scope: Section 9.
- Lemma 9.2 (`corner_identity`).
- Definition 9.3 and Theorem 9.4 (`forced_equalities`, `forced_vanishing`).
- Lemma 9.7 (`spectral_top_node`, `lower_measure`, `lower_rates`, `lower_triple`).
- Proposition 9.9, first statement and part (1).
- Proposition 9.10 (`thinness`).
- Corollary 9.11 (`radius_order`).
- Proposition 9.12 (`raise_measure`, `raise_corner`, `raise_sign`, `raise_bound`).
- Corollary 9.13 (`radius_exp`, `radius_exp_asymp`).
- The updated scope sentences.

**Verdict: PASS.** Every declaration matches.
- Scope notes, all already disclosed in the paper:
  - Lemma 9.7 is stated for the spectral realization;
  - ρ_N(r) is a supremum, and its attainment is not asserted;
  - part (2) of Proposition 9.9 is not formalized.
- No fixes are required.

## Lean statement fidelity, round 7 (2026-10-22)

Reviewer: ChatGPT Pro (gpt-6-pro), job `job_c4410848-34e4-4299-8578-0526ee6f842c`. Brief: `reviews/lean-fidelity7-brief.md`. Answer: `reviews/lean-fidelity7-answer.md`.

Scope:
- Proposition 9.8: `interior_points`, `interior_measure`, `interior_open`, `lamN`;
- the supporting `kraw_g_formula`, `kraw1_zero`, `kraw1_pos`, `kraw_deriv_neg`;
- the scope sentence.

**Verdict: PASS WITH MINOR FIXES (documentation only).** All statements match, and no part of Proposition 9.8 is missing.

Fixes applied:
1. The docstring of `kraw_deriv_neg` now states the bound m + n + k ≤ 2N + 1.
2. The scope sentence now says "a coefficient box of some positive radius". It describes Λ_N as bounding the absolute rate ratios with nonzero r-rate.

## Lean statement fidelity, round 8 (2026-10-22)

Reviewer: ChatGPT Pro (gpt-6-pro), job `job_c9639ce0-6f65-4abf-858e-9514baf989dd`. Brief: `reviews/lean-fidelity8-brief.md`. Answer: `reviews/lean-fidelity8-answer.md`.

Scope:
- Lemma 9.5: `norlund_rice`, with `Ulog` and `altBinom`;
- Corollary 9.6: `analytic_forced_equalities`, `analytic_rule_small`, `expRule_analytic`, `expRule_L`, `expRule_deriv`, with `AnalyticOnOmega` and `DN`, and `analytic_rule_deriv` for context;
- Proposition 9.9 (2): `families_boundary_layers`;
- the new table rows and scope sentences.

**Verdict: PASS WITH MINOR FIXES (documentation only).** All Lean statements match. No Lean statement changes are required.

Fixes applied:
1. The scope sentence now says that only the first statement of Corollary 9.6 is obtained from Proposition 9.9 (2) with zero boundary layers.
2. The grid sentence now names the construction: an axis-parallel grid with mesh 1/M and origin √2(1+i). Irrational origin coordinates alone would not keep the nodes off the grid lines for an arbitrary mesh.

Not covered by this round: the three prose consequences (`no_open_rule_set`, `boundary_layers_palindromic`, `radius_no_uniform`), added after the brief was sent.

## Lean statement fidelity, round 9 (2026-10-22)

Reviewer: ChatGPT Pro (gpt-6-pro), job `job_a216cc35-4227-473c-85e9-1624d7661f2f`. Brief: `reviews/lean-fidelity9-brief.md`. Answer: `reviews/lean-fidelity9-answer.md`.

Scope: the three prose consequences of Section 9 (`no_open_rule_set`, `boundary_layers_palindromic`, `radius_no_uniform`) and their scope sentence.

**Verdict: PASS WITH MINOR FIXES (documentation only).** All three match. `boundary_layers_palindromic` gives only the necessary equality, not a converse. `radius_no_uniform` is stronger than the prose: it excludes every positive radius for all large N.

Fixes applied, both in the Section 9 text and in the scope sentence:
1. The open sets of polynomial rules are now "nonempty", with "for every d ∈ ℕ" in the scope sentence.
2. The palindromic relations are qualified "for k ≥ 1 and N ≥ k + K + 1, where K bounds the supports of p, q, p', q'".
3. The radius claim now reads "for every fixed r ∈ (0,1)" and "a positive radius independent of N".

## Lean statement fidelity, round 10 (2026-10-22)

Reviewer: ChatGPT Pro (gpt-6-pro), job `job_4fab9036-bda4-4ee9-ae8b-38d2dcb041a5`. Brief: `reviews/lean-fidelity10-brief.md`. Answer: `reviews/lean-fidelity10-answer.md`.

Scope: the description of Ω before Lemma 9.5 (`Omega`, `omega_contains`, `omega_half_line`, `omega_corner_zero`, `omega_corner_one`) and its scope sentence.

**Verdict: PASS WITH MINOR FIXES (documentation only).** All four statements match.
- `omega_half_line` matches under the closed-segment reading of "meets the line Re x = ½ at ±0.26276…".
- On the analyticity question, the reviewer finds `¬AnalyticAt ℝ a 0` adequate for "nonanalytic boundary point", for regular analytic parametrizations. The graph has tangent direction i, so any regular analytic parametrization of the boundary germ would make a analytic by analytic inversion.

Fixes applied:
1. The reviewer asked to delete the scope sentence's claim a(b) > b/(2 log(1/b)) unless a declaration supplied it. Instead, the bound is now a conclusion of `omega_corner_zero`, and the sentence states it.
2. The mirror-image claim at 1 now cites the symmetry declarations `Ulog_one_sub`, `Ulog_conj` and `frontier_omega_sigma`.
3. The certified bounds are described as the method of proof of `omega_half_line`, not as part of its statement.

## Round 17: Theorem 8.6 (varying ratio) and Corollary 8.7 (2026-10-22)

Reviewer: ChatGPT Pro (gpt-6-pro), job `job_ecd2c015-e591-4d8f-9e45-31fc4bdac7ce`. Brief: `reviews/limits-review17-brief.md`. Answer: `reviews/limits-review17-answer.md`.

**Verdict: PASS WITH MINOR FIXES.** The reviewer checked the normalization, the generator, the divided-difference formula with both p = 0 terms, the kernel recurrence, the detours, the matching and the corollary, and found no substantive failure.

The reviewer's own exact checks, which import no author code:
- 23,250 kernel/direct coefficients, 0 mismatches;
- 26,667 detour inequalities, 0 violations;
- 7,447 nonzero Q entries of P² ≥ 4Q, 0 violations;
- direct linearization at N = 2, 3, 4, 15, 20, 0 failures among arrays satisfying the hypotheses.

They also gave an exact failure when the mixed hypotheses are dropped (N = 3, b = (0,0,0,1)/13, c = (0,4,8,12)/13, g(3,3;3) = −1/195).

Fixes applied:
1. The corollary proof now begins "Set w_0 = w_1".
2. The pairing (x,y) ↦ (y+1,x−1) is stated as a bijection onto the terms with i+1 ≤ x ≤ y, and the zero cases are written out.
3. The "multiplying gives" step is written out.
4. The ratio is divided only for 1 ≤ ℓ < N.
5. The endpoint convention x E_0 = c_1E_1, x E_N = b_NE_N + a_{N−1}E_{N−1} is stated.
6. The detour inequalities are stated for 0 ≤ ℓ ≤ N−1, with negative second arguments read as zero.
7. "Strictly increasing" was added to the exclusion of linear ratios, with a pointer to Proposition 8.8.

Not covered by this round: Proposition 8.8 (quadratic arrays), which was added after the brief.

## Lean statement fidelity, round 11 (2026-10-22)

Reviewer: ChatGPT Pro (gpt-6-pro), job `job_7091a9bb-954b-4624-9d34-ddce7980f34c`. Brief: `reviews/lean-fidelity11-brief.md`. Answer: `reviews/lean-fidelity11-answer.md`.

Scope:
- Theorem 8.6: `varyratio_matrix`, with `VaryRatioHyp` and `MixedIneq`;
- Corollary 8.7: `varyratio_weights`, with `WeightHyp`;
- Proposition 8.8: `quadratic_matrix`, with `QuadHyp`;
- the table rows and scope sentences.

**Verdict: PASS.** All statements match; no fixes required. Scope notes:
- In Corollary 8.7 the constant-weight conclusion b = w₀c gives the constant ratio 1/(1 + w₀).
- In Proposition 8.8 with N = 1, the second-order parameters are undetermined, but choosing them zero matches the paper's convention.

## Round 18: Proposition 8.8 (quadratic arrays) (2026-10-22)

Reviewer: ChatGPT Pro (gpt-6-pro), job `job_3810e3f8-f75f-4f3d-bacb-280fae14b5c3`. Brief: `reviews/limits-review18-brief.md`. Answer: `reviews/limits-review18-answer.md`.

**Verdict: PASS WITH MINOR FIXES.**
- *The argument.* The recurrence is unconditional, with no circular use of Theorem 8.6. The higher moves vanish, and the j = 0 weights are correct. Sources outside Ω contribute zero.
- *Reviewer's exact audit.* 1,368 quadratic arrays (660,744 table entries), 0 negatives and 0 recurrence mismatches. A further 180 general arrays matched the unrestricted recurrence.
- *Witnesses.* The reviewer gave exact witnesses for each dropped hypothesis, at N = 2, 2 and 3.

Fix applied: the linear-profile sentence now says "for N ≥ 2", with the direct N = 1 argument (R_1² = c_1R_0 + b_1R_1).

## Round 19: Theorem 8.9 (linearly increasing ratio) (2026-10-22)

Reviewer: ChatGPT Pro (gpt-6-pro), job `job_1e1c1a1d-55a5-4d9b-b39c-a9c272e9415b`. Brief: `reviews/limits-review19-brief.md` (the full theorem and proof inline; the cited commit predates the theorem). Answer: `reviews/limits-review19-answer.md`.

**Verdict: PASS WITH MINOR FIXES.**
- *Checked and passed:* the split A_j = H_j − V_j, the nonnegativity of A₀, the four detours and their coefficient ratios (minima 5, 10, 6, 6), the key inequality (coefficient difference zero at n = 2, 2α − 2t(a−1) at n = 3, nonnegative for n ≥ 4), the five operator inequalities, and the resummation.
- *Reviewer's exact audit.* An independent `Fraction` verifier ran on 912 arrays (386 at the upper bound on κ), with 0 failures. Outside the bound, 39 of 225 arrays failed (P); for example, d_i = i/3 with r = κ = 1/2 gives g(3,3;3) = −1/18.

Fixes applied:
1. The Leibniz formulas are stated for 1 ≤ n ≤ N − ℓ, which covers every index used on Ω. Outside that range they can fail, because the Newton coefficients of b and c are truncated at N.
2. The four-term identity is now stated for the zero-extended sequence κ̂_i = p_iν_i + q_iν_{i−1}; κ is its truncation at N, and truncation preserves log-concavity and interval support.
3. The detours are asserted for source nodes in Ω, with ℓ + n + 2 ≤ N in the mixed products.
4. "violate the hypotheses" became "need not satisfy the hypotheses".

## Lean statement fidelity, round 12 (2026-10-22)

Reviewer: ChatGPT Pro (gpt-6-pro), job `job_b46aaa74-bd38-46f6-805e-90ef281f5349`. Brief: `reviews/lean-fidelity12-brief.md`. Answer: `reviews/lean-fidelity12-answer.md`.

Scope: Theorem 8.9 (`affine_matrix`, with `AffineRatioHyp`), the new table row, and the scope sentence.

**Verdict: PASS WITH MINOR FIXES.**
- Hypotheses, conclusion and table row: all MATCH. The cross-multiplied bound (2N−1)κ ≤ N(1−r) is equivalent to the paper's bound because N ≥ 1, and the existential packaging of r, κ loses no cases.

Fix applied: the scope sentence now states the Newton log-concavity hypothesis on the profile explicitly, instead of relying on "as in Theorem 8.1". No change to the Lean statement was needed.

## Round 20: Theorem 8.9 strengthened (nondecreasing b), Proposition 8.10 (2026-10-23)

Reviewer: ChatGPT Pro (gpt-6-pro), job `job_6521a562-61c6-4217-af03-d43e66513276`. Brief: `reviews/limits-review20-brief.md`. Answer: `reviews/limits-review20-answer.md`.

Independence caveat: the new key-inequality proof and Proposition 8.10 came from consult round 6 with the same model. The author re-verified them in exact arithmetic first (runs/varratio/verify_consultH.py).

**Verdict: PASS WITH MINOR FIXES.** Both proofs pass, and no dependence on the old slope bound remains.

Checked: the monotonicity of R_i; the increment formula; the reduction to (eq:affine-red), including the index shift for V₁; K ≥ 0; the minimization at α = tu₀/u₁; the endpoint estimates (no double counting in YJ; the coefficients L_n and E_n); the resummation; and Proposition 8.10's move inventory and its bound P² ≥ 6Q.

**Reviewer's independent exact tests (Fraction):**
- 314 arrays: 340,251 linearization coefficients, all nonnegative;
- the key inequality at 4,241 sources;
- detours at 3,432 sources;
- 900 endpoint sequence cases;
- M ≥ 0 and the resummation identity at N = 4, 6, 8.

**Outside the boundary.** The certificate fails as soon as b stops being monotone, since M_{(N,0),(N−1,1)} = (b_N − b_{N−1})/c_N < 0, but (P) can survive.
- N = 2, d = (0, ½, 1), r = ½, κ = 2/5: b is not monotone, yet (P) holds.
- d = (0, 1/7, 3/7, 1), r = κ = ½: g(3,3;3) = −1/24.

Fixes applied:
1. The "exactly when" sentence of Theorem 8.9 now says that nondecreasing b is equivalent to κ(N + d_{N−1}/(1 − d_{N−1})) ≤ N(1 − r). It no longer reads as a characterization of (P).
2. Strict enlargement of the κ range for nonlinear profiles is now stated for r < 1 only.

## Lean statement fidelity, round 13 (2026-10-23)

Reviewer: ChatGPT Pro (gpt-6-pro), job `job_e84f571e-0902-473b-8b75-8dc9172eda9e`. Brief: `reviews/lean-fidelity13-brief.md`. Answer: `reviews/lean-fidelity13-answer.md`.

Scope:
- Theorem 8.9 as strengthened: `affine_matrix`, with `AffineRatioHyp` (nondecreasing b);
- its equivalence with the endpoint inequality: `affine_bmono_iff`;
- Proposition 8.10: `quadprofile_matrix`, with `QuadProfileHyp`;
- the table rows and scope sentences.

**Verdict: PASS.** All statements match, and no fixes were required.
- Scope note: the remarks after Theorem 8.9 (linear-profile bound, range inclusion, the N = 4 example) are prose and have no separate Lean declarations.
- The reviewer's duplicate-declaration remark refers to the brief's excerpt of the signature, not to the source.

Not covered: `quadprofile_bmono_iff`, the endpoint equivalence after Proposition 8.10. It was formalized after this brief was sent, and the scope sentence now cites it. It should go into the next fidelity round.

## Round 21: Theorem 8.11 (convex quadratic ratio) (2026-10-23)

Reviewer: ChatGPT Pro (gpt-6-pro), job `job_acc16a98-3b96-4df2-b811-6e09c63ce857`. Brief: `reviews/limits-review21-brief.md`. Answer: `reviews/limits-review21-answer.md`.

Independence caveat: the weighted B-detour, its certificate and the key inequality came from consult round 7 with the same model. The author re-verified them in exact and symbolic arithmetic first (runs/varratio/verify_consultI*.py).

**Verdict: PASS WITH MINOR FIXES.**
- *Passed:* monotonicity and the Leibniz formulas, the split and its signs, the four mixed detours (minima 10, 9/2, 3, 6), the summation of (eq:quad-B), the tail and z reductions (the interval for z is a valid relaxation), the certificate (all 25 table entries), the w-coefficients (symbolic in general n), the key inequality with its surplus, and the resummation constants and composition order.
- *Reviewer's independent exact tests:*
  - 216 members up to N = 20, including adversarial ones;
  - 396,226 linearization coefficients, all nonnegative;
  - 12 full operator checks;
  - 15,000 local configurations, ℓ up to 10⁶, with minimum ratio ≈ 1.040.

Fixes applied:
1. The certificate (eq:quad-cert) is stated for real h ≥ 1 (h = 1 + 1/q need not be an integer); the proof is unchanged.
2. The first boundary evaluation now reads 𝓕(q)/(q(1+q)); it had q^n(1+q).
3. The second boundary evaluation now reads 𝓕(q)/q²; it had q^{n+1}. The printed divisors were correct for the residual of (eq:quad-B), which is q^{n−1}𝓕(q).
4. Optional clarifications: at w = 0 the expression equals h₀(K_nAB − L_npC); and only φ_n, h_n, v_n, w_n are claimed nonnegative, not ψ_n.

## Lean statement fidelity, round 14 (2026-10-23)

Reviewer: ChatGPT Pro (gpt-6-pro), job `job_aa9ef75d-4d73-4e65-b3c5-5c6ea7b61a07`. Brief: `reviews/lean-fidelity14-brief.md`. Answer: `reviews/lean-fidelity14-answer.md`.

Scope:
- Theorem 8.11: `quadratic_ratio_matrix`, with `QuadRatioHyp`;
- the equivalence after Theorem 8.11: `quadratic_bmono_iff`;
- the equivalence after Proposition 8.10: `quadprofile_bmono_iff` (left over from round 13);
- the cited auxiliaries (`leibniz_quad`, `quadB_seq`, `cert_nonneg`, `QuadSetting.key`, `quad_key_red`, `ResumWeights2`, `resum_nonneg2`, `gkernel_resum2`), the table rows, scope sentences and disclosure.

**Verdict: PASS WITH MINOR FIXES.** Every statement matches; the two equivalences are slightly stronger than the paper, since they do not need r > 0.

Fixes applied:
1. Both equivalence scope sentences, and the docstrings of `quadprofile_bmono_iff` and `quadratic_bmono_iff`, now say that the Lean statement omits r > 0.
2. The key-inequality citation now reads "on Ω for a ≥ 3 (QuadSetting.key), together with its reduced auxiliary inequality (quad_key_red)".
3. The disclosure now reads "Results and prose remarks not covered by those listed Lean theorems", since the two equivalences are prose claims that are machine-verified.
4. Optional fix applied: `quadprofile_bmono_iff` added to the table row of Proposition 8.10.

## Lean statement fidelity, round 15 (2026-10-23)

Reviewer: ChatGPT Pro (gpt-6-pro), job `job_c8dac65e-630b-4243-a33c-1278086f0f86`. Brief: `reviews/lean-fidelity15-brief.md`. Answer: `reviews/lean-fidelity15-answer.md`.

Scope: the lemmas and corollaries of Sections 2–6, which were formalized as steps of Theorems 2.1 and 5.3 and are now listed in the Lean table:
- Lemma 2.2 (with the new `geometric_coefficients_N_one`), Lemmas 3.1–3.3, Proposition 3.4, Lemma 4.1, Lemmas 5.1–5.2;
- Corollary 5.4 (`nongeometric_perturbation_example`, now also stating that no constant ratio exists; `relatively_open_coefficient_neighborhood`), Corollaries 6.1 and 6.2;
- the declaration that Proposition 6.3 (comparison with Koelink) is not formalized, and the new scope sentences.

**Verdict: PASS.** No fixes required. Scope notes, all disclosed in the paper: Lemma 3.3 is stated for k ≥ 1 (k = 0 is trivial); Proposition 3.4 omits generation by E₁ and independence of the E_k; the neighbourhood in Corollary 5.4 asserts realization, positivity and margin.

## Lean statement fidelity, round 16 (2026-10-23)

Reviewer: ChatGPT Pro (gpt-6-pro), job `job_07baf284-18c4-48f2-80b2-fd3567328a01`. Brief: `reviews/lean-fidelity16-brief.md`. Answer: `reviews/lean-fidelity16-answer.md`.

Scope:
- the remarks after Theorem 8.9: `profile_last_le`, `affine_range_remarks`, `affEx_remark`;
- the example after Theorem 8.11: `quadExample_remark`;
- eq:quad-B with constant 1 fails at N = 20: `quadB_unit_fails`;
- the two N = 3 counterexamples in the open problems: `openEx1_fails`, `openEx2_fails`;
- the new table rows and scope sentences.

**Verdict: PASS.** No fixes required. Scope notes, both disclosed in the paper:
- `profile_last_le` covers profiles whose Newton coefficients are log-concave, not every convex profile;
- the statement that linear-profile arrays are arrays of Proposition 8.8 is not formalized.
