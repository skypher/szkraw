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

## Review round 22: Theorem 8.12, Corollary 8.13, the cubic counterexample (2026-10-23)

Reviewer: ChatGPT Pro (gpt-6-pro), job `job_ef9e0fd0-9044-451a-9e36-af9e65e86c7d`. Brief: `reviews/round22-brief.md`. Answer: `reviews/round22-answer.md`.

Scope:
- Part 1, mathematics: the proofs of Theorem 8.12 and Corollary 8.13, which were derived here without consultation.
- Part 2, Lean fidelity: `lowdeg_matrix`, `lowdeg_newton_lc`, `lowdeg_ratio_matrix`, `cubic_ratio_fails`.
- Part 3, text: the new open-problem text and the abstract sentence.

**Verdict: PASS WITH MINOR FIXES.**
- Part 1: both proofs are valid. The reviewer checked them independently: the identity symbolically, and 20 arrays exactly with N ≤ 10 (8,710 coefficients, M ≥ 0), reproducing the N = 4 coefficient and all five frontier witnesses.
- Part 2: all four Lean statements MATCH.

Fixes, all applied:
1. "A bound on r alone does not restore (P)" became "Even the bound r ≤ 9/10 does not …".
2. "Log-concavity of (r,t,τ,σ)" became "log-concavity without internal zeros of (r,t,τ,σ)".
3. The cubic search is now described as sampled arrays with rσ = u·tτ, listing the tested values. The t = τ = 0 diagnostic is attributed to cubic_diag.py, with its parameters.
4. The Newton-product question is stated for nonnegative, log-concave sequences without internal zeros, as "we leave open whether". The trials are described exactly: ρ₀ > 0, ν₀ = 0, ν₁ > 0, product coefficients through order N.
5. The higher-degree sentence now says "the H_j need not vanish … requires additional estimates".
6. The abstract and the introductory sentence now carry the full hypotheses.
7. A TeX splice inside `\path{Szkraw.quad_key_red}` (from my scope-sentence insertion) was repaired; the sentence now follows its paragraph.

Also in the remark:
- "Nonnegativity of the ratio's Newton coefficients alone does not suffice": the cubic vector satisfies the local log-concavity inequalities and fails no-internal-zeros.
- r > 0 and ε ≥ 0 are now specified for exponential ratios.
- thmQ_check.py is described as checking Lemma 8.3 with i = 2.

Evidence limitation: commands, seeds and summary lines of all cited searches are now archived in runs/varratio/RUNS.md.

## Review round 23: Proposition 8.14 (2026-10-23)

Reviewer: ChatGPT Pro (gpt-6-pro), job `job_9ccb6eb3-f2b9-4304-8448-4f7e13f1fa8a`. Brief: `reviews/round23-brief.md`. Answer: `reviews/round23-answer.md`.

**Verdict: PASS WITH MINOR FIXES.** The reviewer checked every step of the self-contained proof: the layer cake, the two-step identity, T1–T3, and all five cases. Its independent exact checker passed 39,973 boxes, 359,757 ordered-step contributions and 599,595 bracket checks through k = 10.

Fixes, all applied:
1. Domain and zero extension stated; the identically zero case and infinite supports covered.
2. The final sentence now refers to the nine ordered-step contributions; individual T_c(p) can be negative.
3. The second bracket of the (1,1),(1,1) case is written out.
4. **Attribution: the result is Walkup (1976), Theorem 2**, the double-binomial convolution preserving PF₂. The paper now credits Walkup and presents the proof as self-contained. The reviewer matched the theorem against search-indexed text but did not obtain the full scan; neither did we.

## Review round 24: Lemma 8.15 and Theorem 8.16 (2026-10-23)

Reviewer: ChatGPT Pro (gpt-6-pro), job `job_217b9df1-6e7b-48ae-923b-086bdb7edeb3`. Brief: `reviews/round24-brief.md` (paper at commit c145f1f). Answer: `reviews/round24-answer.md`.

**Verdict: PASS WITH MINOR FIXES.** The reviewer found no counterexample and no missing case. Independent checks:
- Lemma 8.15, the setup, (8.7), the Leibniz expansion and the use of Proposition 8.14.
- The detours: the θ_{n,i} re-collected independently, including the target i = m with quotient ≥ 10. The resummation constants (surviving V₁ coefficient 1/6).
- All linear-in-P coefficients, E¹, E², E³, M_{k,m} and (8.9) by direct expansion.
- The affine reduction (iii), with α = tB/F = tR_{ℓ+a−1}.
- The identities and chains of (iii′)–(v).
- The generating functions of (vi), including G^{(s)} and the s = 1 correction.
- All seven polynomial certificates and the 20 small-weight checks, rerun. The LP certificates for a = 3, 4, 5 were rerun: 9/14/20 central sums and 4/5/6 Lin coefficients, accepted only as exact rational solutions.
- Boundary cases: ℓ + a = N, P₁ = 0, zero P_k, a ≤ 2.

Fixes, all applied:
1. Setup: integer arguments are now explicit. The sequence (ρ(n)) is log-concave; the real function x ↦ ρ(x) need not be (example given). The nonnegative quantities are listed explicitly, excluding ψ_n.
2. Step (vi): the form N_W = πC(2a−1,W) + C(a,W−1)ϱ is stated for W ≥ 4 and the forms other than L. W = 3 is treated directly, including the extra Ψ term C(a−1,2)(a−1).
3. Q_s certificate: the script subtracted an extra C(a,W−1), which was harmless (a stronger bound). It now certifies exactly the bound described in the text; rerun, all pass. "Only decrease" became "whose magnitudes decrease".
4. The closed forms are derived in the text by coefficient extraction from the displayed generating functions. key_weight_closed.py is described as a finite check, 5 ≤ a ≤ 30.
5. Scripts:
   - every runs/varratio script now resolves imports relative to its own location, not /home/yang;
   - key_weight_cert.py and key_weight_closed.py assert success;
   - key_phi_ustep.py and key_lin_cert.py fail unless every nonzero target is CERTIFIED;
   - rerun from another working directory: all pass.
6. Literature: Lemma 8.15's Abel argument is Wang and Yeh, JCTA 114 (2007), Lemma 2.1 and Corollary 2.6, now cited. I checked both statements in the arXiv version, math/0504164v5. The reviewer found no prior statement of Theorem 8.16 or of its key inequality; that does not establish novelty.

Also adopted: the reviewer's form Key = (1 − Δc/F)·Lin + Φ/F for reduction (i).

## Lean statement fidelity, round 17: Proposition 8.14 (2026-10-23)

Reviewer: ChatGPT Pro (gpt-6-pro), job `job_3d1729bb-6ed2-46a3-b0de-ac429250fe0a`. Brief: `reviews/lean-fidelity17-brief.md` (commit f74ef1e). Answer: `reviews/lean-fidelity17-answer.md`.

Scope:
- `Szkraw.newton_product_LCNZ`, together with `nval_mul` (existence) and `nval_inj` (uniqueness of the Newton coefficients);
- the predicate `LCNZ`;
- the proposed table row, scope sentence and disclosure change.

**Verdict: MATCH, no hidden narrowing, no fixes required.**
- `hκ` characterizes the Newton coefficients through evaluation, which is equivalent to κ_k = Δ^k(fg)(0).
- The zero and infinite-support cases are covered.

The reviewer could not fetch `lean/axioms.log`: it was not tracked in git. It is now committed. The table row, scope sentence and disclosure ("is machine-verified") are applied.

## Lean statement fidelity, round 18: Theorem 8.16 (2026-10-23)

Reviewer: ChatGPT Pro (gpt-6-pro), job `job_9d71b5a3-c0b5-4721-bfd9-e97476ce46e2`. Brief: `reviews/lean-fidelity18-brief.md` (commit 148cca3). Answer: `reviews/lean-fidelity18-answer.md`.

Scope:
- `Szkraw.lc_general : Stmt_lc_general`, with `GenRatioHyp`, `dd`/`dd_eq_nval` and `LCNZ`;
- the proposed P2 table row, the deletion of the "in progress" sentence, the introduction and disclosure changes;
- the FORMALIZATION.md row and notes sentence.

**Verdict: PASS, no fixes.**
- Ratio, ratio coefficients, data and conclusion all MATCH. Every paper instance satisfies `Admissible`, and omitting strict increase of d does not narrow the statement.
- `lc_general` carries no key-inequality hypothesis.
- The proposed text is accurate, including the description of the edge bounds and of the window certificates.

Applied: all six proposed changes. P2 now lists `Szkraw.lc_general`, and says that Theorem 5.5 is machine-verified and Theorem 5.6 is not.

## Lean statement fidelity, round 19: Theorem 8.17 (2026-10-23)

Reviewer: ChatGPT Pro (gpt-6-pro), job `job_c2ee77e3-befd-47a5-91d6-c9049cf273dd`. Brief: `reviews/lean-fidelity19-brief.md` (commit f8a0e44). Answer: `reviews/lean-fidelity19-answer.md`.

Scope:
- `Szkraw.cubic_ratio_matrix : Stmt_cubic_ratio`, with `CubicRatioHyp`;
- the proposed table rows, the introduction and disclosure changes, and the notes sentence.

**Verdict: PASS WITH MINOR FIXES; theorem-statement fidelity PASS.**
- Ratio, data, monotonicity and conclusion MATCH.
- The Lean statement covers rσ ≤ tτ, the theorem as stated. The disclosure that the 7/4 remark is not formalized is accurate.

Fix applied: the notes sentence "Each coefficient form …" was replaced by the reviewer's text. The rσ form is not nonnegative by itself; it is grouped with tτ using rσ ≤ tτ. All other proposed changes were applied as written.

## Lean statement fidelity, round 20: three remarks (2026-10-23)

Reviewer: ChatGPT Pro (gpt-6-pro), job `job_29b5176b-b0b0-4063-a234-443efb18f684`. Brief: `reviews/lean-fidelity20-brief.md` (commit f2bd5d5). Answer: `reviews/lean-fidelity20-answer.md`.

Scope:
- `Szkraw.affine_linear_quadratic` (P2, remark after Theorem 4.1: linear-profile arrays are arrays of Proposition 3.3);
- `Szkraw.lc_violation_fails` (P1, "How sharp is log-concavity?", the failing case μ = 1/100 only);
- `Szkraw.krawtchouk_range_sharp` (P1 Corollary 3.6 and P3 Corollary 6.1, sharpness of the range);
- the proposed table rows and notes sentences.

**Verdict: PASS WITH MINOR FIXES; no theorem-statement changes.**
- All three statements MATCH. The positive μ = 1/10 example is not formalized, and the new rows and notes say so.
- The notes' attribution of the positive example to exact arithmetic is supported by the archived CERTIFIED outputs.

Fixes applied: the docstring of `productMatrix_one` now reads `g(1,i;i) = b_i`. The docstring of `sharpD` says the profile equals D(i)/D(6) for 0 ≤ i ≤ 6 and is extended by 1 for i > 6. All proposed table rows and notes sentences were applied as written.

## Lean statement fidelity, round 21: Theorem 8.17 extended to rσ ≤ (7/4)tτ (2026-10-23)

Reviewer: ChatGPT Pro (gpt-6-pro), job `job_2d77a527-fed0-45f3-8834-2df63cd4bb53`. Brief: `reviews/lean-fidelity21-brief.md` (commit 7086f41). Answer: `reviews/lean-fidelity21-answer.md`.

Scope:
- `Szkraw.cubic_ratio74_matrix : Stmt_cubic_ratio74`, with `CubicRatioHyp74`;
- `cubic_ratio_matrix`, now derived from the extended form;
- the proposed P2 table row, introduction, disclosure and remark sentences, and the FORMALIZATION.md row and note.

**Verdict: PASS; no fixes.**
- `CubicRatioHyp74` changes only the bound rσ ≤ tτ to rσ ≤ (7/4)tτ (real division). Everything else is unchanged, so the statement MATCHES.
- The description of the small-n certificates matches the generators: positive polynomial scaling, the moves u_j(ℓu₁ − u₀), and separate exact certificates at small ℓ.

All five proposed changes were applied as written. P2 now calls the 7/4 extension machine-verified.

## Lean statement fidelity, round 22: P1, the positive example of "Log-concavity is not necessary either" (2026-10-23)

Reviewer: ChatGPT Pro (gpt-6-pro), job `job_8d275990-31fd-4466-8cd4-b63bbbfa2be2`. Brief: `reviews/lean-fidelity22-brief.md` (commit 1fb1d1e). Answer: `reviews/lean-fidelity22-answer.md`.

Scope: `Szkraw.lc_violation_holds` (μ = 1/10, q = 11/10, N ∈ {6, 8, 10, 12}, 0 < r ≤ 1), the P1 table row and paragraph, and the FORMALIZATION.md note.

**Verdict: PASS WITH MINOR FIXES; theorem statement MATCH.**
- Existence clause, the ν₁ν₃ = 10ν₂² violation and property (P) match the paragraph.
- The theorem exports (P), not the Bernstein representation.

Fixes applied verbatim:
1. In P1 the machine-verification attribution now follows the (P) claim. The Bernstein sentence stays attributed to the script.
2. The FORMALIZATION.md proof description now states the unnormalized basis r^e(1−r)^(m−e) and the Bernstein coefficients H_e/(S_m C(m,e)).

## Lean statement fidelity, round 23: exact computational counterexamples in P1, P2 and P3 (2026-10-23)

Reviewer: ChatGPT Pro (gpt-6-pro), job `job_f314430b-bcc0-4775-8228-7fee3bd9b4f9`. Brief: `reviews/lean-fidelity23-brief.md` (commit 81eddf3). Answer: `reviews/lean-fidelity23-answer.md`.

Scope:
- P2's five ratio counterexamples (N = 48, 64, 40, 40, 120);
- P3's profile counterexamples (seven one-kink, three log-concave-increment, one log-convex-increment, with the two shape lemmas);
- P3's rule (β = 1, γ = 0) and terminal-row failures;
- P1's `combo_shape` and its seven combination failures;
- the proposed table rows and notes.

**Verdict: PASS WITH MINOR FIXES; every Lean statement MATCHES.**

Fixes applied verbatim:
1. The P2 cross-reference now names the top-raised ratio (r = 2/5, ρ_N = r + (1−r)/N) instead of "the last example of this section".
2. The FORMALIZATION.md note now attributes the open-problems examples to Section 10 of paper.tex.

The other proposed changes were applied as written. The P2 sentence that cited P3 for the N = 120 kinked ratio was a split artifact: that example is in P2 itself.

## Lean statement fidelity, round 24: first-order derivatives along the rule β = 1, γ = 0 at r = 4/5 (2026-10-23)

Reviewer: ChatGPT Pro (gpt-6-pro), job `job_f033c651-7bf5-4fec-bdc8-63d1e811119c`. Brief: `reviews/lean-fidelity24-brief.md` (commit e479a4e). Answer: `reviews/lean-fidelity24-answer.md`.

**Verdict: PASS; no fixes.** `Szkraw.PolyCol.rule_deriv_4_5` MATCHES: the derivatives in ε at ε = 0 of g(N,N;N) are 512/1875 (N = 4) and −71936/5859375 (N = 8). The P3 table row and the merged FORMALIZATION.md sentence were applied.

## Lean statement fidelity, round 25: P3 Proposition 3.4 in full, Corollary 7.7 last sentence, Proposition 6.3 transcription (2026-10-23)

Reviewer: ChatGPT Pro (gpt-6-pro), job `job_a369f73b-0b00-4316-8f41-f43e77962fee`. Brief: `reviews/lean-fidelity25-brief.md` (commit f579147). Answer: `reviews/lean-fidelity25-answer.md`.

**Verdict: statement fidelity PASS WITH MINOR FIXES; transcription audit incomplete.**
- `positive_subalgebra_full`, `symmetric_open`, `koelink_relation_32` and `koelink_recurrence_71` MATCH.
- The reviewer could not open the published article (HTTP 403). It compared the transcription with the arXiv preprint q-alg/9605040: both formulas match its Theorem 3.1(ii), equation (3.3), and its Theorem 7.1.
- Claude, the agent that wrote the transcription, compared it with the published article (a copy supplied by the author, not redistributed). This is not an independent check. There the square relations are (3.2); Theorem 3.1(ii), Theorem 7.1 and Theorem 7.8 carry the same numbers and formulas in both versions. The independent check is the reviewer's comparison with the preprint.

Fix: the bibliography's locator sentence now says the locators follow the published version and notes that (3.2) is (3.3) in the preprint. The P3 citation "(3.2)" is consistent with that. The earlier "(3.3)" was the preprint's number, not a copying error.

## Review round 29: completeness of the not-formalized marking (2026-10-23)

Reviewer: ChatGPT Pro (gpt-6-pro), job `job_db388018-0f6f-4a71-849b-fb0683177ed3`. Brief: `reviews/round29-brief.md` (commit 92848bf). Answer: `reviews/round29-answer.md`.

**Verdict: FAIL (completeness).**
- Every numbered result is mapped.
- Many unnumbered calculations, interpretations and scope remarks were unmarked: auxiliary calculations and comparisons in P1; certificate-limit claims and interpretations in P2; reversal obstructions, Λ_N values, the sign-pattern classification and the exact contour identity in P3.

Applied: the reviewer's replacement paragraphs for P1, P2 and P3. P3's was updated for the later formalization of Proposition 3.4 and Corollary 7.7 and for the Proposition 6.3 transcription wording. A follow-up round checks the result.

## Review round 30: completeness of the not-formalized marking, follow-up (2026-10-23)

Reviewer: ChatGPT Pro (gpt-6-pro), job `job_2e0e1d13-b2e4-4d26-800c-e0976cf15f04`. Brief: `reviews/round30-brief.md` (commit abff2bc). Answer: `reviews/round30-answer.md`.

**Verdict: PASS WITH MINOR FIXES.**
- P1 PASS.
- P2: the hypothesis-dropping counterexamples after Proposition 3.3 were unmarked. They are now formalized (`Szkraw.quadratic_hypotheses_needed`) rather than listed as unformalized.
- P3: the quadratic-decomposition applications are combinations of mapped results. The reviewer's FORMALIZATION.md note was inserted verbatim.

After this round, about 40 further exact remarks of P1–P3 were formalized and checked in rounds 31–32.

## Lean statement fidelity, round 31: P1 and P2 remarks (2026-10-23)

Reviewer: ChatGPT Pro (gpt-6-pro), job `job_d58d1116-cca5-4204-9f35-ea5d419f5b27`. Brief: `reviews/lean-fidelity31-brief.md` (commit 3f6ee84). Answer: `reviews/lean-fidelity31-answer.md`.

**Verdict: PASS WITH MINOR FIXES.**
- All statements MATCH except three:
  - the exclusion wording of `linear_ratio_concave_b` needed `N ≥ 2`;
  - `log_rho_not_concave` did not state its full advertised Newton sequence;
  - docstrings cited P2's Theorem 4.2 and Corollary 5.2 as "Theorem 5.3" and "Corollary 4.4".
- The Szwarc Theorem 3.3 transcription MATCHES the survey's indexed text.

Fixes applied verbatim:
- the new docstring of `linear_ratio_concave_b` and the new P2 sentence after Corollary 3.2;
- the strengthened statement of `log_rho_not_concave` (all Newton coefficients and `LCNZ`);
- the corrected numbers.

## Lean statement fidelity, round 32: P3 remarks and the final not-formalized paragraphs (2026-10-23)

Reviewer: ChatGPT Pro (gpt-6-pro), job `job_e87d913b-a652-4826-a2a3-df066e88c795`. Brief: `reviews/lean-fidelity32-brief.md` (commit 3f6ee84). Answer: `reviews/lean-fidelity32-answer.md`.

**Verdict: PASS WITH MINOR FIXES.**
- All statements MATCH except two domain-scope gaps: `convex_superadditive` assumed convexity on all of ℕ, and the palindromic conjunct of `known_directions_satisfy` assumed antisymmetry on all of ℝ.
- Miclo's condition as P3 states it MATCHES.
- The not-formalized paragraphs of P1 and P2 are accurate and complete.
- In P3's paragraph one parenthetical was stale: explicit binomial spectral data are formalized.

Fixes applied verbatim:
- `convex_superadditive` now takes convexity on `0, …, N` and `i + j ≤ N`;
- the palindromic conjunct now takes antisymmetry on `[0, 1]`;
- the P3 parenthetical was replaced.

## Lean statement fidelity, round 35: the negative entry of the operator M (P2, Section 6) (2026-10-24)

Reviewer: ChatGPT Pro (gpt-6-pro), job `job_e047ff95-0ab8-46b2-ad5e-ebfbec4598a0`. Brief: `reviews/lean-fidelity35-brief.md` (commit 4a03165). Answer: `reviews/lean-fidelity35-answer.md`.

**Verdict: PASS.**
- The operators `opU`, `opP`, `opQ`, `opCp`, `opCm`, `opA`, `opG`, `opS` and `opM` MATCH the operator M of the proof of P2 Theorem 4.1. They are built from the weights of the Theorem 3.1 recurrence (`kernelRecV_iff`, `tmat_split`, `opS_eq`). The square index set is harmless.
- The cubic data MATCH: N = 6, d_i = i/6, r = 1/5, t = τ = 0, σ = 1/200.
- `opM_negative_entry` (M_{(2,2),(0,6)} = −9/32) and `opM_has_negative_entry` MATCH the example. They do not claim a universal statement for t = τ = 0.
- The P2 table row, the shortened not-formalized paragraph and the moved obstruction/non-contradiction clause MATCH.

No fixes were required.

## Lean statement fidelity, round 34: the raising direction at fixed r, and non-uniformity from every N₀ (2026-10-24)

Reviewer: ChatGPT Pro (gpt-6-pro), job `job_a24b6d69-57b7-4896-b4c7-6f3bd0dbc25b`. Brief: `reviews/lean-fidelity34-brief.md` (commit ee6b5a6). Answer: `reviews/lean-fidelity34-answer.md`.

Context: after round 33, an internal check found that `direction_not_uniform` excluded only a rule fitting at every `N ≥ 1`. Admission in Definition 9.3, and hence Theorem 9.4, uses only `N ≥ N₀`. Both statements below now quantify over every `N₀` and every nonzero size-dependent rescaling `s_N`.

**Verdict: PASS.**
- `raise_direction` MATCHES: these are the derivatives in the relative parameter `τ` of the affine-normalized raised array, built from the binomial masses `w_n`. Covering `r = 1` and using a two-sided derivative leave the paper's case `0 < r < 1`, `τ > 0` covered.
- `raise_not_uniform` MATCHES: it excludes every tail `N ≥ N₀` and every nonzero speed `s_N`. That covers the relative parameter, the additive mass and lowering, though not zero-speed reparametrizations. It is strong enough for the consistency remark.
- The restated `direction_not_uniform` MATCHES the direction displayed after Proposition 9.8.
- The P3 table row and the deletion of the round-33 sentence from the not-formalized paragraph MATCH.

No fixes were required.

## Lean statement fidelity, round 33: Λ_N values and the top-mass direction (2026-10-24)

Reviewer: ChatGPT Pro (gpt-6-pro), job `job_9a723fb6-b03b-4d53-a2af-7d7387df0621`. Brief: `reviews/lean-fidelity33-brief.md` (commit 077e5e5). Answer: `reviews/lean-fidelity33-answer.md`.

**Verdict: PASS WITH MINOR FIXES.**
- `lambda_values` MATCHES: it characterizes the proof's maximum over `Z_N`, not the sum `lamN`.
- `topmass_rates`, `normK` and `normalized_direction` MATCH.
- `direction_not_uniform` MATCHES at `r = 1`, for lowering and for raising by additive mass. It does not cover the later remark on raising at fixed `0 < r < 1`.

Fix applied verbatim: a sentence in P3's not-formalized paragraph keeps the fixed-`r` raising remark listed as unformalized.

## Review round 28: P2 proofs of Theorems 5.5 and 5.6 rewritten along the Lean route (2026-10-23)

Reviewer: ChatGPT Pro (gpt-6-pro), job `job_5a7e4f8c-7444-4946-a34d-32ff2a003f79`. Brief: `reviews/round28-brief.md` (commit 911524a). Answer: `reviews/round28-answer.md`.

**Verdict: PASS WITH MINOR FIXES; no algebraic error.**

The reviewer reran edge_exact.py 60, forms_iii_v.py, window_cert.py (11 windows), the six B and five E generator cases, phi3_edge.py 40 and phi3_generic.py, all passing. The edge_exact exceptions are exactly R₂ at a ≤ 5 and K_a at a ≤ 4, as stated. The reviewer also checked:
- the Q_s domination, the edge-pair counting, the Abel tail identity, the reduction to A and B (exact remainder 4C(a−1,2)u₀(u₁H₊ − u₀H) + C(a,3)u₀²u₁);
- the 7/4 scripts: bdetour_u.py 7/4 passes 51 checks, edetour_u.py 3 7/4 passes 18, and bdetour_u.py 9/5 fails (a certificate failure, not a counterexample).

Fixes applied verbatim:
1. Denominator positivity is stated in step (vi) and in the Φ₃^loc paragraph.
2. "the only negative term quadratic in u₀".
3. Generator checks are distinguished from Lean identity checks.
4. The 7/4 remark now names the modified coefficient, covers the boundary regimes, the case q = 0 and the corner, and says which script certifies what.

## Review round 25: Theorem 8.17 (cubic ratios with rσ ≤ tτ) (2026-10-23)

Reviewer: ChatGPT Pro (gpt-6-pro), job `job_3b695c0a-d1b9-48dc-8fd3-d71c7c1774b6`. Brief: `reviews/round25-brief.md` (paper at commit faaa5a0). Answer: `reviews/round25-answer.md`.

**Verdict: PASS WITH MINOR FIXES.** The reviewer found no failed certificate and no substantive gap in the detours, the key inequality or the resummation. Independent checks:
- reran bdetour_cert.py (349 checks), corner_cert.py, edetour_cert.py (124 checks), phi2loc_cert.py and phi3loc_cert.py, all CERTIFIED;
- re-derived the cubic Leibniz splitting, the Γ identity and the B/E coefficient constructors;
- checked the E-detour weights (j−2)(m−1)/j, the corner supply 2(a−2)C(a,4) ≥ 4C(a,4), the key reduction (α, the polarization, Φ₁ = F(z), both local decompositions, the y₂ balance s/3, and the case n = a), the survivals 1/18 and 1/12, and the boundary cases ℓ + a = N, small a, q = 0, ℓ = 0, r > 0;
- found no prior statement of the theorem. The condition tτ > rσ is the cubic Routh–Hurwitz condition for the ordinary coefficient polynomial r + tz + τz² + σz³; this is not related to the theorem.

Fixes, all applied:
1. The claimed cutoff at u = 1 was wrong: κ_tτ/|κ_rσ| → 2 at (0,3), so the geometric family obstructs only u > 2. The remark after the proof and the open problem are corrected.
2. The B reduction is not concave in c (example: the rt coefficient at (0,4,1,0)). The text now gives the y = 0 branch (affine in c) and the y = c branch (a cubic certified on the whole interval), which is what bdetour_cert.py does. For E the bound is a concave quadratic in c. The second block is normalized separately, and "overlap" is replaced by "exceptional low-index cases".
3. The q → 0 limit sentence after the Φ₃^loc bounds was false in general (counterexample a = 3, u = (1/q,1,q,0)) and unused. Deleted.
4. Corner wording: "only κ_tσ requires a new check; the added quadratic form has nonnegative coefficients".
5. Boundary cases: zero tails and q = 0 by continuity within the local log-concavity constraints, keeping u₀ = 0 when ℓ = 0.

## Review round 26: additions after round 25 (Theorem 8.17 extension to 7/4; sharpness remark) (2026-10-23)

Reviewer: ChatGPT Pro (gpt-6-pro), job `job_7f5e4383-ff52-45d3-8eb5-e003bd9ee2eb`. Brief: `reviews/round26-brief.md` (paper at commit 19b0346). Answer: `reviews/round26-answer.md`.

**Verdict: PASS WITH MINOR FIXES.** The reviewer confirmed that the round-25 fixes are applied correctly, that the extension to rσ ≤ (7/4)tτ is fully justified, and that the four all-r examples are correct. Independent checks:
- κ_tτ t τ + κ_rσ r σ ≥ (κ_tτ + uκ_rσ)tτ when κ_rσ < 0. The corner, the inherited quadratic block and the key inequality need no further trade.
- Reruns: the baseline B and E certificates (349 / 124 checks); B at u = 7/4 (51) and E at u = 7/4 (18) pass; B at u = 9/5 rejects (a certificate failure, not a counterexample).
- 330 polarized coefficients rebuilt from forward differences. 13,800 exact table entries matched by multiplication modulo the terminal polynomial. The geometric limit 2 at (0,3).
- lc_violation_cert.py: all four positive examples have nonnegative Bernstein forms. The control's g(6,6;6) at r = 1 matches exactly.
- Citations verified in PDF: Askey, Koelink, Miclo 2015/2017, Szwarc 2003, Wang–Yeh. Unverified (PDF not openable): Eagleson 1969, Walkup 1976, Szwarc's Inzell survey.

Fixes, all applied:
1. lc_violation_cert.py's fallback root test was not exact; the reviewer built a false certificate with two roots 10⁻⁶⁰ apart. The script now prints CERTIFIED only when every entry has a nonnegative Bernstein form, FAILS with an exact negative value on the grid r = j/64, and INCONCLUSIVE otherwise. Rerun: N = 6, 8, 10, 12 CERTIFIED; the control FAILS with the same exact value.
2. Grid wording: "float64 screening with high-precision confirmation (N ≤ 20) and high-precision searches in this family (20 ≤ N ≤ 80)". The figures are now 10^{5/2} at N = 4, 10² for 6 ≤ N ≤ 30 and 10^{3/2} at N = 40, 60, 80. "The observed failures lay in narrow windows on the tested grids." r1_large.py is cited, r1_trend.py sorts its exponent list, the docstrings are corrected, and the commands and outputs are archived in runs/sharp/RESULTS.md.
3. The control is now stated at r = 1, and the open problem defines V_N (the infimum of the failing factors 1/μ at r = 1) and asks whether V_N → 1.
4. The stale comment in corner_cert.py is fixed.
5. \bibitem{code} now pins 4f739c3 (contains all certificate scripts and the fixes above).

**Fresh-clone certificate run (2026-10-23).** In rounds 24–26 the reviewer could not download the repository and reran transcribed copies of the scripts. To close that gap, all 16 certificate scripts of Theorems 8.16 and 8.17 and of the sharpness remark were run unmodified from a fresh clone at 4f739c3 (runs/verify/run_certs.sh, record in runs/verify/RESULTS.md). All exit with code 0 and print CERTIFIED/pass; the control prints FAILS as intended. The disclosure now says that the reviewers reran transcribed copies and that the scripts were also run from a fresh clone.

## Review round 27: the split into three papers (2026-10-23)

Reviewer: ChatGPT Pro (gpt-6-pro). The first job (`job_4d6ffc8f-…`) was rejected upstream (HTTP 403, "unusual activity"). The resubmission is job `job_cd2d9ddf-9316-47f9-9f3a-e82dd96e731b`, brief `reviews/round27b-brief.md` (commit 9c9e1e3), answer `reviews/round27b-answer.md`.

**Verdict: PASS WITH MINOR FIXES.** No gap caused by the split. P1's written proofs stand alone, and P2 and P3 use P1 in proofs but not each other. Independent checks:
- P1's spectral argument, the G/K definitions, the symmetry argument, Corollary 4.2 (N = 1 directly; for N ≥ 2 the components G_{N,q,r} and G_{N−1,q,r/q}), Theorem 4.3, the cube proof of the corner value, detailed balance, and the two radius definitions.
- P2's generalized Lemma 2.1, including leading and trailing zeros; the P1 label targets; the removal of Proposition 8.10.
- P3's cuts leave no dangling dependency except the missing t, and no moved statement was weakened.
- Exact arithmetic on 45 geometric systems, 45 parity systems, 20 raised-mass perturbations and 160 log-concave sequences.
- Citations verified in PDFs: Askey, Koelink, Miclo 2015/2017, Wang–Yeh, Szwarc 2003. Unverified: Szwarc's survey, Eagleson 1969, Walkup 1976.

Fixes, applied directly to the papers (now the primary sources):
1. P2 abstract, introduction and §6: the weights criterion now states its hypotheses (Newton coefficients of c log-concave without internal zeros, nonincreasing nonnegative weights). Without them the claim is false: N = 4, d = (0,10,20,30,41)/41, c = 0.9d has g(4,4;4) < 0. The low-degree claim now states ν₁ > 0, ν₂ ≥ 0 and nondecreasing b, and P1 §6 adds nondecreasing b.
2. P1 and P3: the exact order (1−r)^N is now stated for fixed N ≥ 2, and the endpoint equalities for polynomial or qualifying analytic rules. P1's abstract now says "fixed 0 < r < 1" and "0 < p₀ ≤ 1/2".
3. P2 defines ρ(i) only where d_i > 0. P1 adds N ≥ 3 before ν₂² < ν₁ν₃. P3 restores the definition of t.
4. P3's open question is now about linear-inequality criteria that admit all K_{N,r} and G_{N,q,r}. P1's last open problem uses "give shape conditions that control them".
5. P1: Remark 3.5 is labelled, the table row reads "Corollary 5.3 and its no-uniform-radius conclusion", and the disclosure says "unlisted remarks and computational observations are not claimed machine-verified". P2's introduction now points to the Lean table instead of making a blanket claim.
6. Concordance and FORMALIZATION.md: Remark 8.5 → P1 3.5 and Definition 9.3 → P3 9.3 added, placeholders resolved, the cut entry explained (commit b018bac).
7. A new citation \bibitem{docs} pins b018bac for the split documentation; the code citation keeps 4f739c3. The P2 typo "$b$,," is fixed.

**Citation check by us (2026-10-23).** In rounds 24–27 the reviewer could not open Szwarc's survey, Eagleson (1969) or Walkup (1976). We checked them as follows.
- **Szwarc, Inzell survey** (author version, 37 pp., local copy `sources/szwarc-inzell.pdf`, retrieved 2026-10-18; the live URL currently fails TLS verification): checked against the PDF text.
  - §5, Problem 2 (printed pp. 125–126) matches P1's quotation word for word: "Find any criteria for the property (P) for finite systems of orthogonal polynomials, like the Krawtchouk polynomials" and "The problem is to find a general criterion that would handle this case."
  - Also matching: the Q_n recurrence, K_n(y²) = Q_{2n}(y), "(P) for p ≤ 1/2", and "Eagleson showed that they satisfy the property (P) if and only if p ≤ 1/2".
  - Matching locators: Theorems 3.2 and 3.3 (Sz. 1992, monotonicity conditions), Theorem 3.4 (Sz. 2001, the boundary problem (3.13)), equation (3.9), §3.4 (H = L₁ − L₂) and §3.5 (quadratic transformation).
  - The survey's displayed weights and recurrence use opposite conventions (∫K₁dμ = (1−2p)/(1−p)). P1 now restores the footnote of paper.tex that says so.
- **Eagleson 1969 and Walkup 1976:** Crossref metadata match our bibitems exactly (authors, titles, journals, volumes, issues, pages, years). Eagleson's content is cited only for the classical Krawtchouk range, which Szwarc's survey attributes to him. For Walkup:
  - the Cambridge Core abstract states the binomial-convolution result for Pólya frequency sequences and its use, "this and similar results", for unions of independent random subsets;
  - Wang–Yeh (PDF verified) cite Walkup's Theorem 1 for binomial convolution;
  - which theorem gives P2's Proposition 5.3 (round 23's reviewer said Theorem 2, from search-indexed text) was at first not verified in the full text. **Update (2026-10-23):** now verified in the full text, using the JSTOR copy the user provided (private collection, not redistributed here). Walkup's Theorem 2 (p. 77, formula (2)) proves that h_k = Σ_i Σ_j C(k,i) C(i,j) f_i g_{k−j} is PF₂ when f and g are. With f = ρ, g = ν and m = k − j this is our union product κ_k = Σ C(k,i) C(i, m+i−k) ρ_i ν_m, so it is P2's Proposition 5.3 (PF₂ = nonnegative and log-concave without internal zeros). The random-sets remark after it is his Theorem 4 (unions of conditionally uniform random sets), which he derives from Theorem 2. P2 now cites both theorems.
