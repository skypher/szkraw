# Independent final mathematical review

Reviewer: sol_low_ceres, working alone. Owner: root. Scope: the geometric increment theorem and its applications to MISSION.md criteria 1–5. No manuscript edits were made.

## Version and verdict

Initial paper SHA-256: `e1131fd1ee81b39232b785a198650cc59da3bb7cb49a96b56c21480cf2848a6f`.

Final reviewed paper SHA-256: `1fd5a6411dd0802a388f577abfbc43544cfef9f4743c4c052f462e9360978016`.

The owner disclosed intervening changes to the display layout and opening spectral sentence. I reread the complete final source, including those changes. Verdict for that exact final version: **PASS** for the mathematical theorem, its two applications, and the five recorded acceptance criteria. No open mathematical assumption or blocking proof defect was found. This verdict does not certify a novel resolution of the historical problem intended by Szwarc.

Sources reviewed: `sources/koelink-1996.pdf` (SHA-256 `ad60d539e55075973135c2c0a3cbb08691c6ec7e504a2df2491218f23d6e69d7`) and its text transcription (SHA-256 `f23498a18f85d11595138edf7667c38b5df3204521d2d5eba62d255f064da785`). Koelink Theorem 3.1(ii), (3.3), Theorem 7.1, and the discussion immediately after Theorem 7.8 are the relevant source passages. The paper's mathematical argument is self-contained; no positivity theorem is imported from that source. An attempted retrieval of the linked Inzell PDF timed out; the acceptance judgment below uses the exact recorded MISSION.md, not an unverified broader interpretation of Szwarc's intentions.

## Proof checks and double-check

Before issuing the verdict I replayed the coefficient parametrization, both branches of the multiplication induction, character normalization, and consumer applications algebraically a second time. In particular:

1. From the terminal stochastic relation, d_N=1; from d_0=0 and geometric increments, d_i=[i]_q/[N]_q. The ratio b_i/c_i=β gives r=1/(1+β) in (0,1]. The identity [N]_q−[i]_q=q^i[N−i]_q supplies a_i. Conversely every displayed parameter choice satisfies all original hypotheses. For N=1 the q condition is vacuous and q=1 is available.

2. The tower consists of monic quadratic extensions over commutative rings. Each is free of rank two over its predecessor, including rings with zero divisors. Thus the squarefree basis and dimension 2^N do not assume algebraic independence or a semisimplicity result. Each rewriting replaces weight 2·2^(N−j) by a strictly smaller weight; every coefficient is nonnegative for the full real ranges p,q≥1. This proves positivity of every squarefree product, rather than merely selected products.

3. The constant-coefficient induction in `lem:trace` is valid: after isolating the least remaining index, the tail contains no occurrence of that variable. The term proportional to z_j in its square relation contributes no constant coefficient, even after reducing the tail. A mismatched membership gives zero; equal memberships give exactly pq^(N−j). Consequently all basis norms are positive and distinct basis elements are orthogonal. Associativity supplies self-adjoint multiplication.

4. In `lem:three`, the tail algebra has size N−1 with exactly the same p,q and exponents N−j. Expanding E_k=F_k+z_1F_(k−1) gives the stated q coefficient after squaring z_1. The paired upper coefficients are [k+1]_q, paired diagonal coefficients are (p−1)[k]_q, and paired lower coefficients are pq^(k−1)[N−k+1]_q. In the last pair, the tail contributions are pq^(k−1)[N−k]_q+pq^(N−1) and q·pq^(k−2)[N−k+1]_q, respectively, so they agree. At k=1 the formal F_(−1) term is zero. At k=N, the endpoint calculation gives exactly (p−1)[N]_q E_N+pq^(N−1)E_(N−1), with no omitted upper term. N=1 is separately the defining quadratic relation.

5. Invariance under E_1 and recursive polynomial generation prove B=R[E_1], not merely a tridiagonal invariant subspace. Closure therefore covers all E_mE_n, including m+n>N. Their squarefree coefficients are constant on each cardinality because the product belongs to B. Positivity in the larger algebra thus implies positivity in the E_k basis without assuming it in advance.

6. The character substitution uses sum_(l>j) pq^(N−l)=p[N−j]_q and (q−1)[h]_q+1=q^h, so it satisfies each quadratic exactly. The generating polynomial identity gives (q^k−1)t_k=p(q^N−q^(k−1))t_(k−1); its ratio is the stated one. At q=1 the binomial formula supplies the ratio without division by zero. Dividing the three-term identity yields exactly a_k,b_k,c_k of `eq:parameters`, with r=1/p, including the terminal coefficients b_N=1−r and c_N=r.

7. The positive trace restricts to B. Its self-adjoint multiplication operator has cyclic vector 1 and dimension N+1. A self-adjoint cyclic operator has N+1 distinct eigenvalues and nonzero cyclic projection at each; hence all spectral masses are positive. Orthogonality of E_k gives that of R_k. No infinite-dimensional spectral or convergence assertion is needed. Spectral evaluation carries the algebra identities to the finite support, and degree 0 through N gives the full function basis there. Applying the character to a product gives total coefficient mass one. These arguments check both existence of the orthogonality measure and uniqueness of the finite linearization.

## Boundaries and applications

- N=1 gives R_1=x and x²=(1−r)x+r on support {1,−r}. The positive masses are r/(1+r) and 1/(1+r), respectively. This checks the smallest case, all r in (0,1], and the product exceeding the terminal degree.
- At q=1 the tower has independent relations z_j²=(p−1)z_j+p, t_k=binomial(N,k)p^k, and the theorem reduces to the stated Krawtchouk recurrence. At p=1 the diagonal vanishes and all other rewriting coefficients remain nonnegative; no step divides by p−1. At p=q=1, the tower is the real group algebra of the Boolean cube, and E_N²=1. These specializations agree with the general proof.
- As an independent nonconstant-increment endpoint example, N=2,q=2,p=1 gives z_2²=1 and z_1²=z_1z_2+2. Then E_1E_2=3E_1, E_2²=E_2+2, t_1=3,t_2=2, and U_2²=(U_2+1)/2. This checks a terminal and a high-degree product in the additional class; it supplements rather than substitutes for the general proof.
- In `cor:kraw`, E[Y]=p_0−(1−p_0)r=0 and Y²=(1−r)Y+r. Orthogonality of the elementary sums follows term by term from independence, and their squared norms are positive. The negative-coordinate count has exactly the claimed binomial law. Since 1+r=1/(1−p_0), its affine variable is exactly x=1−j/(N(1−p_0)). The combinatorial upper and lower multiplicities, after division by the binomial normalizers, give (N−i)/N and ri/N. The resulting polynomials have successive degrees and value one at j=0. This identifies the stated binomial orthogonal system with no hidden normalization change. The full positive range in this convention is indeed 0<p_0≤1/2: if p_0>1/2 then r>1 and the coefficient of K_1 in K_1² is (1−r)/N<0 (also for N=1). The degenerate binomial endpoints are not N+1-point systems.
- In `cor:additional`, N≥2 and q>1 give two unequal consecutive increments. Thus these normalized recurrence coefficients cannot be those of a Krawtchouk system, which have constant increments. Relabeling the spectral variable affinely does not change product coefficients of the fixed normalized polynomial basis; after using its degree-one polynomial as coordinate again, the same recurrence is recovered. The class has arbitrary size and continuous q,r parameters, and is not a single exceptional finite example.

## Exact mission consumption

| Recorded criterion | Review result |
|---|---|
| 1. Checkable structural recurrence hypotheses | PASS: ratio and geometric increment equalities/inequalities require O(N) arithmetic comparisons. They neither require linearization coefficients nor encode product positivity inequalities. |
| 2. Positivity for the entire stated class, including high degree | PASS: the positive algebra and polynomial subalgebra argument applies to every admitted coefficient array and every pair m,n≤N, as functions on the constructed N+1-point support. |
| 3. Every size and full positive Krawtchouk range | PASS: the binomial model fixes the parameter and endpoint convention and reaches every N≥1 and 0<p_0≤1/2. |
| 4. Meaningful additional finite class | PASS: the continuous q>1 dual q-Krawtchouk class at every N≥2 satisfies the same hypotheses and is distinguished by its nonconstant increments. The mission does not require an additional family beyond all q-Krawtchouk families or an open set of arbitrary recurrence arrays. |
| 5. Paper proof, boundaries, parameters, independent review | PASS for this exact source: the full proof and consuming corollaries were checked above, including termination, q=1, p=1, N=1 and all 0<r≤1. |

The equalities substantially restrict the admissible recurrence arrays to a known two-parameter family. That is a limitation of generality, but does not violate any of the five recorded criteria: they request sufficient structural assumptions covering Krawtchouk and a meaningful additional class, not a characterization of all finite property-(P) systems.

## Provenance and historical scope

Koelink's square relation (3.3) is exactly the tower relation. His Theorem 7.1 has next/current/previous coefficients pq^i(1−q^(N−i)), (p−1)(1−q^i), and 1−q^i. Division by p(1−q^N) yields the manuscript recurrence for q>1. More explicitly, its spectral coordinate is [p(1−q^(N−f))−(1−q^f)]/[p(1−q^N)], so this identification includes the spectral normalization. The discussion following Theorem 7.8 identifies the degree/spectral interchange as the dual q-Krawtchouk interpretation. These source passages support `prop:source`.

Accordingly the mechanism and additional named family predate the survey. The manuscript correctly discloses that fact. Its accepted deliverable is a self-contained recurrence criterion meeting MISSION.md as written; it should not be presented as proof that a historically new solution of Szwarc's intended open problem has been obtained. Establishing such a novelty or historical claim would require a separate comparison with the original problem and intervening literature. No such claim is needed for, or licensed by, this review.
