# Research consult, round 3: a combinatorial model for lemma (D)

Thanks for round 2 (reviews/consult-D-answer.md at github.com/skypher/szkraw, commit 9c35a94). I verified all of it in exact arithmetic: the weighted ballot proof for geometric profiles; identity (4) = (6) for [t⁰]D_{3,N}^N against direct tables on 36 LC profiles, N = 4–12; formula (10); and D_{3,4}^4 = (4t² − 1)/84 for d = (0,1,3,5,7)/7. Here is a new finding, and a focused question.

## New: (D) is manifestly positive in LC coordinates for N ≤ 6

Coordinates: σ_1 = 1, σ_{k+1} = σ_k ρ_k with ρ_k = x_k + x_{k+1} + … + x_{N−1}. Then x ≥ 0 is exactly (LC), and D_n = Σ_k C(n,k) σ_k is the unnormalized profile, a polynomial in x with nonnegative coefficients.

Fraction-free recurrence at v = 1, u = t:
P_{m+1}[n] = t(D_n − D_m) P_m[n] + (D_N − D_n) P_m[n+1] + D_n P_m[n−1] − D_m (D_N − D_{m−1}) P_{m−1}[n],
with H_m = P_m/Q_m and Q_m = Π_{m'<m}(D_N − D_{m'}). Then
D_{mn}^k · D_N · Q_m = D_n P_m[n−1] − D_m (D_N − D_{m−1}) P_{m−1}[n].

Result: for N = 3, 4, 5, 6, every one of these numerators (3, 7, 13, 22 nonzero ones, m < n ≤ k) has **nonnegative integer coefficients as a polynomial in (t, x_1, …, x_{N−1})**. So (D), (Γ), (B) and (P) hold for every LC constant-ratio profile at N ≤ 6. (N = 7 is too expensive by brute force.) The H numerators P_m themselves are not all manifestly positive; the subtraction in the recurrence matters. The numerators of (B) in (R, W, x) were also manifestly positive for N ≤ 6.

The m = 1 case in these coordinates, for all N: the numerator of φ(n) − φ(1) is
(D_N − D_n)(D_n − 1) + D_n(δ_n − 1), with δ_n − 1 = Σ_{k≥2} C(n−1, k−1) σ_k,
and each factor has nonnegative coefficients.

Manifest positivity in x for every N tested suggests a combinatorial model. Note σ_{k+1} = Π_{t=1}^{k} (Σ_{i≥t} x_i) is a generating function of sequences (i_1, …, i_k) with i_t ≥ t, weighted by Π x_{i_t}.

## Question

1. Find a combinatorial model (weighted lattice paths, sequences, set partitions, or an algebra with positive structure constants in x) in which these D numerators, or the H coefficients after a suitable positive normalization, count objects. A Koelink-type quadratic algebra on N generators with weighted level sums reproduces only geometric profiles (I checked this numerically at N = 3 and 4). A model probably needs more structure: generators labelled by depth, or the sequences i_t ≥ t above.
2. Failing a full model: prove (D), or just (Γ), for all N for the quadratic profiles D_n = n + x·C(n,2) (truncated geometric with K = 2, the simplest non-geometric LC family). Its corner and its terminal D are positive by your formula (10).
3. Alternatively: prove the all-m terminal family D_{m,N}^N ≥ 0 under (LC), generalizing your (3,N;N) certificate. Is there an induction in m along the terminal column that closes?

Complete arguments for whatever you can prove are more useful than general remarks.
