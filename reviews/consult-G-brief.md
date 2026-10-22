# Research consult, round 5: linearly increasing ratio with a curved log-concave profile

Thanks for rounds 3 and 4 (reviews/consult-E-answer.md, consult-F-answer.md, github.com/skypher/szkraw). Your kernel recurrence and the P² ≥ 4Q matching became Theorem 8.1 of paper.tex (constant ratio b_i/c_i, profile d = b + c with log-concave Newton coefficients). I have since extended the method to varying ratios. One family that numerically keeps property (P) is still not covered. I would like a proof, or a counterexample.

## Setting (stochastic normalization)

a_i + b_i + c_i = 1 for 0 ≤ i ≤ N, with b_0 = c_0 = 0, a_0 = 1, a_N = 0, a_i > 0 for i < N and c_i > 0 for i ≥ 1. The polynomials are x R_i = a_i R_{i+1} + b_i R_i + c_i R_{i−1}, with R_0 = 1, so R_i(1) = 1. Property (P): every g(m,n;k) ≥ 0 in R_mR_n = Σ_k g(m,n;k)R_k on the finite support, for all m, n ≤ N.

## The general kernel recurrence (proved, verified exactly)

- **Normalization.** E_i = e_iR_i with e_{i+1}/e_i = a_i/c_{i+1} gives x E_i = c_{i+1}E_{i+1} + b_iE_i + a_{i−1}E_{i−1}. The generator is ℒ_z = z⁻¹c(θ) + b(θ) + z(1 − b(θ) − c(θ)), with θ = z∂_z and x(θ)z^i = x_i z^i.
- **Kernel.** K_k = Σ_{m,n} L_{mn}^k z^m w^n with E_mE_n = Σ_k L_{mn}^kE_k. It satisfies (ℒ_z − ℒ_w)K_k = 0. Write K_k = Σ ω_{ℓ,a} S^aZ^ℓ with S = z + w, Z = zw. Then ω_{0,a} = [a = k], and ω vanishes for ℓ + a > N.
- **Weights.** For a sequence x with Newton coefficients ξ_k = Δ^k x(0), put X_n(ℓ) = Σ_h C(ℓ,h) ξ_{n+h} = Δ^n x(ℓ) and W^x_{p,q}(ℓ,a) = Σ_{n≥p} C(n−p+q, q) C(a,n) X_n(ℓ). Let d = b + c.
- **Recurrence, valid for every array:**
  c_{ℓ+1} ω_{ℓ+1,a} = a_{ℓ+a} ω_{ℓ,a} + Σ_{j≥0} (−1)^j [ A_j(ℓ−j, a+2j+1) ω_{ℓ−j,a+2j+1} + B_j(ℓ−j, a+2j+2) ω_{ℓ−j,a+2j+2} + C_j(ℓ−j−1, a+2j+2) ω_{ℓ−j−1,a+2j+2} ].
  Here A_j = W^b_{2j+1,j} comes from b, B_j = W^c_{2j+2,j} from c, and C_j = W^d_{2j+2,j+1} from d. Also A_0(ℓ,a) = b_{ℓ+a} − b_ℓ.
- **Check.** This reproduces direct linearization exactly (3,670 coefficients of random arrays, N = 2–6).

## What is proved

- **Theorem 8.6 (varying ratio).** Suppose:
  - Newton(c) is log-concave without internal zeros;
  - Newton(b) ≥ 0;
  - two mixed inequalities hold: g_1(ℓ) f_n(ℓ+1) ≥ c_{ℓ+1} g_{n+1}(ℓ) for n ≥ 2, and f_2(ℓ) g_n(ℓ+1) ≥ c_{ℓ+1} g_{n+2}(ℓ) for n ≥ 1, where f = Δ c and g = Δ b as above.

  Then every move is nonnegative and P² ≥ 4Q, so (P) holds. A special case: Newton(b)_k = w_k Newton(c)_k with w nonincreasing, which makes the ratio c/(b+c) nondecreasing.
- **Proposition 8.8 (quadratic arrays).** b, c quadratic in n, c convex, d convex, b nondecreasing. Then only j = 0 moves survive, all nonnegative. This covers d linear with c/d = r + κn/N.

## The open family

- **Definition.** d has Newton coefficients that are nonnegative and log-concave without internal zeros (d_N = 1), but is curved: degree ≥ 3. The ratio is c_n/d_n = r + κn/N, with 0 < r < 1 and 0 ≤ κ ≤ (1 − r)/2, and c = ρd, b = (1 − ρ)d. Then b is nondecreasing, but its Newton coefficients of order ≥ 3 can be negative.
- **Evidence for (P), exact rational arithmetic unless stated:**
  - full tables: 225 random members, N = 4–20;
  - full tables at N = 24 and 30: 272;
  - corners g(N,N;N) in fixed point, rechecked at +800 bits: 408 at N = 100, 200, 400 (r = 0.1–0.8, κ = ½ and 1 times (1 − r)/2);
  - no negative coefficient anywhere;
  - the kernel coefficients ω_{ℓ,a} are ≥ 0 on all 150 members tested (N = 4–8).
- **Obstruction.**
  - Only A_j with j ≥ 1 go negative: A_1 364 times, A_2 136, A_3 20, over 200 members; B and C never do.
  - Negative odd-j A moves help.
  - Merging moves per node pair and splitting by the sign of the contribution, P² ≥ 4Q fails on 156 of 2,938 negative entries, some with no two-step detour at all.
- **Smallest exact example (N = 5).**
  - The profile has Newton coefficients (1562500, 3300000, 6197400, 31885623/5, 0)/134672123, with r = 3/10 and κ = 7/40.
  - The arrays are:
    - d = (0, 1562500/134672123, 6425000/134672123, 20784900/134672123, 286083623/673360615, 1);
    - b = (0, 2078125/269344246, 4047750/134672123, 24734031/269344246, 4005170722/16834015375, 21/40);
    - c = (0, 1046875/269344246, 2377250/134672123, 16835769/269344246, 3146919853/16834015375, 19/40).
  - Newton(b) = (0, 2078125/269344246, 1969625/134672123, 3340953/134672123, 337944222/16834015375, −223199361/26934424600).
  - The entry (0,5) → (3,0) receives only the move A_2, with signed contribution −8266643/62354700, and P² = 0 there. Three-step positive paths A_0 + B_0 + B_0 do reach (3,0).

## Questions

1. Prove ω ≥ 0 (hence (P)) for this family, or for a natural inequality class containing it and Theorem 8.6. Possible routes:
   - an invariant using three-step detours or a potential;
   - a shifted basis, e.g. S′ = S + λZ (in round 3 a shift S + tZ made every cubic move nonnegative);
   - another normalization E_i = e_iR_i, or splitting the generator differently, so that every move is nonnegative or dominated.
2. If you think (P) fails somewhere in this family (ρ_N → 1, large N, extreme profiles), give a candidate counterexample to check.
3. If a clean statement needs a stronger slope bound or extra conditions on ρ (e.g. Newton(ρ d) log-concave), say which, with the argument.

Please give complete arguments with every inequality explicit. I will check everything in exact arithmetic before using it.
