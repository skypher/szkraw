# Research consult, round 8: cubic ratios

Thanks for round 7 (reviews/consult-I-answer.md, github.com/skypher/szkraw). Your weighted detour and key inequality are now Theorem 8.11 of paper.tex (convex quadratic ratios ρ(x) = r + tx + τC(x,2) on log-concave Newton profiles with nondecreasing b). It passed review round 21 (minor fixes) and is machine-verified in Lean 4 (`Szkraw.quadratic_ratio_matrix`, `Szkraw.quadratic_bmono_iff`).

This round asks whether a cubic Newton term can be added, and under which condition.

## New findings (all in exact rational arithmetic)

1. **No unconditional cubic extension.** For N = 4, d_i = i/4 and ρ(x) = 19/20 + C(x,3)/320 (Newton coefficients (19/20, 0, 0, 1/320)), b = (0, 1/80, 1/40, 9/256, 3/80) is nondecreasing but g(4,4;4) = −14011/30720000. This is machine-checked (`Szkraw.cubic_ratio_fails`).
2. **A bias cap does not rescue pure cubics.** On linear profiles with κ = 1/80 (b nondecreasing):
   - ρ_i = 9/10 + κC(i,3)/C(48,3) at N = 48 gives g(48,48;48) < 0;
   - ρ_i = 9/10 + κ(i/64)³ at N = 64 gives g(64,64;63) < 0.

   The failing bias drops as N grows: 19/20 from N = 4, 47/50 from N = 4, 23/25 from N = 16, 9/10 from N = 48.
3. **Steeper shapes fail at smaller bias.**
   - (i/N)⁴ fails at r = 4/5 (N = 15).
   - 10^{i−N} with κ = 1/100 fails at r = 1/2 (N = 40).
   - Raising only the last ratio fails: ρ_i = r for i < N and ρ_N = r + (1−r)/N, which keeps b nondecreasing and has nonnegative Newton coefficients, gives g(40,40;38) < 0 at r = 1/2 and g(120,120;119) < 0 at r = 2/5.
   - Curvatures Δ²ρ that decrease, saturate or have a kink fail from r ≈ 1/2 to 9/10.
4. **Conjecture (C3).** Assume:
   - d has Newton coefficients log-concave without internal zeros;
   - ρ(x) = r + tx + τC(x,2) + σC(x,3), with r > 0, t, τ, σ ≥ 0 and **rσ ≤ u·tτ**;
   - c = ρd, b = (1 − ρ)d, and b is nondecreasing.

   Then (P) holds. The conjectured condition is the consequence tτ ≥ rσ of log-concavity of the ratio's Newton coefficients (r, t, τ, σ); it says nothing about t² ≥ rτ, which Theorem 8.11 does not need. Every failing example above violates it. In example 1, t = τ = 0. For (i/N)³, tτ = 6κ²/N⁶ against rσ = 6rκ/N³.

## Evidence for (C3)

The test arrays have random log-concave Newton profiles, random (t, τ) directions, and σ = u·tτ/r. The scale is λ times the largest value keeping b nondecreasing, with λ ∈ {1/2, 1}.
- **(P), full tables.** 9,000 arrays, N = 4–18, u ∈ {1/4, 1, 4, 16, 64}, r ∈ {1/10, 1/3, 1/2, 4/5, 19/20, 99/100}: no failure.
- **(P), rows g(m,N;k).** N = 24, 32, 48, 64, u ∈ {1, 4, 16}, r ∈ {1/2, 9/10, 19/20, 99/100}: no failure. N = 96 is in progress.
- **The Theorem 8.11 resummation.** The operator is M = G(U + P²/4 − Q + C + A)G with G = (I − P/2)⁻¹, in the notation of the proof of Theorem 8.9. It is entrywise ≥ 0 on all 2,520 random members with N ≤ 10 and u ≤ 4, at every r tested including 99/100, and on 360 further members with N = 11–13 and u ∈ {1, 4}. Negative entries appear only at u = 16 with r ≥ 4/5.
- **Where pure cubics break this route.** For t = τ = 0 the operator M < 0 at every r. For example, N = 6, d linear, r = 1/5, σ = 1/200 gives min M = −0.28 at (2,2) ← (0,6).
  - The only negative block is R = U + P²/4 − Q; GAG ≥ 0 and GCG ≥ 0.
  - The failing scalar inequality is the B-detour at ℓ = 0: 4c₁B₁(0,a) ≤ B₀(0,a)B₀(1,a−2).
  - Reason: φ₂(0) = ρ(2)f₂(0) + 2Δρ(1)f₁(0) has no σ term because d₀ = 0, whereas φ₄(0) contains 4σf₁(0)-type terms. So Q is linear in σ while P² is quadratic.
  - With t, τ > 0 and rσ ≲ tτ the B-detour holds at ℓ = 0 in all tests.

Scripts are in runs/varratio/: cubic_lc_test.py, cubic_diag.py, cubic_random.py, ratio_frontier.py, rowN_frontier.py and frontier_examples.py.

## Notation (as in the proof of Theorem 8.11)

Leibniz gives, for ℓ + n ≤ N and all quantities at ℓ,

φ_n = ρ(ℓ+n)f_n + nΔρ(ℓ+n−1)f_{n−1} + C(n,2)Δ²ρ(ℓ+n−2)f_{n−2} + C(n,3)σf_{n−3},

with Δρ(x) = t + τx + σC(x,2), Δ²ρ(x) = τ + σx and Δ³ρ = σ. Accordingly ψ_n = h_n − v_n − w_n − x_n, where:
- h_n = (1 − ρ(ℓ+n))f_n and v_n = nΔρ(ℓ+n−1)f_{n−1}, as before;
- w_n = C(n,2)Δ²ρ(ℓ+n−2)f_{n−2}, now with a nonconstant Δ²ρ;
- x_n = C(n,3)σf_{n−3}, which gives new moves X_j.

Nondecreasing b is equivalent to 1 − ρ(m+1) ≥ Δρ(m)R_m for 0 ≤ m < N, with R_m = d_m/f₁(m), exactly as in Theorem 8.11.

## Questions

1. **Prove (C3)** for some explicit u > 0, at every r ∈ (0, 1]. Any u > 0 is useful; u = 1, the log-concavity consequence, would be ideal. Following the Theorem 8.11 skeleton, this needs:
   - the B-detour (analogue of (quad-B)), where rσ ≤ u·tτ must enter at small ℓ;
   - detours for the new X moves and for the modified W moves;
   - the key inequality A₀B₀′ + B₀A₀″ ≥ c(4H₁ − γ_V V₁ − γ_W W₁ − γ_X X₁) with affordable constants;
   - the sign bookkeeping in the resummation. With the signs (−1)^j, X_j should behave like V_j and W_j; please confirm.
2. **If (C3) is the wrong class for this route**, give the cleanest provable condition. It must contain every convex quadratic ratio (σ = 0) and admit some σ > 0 at every r. Candidates are σ ≤ u·τ²/(something), or a condition involving ℓ-dependent quantities, but it has to stay checkable from (r, t, τ, σ) and d.
3. **Optional: higher degree.** A natural generalization is ρ(x) = Σ_k ρ_k C(x,k) with ρ₀ = r, nonnegative ρ_k, and rρ_{k+1} ≤ u·ρ₁ρ_k for k ≥ 2. A random test of this, N ≤ 16, all r up to 99/100, is in progress (runs/varratio/ratio_degree_test.py). Does your argument extend?

As before, please give complete arguments with every inequality explicit. I check everything in exact arithmetic and then formalize it in Lean.
