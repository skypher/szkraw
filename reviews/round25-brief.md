# Independent review, round 25: Theorem 8.17 (cubic ratios with rσ ≤ tτ on log-concave Newton profiles)

Repository: github.com/skypher/szkraw, commit faaa5a0 (paper.tex; scripts under runs/cubic/). Read paper.tex at that commit: Theorem 8.17 and its proof (search for `thm:lc-cubic`), and the results it builds on: Lemmas 8.3–8.4, Theorems 8.6, 8.9 (`thm:lc-affine`, whose proof defines u_n, y_n, D, X, Y, X′, Y′, J, H_*, T, K and F(z)) and 8.11 (`thm:lc-quadratic`, whose proof gives the move/detour/resummation framework, (8.4) and (8.6)).

Theorem 8.17 is new. It was found and proved here, without research consultation, and answers the question in Section 10 ("decide whether rσ ≤ u·tτ suffices for some u > 0") for u = 1. Its proof is computer-assisted. Please review completely and independently, including the certificate scripts. This is a mathematics review, not a Lean review. Every citation of a paper or book must be verified in its PDF; mark any citation you cannot open as unverified (the project's own TeX and scripts are their own originals).

Check in particular:
1. Setup: the Leibniz expansion of φ_n for a cubic ratio; the splitting ψ_n = h_n − v_n − e_n, with
   - Γ_n(ℓ) = t + τ(ℓ+n−1) + σ(C(ℓ,2) + ℓ(n−1)),
   - e_n = C(n,2)(τ+σℓ)f_{n−2} + σC(n,3)(3f_{n−1} + 3f_{n−2} + f_{n−3}).
   Verify that v_n + e_n is all of φ_n except its top term.
2. Detours:
   - V: the identity (n+1)Γ_n(ℓ+1) − nΓ_{n+2}(ℓ) = t + τℓ + σ(C(ℓ,2) + n² − 1), and that the Theorem 8.11 argument then gives constant 9/2.
   - E: that the summed detour B₀E_{j−1}′ ≥ 3cE_j (j ≥ 2) follows from the pointwise (8.10). Check the use of C(a,3)φ₃ inside B₀ for every term, the identity C(a,3)C(a−2,n) = ((a−2)/3)C(a,2)C(a−2,n) with a − 2 ≥ n, and the weight inequality (j−2)(m−1) ≥ 0.
   - B: that P² ≥ 4Q follows from (8.11) off (ℓ,n) = (0,2) and from (8.12) at the corner, including the coefficient 2(a−2)C(a,4) ≥ 4C(a,4) and that no other term needs the corner.
   - H and C′: that they carry over verbatim.
3. Proof of (8.10)–(8.12):
   - the polarization in (r,t,τ,σ) and the use of rσ ≤ tτ (only κ_tτ + κ_rσ ≥ 0);
   - that for (8.11) the part with t = σ = 0 is (8.4);
   - the exact reduction: sign pattern of the end coefficients, the normalization at u_{n−1} = 1, the bounds u_{n−2} ≥ 1/x and u_{n−3} ≥ 1/x², concavity in y and c, the overlap cases and the non-affine z cases;
   - the three regimes for z.
   Do runs/cubic/bdetour_cert.py, runs/cubic/corner_cert.py and runs/cubic/edetour_cert.py prove what is claimed, for every ℓ ≥ 0 and n? Look for a missed case, a sign condition used but not checked, a wrong substitution, or a Bernstein step on the wrong interval. Rerun them if you can; each asserts every step and prints CERTIFIED.
4. Key inequality (8.13):
   - that every 1 sits in α, the bound α ≥ sR_{ℓ+a−1} ≥ sz, and that the coefficient of α is ≥ ρ(ℓ+1)K ≥ 0;
   - the polarization bound κ_βγ ≥ e_γ(ℓ+1)Φ_β + e_β(ℓ+1)Φ_γ, including the convexity claims A^ψ₀[e_β] ≥ 0;
   - the local decompositions Φ₂ = ℓΦ₁ + Φ₂^loc and Φ₃ = C(ℓ,2)Φ₁ + ℓΦ₂^loc + Φ₃^loc, consistent with the family splittings;
   - Φ₁ = F(z) of Theorem 8.9;
   - Φ₂^loc ≥ 0 from Theorem 8.11, and independently from runs/cubic/phi2loc_cert.py;
   - the closed form and concavity of the Φ₃^loc bound (s = C(a−1,2), κ = s(2a−3)/3, T₃);
   - the per-index coefficients at z = 0 and z = 1/q, in particular the y₂ balance s/3 and the shifted terms;
   - runs/cubic/phi3loc_cert.py: does it prove the per-index bounds for every a ≥ 3 and 3 ≤ n ≤ a?
5. Resummation: the constants 10, 9/2, 3, 6, P² ≥ 4Q, and the survivals 1/18 (V) and 1/12 (E).
6. Anything missing for a complete proof of (P): windows with ℓ + a = N, small a, u₁ = 0, q = 0, ℓ = 0 (z = 0), and the use of r > 0.
7. The remark that the coefficientwise argument stops at u = 1 (the quotient at (0,3) tending to 1).
8. Literature: is Theorem 8.17, or a condition like rσ ≤ tτ for cubic ratios, known?

Answer format: PASS / PASS WITH MINOR FIXES / FAIL, every defect with an exact fix, and your independent checks. Be terse.
