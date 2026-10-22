# Research consult, round 4: a uniform argument for the symmetric-kernel recurrence

Thanks for round 3 (reviews/consult-E-answer.md, github.com/skypher/szkraw). I verified your quadratic proof in exact arithmetic for N = 3–10 at x ∈ {1/3, 1, 7/2}: the kernel recurrence reproduces every L_{mn}^k, the support and positivity claims hold, and so do the D identity, the factorization W = (w − z)B_k and both terminal formulas. I then extended your method. Notation is as in your answer: E_i = e_i p_i, Y = TX, F(z) = ΣE_iz^i, ℒ_z = (1 + tz − z²)·Σ_k (σ_k/k!) z^{k−1}∂_z^k + Tz, K_k = Σ c_{r,a}S^aZ^r with S = z + w, Z = zw, c_{0,a} = [a = k]. Here D_i = Σ_k C(i,k)σ_k with σ_1 = 1, and T = D_N.

## New results (proved here, checked exactly)

1. **General recurrence in closed form.** For any profile, with
   W_{i,j}(r,a) = Σ_{i'≥i, j'≥0} C(i'−i+j, j)·C(a,i')·C(r,j')·σ_{i'+j'}   (nonnegative coefficients),
   D_{r+1}c_{r+1,a} = (T − D_{r+a})c_{r,a} + Σ_{j≥0} (−1)^j G_j,
   G_j = t·W_{2j+1,j}(r−j, a+2j+1)·c_{r−j,a+2j+1} + W_{2j+2,j}(r−j, a+2j+2)·c_{r−j,a+2j+2} + W_{2j+2,j+1}(r−j−1, a+2j+2)·c_{r−j−1,a+2j+2}.
   This matches a symbolic-exponent computation of (ℒ_z − ℒ_w)(S^aZ^r)/(z − w) term by term for profiles of degree K = 3, …, 7. The signs come from h_n(S,Z) = Σ_j (−1)^j C(n−j,j)S^{n−2j}Z^j. The support r + a ≤ N is preserved, since every move except the first lowers or keeps r + a, and the first has weight T − D_{r+a}.
2. **Cubic profiles (σ_k = 0 for k ≥ 4), any σ_2, σ_3 ≥ 0: (Γ) and (P) for all N.** Two proofs.
   - (a) Only one negative term, −σ_3 t C(a+3,3) c_{r−1,a+3}. Induction "D_rc_{r,a} ≥ ½(t-inflow + B-inflow)", using the factor-4 local inequality (D_{r+a+1} − D_r)B(r−1,a+3) + (D_{r+a+2} − D_{r−1})B(r,a+2) ≥ 4D_rσ_3C(a+3,3). As a polynomial in (r−1, a, σ_2, σ_3) it has nonnegative coefficients.
   - (b) Simpler: in the shifted basis S' = S + tZ, every move of the cubic recurrence is nonnegative. Since (z + w + tzw)^a(zw)^r has nonnegative coefficients, L ≥ 0. (For Krawtchouk the kernel is (1 + Z)^{N−k}S'^k.)
   LC is not needed in degree 3.
3. **Quartic LC profiles: (Γ) and (P) for all N.** The G_1 terms are three jumps:
   - −tW3, (r−1, a+3) → (r+1, a);
   - −W4, (r−1, a+4) → (r+1, a);
   - −W4, (r−2, a+4) → (r+1, a).
   Each is paid by half of the inflows of the intermediate nodes on two-step G_0∘G_0 detours (induction with κ = ½ for each inflow type). The three local inequalities have nonnegative coefficients in LC coordinates σ_2 = ρ_1, σ_3 = ρ_1ρ_2, σ_4 = ρ_1ρ_2ρ_3 (ρ_1 = x_1+x_2+x_3, ρ_2 = x_2+x_3, ρ_3 = x_3). For the B'B detour this holds at r = 2, 3 exactly and for r = 4 + p. In raw σ coordinates they have negative terms, and they fail at internal zeros such as σ = (1,0,0,0.01). So log-concavity is exactly what makes the B·B detours dominate the σ_4 jumps.
4. The shifted basis S' = S + tZ does not remove the alternation from degree 4 on: there are negative moves (+2,−4), mixed (+3,−4), and more in degree 5. The two-variable Schur basis Z^r h_a is worse.

Exact node-by-node checks of the recurrence and the induction hypothesis: cubic N ≤ 10, quartic N ≤ 8.

## Question

Find a uniform argument, for all degrees at once, that the kernel coefficients (in some positive basis) are nonnegative when σ is log-concave. Possible shapes:
- (a) a resummation Σ_j (−1)^j G_j = G_0∘(1 + X)^{−1} with a transformed unknown that satisfies a positive recurrence, or a profile-dependent family of shifted bases (for example Π_{j<a}(S + tλ_jZ), with λ chosen so that the geometric-profile kernel is a product) in which all moves are nonnegative under LC;
- (b) an alternating-series domination: G_j covered by (j+1)-fold G_0 compositions with geometrically decreasing shares, where LC (ρ_k nonincreasing) gives the needed 2×2 inequalities;
- (c) a combinatorial model of the kernel (weighted paths with a sign-reversing involution) built from the sequences i_t ≥ t that the LC coordinates count.
Even degree 5 or the two-level family σ_{k+1} = σ_k·ρ_k with ρ_1 = … = ρ_{K−1} = α ≥ ρ_K = … = β, for all N, would help. Please give complete arguments for what you can prove.
