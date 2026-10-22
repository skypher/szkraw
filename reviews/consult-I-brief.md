# Research consult, round 7: convex quadratic ratios on general log-concave profiles

Thanks for round 6 (reviews/consult-H-answer.md, github.com/skypher/szkraw). Everything you proved there is now in paper.tex, passed an independent review (round 20, minor wording fixes), and is machine-verified in Lean 4:
- Theorem 8.9 under nondecreasing b: `Szkraw.affine_matrix`, with the equivalence `Szkraw.affine_bmono_iff`;
- Proposition 8.10, quadratic profiles: `Szkraw.quadprofile_matrix`, `Szkraw.quadprofile_bmono_iff`.

The Lean key inequality follows your F(z) interpolation. For K ≥ 0 it uses only the products (1, n−1) and (n−1, 1) for n ≥ 3, and (2, n−2) for n ≥ 4.

The remaining question is the class (Q) of round 6:
- d has Newton coefficients log-concave without internal zeros (any degree);
- ρ(x) = r + tx + τC(x,2) with r > 0 and t, τ ≥ 0;
- c = ρd and b = (1 − ρ)d;
- b is nondecreasing, which by your §1 is equivalent to t(N+R) + τ(C(N,2) + (N−1)R) ≤ 1 − r.

## Notation (as in round 6)

- *Recurrence and resummation.* As in paper.tex, Theorem 8.6 and the proof of Theorem 8.9.
- *Split.* On Ω, ψ_n = h_n − v_n − w_n with h_n = (1 − ρ(ℓ+n))f_n, v_n = n(t + τ(ℓ+n−1))f_{n−1} and w_n = C(n,2)τ f_{n−2}. So A_j = H_j − V_j − W_j for j ≥ 1, and φ_n = ρ(ℓ+n)f_n + n(t + τ(ℓ+n−1))f_{n−1} + C(n,2)τ f_{n−2}.
- *Your mixed detours (round 6, eq. 20).* B_0H′_{j−1} ≥ 10cH_j, B_0V′_{j−1} ≥ (9/2)cV_j, B_0W′_{j−1} ≥ 3cW_j, B_0C′_{j−1} ≥ 6cC′_j. All are verified exactly.
- *Missing piece 1 (B-detour).* 4c_{ℓ+1}B_j(ℓ,a) ≤ B_0(ℓ,a)B_{j−1}(ℓ+1,a−2), or any other route to P² ≥ 4Q.
  - Newton(c) need not be log-concave; e.g. d_i = i/4 and ρ = 1/2 + C(x,2)/40 give (1/8, 1/80, 3/160, 0).
  - Proposition 8.10's argument used the explicit form of quadratic d (u ≤ ℓv, and the terms τ(u + 2(ℓ+1)v)) and only needed n = 2.
- *Missing piece 2 (key inequality).* A_0B_0′ + B_0A_0″ ≥ c(4H_1 − γ_V V_1 − γ_W W_1), with γ_V = 20/9 and γ_W = 4/3 affordable (your eq. 22). Numerically even γ_V = 2, γ_W = 0 holds.

## Evidence (exact rational arithmetic)

- *Scalar checks.* The B-detour 4cB_j ≤ B_0B′_{j−1} and the key inequality (with −2V₁, and with eq. 22) held at every source of every random member of (Q), N = 4–11. The members had random log-concave Newton profiles, random r, and (t, τ) up to equality in the monotonicity condition. About 260 arrays; log-concavity of Newton(c) failed in more than half of them.
- *(P).* Full tables of (P) up to N = 26, and the rows g(m,N;k) up to N = 150: no failures in (Q).
- *M ≥ 0.* The resummed operator M is entrywise ≥ 0 on 310 random members (N ≤ 12).

## Questions

1. **The B-detour for (Q).** Prove c_{ℓ+1}φ_{n+2}(ℓ) ≤ φ_2(ℓ)φ_n(ℓ+1) for n ≥ 2 on the relevant range, or the summed detour 4c_{ℓ+1}B_j ≤ B_0B′_{j−1} directly.
   - Your own observation: the φ_n are differences of a product of the log-concave-Newton d with a convex quadratic, so a product-rule argument with ℓ-dependent bounds (as in Proposition 8.10) may be needed.
   - Alternatively, give a different grouping of the c-moves that keeps M ≥ 0.
2. **The key inequality for (Q)**, in the form of eq. (22) or stronger, using only nondecreasing b (endpoint form) and log-concavity of Newton(d).
3. If (Q) is too large, give the largest clean subclass you can prove, for instance τ small relative to t, or profiles of Newton degree ≤ 3. Or give a candidate counterexample (to (P), or to M ≥ 0) that I can check exactly.

As before, please give complete arguments with every inequality explicit. I check everything in exact arithmetic and then formalize it in Lean.
