# Research consult, round 6: convex quadratic ratios, and nondecreasing b in place of the slope bound

Thanks for round 5 (reviews/consult-G-answer.md, github.com/skypher/szkraw). Your resummation is now Theorem 8.9 of paper.tex (linearly increasing ratio ρ_i = r + ti with (2N−1)t ≤ 1 − r and a profile d with log-concave Newton coefficients). Its written proof passed an independent review, and it is machine-verified in Lean 4: `Szkraw.affine_matrix`, files lean/Szkraw/VRResum.lean, VRMoves.lean, VRAffine*.lean. The Lean proof needs the detour constant 4 only, and in the key inequality only the products (i,j) = (1,n−1), (n−1,1) for n ≥ 3 and (2,n−2) for n ≥ 4.

I would like to push the same proof one step further: a proof for the class below, or a counterexample.

## Setting (unchanged from round 5)

- *Normalization.* a_i + b_i + c_i = 1 (0 ≤ i ≤ N), b_0 = c_0 = 0, a_N = 0, a_i > 0 for i < N, c_i > 0 for i ≥ 1. Property (P) means g(m,n;k) ≥ 0 for all m, n, k.
- *Kernel recurrence (every array).* c_{ℓ+1} ω_{ℓ+1,a} = a_{ℓ+a} ω_{ℓ,a} + Σ_{j≥0} (−1)^j [A_j(ℓ−j, a+2j+1) ω_{ℓ−j,a+2j+1} + B_j(ℓ−j, a+2j+2) ω_{ℓ−j,a+2j+2} + C_j(ℓ−j−1, a+2j+2) ω_{ℓ−j−1,a+2j+2}].
- *Weights.* A_j = W^ψ_{2j+1,j}, B_j = W^φ_{2j+2,j}, C_j = W^f_{2j+2,j+1}, with W^X_{p,q}(ℓ,a) = Σ_{n≥p} C(n−p+q,q) C(a,n) X_n(ℓ). Here φ_n = Δ^n c, ψ_n = Δ^n b, f_n = Δ^n d at ℓ; all occurring indices satisfy ℓ + n ≤ N. Also A_0(ℓ,a) = b_{ℓ+a} − b_ℓ.
- *Resummation of Theorem 8.9.* Operators are taken on Ω = {ℓ + a ≤ N}, divided by c at the destination. P, Q are the B-moves with j even and odd. G = (I − P/2)^{−1}, and the target is M = G(U + P²/4 − Q + C + A)G ≥ 0.

## Target class (Q)

- *Profile.* d = b + c has Newton coefficients log-concave without internal zeros, as before.
- *Ratio.* ρ(x) = r + tx + τ C(x,2) with r > 0, t ≥ 0, τ ≥ 0: an increasing convex quadratic. Then c_i = ρ(i)d_i and b_i = (1 − ρ(i))d_i.
- *Monotonicity.* b is nondecreasing; this forces ρ(N) ≤ 1.

Class (Q) contains Theorem 8.9: when τ = 0, (2N−1)t ≤ 1 − r and convexity of d imply that b is nondecreasing. For curved d, nondecreasing b allows t up to about 1.2–1.7 times the Theorem 8.9 bound.

## Evidence (exact rational arithmetic)

- *(P), full tables (all m, n, k).*
  - Convex quadratic, cubic and linear-plus-quadratic ratios (with linear ratios as controls), N ≤ 26: about 2,600 arrays, linear and curved profiles, κ up to the maximum allowed by nondecreasing b. No negative coefficient.
- *(P), the row g(m,N;k), m, k ≤ N.*
  - N = 20–150 for the same families: about 2,100 arrays. No negative coefficient.
- *M ≥ 0.* The operator M of Theorem 8.9's proof is entrywise ≥ 0 on 310 random members of (Q), N = 4–12.
  - This includes linear ratios beyond the Theorem 8.9 bound.
  - Calibration: M has negative entries for the failing families below and for the cubic ratio ρ = r + κ(i/N)³ on a linear profile, where (P) holds but M does not.
- *Failures outside (Q).*
  - Concave increasing ratios fail already at N = 3: d_i = i/3 and ρ = (1/2, 3/4, 5/6), where b_i = 1/6 for i ≥ 1, give g(3,3;3) = −1/24.
  - Kinked convex ratios fail; paper.tex records a linear-profile example at N = 120.
  - The steep ratio ρ_i = r + κ2^{i−N} fails on linear profiles from N = 8.

## Ingredients: exact checks on 180 random members of (Q), N = 4–11

- *Split.* ψ_n = h_n − v_n − w_n with h_n = (1 − ρ(ℓ+n)) f_n, v_n = n (t + τ(ℓ+n−1)) f_{n−1}, w_n = C(n,2) τ f_{n−2}; exact. Split A_j = H_j − V_j − W_j for j ≥ 1. With the signs (−1)^j, W behaves like V: W₊ (odd j, including W_1) is positive and W₋ (even j ≥ 2) negative.
- *Detours.* All of the following held on Ω, for every member:
  - 4c B_j ≤ B_0 B_{j−1}′;
  - 4c H_j ≤ B_0 H_{j−1}′ (j ≥ 2);
  - 4c V_j ≤ B_0 V_{j−1}′ (j ≥ 2);
  - 2c W_j ≤ B_0 W_{j−1}′ (j ≥ 2);
  - 4c C′_j ≤ B_0 C′_{j−1}′.

  Here the prime denotes evaluation at (ℓ+1, a−2).
- *Key inequality.* A_0(ℓ,a) B_0(ℓ+1,a−1) + B_0(ℓ,a) A_0(ℓ+1,a−2) ≥ c_{ℓ+1}(4H_1 − 2V_1) held at every source with a ≥ 3.
- *Sufficiency.* With these, the resummation of Theorem 8.9 goes through. W needs only the constant 2, since G(W₊ − W₋)G ≥ GW₊ ≥ 0, and V keeps its leftover (1/2)GV_1G for the key inequality.

## What breaks in the Theorem 8.9 proof

1. **Newton(c) is not log-concave** in about 60% of members, so Lemma 8.3 for φ, behind P² ≥ 4Q, is unavailable. Smallest example: d_i = i/4, ρ(x) = 1/2 + C(x,2)/40, so b is nondecreasing and Newton(c) = (1/8, 1/80, 3/160, 0), with (1/80)² < (1/8)(3/160). Yet the scalar B-detour 4c_{ℓ+1}B_j(ℓ,a) ≤ B_0(ℓ,a)B_{j−1}(ℓ+1,a−2) held everywhere. Splitting φ_n = ρ(ℓ+n)f_n + nΔρ(ℓ+n−1)f_{n−1} + C(n,2)τ f_{n−2} and treating the three pieces separately loses too much: the piece with f_{n−2} needs the constant C(n+2,2)/C(n,2) = 6 at n = 2.
2. **The key inequality** used α = 1 − ρ(ℓ+a) ≥ t(a−1), which came from the slope bound. Under nondecreasing b only, this fails, yet the key inequality held numerically.
3. **The V and W detours** have per-term constants up to (5/3)(4/3) = 20/9 and C(n+2,2)/C(n,2), from Lemma 8.3 with indices (2, n−1) and (2, n−2). Against the coefficient ratios jm(m−1)/(2(m−j−1)), these seem to suffice for factor 4 (V) and factor 2 (W), but I have not checked every corner.

## Questions

1. Prove the B-detour inequality for class (Q) without log-concavity of Newton(c), or give another way to get P² ≥ 4Q, or an alternative splitting of the c-moves that keeps the resummation.
2. Prove the key inequality A_0B_0′ + B_0A_0″ ≥ c(4H_1 − 2V_1) for class (Q) using only nondecreasing b (and log-concave Newton(d)). Use 2W_1 on the right if that helps; the resummation can afford γW_1 only if the W detour has a constant μ_W with 1 − 2/μ_W ≥ γ/4.
3. If (Q) is too large for this route, give the cleanest subclass that works, for instance τ = 0 with nondecreasing b, which would sharpen Theorem 8.9. If you think (P) fails in (Q), give a candidate counterexample: large N, ρ(N) close to 1, extreme profiles.

Please give complete arguments with every inequality explicit; I will check everything in exact arithmetic and then formalize it in Lean.
