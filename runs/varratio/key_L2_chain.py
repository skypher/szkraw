"""(L2) reduction chain and the Lin coefficients (exact, random LC u). For m >= 2:
  E2^(m) >= C(a-1,m-1) A (B-d1)/2,  E1^(m) >= C(a-1,m-1) A (B-d0)/2,  B0'^(1) >= (a-2)(A-d1),
  (i)  R = a(A-d1)(B-d1) - 8 d1 H* >= 0  ==>  B0^(1) E2^(m) >= 4 D C(a-1,m-1) B H*,
  (ii) R2 = (a-2)(A-d1)(B-d0) - 4a d1 H* >= 0  ==>  B0'^(1) E1^(m) >= D F [4 Z_m - 2 V1^(m)]  (the other terms of (ii) are >= 0),
  and M_{1,m} + M_{m,1} = [(i) lhs - rhs] + [(ii) lhs - rhs] (identity).
Lin(P) coefficients: l_0 = K (Theorem 8.9), l_1 >= L1low = (A-d1)((a-2)X + a X') - 4 D H*, l_k >= 0 for k >= 2.
Usage: key_L2_chain.py amax trials seed"""
import sys, math, random
from fractions import Fraction as Fr
import sympy as sp
sys.path.insert(0, '/home/yang/szkraw/runs/varratio')
from key_S_low import pieces
from key_phi import parts
C = math.comb
amax, T, rng = int(sys.argv[1]), int(sys.argv[2]), random.Random(int(sys.argv[3]))
def lc(L):
    r = sorted((Fr(rng.randint(1, 40), 10) for _ in range(L)), reverse=True)
    u = [Fr(rng.randint(0, 30), 10)]; u.append(u[0] * r[0] if u[0] else Fr(1))
    for x in r[1:]: u.append(u[-1] * x)
    return u
fails = {}
def chk(name, ok):
    if not ok: fails[name] = fails.get(name, 0) + 1
cnt = 0
for a in range(3, amax + 1):
    seqs = [lc(a + 4) for _ in range(T)] + [[1 / w, Fr(1)] + [w ** (n - 1) for n in range(2, a + 5)] for w in (Fr(1, 10), Fr(1, 1000), Fr(10))]
    for u in seqs:
        d = lambda n: sum(C(n, k) * u[k] for k in range(n + 1))
        A, B, d0, d1, d2 = d(a), d(a - 1), d(0), d(1), d(2); D = d1; Fv = A - B
        y = lambda n: C(a, n) * u[n]; Hs = sum((n - 2) * y(n) for n in range(3, a + 1))
        X, Xp = A - d0, B - d1
        B0_1, B0p_1 = a * (A - d1), a * A - 2 * (a - 1) * d2 + (a - 2) * d1
        E1 = lambda m: C(a, m) * A * (B - d0) - C(a - 1, m) * B * (A - d0)
        E2 = lambda m: C(a, m) * A * (B - d1) - C(a - 1, m) * B * (A - d1) + (d1 * Fv if m == 1 else 0)
        R = a * (A - d1) * (B - d1) - 8 * d1 * Hs; R2 = (a - 2) * (A - d1) * (B - d0) - 4 * a * d1 * Hs
        chk('B0p1 >= (a-2)(A-d1)', B0p_1 >= (a - 2) * (A - d1))
        M = pieces(u, a)
        for m in range(2, a + 1):
            cnt += 1
            c1 = C(a - 1, m - 1)
            V1 = sum((n - 2) * C(a, n) * n * C(n - 1, m - 1) * u[n - 1] for n in range(3, a + 1))
            Zm = sum((n - 2) * y(n) * (C(a, m) - C(n, m)) for n in range(3, a + 1))
            chk('E2 >= c1 A (B-d1)/2', E2(m) >= c1 * A * (B - d1) / 2); chk('E1 >= c1 A (B-d0)/2', E1(m) >= c1 * A * (B - d0) / 2)
            lhs_i, rhs_i = B0_1 * E2(m), 4 * D * c1 * B * Hs
            if R >= 0: chk('(i)', lhs_i >= rhs_i)
            B0p_m = C(a, m) * A - ((a - 1) * d2 if m == 2 else 0); B0_m = C(a, m) * A
            rest = B0p_1 * E1(m) + B0p_m * E1(1) + B0_m * E2(1)
            rhs_ii = D * Fv * (4 * Zm - 2 * V1)
            chk('other (ii) terms >= 0', B0p_m * E1(1) >= 0 and B0_m * E2(1) >= 0)
            if R2 >= 0: chk('(ii)', B0p_1 * E1(m) >= rhs_ii)
            chk('identity', M(1, m) + M(m, 1) == (lhs_i - rhs_i) + (rest - rhs_ii))
        if a <= 9:
            P, Lin, Quad, f1, Dc = parts([sp.Rational(v.numerator, v.denominator) for v in u] + [0] * 3, a)
            co = sp.Poly(Lin, *P)
            l = [co.coeff_monomial(P[k]) for k in range(a + 1)]
            K = X * (Xp + Fv - (a - 2) * u[1] + 0) if False else None
            L1low = (A - d1) * ((a - 2) * X + a * Xp) - 4 * D * Hs
            chk('l1 >= L1low', l[1] >= L1low); chk('lk >= 0 (k>=2)', all(v >= 0 for v in l[2:]))
            Y = sum(y(n) for n in range(2, a + 1)); Yp = Y - (a - 1) * u[2]
            chk('l0 == K', l[0] == X * Yp + Y * Xp - 4 * D * Hs)
print(f'{cnt} (a, u, m) cases, a <= {amax}: failures {fails if fails else "none"}')
