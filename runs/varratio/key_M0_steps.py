"""M_0(s) = Y' E1(s) + Y E2(s) + D E3(s), linear in the ratio increments s_i = D rho(l+i), i = 0..a-1.
Test M_0 >= 0 on step increments e^(q) (s_i = [i >= q]) and on binomial increments (s_i = C(i,k)) for LC u (exact).
E1(s) = s_{a-1} A (B - d0) - (sum_{i<a-1} s_i) d0 F, E2(s) = s_{a-1} A (B - d1) - (sum_{1<=i<a-1} s_i) d1 F,
E3(s) = 2 F V1(s) - 4 sum_{n>=3} (n-2) y_n [F sum_{i=n}^{a-1} s_i + s_{a-1} B],  V1(s) = sum_{m=2}^{a-1} (m-1)(a-m) s_m y_m.
Usage: key_M0_steps.py amax trials seed"""
import sys, math, random
from fractions import Fraction as Fr
C = math.comb
amax, T, rng = int(sys.argv[1]), int(sys.argv[2]), random.Random(int(sys.argv[3]))
def lc(rng, L):
    ratios = sorted((Fr(rng.randint(1, 40), 10) for _ in range(L)), reverse=True)
    u = [Fr(rng.randint(0, 30), 10)]; u.append(u[0] * ratios[0] if u[0] > 0 else Fr(1))
    for r in ratios[1:]: u.append(u[-1] * r)
    return u
seqs = [lc(rng, amax + 4) for _ in range(T)]
for w in [Fr(1, 10), Fr(1, 1000), Fr(1, 10 ** 6), Fr(1), Fr(10)]:
    seqs.append([1 / w, Fr(1)] + [w ** (n - 1) for n in range(2, amax + 5)]); seqs.append([Fr(0), Fr(1)] + [w ** (n - 1) for n in range(2, amax + 5)])
step_bad = {}; binom_bad = 0; cnt = 0
for a in range(3, amax + 1):
    for u in seqs:
        d = lambda n: sum(C(n, m) * u[m] for m in range(n + 1))
        A, B, d0, d1 = d(a), d(a - 1), d(0), d(1); Fv = A - B
        y = lambda n: C(a, n) * u[n]; Y = sum(y(n) for n in range(2, a + 1)); Yp = sum(C(a - 1, n) * (u[n] + u[n + 1]) for n in range(2, a))
        def M0(s):
            E1 = s[a - 1] * A * (B - d0) - sum(s[i] for i in range(a - 1)) * d0 * Fv
            E2 = s[a - 1] * A * (B - d1) - sum(s[i] for i in range(1, a - 1)) * d1 * Fv
            V1 = sum((m - 1) * (a - m) * s[m] * y(m) for m in range(2, a))
            E3 = 2 * Fv * V1 - 4 * sum((n - 2) * y(n) * (Fv * sum(s[i] for i in range(n, a)) + s[a - 1] * B) for n in range(3, a + 1))
            return Yp * E1 + Y * E2 + d1 * E3
        for q in range(a):
            v = M0([1 if i >= q else 0 for i in range(a)]); cnt += 1
            if v < 0: step_bad[q - a] = step_bad.get(q - a, 0) + 1
        for k in range(a):
            if M0([C(i, k) for i in range(a)]) < 0: binom_bad += 1
print(f'{cnt} step tests; failures by (q - a): {step_bad}; binomial-ray failures: {binom_bad}')
