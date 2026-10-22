"""Is log-concavity of Newton coefficients preserved under pointwise products? Random rho, d with nonnegative
log-concave Newton coefficients without internal zeros (rho_0 = r > 0; d: nu_0 = 0, nu_1 > 0); check Newton(rho*d) on 0..N.
Usage: newton_product_lc.py N trials seed"""
import sys, random, math
from fractions import Fraction as F

def lc_seq(rng, K, first_zero):
    ratios = sorted((F(rng.randint(0, 60), 20) for _ in range(K)), reverse=True)
    out = [F(0)] if first_zero else []
    x = F(rng.randint(1, 20), 10)
    for i in range(K + 1):
        out.append(x); x *= ratios[i] if i < K else 0
    return out

def newton(seq):
    return [sum((-1) ** (k - i) * math.comb(k, i) * seq[i] for i in range(k + 1)) for k in range(len(seq))]

def is_lcnz(nu, start):
    v = nu[start:]
    if any(x < 0 for x in v): return False
    sup = [i for i, x in enumerate(v) if x > 0]
    if sup and sup != list(range(sup[0], sup[-1] + 1)): return False
    return all(v[k] ** 2 >= v[k - 1] * v[k + 1] for k in range(1, len(v) - 1))

if __name__ == '__main__':
    N, T, rng = int(sys.argv[1]), int(sys.argv[2]), random.Random(int(sys.argv[3]))
    bad = 0
    for _ in range(T):
        rc = lc_seq(rng, rng.randint(0, N), False)[:N + 1]; dc = lc_seq(rng, rng.randint(0, N - 1), True)[:N + 1]
        rc += [F(0)] * (N + 1 - len(rc)); dc += [F(0)] * (N + 1 - len(dc))
        rho = [sum(rc[k] * math.comb(n, k) for k in range(N + 1)) for n in range(N + 1)]
        d = [sum(dc[k] * math.comb(n, k) for k in range(N + 1)) for n in range(N + 1)]
        kap = newton([x * y for x, y in zip(rho, d)])
        if not is_lcnz(kap, 1):
            bad += 1
            if bad <= 3: print('counterexample: Newton(rho) =', [str(x) for x in rc], ' Newton(d) =', [str(x) for x in dc], ' Newton(c) =', [float(x) for x in kap])
    print(f'N={N}: {bad}/{T} products not log-concave')
