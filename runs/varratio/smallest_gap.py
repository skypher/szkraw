"""Smallest curved-profile linear-ratio example where signed P^2 >= 4Q fails; print the array and the offending entries."""
import sys, math, random
from fractions import Fraction as F
_HERE = __import__('os').path.dirname(__import__('os').path.abspath(__file__))
sys.path.insert(0, __import__('os').path.join(_HERE, '..', '..')); sys.path.insert(0, _HERE)
from kernel_check import tools
from mixed import newton_coeffs
from hform import lc_seq

def signed_entries(b, c):
    N = len(c) - 1
    nu, be, f, W, cpol, bpol = tools(b, c)
    dn = [x + y for x, y in zip(nu, be)]
    M = {}
    for l in range(N + 1):
        for a in range(N + 1 - l):
            for j in range(N + 1):
                for typ, wt, (dl, da) in (('A', W(be, 2*j+1, j, l, a), (j+1, -(2*j+1))), ('B', W(nu, 2*j+2, j, l, a), (j+1, -(2*j+2))),
                                          ('C', W(dn, 2*j+2, j+1, l, a), (j+2, -(2*j+2)))):
                    lt, at = l + dl, a + da
                    if at < 0 or lt + at > N or wt == 0: continue
                    key = ((l, a), (lt, at))
                    M.setdefault(key, []).append((typ, j, (-1) ** j * wt / cpol(lt)))
    tot = {k: sum(x[2] for x in v) for k, v in M.items()}
    P = {k: v for k, v in tot.items() if v > 0}; Q = {k: -v for k, v in tot.items() if v < 0}
    P2 = {}
    for (x, y), w1 in P.items():
        for (y2, z), w2 in P.items():
            if y2 == y: P2[(x, z)] = P2.get((x, z), F(0)) + w1 * w2
    return [(k, M[k], q, P2.get(k, F(0))) for k, q in Q.items() if P2.get(k, F(0)) < 4 * q]

rng = random.Random(11)
for N in range(3, 9):
    found = None
    for trial in range(400):
        sig = lc_seq(rng, N)
        D = [sum(math.comb(n, k) * sig[k - 1] for k in range(1, n + 1)) for n in range(N + 1)]
        d = [x / D[N] for x in D]
        r = F(rng.randint(1, 9), 10); kappa = (1 - r) / 2 * F(rng.randint(1, 4), 4)
        rho = [r + kappa * n / N for n in range(N + 1)]
        c = [p * x for p, x in zip(rho, d)]; b = [(1 - p) * x for p, x in zip(rho, d)]
        bad = signed_entries(b, c)
        if bad:
            found = (sig, d, r, kappa, b, c, bad); break
    if found:
        sig, d, r, kappa, b, c, bad = found
        print(f'N={N}: profile Newton coefficients {[str(x) for x in newton_coeffs(d)[1:]]}, r={r}, kappa={kappa}')
        print('  d =', [str(x) for x in d]); print('  b =', [str(x) for x in b]); print('  c =', [str(x) for x in c])
        print('  Newton(b) =', [str(x) for x in newton_coeffs(b)]); print('  Newton(c) =', [str(x) for x in newton_coeffs(c)])
        for k, moves, q, p2 in bad[:3]:
            print(f'  entry {k}: moves {[(t, j, str(w)) for t, j, w in moves]}, |Q| = {q}, P^2 = {p2}')
        break
    else:
        print(f'N={N}: none in 400 trials')
