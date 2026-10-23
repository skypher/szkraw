"""Small n (2, 3): test the scalar coefficient forms (affine in u0) at u0 = 0 and u0 = its maximum, over random
log-concave (u1..u7), for two u0 bounds: (A) min(l u1, u1^2/u2); (B) (u1^2/u2)(1 - (u1/(u1+u2))^l) (geometric-extremal).
Also checks bound (B) on realizable u (u_k = sum_h C(l,h) nu_{k+h}, nu LC, nu_0 = 0). Usage: small_n_test.py trials seed"""
import sys, math, random
sys.path.insert(0, __import__('os').path.dirname(__import__('os').path.abspath(__file__)))
from small_n_forms import lam
T, rng = int(sys.argv[1]), random.Random(int(sys.argv[2]))
TG = {'rt': ['rt'], 'tt': ['tt'], 'ts': ['ts'], 'taus': ['taus'], 'ss': ['ss'], 'ttau': ['ttau'], 'ttau+rs': ['ttau', 'rs']}
def lc_tail():
    x = [10 ** rng.uniform(-3, 3) for _ in range(6)]; x.sort(reverse=True)  # ratios u_{k}/u_{k+1}... decreasing q's
    us = [1.0]
    for q in x: us.append(us[-1] * q)
    return us  # u1..u7
def bA(l, u1, u2): return min(l * u1, u1 * u1 / u2)
def bB(l, u1, u2): return (u1 * u1 / u2) * (1 - (u1 / (u1 + u2)) ** l)
# (B) on realizable profiles
viol = 0
for _ in range(T):
    L = rng.choice([1, 2, 3, 6, 40])
    qs = sorted((10 ** rng.uniform(-3, 3) for _ in range(L)), reverse=True)
    nu = [0.0, 1.0]
    for q in qs: nu.append(nu[-1] * q)
    nu += [0.0] * 60
    for l in range(1, 12):
        uu = [sum(math.comb(l, h) * nu[k + h] for h in range(l + 1)) for k in range(3)]
        if uu[2] > 0 and uu[0] > bB(l, uu[1], uu[2]) * (1 + 1e-9): viol += 1
print('bound (B) violations on realizable profiles:', viol)
for n in (2, 3):
    F = lam(n); worst = {}
    for _ in range(T):
        tail = lc_tail()
        for l in list(range(1, 13)) + [20, 50, 200]:
            for bname, bf in (('A', bA), ('B', bB)):
                for u0 in (0.0, bf(l, tail[0], tail[1])):
                    uv = [u0] + tail
                    vals = {k: F[k](l, uv) for k in F}
                    for name, keys in TG.items():
                        v = sum(vals[k] for k in keys)
                        scale = sum(abs(x) for x in vals.values()) + 1e-300
                        key = (bname, name)
                        if key not in worst or v / scale < worst[key][0]: worst[key] = (v / scale, l, u0 > 0)
    print(f'n = {n}: worst relative value (value/scale, l, at u0 max):')
    for k in sorted(worst): print('  ', k, '%.3e' % worst[k][0], worst[k][1:])
