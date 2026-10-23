"""tau = 0. E_mid/rho' = alpha*Aal + t*T (exactly linear in alpha for fixed t, u). Where T < 0, the needed ratio is
alpha/t >= -T/Aal. Compare with lower bounds from nondecreasing b:
 (i) A0 >= 0: alpha/t >= a u0 / X;  (ii) A0'' >= 0: alpha/t >= (a-2) D / X' - 1;
 (iii) last step b_{l+a} >= b_{l+a-1}: alpha/t >= d_{l+a-1} / (d_{l+a} - d_{l+a-1}).
Reports the worst needed/bound ratio for each (<= 1 means that bound suffices everywhere)."""
import sys, math, random
from fractions import Fraction as F
_HERE = __import__('os').path.dirname(__import__('os').path.abspath(__file__))
sys.path.insert(0, _HERE)
from hform import lc_seq
if __name__ == '__main__':
    Ns = [int(x) for x in sys.argv[1].split(',')]; per = int(sys.argv[2]); rng = random.Random(int(sys.argv[3]))
    worst = {'i': 0, 'ii': 0, 'iii': 0, 'max': 0}; nT = 0; nsrc = 0; ex = {}
    for N in Ns:
        for _ in range(per):
            sig = lc_seq(rng, N)
            Dd = [sum(math.comb(n, k) * sig[k - 1] for k in range(1, n + 1)) for n in range(N + 1)]
            d = [x / Dd[N] for x in Dd]
            dif = lambda x, n, l: sum((-1) ** (n - i) * math.comb(n, i) * x[l + i] for i in range(n + 1))
            for l in range(N + 1):
                for a in range(3, N + 1 - l):
                    nsrc += 1
                    u = [dif(d, n, l) for n in range(a + 1)]; F1 = lambda j: dif(d, j, l + 1); D = d[l + 1]
                    X = sum(math.comb(a, n) * u[n] for n in range(1, a + 1)); Y = sum(math.comb(a, n) * u[n] for n in range(2, a + 1))
                    Xp = sum(math.comb(a - 2, j) * F1(j) for j in range(1, a - 1)); Yp = sum(math.comb(a - 1, j) * F1(j) for j in range(2, a))
                    Ht = sum((n - 2) * math.comb(a, n) * u[n] for n in range(3, a + 1))
                    Aal = X * Yp + Y * Xp - 4 * D * Ht
                    # t-part: alpha-free coefficient of t
                    H1t = sum((n - 2) * math.comb(a, n) * (a - n) * u[n] for n in range(3, a + 1))
                    V1t = sum((n - 2) * math.comb(a, n) * n * u[n - 1] for n in range(3, a + 1))
                    T = Y * Xp - a * u[0] * Yp - (a - 2) * D * Y - D * (4 * H1t - 2 * V1t)
                    if T >= 0: continue
                    nT += 1
                    need = -T / Aal
                    bi = a * u[0] / X; bii = (a - 2) * D / Xp - 1; biii = d[l + a - 1] / (d[l + a] - d[l + a - 1])
                    for k, bnd in (('i', bi), ('ii', bii), ('iii', biii), ('max', max(bi, bii, biii))):
                        q = need / bnd if bnd > 0 else F(10 ** 9)
                        if q > worst[k]: worst[k] = q; ex[k] = (N, l, a, float(need), float(bnd))
        print(N, 'sources', nsrc, 'T<0', nT, {k: float(v) for k, v in worst.items()}, flush=True)
    print(ex)
