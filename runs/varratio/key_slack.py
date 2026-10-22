"""tau = 0, b nondecreasing (t up to the max), curved log-concave profiles. At sources (l,a) in Omega, a >= 3, compare:
 E_exact = A0 B0' + B0 A0'' - c(4H1 - 2V1)   (the key inequality)
 E_red   = D*rho'*[alpha*Gfull - t(aY' + (a-2)Y) - 4H1 + 2V1]  (Theorem 8.9's reduction, full gamma_n)
 E_mid   = rho'*[(alpha X - t a u0) Y' + Y((alpha+t)X' - t(a-2)D)] - c(4H1-2V1)  (B0, B0' replaced by rho' Y, rho' Y' only)
Reports counts where alpha < t(a-1), E_red < 0, E_mid < 0, E_exact < 0. Usage: key_slack.py Ns per seed"""
import sys, math, random
from fractions import Fraction as F
sys.path.insert(0, '/home/yang/szkraw/runs/varratio')
from hform import lc_seq

def run(d, r, t):
    N = len(d) - 1; s = 1 - r
    dif = lambda x, n, l: sum((-1) ** (n - i) * math.comb(n, i) * x[l + i] for i in range(n + 1))
    rho = lambda x: r + t * x
    c = [rho(i) * d[i] for i in range(N + 1)]; b = [d[i] - c[i] for i in range(N + 1)]
    out = []
    for l in range(N + 1):
        for a in range(3, N + 1 - l):
            u = [dif(d, n, l) for n in range(a + 1)]
            F1 = lambda j: dif(d, j, l + 1)
            D = d[l + 1]; al = s - t * (l + a); rp = r + t * (l + 1); cc = rp * D
            X = sum(math.comb(a, n) * u[n] for n in range(1, a + 1)); Y = sum(math.comb(a, n) * u[n] for n in range(2, a + 1))
            Xp = sum(math.comb(a - 2, j) * F1(j) for j in range(1, a - 1)); Yp = sum(math.comb(a - 1, j) * F1(j) for j in range(2, a))
            phi = lambda n, ll: dif(c, n, ll)
            B0 = sum(math.comb(a, n) * phi(n, l) for n in range(2, a + 1)); B0p = sum(math.comb(a - 1, j) * phi(j, l + 1) for j in range(2, a))
            A0 = b[l + a] - b[l]; A0pp = b[l + a - 1] - b[l + 1]
            H1 = sum((n - 2) * math.comb(a, n) * (s - t * (l + n)) * u[n] for n in range(3, a + 1))
            V1 = sum((n - 2) * math.comb(a, n) * t * n * u[n - 1] for n in range(3, a + 1))
            G = sum(2 * (2 ** n - n - 2) * math.comb(a, n) * u[n] for n in range(3, a + 1))
            Eex = A0 * B0p + B0 * A0pp - cc * (4 * H1 - 2 * V1)
            Ered = D * rp * (al * G - t * (a * Yp + (a - 2) * Y) - 4 * H1 + 2 * V1)
            Emid = rp * ((al * X - t * a * u[0]) * Yp + Y * ((al + t) * Xp - t * (a - 2) * D)) - cc * (4 * H1 - 2 * V1)
            out.append((l, a, al < t * (a - 1), Eex, Emid, Ered, float(al / (t * (a - 1))) if t > 0 else 9))
    return out

if __name__ == '__main__':
    Ns = [int(x) for x in sys.argv[1].split(',')]; per = int(sys.argv[2]); rng = random.Random(int(sys.argv[3]))
    cnt = {'src': 0, 'alpha_small': 0, 'Ered<0': 0, 'Emid<0': 0, 'Eex<0': 0}; worst = []
    for N in Ns:
        for _ in range(per):
            sig = lc_seq(rng, N)
            Dd = [sum(math.comb(n, k) * sig[k - 1] for k in range(1, n + 1)) for n in range(N + 1)]
            d = [x / Dd[N] for x in Dd]
            r = F(rng.randint(1, 19), 20)
            def ok(t):
                bb = [(1 - r - t * i) * d[i] for i in range(N + 1)]
                return all(bb[i + 1] >= bb[i] for i in range(N))
            lo, hi = F(0), (1 - r) / N
            for _ in range(25):
                mid = (lo + hi) / 2; lo, hi = (mid, hi) if ok(mid) else (lo, mid)
            for (l, a, small, Eex, Emid, Ered, ratio) in run(d, r, lo):
                cnt['src'] += 1
                if small: cnt['alpha_small'] += 1
                if Ered < 0: cnt['Ered<0'] += 1
                if Emid < 0: cnt['Emid<0'] += 1; worst.append((ratio, N, l, a, float(Emid), float(Eex)))
                if Eex < 0: cnt['Eex<0'] += 1
        print(N, cnt, flush=True)
    worst.sort(); print(worst[:8])
