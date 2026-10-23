"""Phi = a u0 Aal + X T >= 0 for nonnegative log-concave sequences u_0..u_{a+1}? (X = sum_{n>=1} C(a,n) u_n).
Adversarial families: geometric with small ratio, two-ratio sequences, random sorted ratios, random u0 scale."""
import sys, math, random
from fractions import Fraction as F
_HERE = __import__('os').path.dirname(__import__('os').path.abspath(__file__))
sys.path.insert(0, _HERE)
from T_test import TA
def Phi(u, a):
    T, A = TA(u, a); X = sum(math.comb(a, n) * u[n] for n in range(1, a + 1))
    return a * u[0] * A + X * T, T, A
if __name__ == '__main__':
    rng = random.Random(int(sys.argv[1])); worst = (F(10**9),); n = 0
    def consider(u, a, tag):
        global worst, n
        P, T, A = Phi(u, a); n += 1
        scale = (sum(u[:a + 1])) ** 3
        if P / scale < worst[0]: worst = (P / scale, float(P), a, tag, [float(x) for x in u[:5]])
    for a in range(3, 15):
        for q in [F(1, 10 ** k) for k in range(0, 6)] + [F(1, 2), F(1, 3), F(2), F(10)]:
            for u0 in [F(1), F(10), F(1, 10), F(1000)]:
                u = [u0] + [q ** k for k in range(a + 1)]
                if u0 * q ** 1 <= 1 or True:
                    # LC needs u0*u2 <= u1^2: u0*q <= 1
                    if u0 * q <= 1: consider(u, a, ('geo', q, u0))
        for _ in range(3000):
            u0 = F(rng.choice([1, 10, 100, 10 ** 4])) / rng.choice([1, 10, 1000])
            qs = sorted((F(rng.randint(1, 1000), rng.choice([10, 1000, 10 ** 5])) for _ in range(a + 1)), reverse=True)
            if rng.random() < .3: qs = [qs[0]] * 2 + [qs[-1]] * (a - 1)
            u = [u0]; ok = True
            for k in range(a + 1): u.append(u[-1] * qs[k])
            consider(u, a, ('rand',))
    print(n, 'worst Phi/scale', float(worst[0]), worst[1:])
