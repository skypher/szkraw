"""T = Y X' - a u0 Y' - (a-2) D Y - D*(4*sum (n-2)(a-n)C(a,n)u_n - 2*sum (n-2) n C(a,n) u_{n-1}) >= 0 ?
for arbitrary nonnegative log-concave sequences u_0..u_a without internal zeros (F1_j = u_j + u_{j+1}, D = u_0 + u_1).
Also tests Aal = X Y' + Y X' - 4 D sum (n-2) C(a,n) u_n >= 0."""
import sys, math, random
from fractions import Fraction as F
def TA(u, a):
    F1 = lambda j: u[j] + (u[j + 1] if j + 1 < len(u) else 0); D = u[0] + u[1]
    X = sum(math.comb(a, n) * u[n] for n in range(1, a + 1)); Y = sum(math.comb(a, n) * u[n] for n in range(2, a + 1))
    Xp = sum(math.comb(a - 2, j) * F1(j) for j in range(1, a - 1)); Yp = sum(math.comb(a - 1, j) * F1(j) for j in range(2, a))
    H1t = sum((n - 2) * math.comb(a, n) * (a - n) * u[n] for n in range(3, a + 1))
    V1t = sum((n - 2) * math.comb(a, n) * n * u[n - 1] for n in range(3, a + 1))
    Ht = sum((n - 2) * math.comb(a, n) * u[n] for n in range(3, a + 1))
    T = Y * Xp - a * u[0] * Yp - (a - 2) * D * Y - D * (4 * H1t - 2 * V1t)
    A = X * Yp + Y * Xp - 4 * D * Ht
    return T, A
if __name__ == '__main__':
    rng = random.Random(int(sys.argv[1])); worstT = None; worstA = None; n = 0
    for _ in range(int(sys.argv[2])):
        a = rng.randint(3, 12)
        # LC sequence: u_0 = U0, ratios nonincreasing
        u0 = F(rng.choice([1, 1, 1, 10, 100, 1000]))
        q = sorted((F(rng.randint(0, 1000), rng.choice([10, 100, 1000])) for _ in range(a + 1)), reverse=True)
        K = rng.randint(1, a + 1)
        u = [u0]
        for k in range(a + 1):
            u.append(u[-1] * q[k] if k + 1 < K + 1 else F(0))
        u = u[:a + 2]
        T, A = TA(u, a); n += 1
        if worstT is None or T / max(abs(A), F(1, 10**9)) < worstT[0]: worstT = (T / max(abs(A), F(1, 10**9)), float(T), a, [float(x) for x in u[:6]])
        if A < 0: worstA = (float(A), a)
    print(n, 'min T/|A|', float(worstT[0]), worstT[1:], 'A<0 example', worstA)
