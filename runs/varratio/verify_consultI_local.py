"""(1) on local configurations: u_0..u_{n+3} nonnegative log-concave without internal zeros, u_0 <= l u_1 (convexity),
rho(x) = r + t x + tau C(x,2) with r > 0, t, tau >= 0; phi_n(l) by the quadratic Leibniz rule; u(l+1)_k = u_k + u_{k+1}.
Checks (n+1)(n+2) phi_2(l) phi_n(l+1) >= 8(n-1) c_{l+1} phi_{n+2}(l). Usage: seed count"""
import sys, random, math
from fractions import Fraction as F
rng = random.Random(int(sys.argv[1])); worst = None; cnt = 0
for _ in range(int(sys.argv[2])):
    n = rng.randint(2, 12); l = rng.choice([0, 1, 2, 3, 5, 10, 30, 100, 200])
    m = n + 4
    qs = sorted((F(rng.randint(1, 1000), rng.choice([1, 10, 100, 1000, 10 ** 5])) for _ in range(m)), reverse=True)
    if rng.random() < .3: qs = [qs[0]] * m
    u = [F(1)]
    for k in range(m): u.append(u[-1] * qs[k])
    u = u[1:] if rng.random() < 0 else u
    # u_0 is index 0: enforce u_0 <= l u_1 by scaling u_0 down if needed, keeping LC (lowering u_0 keeps LC)
    if u[0] > l * u[1]: u[0] = l * u[1] * F(rng.randint(0, 100), 100)
    if rng.random() < .3: u[0] = u[0] * F(rng.randint(0, 10), 10)
    r = F(rng.randint(1, 100), 100); t = F(rng.randint(0, 100), rng.choice([100, 10 ** 4])); tau = F(rng.randint(0, 100), rng.choice([100, 10 ** 4, 10 ** 6]))
    rho = lambda x: r + t * x + tau * F(x * (x - 1), 2)
    dr = lambda x: t + tau * x
    U = lambda k: u[k] if k >= 0 else F(0)
    U1 = lambda k: (u[k] + u[k + 1]) if k >= 0 else F(0)
    phi = lambda nn, base, uu: rho(base + nn) * uu(nn) + nn * dr(base + nn - 1) * uu(nn - 1) + F(nn * (nn - 1), 2) * tau * uu(nn - 2)
    lhs = (n + 1) * (n + 2) * phi(2, l, U) * phi(n, l + 1, U1)
    rhs = 8 * (n - 1) * rho(l + 1) * (u[0] + u[1]) * phi(n + 2, l, U)
    cnt += 1
    if rhs > 0:
        q = lhs / rhs
        if worst is None or q < worst[0]: worst = (q, n, l, float(r), float(t), float(tau), [float(x) for x in u[:4]])
print(cnt, 'min lhs/rhs', float(worst[0]), worst[1:])
