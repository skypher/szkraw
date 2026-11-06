"""Property (P) and the criteria of P1 and P2, exact."""
from fractions import Fraction as F
from math import comb


def min_g(a, b, c):
    """Smallest product coefficient g(m,n;k) = [R_m(J)]_{n,k}."""
    N = len(a) - 1
    J = [[F(0)] * (N + 1) for _ in range(N + 1)]
    for i in range(N + 1):
        if i < N:
            J[i][i + 1] = a[i]
        J[i][i] = b[i]
        if i > 0:
            J[i][i - 1] = c[i]
    mul = lambda X, Y: [[sum(X[i][k] * Y[k][j] for k in range(N + 1) if X[i][k]) for j in range(N + 1)]
                        for i in range(N + 1)]
    I = [[F(int(i == j)) for j in range(N + 1)] for i in range(N + 1)]
    prev, cur = None, I
    best = min(min(r) for r in I)
    for m in range(N):
        JR = mul(J, cur)
        nxt = [[(JR[i][j] - b[m] * cur[i][j] - (c[m] * prev[i][j] if prev else 0)) / a[m]
                for j in range(N + 1)] for i in range(N + 1)]
        prev, cur = cur, nxt
        best = min(best, min(min(r) for r in cur))
    return best


def newton(u):
    return [sum((-1) ** (k - i) * comb(k, i) * u[i] for i in range(k + 1)) for k in range(len(u))]


def lcnz(u):
    u = list(u)
    if any(v < 0 for v in u):
        return False
    pos = [k for k, v in enumerate(u) if v > 0]
    if not pos or pos[-1] - pos[0] + 1 != len(pos):
        return False
    z = [F(0)] + u + [F(0)]
    return all(z[k] ** 2 >= z[k - 1] * z[k + 1] for k in range(1, len(z) - 1))


def nondecr(u):
    return all(u[i + 1] >= u[i] for i in range(len(u) - 1))


def ratio_newton(rho1, t):
    """Newton coefficients of (t, rho(1), ..., rho(N))."""
    return newton([t] + rho1)


def t_candidates(rho1):
    """Candidate values of the free rho(0): roots of the linear and quadratic
    constraints in t, midpoints between them, and points beyond."""
    N = len(rho1)
    s = [newton([F(0)] + rho1)[k] for k in range(N + 1)]  # rho_k = s_k + (-1)^k t
    roots = set()
    for k in range(N + 1):
        roots.add((-1) ** (k + 1) * s[k] if k else F(0))
    fl = sorted(float(r) for r in roots)
    for k in range(1, N + 1):
        # (s_k+e_k t)^2 - (s_{k-1}+e_{k-1} t)(s_{k+1}+e_{k+1} t), e_j = (-1)^j
        sk = [float(s[j]) if j <= N else 0.0 for j in range(k - 1, k + 2)]
        ek = [(-1) ** j if j <= N else 0 for j in range(k - 1, k + 2)]
        A2 = ek[1] ** 2 - ek[0] * ek[2]
        A1 = 2 * sk[1] * ek[1] - sk[0] * ek[2] - sk[2] * ek[0]
        A0 = sk[1] ** 2 - sk[0] * sk[2]
        if A2 == 0:
            if A1 != 0:
                fl.append(-A0 / A1)
        else:
            D = A1 * A1 - 4 * A2 * A0
            if D >= 0:
                fl += [(-A1 - D ** 0.5) / (2 * A2), (-A1 + D ** 0.5) / (2 * A2)]
    fl = sorted(set(fl))
    cands = set(r for r in roots if r > 0)
    pts = [x for x in fl if x > 0]
    for x, y in zip([0.0] + pts, pts + [(pts[-1] if pts else 1.0) * 2 + 1]):
        cands.add(F((x + y) / 2).limit_denominator(10**12))
    return sorted(cands)


def exists_t(rho1, pred):
    for t in t_candidates(rho1):
        if t > 0 and pred(ratio_newton(rho1, t)):
            return t
    return None


def check_all(a, b, c):
    N = len(a) - 1
    d = [b[i] + c[i] for i in range(N + 1)]
    res = {}
    res["stoch"] = all(v >= 0 for v in b)
    incr = all(d[i + 1] > d[i] for i in range(N))
    nu = newton(d)
    prof = incr and lcnz(nu[1:])
    if not all(d[i] > 0 for i in range(1, N + 1)):
        rho1 = None
        res["const_ratio"] = False
    else:
        rho1 = [c[i] / d[i] for i in range(1, N + 1)]
        res["const_ratio"] = len(set(rho1)) == 1
    res["profile_lc"] = prof
    res["b_nondecr"] = nondecr(b)
    res["P1"] = bool(prof and res["const_ratio"] and rho1[0] <= 1)
    res["P2_A"] = bool(prof and res["b_nondecr"] and exists_t(rho1, lcnz))

    def quad(r):
        return all(v == 0 for v in r[3:]) and r[0] > 0 and all(v >= 0 for v in r[1:3])

    def cubic74(r):
        if not (all(v == 0 for v in r[4:]) and r[0] > 0 and all(v >= 0 for v in r[1:4])):
            return False
        r4 = list(r) + [F(0)] * 4
        return r4[0] * r4[3] <= F(7, 4) * r4[1] * r4[2]

    res["P2_quadratic"] = bool(prof and res["b_nondecr"] and exists_t(rho1, quad))
    res["P2_cubic"] = bool(prof and res["b_nondecr"] and exists_t(rho1, cubic74))
    ka, be = newton(c), newton(b)
    # Theorem lc-vary
    ok = lcnz(ka[1:]) and all(v >= 0 for v in be)
    if ok:
        K = [F(0)] + ka[1:] + [F(0)] * (N + 3)
        Bt = [F(0)] + be[1:] + [F(0)] * (N + 3)
        phi = lambda n, l: sum(comb(l, h) * K[n + h] for h in range(l + 1) if n + h < len(K))
        psi = lambda n, l: sum(comb(l, h) * Bt[n + h] for h in range(l + 1) if n + h < len(Bt))
        for l in range(N):
            for n in range(2, N + 2):
                if psi(1, l) * phi(n, l + 1) < c[l + 1] * psi(n + 1, l):
                    ok = False
            for n in range(1, N + 2):
                if phi(2, l) * psi(n, l + 1) < c[l + 1] * psi(n + 2, l):
                    ok = False
    res["P2_vary"] = ok
    res["P2_quadarray"] = (all(v == 0 for v in ka[3:]) and all(v == 0 for v in be[3:])
                           and (N < 2 or (ka[2] >= 0 and ka[2] + be[2] >= 0)) and res["b_nondecr"])
    res["P2_lowdeg"] = (incr and all(v == 0 for v in nu[3:]) and nu[1] > 0 and (N < 2 or nu[2] >= 0)
                        and lcnz(ka[1:]) and res["b_nondecr"])
    res["any_P1P2"] = any(res[k] for k in ["P1", "P2_A", "P2_quadratic", "P2_cubic", "P2_vary",
                                            "P2_quadarray", "P2_lowdeg"])
    return res
