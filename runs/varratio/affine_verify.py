"""Independent exact check of the consult-G proof for affine ratios rho_m = r + t m (t = kappa/N) with a log-concave
Newton profile d, under (T): (2N-1) t <= s = 1 - r.
Checks, on Omega = {l + a <= N}:
 (a) the split A_j = H_j - V_j (j >= 1) of the b-moves, with h_n = (s - t(l+n)) D_n, v_n = t n D_{n-1};
 (b) nonnegativity of A_0, H_j, V_j, B_j, C_j, U;
 (c) the operator inequalities (13): P^2 >= 4Q, H_+P >= 6H_-, V_+P >= 6V_-, C_+P >= 6C_-, A_0P + PA_0 + 2V_1 >= 4H_1;
 (d) M = G(R + C + A)G >= 0 with G = (I - P/2)^{-1}, R = U + P^2/4 - Q;
 (e) omega from the original recurrence equals G sum M^q G beta, and omega >= 0;
 (f) (P) by direct linearization; and Newton(c) log-concave.
Matrices act on column vectors: (T w)(y) = sum_x T[y][x] w(x); every move divided by c at its destination level."""
import sys, math, random, time
from fractions import Fraction as F
_HERE = __import__('os').path.dirname(__import__('os').path.abspath(__file__))
sys.path.insert(0, __import__('os').path.join(_HERE, '..', '..')); sys.path.insert(0, _HERE)
from probe import linearization, first_negative
from hform import lc_seq

def member(rng, N, endpoint=False):
    sig = lc_seq(rng, N)
    D = [sum(math.comb(n, k) * sig[k - 1] for k in range(1, n + 1)) for n in range(N + 1)]
    d = [x / D[N] for x in D]
    r = F(rng.randint(1, 99), 100); s = 1 - r
    tmax = s / (2 * N - 1)
    t = tmax if endpoint else tmax * F(rng.randint(0, 100), 100)
    rho = [r + t * m for m in range(N + 1)]
    c = [p * x for p, x in zip(rho, d)]; b = [(1 - p) * x for p, x in zip(rho, d)]
    return d, r, s, t, [1 - x for x in d], b, c

def newton(x):
    out, cur = [], list(x)
    while cur: out.append(cur[0]); cur = [cur[i + 1] - cur[i] for i in range(len(cur) - 1)]
    return out

def run(d, r, s, t, a_, b, c):
    N = len(d) - 1
    Dd = lambda n, l: sum((-1) ** (n - i) * math.comb(n, i) * d[l + i] for i in range(n + 1))  # Delta^n d(l), l+n <= N
    dif = lambda x, n, l: sum((-1) ** (n - i) * math.comb(n, i) * x[l + i] for i in range(n + 1))
    nodes = [(l, a) for l in range(N + 1) for a in range(N + 1 - l)]
    idx = {nd: i for i, nd in enumerate(nodes)}; K = len(nodes)
    Z = lambda: [[F(0)] * K for _ in range(K)]
    def W(seq_n, p, q, l, a):
        return sum(math.comb(n - p + q, q) * math.comb(a, n) * seq_n(n, l) for n in range(p, a + 1))
    h = lambda n, l: (s - t * (l + n)) * Dd(n, l)
    v = lambda n, l: t * n * Dd(n - 1, l)
    fc = lambda n, l: dif(c, n, l); fb = lambda n, l: dif(b, n, l); fd = lambda n, l: dif(d, n, l)
    mats = {k: Z() for k in ('U', 'A0', 'Hp', 'Hm', 'H1', 'Vp', 'Vm', 'V1', 'P', 'Q', 'Cp', 'Cm', 'Afull')}
    neg = []; split_bad = 0
    for (l, a) in nodes:
        x = idx[(l, a)]
        # straight
        if l + 1 + a <= N: mats['U'][idx[(l + 1, a)]][x] += a_[l + a] / c[l + 1]
        for j in range(N + 1):
            # A-type: displacement (j+1, -(2j+1))
            lt, at = l + j + 1, a - 2 * j - 1
            if at >= 0 and lt + at <= N:
                y = idx[(lt, at)]; cd = c[lt]
                Ab = W(fb, 2 * j + 1, j, l, a)
                if j == 0:
                    A0 = b[l + a] - b[l]
                    if A0 != Ab: split_bad += 1
                    if A0 < 0: neg.append(('A0', l, a))
                    mats['A0'][y][x] += A0 / cd
                else:
                    Hj, Vj = W(h, 2 * j + 1, j, l, a), W(v, 2 * j + 1, j, l, a)
                    if Hj - Vj != Ab: split_bad += 1
                    if Hj < 0 or Vj < 0: neg.append(('HV', j, l, a))
                    if j % 2 == 0: mats['Hp'][y][x] += Hj / cd; mats['Vm'][y][x] += Vj / cd
                    else:
                        (mats['H1'] if j == 1 else mats['Hm'])[y][x] += Hj / cd
                        mats['Vp'][y][x] += Vj / cd
                        if j == 1: mats['V1'][y][x] += Vj / cd
                mats['Afull'][y][x] += (-1) ** j * Ab / cd
            # B-type: (j+1, -(2j+2))
            lt, at = l + j + 1, a - 2 * j - 2
            if at >= 0 and lt + at <= N:
                Bj = W(fc, 2 * j + 2, j, l, a)
                if Bj < 0: neg.append(('B', j, l, a))
                (mats['P'] if j % 2 == 0 else mats['Q'])[idx[(lt, at)]][x] += Bj / c[lt]
            # C-type: (j+2, -(2j+2)), from d
            lt, at = l + j + 2, a - 2 * j - 2
            if at >= 0 and lt + at <= N:
                Cj = W(fd, 2 * j + 2, j + 1, l, a)
                if Cj < 0: neg.append(('C', j, l, a))
                (mats['Cp'] if j % 2 == 0 else mats['Cm'])[idx[(lt, at)]][x] += Cj / c[lt]
    def mm(X, Y):
        out = Z()
        for i in range(K):
            Xi = X[i]
            for k2 in range(K):
                if Xi[k2] == 0: continue
                Yk = Y[k2]; xv = Xi[k2]
                for j2 in range(K):
                    if Yk[j2] != 0: out[i][j2] += xv * Yk[j2]
        return out
    def add(*terms):
        out = Z()
        for coef, X in terms:
            for i in range(K):
                for j2 in range(K): out[i][j2] += coef * X[i][j2]
        return out
    ge = lambda X, Y: all(X[i][j2] >= Y[i][j2] for i in range(K) for j2 in range(K))
    nonneg = lambda X: all(X[i][j2] >= 0 for i in range(K) for j2 in range(K))
    P, Q = mats['P'], mats['Q']
    P2 = mm(P, P)
    checks = {
        'P2>=4Q': ge(P2, add((4, Q))),
        'H+P>=6H-': ge(mm(mats['Hp'], P), add((6, mats['Hm']))),
        'V+P>=6V-': ge(mm(mats['Vp'], P), add((6, mats['Vm']))),
        'C+P>=6C-': ge(mm(mats['Cp'], P), add((6, mats['Cm']))),
        '(9)': ge(add((1, mm(mats['A0'], P)), (1, mm(P, mats['A0'])), (2, mats['V1'])), add((4, mats['H1']))),
    }
    I = [[F(int(i == j2)) for j2 in range(K)] for i in range(K)]
    G = I; term = I
    for m in range(1, N + 2):
        term = mm(term, add((F(1, 2), P)))
        G = add((1, G), (1, term))
    R = add((1, mats['U']), (F(1, 4), P2), (-1, Q))
    Cmat = add((1, mats['Cp']), (-1, mats['Cm']))
    A = add((1, mats['A0']), (1, mats['Hp']), (-1, mats['Hm']), (-1, mats['H1']), (1, mats['Vp']), (-1, mats['Vm']))
    # consistency: A equals the signed original A-moves
    checks['A=signed A'] = all(A[i][j2] == mats['Afull'][i][j2] for i in range(K) for j2 in range(K))
    M = mm(mm(G, add((1, R), (1, Cmat), (1, A))), G)
    checks['M>=0'] = nonneg(M); checks['R>=0'] = nonneg(R)
    # (e) omega from the original recurrence for each k vs G sum M^q G beta
    T = add((1, mats['U']), (1, P), (-1, Q), (1, Cmat), (1, A))
    ok_rec = True; ok_nn = True
    Msum = I; term = I
    for q in range(1, N + 2):
        term = mm(term, M); Msum = add((1, Msum), (1, term))
    Gfull = mm(mm(G, Msum), G)
    for k in range(N + 1):
        beta = [F(int(nd == (0, k))) for nd in nodes]
        om = beta[:]
        for lvl in range(1, N + 1):  # iterate omega = beta + T omega level by level
            om = [beta[i] + sum(T[i][j2] * om[j2] for j2 in range(K)) for i in range(K)]
        om2 = [sum(Gfull[i][j2] * beta[j2] for j2 in range(K)) for i in range(K)]
        if om != om2: ok_rec = False
        if any(x < 0 for x in om): ok_nn = False
    checks['omega=G sum M^q G beta'] = ok_rec; checks['omega>=0'] = ok_nn
    nu = newton(c)[1:]
    checks['Newton(c) LC'] = all(nu[i] ** 2 >= nu[i - 1] * nu[i + 1] for i in range(1, len(nu) - 1)) and all(x >= 0 for x in nu)
    checks['(P)'] = first_negative(linearization(a_, b, c)) is None
    return checks, neg, split_bad

if __name__ == '__main__':
    rng = random.Random(int(sys.argv[3])); Ns = [int(x) for x in sys.argv[1].split(',')]; per = int(sys.argv[2])
    tally = {}; negs = 0; splits = 0; tot = 0; t0 = time.time()
    for N in Ns:
        for i in range(per):
            m = member(rng, N, endpoint=(i % 3 == 0))
            d, r, s, t, a_, b, c = m
            checks, neg, sb = run(d, r, s, t, a_, b, c)
            tot += 1; negs += len(neg); splits += sb
            for k2, v2 in checks.items(): tally[k2] = tally.get(k2, 0) + (0 if v2 else 1)
        print(f'[{time.strftime("%H:%M:%S")}] N={N} done, {tot} members, elapsed {time.time()-t0:.0f}s', flush=True)
    print(f'{tot} members; negative individual weights: {negs}; split mismatches: {splits}')
    for k2, v2 in tally.items(): print(f'  {k2}: {v2} failures')
