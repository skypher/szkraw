"""(NP) for profiles of Newton degree 3: nu = (0, nu1, nu2, nu3), nu2^2 >= nu1 nu3. With s LC (arbitrary, or the
shift sum s_k = rho_{k-1} + rho_k of an LC rho), is kappa_k = k e_k LC (e_k = A_k s_k + B_k s_{k-1} + C_k s_{k-2}) for 2 <= k <= K?
A_k = nu1 + (k-1) nu2/2 + (k-1)(k-2) nu3/6, B_k = (k-1) nu2/2 + (k-1)(k-2) nu3/3, C_k = (k-1)(k-2) nu3/6.
Usage: deg3_test.py trials K seed mode(arb|shift)"""
import sys, random
from fractions import Fraction as F

def lc_seq(rng, L):
    ratios = sorted((F(rng.randint(0, 60), 20) for _ in range(L)), reverse=True)
    K = rng.randint(1, L); out = [F(rng.randint(1, 20), 10)]
    for i in range(L - 1): out.append(out[-1] * ratios[i] if i + 1 < K else F(0))
    return out

def run(T, K, rng, mode):
    bad = 0
    for _ in range(T):
        n1 = F(rng.randint(1, 20)); n2 = F(rng.randint(0, 30)); n3 = n2 * n2 / n1 * F(rng.randint(0, 20), 20)
        if mode == 'arb': s = lc_seq(rng, K + 3)  # s_0 > 0, LC without internal zeros
        else:
            rho = lc_seq(rng, K + 3); s = [rho[0]] + [rho[i - 1] + rho[i] for i in range(1, K + 2)]  # s_k = rho_{k-1} + rho_k
        S = lambda i: s[i] if 0 <= i < len(s) else F(0)
        A = lambda k: n1 + (k - 1) * n2 / 2 + (k - 1) * (k - 2) * n3 / 6
        B = lambda k: (k - 1) * n2 / 2 + (k - 1) * (k - 2) * n3 / 3
        C = lambda k: (k - 1) * (k - 2) * n3 / 6
        e = [F(0)] + [A(k) * S(k) + B(k) * S(k - 1) + C(k) * S(k - 2) for k in range(1, K + 2)]
        for k in range(2, K + 1):
            if k * k * e[k] ** 2 < (k * k - 1) * e[k - 1] * e[k + 1]:
                bad += 1
                if bad <= 2: print('fail', mode, 'nu', n1, n2, n3, 'k', k, 's', [str(x) for x in s[:6]])
                break
    print(f'mode={mode}: {bad}/{T} sequences with a log-concavity failure (k <= {K})')

if __name__ == '__main__':
    T, K, seed, mode = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), sys.argv[4]
    run(T, K, random.Random(seed), mode)
