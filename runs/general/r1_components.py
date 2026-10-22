"""r = 1 layer (t^0 of (Gamma)): b = 0, c = d, a = 1 - d on 0..N (N even). Quadratic components (Theorem 7.8), normalized.
Test: (1) component beta nondecreasing up to the terminal index (needed by Theorem 7.12 whatever sigma is);
(2) existence of sigma_n = s^n (grid) with all hypotheses of Theorem 7.12; (3) (P) of the components (exact)."""
import sys, random
from fractions import Fraction as F
sys.path.insert(0, '/home/yang/szkraw'); sys.path.insert(0, '/home/yang/szkraw/runs/ql_proof')
from probe import linearization, first_negative
from corner_bern_num import profile

def components(d):
    N2 = len(d) - 1; Nh = N2//2
    a = [1 - x for x in d] + [F(0)]; c = list(d) + [F(0)]
    A = lambda k: a[k] if 0 <= k <= N2 else F(0); C = lambda k: c[k] if 0 <= k <= N2 else F(0)
    ev = ([A(2*n)*A(2*n+1) for n in range(Nh+1)], [C(2*n)*A(2*n-1) + A(2*n)*C(2*n+1) for n in range(Nh+1)], [C(2*n)*C(2*n-1) for n in range(Nh+1)])
    od = ([A(2*n+1)*A(2*n+2) for n in range(Nh)], [A(2*n+1)*C(2*n+2) + C(2*n+1)*A(2*n) for n in range(Nh)], [C(2*n+1)*C(2*n) for n in range(Nh)])
    def norm(t):
        a_, b_, c_ = t; a0 = a_[0]; b0 = b_[0]
        return [x/a0 for x in a_], [(x - b0)/a0 for x in b_], [x/a0 for x in c_]
    return norm(ev), norm(od)

def thm712(arr, s):
    a, b, c = arr; M = len(a) - 1
    al = [F(0)] + [c[n]/s for n in range(1, M+1)]; ga = [a[n]*s for n in range(M)] + [F(0)]
    if any(b[n+1] < b[n] for n in range(M)) or any(al[n+1] < al[n] for n in range(M)): return False
    if any(al[n+1] + ga[n+1] < al[n] + ga[n] for n in range(M)): return False
    return all(ga[i] >= al[j] for i in range(M) for j in range(i+1))

if __name__ == '__main__':
    rng = random.Random(5)
    grid = [F(k, 20) for k in range(1, 61)]
    for N in (4, 6, 8, 10):
        fams = [('Krawtchouk', [F(0)]*(N-1)), ('geom x=1/5', [F(1, 5)]*(N-1)), ('geom x=1', [F(1)]*(N-1))]
        fams += [(f'LC random {i}', sorted([F(rng.randint(0, 30), 10) for _ in range(N-1)], reverse=True)) for i in range(3)]
        for name, q in fams:
            d = profile(N, q); ev, od = components(d)
            bmono = [all(arr[1][n+1] >= arr[1][n] for n in range(len(arr[1]) - 1)) for arr in (ev, od)]
            sig_ok = [any(thm712(arr, s) for s in grid) for arr in (ev, od)]
            P_ok = [not first_negative(linearization(*arr)) for arr in (ev, od)]
            print(f'N={N} {name:14s}: beta nondecreasing (even, odd) {bmono}; Thm 7.12 with sigma=s^n {sig_ok}; (P) {P_ok}', flush=True)
