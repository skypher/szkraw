"""Linear rising ratio family L: d with log-concave Newton coefficients (d_N = 1), rho_n = r + kappa*n/N (kappa <= (1-r)/2),
c = rho d, b = (1 - rho) d (paper normalization). Checks the kernel moves of Theorem 8.6's recurrence:
A-moves from b, B-moves from c, C-moves from d = b + c. Reports negative move weights and P^2 >= 4Q violations,
and (P) directly."""
import sys, math, random
from fractions import Fraction as F
sys.path.insert(0, '/home/yang/szkraw'); sys.path.insert(0, '/home/yang/szkraw/runs/varratio')
from probe import linearization, first_negative
from kernel_check import operator_check
from hform import lc_seq

def lmember(rng, N, linear_d=False):
    sig = [F(1)] + [F(0)] * (N - 1) if linear_d else lc_seq(rng, N)
    D = [sum(math.comb(n, k) * sig[k - 1] for k in range(1, n + 1)) for n in range(N + 1)]
    d = [x / D[N] for x in D]
    r = F(rng.randint(1, 95), 100)
    kappa = (1 - r) / 2 * F(rng.randint(0, 100), 100)
    rho = [r + kappa * n / N for n in range(N + 1)]
    c = [p * x for p, x in zip(rho, d)]; b = [(1 - p) * x for p, x in zip(rho, d)]
    return [1 - x for x in d], b, c

if __name__ == '__main__':
    rng = random.Random(int(sys.argv[3])); Ns = [int(x) for x in sys.argv[1].split(',')]; per = int(sys.argv[2])
    for lin in (True, False):
        neg = viol = q = fails = tot = 0
        for N in Ns:
            for _ in range(per):
                a, b, c = lmember(rng, N, lin)
                ng, nq, vi = operator_check(b, c)
                neg += (ng > 0); viol += (vi > 0); q += nq; tot += 1
                if first_negative(linearization(a, b, c)): fails += 1
        print(f"linear d={lin}: {tot} members; members with a negative move weight {neg}; with P^2>=4Q violations {viol}; (P) failures {fails}", flush=True)
