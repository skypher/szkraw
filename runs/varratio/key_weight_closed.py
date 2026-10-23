"""Closed forms of the weight sums N_W (W >= 3) of the quadratic forms Ka, Psi, Qh (S_{2,0}) and R, R2 (lemma L2),
checked against their coefficient expansions for 5 <= a <= 30. Usage: key_weight_closed.py"""
import sys, math
from fractions import Fraction as Fr
sys.argv = ['x', '3']
src = open('/home/yang/szkraw/runs/varratio/key_S20_proof.py').read()
exec(src.split('rng = random.Random')[0])
C = lambda n, k: math.comb(n, k) if 0 <= k <= n else 0
def YXW(a, W): return 2*C(2*a-1, W) - 2*C(a, W) - 2*C(a-1, W) - 2*a*C(a-1, W-1) - C(a, W-1) - (a-1)*C(a-1, W-2)
def HW(a, W): return (W - 2) * C(a, W) if W >= 3 else 0
def G1W(a, W): return a*((a-1)*C(a-2, W-2) - C(a-1, W-1)) + (a if W == 1 else 0)
def G2W(a, W): return C(a, 2) * (a-2) * C(a-3, W-3)
def Ka_W(a, W): return (a-1)*YXW(a, W) - 4*a*(HW(a, W) + HW(a, W-1))
def Psi_W(a, W): return a*(C(2*a-1, W) - 2*C(a, W) - (a-1)*C(a, W-1)) - 2*C(a-1, 2)*C(a, W-1) + (C(a-1, 2)*(a-1) if W == 3 else 0)
def Qh_W(a, W): return (a-1)*YXW(a, W) - 4*a*HW(a, W) + 2*G1W(a, W) + 4*G2W(a, W) - 4*((a + C(a, 2))*HW(a, W-1) - G1W(a, W-1) - G2W(a, W-1))
def R_W(a, W): return a*(C(2*a-1, W) - 2*C(a, W) - C(a, W-1)) - 8*(HW(a, W) + HW(a, W-1))
def R2_W(a, W): return (a-2)*(C(2*a-1, W) - 2*C(a, W)) - 4*a*(HW(a, W) + HW(a, W-1))
mism = 0
for a in range(5, 31):
    Ka, Psi, Qh = forms(a)
    # R, R2 forms
    e = lambda m: {m: 1}
    A = {m: C(a, m) for m in range(a + 1)}; B = {m: C(a - 1, m) for m in range(a)}; d1 = {0: 1, 1: 1}
    H = {n: (n - 2) * C(a, n) for n in range(3, a + 1)}
    R = {}; mul(R, add((1, A), (-1, d1)), add((1, B), (-1, d1)), a); mul(R, d1, H, -8)
    R2 = {}; mul(R2, add((1, A), (-1, d1)), add((1, B), (-1, e(0))), a - 2); mul(R2, d1, H, -4 * a)
    for name, Q, f in [('Ka', Ka, Ka_W), ('Psi', Psi, Psi_W), ('Qh', Qh, Qh_W), ('R', R, R_W), ('R2', R2, R2_W)]:
        S = {}
        for (i, j), q in Q.items(): S[i + j] = S.get(i + j, 0) + q
        for W in range(3, 2 * a + 1):
            if S.get(W, 0) != f(a, W): mism += 1; print('mismatch', name, a, W, S.get(W, 0), f(a, W)) if mism < 5 else None
        assert all(S.get(W, 0) >= 0 for W in range(3)), (name, a, [S.get(W, 0) for W in range(3)])
print('closed-form mismatches:', mism)
