"""(L1') sigma >= 3: per-weight sums of Q and K'' (the only negative coefficients sit at pairs (0,W), (1,W-1), so
the Abel tail criterion reduces to the full weight sums N_W >= 0). Checks the closed form of N_W(Q) (W >= 4) against the
coefficient expansion, the W = 3 formulas, and the crude bound used in the proof for 4 <= W <= a+1:
  2C(2a-1,W) >= 2C(a,W) + 2C(a-1,W) + 2aC(a-1,W-1) + (a-1)C(a-1,W-2) + 4(W-2)C(a,W) + C(a,W-1)[(2a-3)/3 + 4a(W-3)/3].
Usage: key_L1_weights.py amax"""
import sys, math
from fractions import Fraction as Fr
AMAX = int(sys.argv[1]); sys.argv = sys.argv[:1] + ["3", "3"]
_HERE = __import__('os').path.dirname(__import__('os').path.abspath(__file__))
exec(open(__import__('os').path.join(_HERE, 'key_L1_quad.py')).read().split('rng = random')[0])
C = lambda n, k: math.comb(n, k) if 0 <= k <= n else 0
def NW(a, s, W):
    c1, c2, cas = C(a - 1, s - 1), C(a - 1, s), C(a, s)
    t = c1 * (2 * C(2*a-1, W) - 2*C(a, W) - 2*C(a-1, W) - 2*a*C(a-1, W-1) - C(a, W-1) - (a-1)*C(a-1, W-2) - 4*(W-2)*C(a, W))
    t -= 4 * cas * (W - 3) * C(a, W - 1) + 2 * c2 * C(a, W - 1)
    t += cas * (2*s*((s-2)*C(a-s, W-s) + (a-s)*C(a-s-1, W-s-1)) + 4*((s-2)*C(a-s, W-s-1) + (a-s)*C(a-s-1, W-s-2)))
    return t
def crude(a, W):
    return 2*C(2*a-1, W) - (2*C(a, W) + 2*C(a-1, W) + 2*a*C(a-1, W-1) + (a-1)*C(a-1, W-2) + 4*(W-2)*C(a, W)
                            + C(a, W-1) * (Fr(2*a-3, 3) + Fr(4*a*(W-3), 3)))
mism = crudebad = negQ = negK = 0
for a in range(3, AMAX + 1):
    for s in range(3, a + 1):
        B, Xpp, Xp, Y, Yp, H, V1, Z = lin(a, s); c1, c2 = C(a - 1, s - 1), C(a - 1, s)
        Q = {}; mul(Q, Yp, Xpp, c1); mul(Q, Y, Xp, c1); mul(Q, {0: 1}, H, -4 * c1)
        mul(Q, {1: 1}, add(V1, Z, -2), 2); mul(Q, {1: 1}, add(Y, Yp), -c2)
        S = {}
        for (i, j), q in Q.items(): S[i + j] = S.get(i + j, 0) + q
        assert all(S.get(W, 0) == 0 for W in range(3))
        w3 = Fr(c1 * (a-1) * (a-2) * (2*a-3), 6) + (6 * C(a, 3) if s == 3 else 0) - c2 * (a-1) ** 2
        mism += S.get(3, 0) != w3
        for W in range(4, 2 * a + 1): mism += S.get(W, 0) != NW(a, s, W)
        negQ += min(S.values()) < 0
    K = {}; mul(K, Yp, Xpp); mul(K, Y, Xp); mul(K, {0: 1, 1: 1}, H, -4)
    SK = {}
    for (i, j), q in K.items(): SK[i + j] = SK.get(i + j, 0) + q
    negK += min(SK.values()) < 0
    crudebad += sum(crude(a, W) < 0 for W in range(4, a + 2))
print(f"a <= {AMAX}: closed-form mismatches {mism}; negative weight sums: Q {negQ}, K'' {negK}; crude-bound failures {crudebad}")
