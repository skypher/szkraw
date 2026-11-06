from fractions import Fraction as F
from families import *
from criteria import *
for p in [F(1, 4), F(1, 2), F(2, 3)]:
    for e in [0, 5]:
        X, P = krawtchouk(5, p)
        arr = normalize(X, P, e)
        if arr is None:
            print("kraw", p, e, "not normalizable"); continue
        a, b, c = arr
        r = check_all(a, b, c)
        print("kraw p=%s e=%d" % (p, e), "ming=%s" % float(min_g(a, b, c)),
              {k: v for k, v in r.items() if v}, [str(x) for x in c[:3]])
for cc in [F(1, 2), F(3)]:
    X, P = dual_q_krawtchouk(4, cc, F(1, 2))
    for e in [0, 4]:
        arr = normalize(X, P, e)
        if arr is None:
            print("dqk", cc, e, "none"); continue
        a, b, c = arr
        print("dqk c=%s e=%d" % (cc, e), float(min_g(a, b, c)), {k: v for k, v in check_all(a, b, c).items() if v})
