# Fresh-clone run of the certificate scripts (2026-10-23)

Clone of https://github.com/skypher/szkraw at 4f739c3 (the revision cited in the paper's \bibitem{code}), scripts run unmodified with python3 by run_certs.sh. Each line gives the exit code, the run time and the last output line. Full outputs are in r4f739c3/NN.out (not tracked).

```
[15:30:15] start 01/16: runs/cubic/bdetour_cert.py  sha256 c1234cd3a53edc5c
[15:33:04] end 01: rc=0, 169s, last line: ALL CERTIFIED (349 polynomial and sign checks)
[15:33:04] start 02/16: runs/cubic/corner_cert.py  sha256 1af8fb16d3039cc2
[15:33:10] end 02: rc=0, 6s, last line: CERTIFIED: corner repair (12 phi_2(0) + 8 phi_3(0)) phi_2(1) >= 8 c_1 phi_4(0) under r sigma <= t tau
[15:33:10] start 03/16: runs/cubic/edetour_cert.py 3  sha256 1e37a310894c7d23
[15:35:41] end 03: rc=0, 151s, last line: CERTIFIED: E detour with constant 3 (124 checks)
[15:35:41] start 04/16: runs/cubic/phi2loc_cert.py  sha256 631bdcff8c7ca0ef
[15:35:46] end 04: rc=0, 5s, last line: CERTIFIED: Phi2loc >= 0 for all a >= 3
[15:35:47] start 05/16: runs/cubic/phi3loc_cert.py  sha256 96e033c94690a1de
[15:35:52] end 05: rc=0, 5s, last line: CERTIFIED (with chain check)
[15:35:52] start 06/16: runs/cubic/bdetour_u.py 7/4  sha256 0c25196c8b57dcc2
[15:36:17] end 06: rc=0, 25s, last line: ALL CERTIFIED for kappa_ttau + 7/4 kappa_rs (51 checks)
[15:36:17] start 07/16: runs/cubic/edetour_u.py 3 7/4  sha256 6c895068baa1a1bb
[15:36:34] end 07: rc=0, 17s, last line: CERTIFIED: E detour, constant 3, kappa_ttau + 7/4 kappa_rs (18 checks)
[15:36:34] start 08/16: runs/sharp/lc_violation_cert.py 6 1/10 11/10  sha256 a580479d73aee4e4
[15:36:35] end 08: rc=0, 1s, last line: CERTIFIED: (P) for every r in [0,1]
[15:36:35] start 09/16: runs/sharp/lc_violation_cert.py 8 1/10 11/10  sha256 a580479d73aee4e4
[15:36:36] end 09: rc=0, 1s, last line: CERTIFIED: (P) for every r in [0,1]
[15:36:36] start 10/16: runs/sharp/lc_violation_cert.py 10 1/10 11/10  sha256 a580479d73aee4e4
[15:36:38] end 10: rc=0, 2s, last line: CERTIFIED: (P) for every r in [0,1]
[15:36:38] start 11/16: runs/sharp/lc_violation_cert.py 12 1/10 11/10  sha256 a580479d73aee4e4
[15:36:40] end 11: rc=0, 2s, last line: CERTIFIED: (P) for every r in [0,1]
[15:36:40] start 12/16: runs/sharp/lc_violation_cert.py 6 1/100 11/10  sha256 a580479d73aee4e4
[15:36:41] end 12: rc=0, 1s, last line: FAILS: g(6, 6, 6) = -11421689396209222100480371/11282159504913398311706203653864919 < 0 at r = 1 (exact)
[15:36:41] start 13/16: runs/varratio/key_weight_cert.py  sha256 98cdfd094853b19a
[15:36:47] end 13: rc=0, 6s, last line: all small-weight checks pass: True
[15:36:47] start 14/16: runs/varratio/key_weight_closed.py  sha256 104ff8b35eb2f33f
[15:36:48] end 14: rc=0, 1s, last line: closed-form mismatches: 0
[15:36:48] start 15/16: runs/varratio/key_phi_ustep.py 5  sha256 0e1e48daf8f7eb9b
[15:36:57] end 15: rc=0, 9s, last line: a=5: central sums {'CERTIFIED': 20}
[15:36:57] start 16/16: runs/varratio/key_lin_cert.py 5  sha256 bebde4f1f76d13cc
[15:37:00] end 16: rc=0, 3s, last line: a=5: Lin coefficients {'CERTIFIED': 6}
```

Theorem 8.16, windows a = 3, 4, 5: central sums 9/14/20 and Lin coefficients 4/5/6, all CERTIFIED (key_phi_ustep.py 5, key_lin_cert.py 5).
