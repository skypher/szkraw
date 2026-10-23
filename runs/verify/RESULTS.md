# Fresh-clone runs of the certificate scripts

## Revision 2055ea3 (2026-10-24)

Clone of https://github.com/skypher/szkraw at `2055ea34c67edc7aacf73e1e17190468ddd7b413` (the revision cited as \bibitem{code} in the three papers). The same 34 scripts as in the bd23d2d run were run unmodified with python3 by `run_certs.sh` (local clone and outputs, not committed). All 34 exit with code 0; their SHA-256 prefixes and last lines are identical to those of the bd23d2d run. This revision adds `lean/Szkraw/FiniteSystem.lean` (`Szkraw.FinSys.finite_system_reduction`; Lean fidelity round 37, PASS) and the clean memory measurement of the optional N = 500 certificate (see the bd23d2d section). The Lean development builds with `make lean`; its axiom audit is `lean/axioms.log` (405 lines), and that of the optional target is `lean/axioms-kink500.log` (6 lines), both with only propext, Classical.choice and Quot.sound. Rerunning both audits on a working tree equal to this revision, with no untracked files under `lean/`, reproduces them byte for byte.

```
[03:14:23] start 01/34: runs/cubic/bdetour_cert.py  sha256 c1234cd3a53edc5c
[03:16:47] end 01: rc=0, 144s, last line: ALL CERTIFIED (349 polynomial and sign checks)
[03:16:47] start 02/34: runs/cubic/corner_cert.py  sha256 1af8fb16d3039cc2
[03:16:49] end 02: rc=0, 2s, last line: CERTIFIED: corner repair (12 phi_2(0) + 8 phi_3(0)) phi_2(1) >= 8 c_1 phi_4(0) under r sigma <= t tau
[03:16:49] start 03/34: runs/cubic/edetour_cert.py 3  sha256 1e37a310894c7d23
[03:19:00] end 03: rc=0, 131s, last line: CERTIFIED: E detour with constant 3 (124 checks)
[03:19:00] start 04/34: runs/cubic/phi2loc_cert.py  sha256 631bdcff8c7ca0ef
[03:19:04] end 04: rc=0, 4s, last line: CERTIFIED: Phi2loc >= 0 for all a >= 3
[03:19:04] start 05/34: runs/cubic/phi3loc_cert.py  sha256 96e033c94690a1de
[03:19:07] end 05: rc=0, 3s, last line: CERTIFIED (with chain check)
[03:19:07] start 06/34: runs/cubic/bdetour_u.py 7/4  sha256 0c25196c8b57dcc2
[03:19:26] end 06: rc=0, 19s, last line: ALL CERTIFIED for kappa_ttau + 7/4 kappa_rs (51 checks)
[03:19:26] start 07/34: runs/cubic/edetour_u.py 3 7/4  sha256 6c895068baa1a1bb
[03:19:38] end 07: rc=0, 12s, last line: CERTIFIED: E detour, constant 3, kappa_ttau + 7/4 kappa_rs (18 checks)
[03:19:38] start 08/34: runs/sharp/lc_violation_cert.py 6 1/10 11/10  sha256 a580479d73aee4e4
[03:19:39] end 08: rc=0, 1s, last line: CERTIFIED: (P) for every r in [0,1]
[03:19:39] start 09/34: runs/sharp/lc_violation_cert.py 8 1/10 11/10  sha256 a580479d73aee4e4
[03:19:39] end 09: rc=0, 0s, last line: CERTIFIED: (P) for every r in [0,1]
[03:19:39] start 10/34: runs/sharp/lc_violation_cert.py 10 1/10 11/10  sha256 a580479d73aee4e4
[03:19:40] end 10: rc=0, 1s, last line: CERTIFIED: (P) for every r in [0,1]
[03:19:40] start 11/34: runs/sharp/lc_violation_cert.py 12 1/10 11/10  sha256 a580479d73aee4e4
[03:19:41] end 11: rc=0, 1s, last line: CERTIFIED: (P) for every r in [0,1]
[03:19:41] start 12/34: runs/sharp/lc_violation_cert.py 6 1/100 11/10  sha256 a580479d73aee4e4
[03:19:42] end 12: rc=0, 1s, last line: FAILS: g(6, 6, 6) = -11421689396209222100480371/11282159504913398311706203653864919 < 0 at r = 1 (exact)
[03:19:42] start 13/34: runs/varratio/key_weight_cert.py  sha256 98cdfd094853b19a
[03:19:46] end 13: rc=0, 4s, last line: all small-weight checks pass: True
[03:19:46] start 14/34: runs/varratio/key_weight_closed.py  sha256 104ff8b35eb2f33f
[03:19:47] end 14: rc=0, 1s, last line: closed-form mismatches: 0
[03:19:47] start 15/34: runs/varratio/key_phi_ustep.py 5  sha256 0e1e48daf8f7eb9b
[03:19:55] end 15: rc=0, 8s, last line: a=5: central sums {'CERTIFIED': 20}
[03:19:55] start 16/34: runs/varratio/key_lin_cert.py 5  sha256 bebde4f1f76d13cc
[03:19:58] end 16: rc=0, 3s, last line: a=5: Lin coefficients {'CERTIFIED': 6}
[03:19:58] start 17/34: runs/lean_plan/edge_exact.py 60  sha256 5c672d687645c760
[03:19:58] end 17: rc=0, 0s, last line: Qhat: fails at []
[03:19:58] start 18/34: runs/lean_plan/forms_iii_v.py  sha256 ec8d35c58fa468a6
[03:20:02] end 18: rc=0, 4s, last line: generic formulas agree with the exact sequences for 4 <= n <= a <= 13
[03:20:02] start 19/34: runs/lean_plan/window_cert.py  sha256 9d97b37700afe147
[03:20:05] end 19: rc=0, 3s, last line: ALL CERTIFIED
[03:20:05] start 20/34: runs/lean_plan/gen_cubicB.py gen /home/yang/szkraw/runs/verify/r6816468-out/gen/B_gen.lean  sha256 a14373132671fa5a
[03:20:10] end 20: rc=0, 5s, last line: case gen: 93 tail facts
[03:20:10] start 21/34: runs/lean_plan/gen_cubicB.py 2 /home/yang/szkraw/runs/verify/r6816468-out/gen/B_2.lean  sha256 a14373132671fa5a
[03:20:12] end 21: rc=0, 2s, last line: case 2: 67 tail facts
[03:20:12] start 22/34: runs/lean_plan/gen_cubicB.py 3 /home/yang/szkraw/runs/verify/r6816468-out/gen/B_3.lean  sha256 a14373132671fa5a
[03:20:14] end 22: rc=0, 2s, last line: case 3: 94 tail facts
[03:20:14] start 23/34: runs/lean_plan/gen_cubicB.py 4 /home/yang/szkraw/runs/verify/r6816468-out/gen/B_4.lean  sha256 a14373132671fa5a
[03:20:17] end 23: rc=0, 3s, last line: case 4: 102 tail facts
[03:20:17] start 24/34: runs/lean_plan/gen_cubicB.py 5 /home/yang/szkraw/runs/verify/r6816468-out/gen/B_5.lean  sha256 a14373132671fa5a
[03:20:19] end 24: rc=0, 2s, last line: case 5: 121 tail facts
[03:20:19] start 25/34: runs/lean_plan/gen_cubicB.py corner /home/yang/szkraw/runs/verify/r6816468-out/gen/B_corner.lean  sha256 a14373132671fa5a
[03:20:20] end 25: rc=0, 1s, last line: case corner: 46 tail facts
[03:20:20] start 26/34: runs/lean_plan/gen_cubicE.py gen /home/yang/szkraw/runs/verify/r6816468-out/gen/E_gen.lean  sha256 f3d0db86e107626c
[03:20:24] end 26: rc=0, 4s, last line: case gen: 92 tail facts
[03:20:24] start 27/34: runs/lean_plan/gen_cubicE.py 3 /home/yang/szkraw/runs/verify/r6816468-out/gen/E_3.lean  sha256 f3d0db86e107626c
[03:20:25] end 27: rc=0, 1s, last line: case 3: 62 tail facts
[03:20:25] start 28/34: runs/lean_plan/gen_cubicE.py 4 /home/yang/szkraw/runs/verify/r6816468-out/gen/E_4.lean  sha256 f3d0db86e107626c
[03:20:26] end 28: rc=0, 1s, last line: case 4: 77 tail facts
[03:20:26] start 29/34: runs/lean_plan/gen_cubicE.py 5 /home/yang/szkraw/runs/verify/r6816468-out/gen/E_5.lean  sha256 f3d0db86e107626c
[03:20:27] end 29: rc=0, 1s, last line: case 5: 88 tail facts
[03:20:27] start 30/34: runs/lean_plan/gen_cubicE.py 6 /home/yang/szkraw/runs/verify/r6816468-out/gen/E_6.lean  sha256 f3d0db86e107626c
[03:20:28] end 30: rc=0, 1s, last line: case 6: 92 tail facts
[03:20:28] start 31/34: runs/lean_plan/phi3_edge.py 40  sha256 9977f63f232e1e89
[03:20:28] end 31: rc=0, 0s, last line: done
[03:20:28] start 32/34: runs/lean_plan/phi3_generic.py  sha256 0e2fd112c023b819
[03:20:30] end 32: rc=0, 2s, last line: generic formulas agree with the exact coefficients for 4 <= n <= a <= 15
[03:20:30] start 33/34: runs/lean_plan/p3_numeric_witnesses.py  sha256 f16727cce76173f5
[03:20:32] end 33: rc=0, 2s, last line: terminal r=1/3 N=120 e=-2/125: g(N,N;N) < 0: True
[03:20:32] start 34/34: runs/lean_plan/lambda_n.py 10  sha256 88951c89fad2f145
[03:20:32] end 34: rc=0, 0s, last line: 10 165 (2, 2, 3)
[03:20:32] all done
```

## Revision bd23d2d (2026-10-24)

Clone of https://github.com/skypher/szkraw at `bd23d2dd8a62d22590d8b4997eddb52313e4336a` (the revision cited as \bibitem{code} in the three papers). The same 34 scripts as in the 681ab21 run were run unmodified with python3 by `run_certs.sh` (local clone and outputs, not committed). All 34 exit with code 0; their SHA-256 prefixes and last lines are identical to those of the 681ab21 run. This revision adds the N = 500 one-kink certificate of P3: `lean/Szkraw/WindowColumn.lean` (in the default build) and the optional target `make lean-kink500` (`Szkraw.kink500_1_10_fails`; Lean fidelity round 36, PASS WITH MINOR FIXES, applied). Its data files are regenerated identically by `runs/kink500/gen_ckpt.py --check`. The time and memory figures cited in P3 come from a clean measurement run: `runs/kink500/build_chunks.sh … --clean` removed the four chunk build outputs, so all four chunks were checked concurrently. The build took 5 min 49 s (02:50:33–02:56:22) with a peak summed RSS of the chunk checks of 20.4 GB, sampled every 5 s (`runs/kink500/clean-run.log`). An earlier run in which chunk 1 was already built peaked at about 15 GB. The Lean development builds with `make lean`; its axiom audit is `lean/axioms.log` (400 lines), and that of the optional target is `lean/axioms-kink500.log` (6 lines), both with only propext, Classical.choice and Quot.sound. Rerunning both audits on a working tree equal to this revision, with no untracked files under `lean/`, reproduces them byte for byte.

```
[02:32:13] start 01/34: runs/cubic/bdetour_cert.py  sha256 c1234cd3a53edc5c
[02:34:31] end 01: rc=0, 138s, last line: ALL CERTIFIED (349 polynomial and sign checks)
[02:34:31] start 02/34: runs/cubic/corner_cert.py  sha256 1af8fb16d3039cc2
[02:34:34] end 02: rc=0, 3s, last line: CERTIFIED: corner repair (12 phi_2(0) + 8 phi_3(0)) phi_2(1) >= 8 c_1 phi_4(0) under r sigma <= t tau
[02:34:34] start 03/34: runs/cubic/edetour_cert.py 3  sha256 1e37a310894c7d23
[02:36:45] end 03: rc=0, 131s, last line: CERTIFIED: E detour with constant 3 (124 checks)
[02:36:45] start 04/34: runs/cubic/phi2loc_cert.py  sha256 631bdcff8c7ca0ef
[02:36:48] end 04: rc=0, 3s, last line: CERTIFIED: Phi2loc >= 0 for all a >= 3
[02:36:48] start 05/34: runs/cubic/phi3loc_cert.py  sha256 96e033c94690a1de
[02:36:52] end 05: rc=0, 4s, last line: CERTIFIED (with chain check)
[02:36:52] start 06/34: runs/cubic/bdetour_u.py 7/4  sha256 0c25196c8b57dcc2
[02:37:12] end 06: rc=0, 20s, last line: ALL CERTIFIED for kappa_ttau + 7/4 kappa_rs (51 checks)
[02:37:13] start 07/34: runs/cubic/edetour_u.py 3 7/4  sha256 6c895068baa1a1bb
[02:37:25] end 07: rc=0, 12s, last line: CERTIFIED: E detour, constant 3, kappa_ttau + 7/4 kappa_rs (18 checks)
[02:37:25] start 08/34: runs/sharp/lc_violation_cert.py 6 1/10 11/10  sha256 a580479d73aee4e4
[02:37:25] end 08: rc=0, 0s, last line: CERTIFIED: (P) for every r in [0,1]
[02:37:25] start 09/34: runs/sharp/lc_violation_cert.py 8 1/10 11/10  sha256 a580479d73aee4e4
[02:37:26] end 09: rc=0, 1s, last line: CERTIFIED: (P) for every r in [0,1]
[02:37:26] start 10/34: runs/sharp/lc_violation_cert.py 10 1/10 11/10  sha256 a580479d73aee4e4
[02:37:27] end 10: rc=0, 1s, last line: CERTIFIED: (P) for every r in [0,1]
[02:37:27] start 11/34: runs/sharp/lc_violation_cert.py 12 1/10 11/10  sha256 a580479d73aee4e4
[02:37:28] end 11: rc=0, 1s, last line: CERTIFIED: (P) for every r in [0,1]
[02:37:28] start 12/34: runs/sharp/lc_violation_cert.py 6 1/100 11/10  sha256 a580479d73aee4e4
[02:37:29] end 12: rc=0, 1s, last line: FAILS: g(6, 6, 6) = -11421689396209222100480371/11282159504913398311706203653864919 < 0 at r = 1 (exact)
[02:37:29] start 13/34: runs/varratio/key_weight_cert.py  sha256 98cdfd094853b19a
[02:37:33] end 13: rc=0, 4s, last line: all small-weight checks pass: True
[02:37:33] start 14/34: runs/varratio/key_weight_closed.py  sha256 104ff8b35eb2f33f
[02:37:34] end 14: rc=0, 1s, last line: closed-form mismatches: 0
[02:37:34] start 15/34: runs/varratio/key_phi_ustep.py 5  sha256 0e1e48daf8f7eb9b
[02:37:43] end 15: rc=0, 9s, last line: a=5: central sums {'CERTIFIED': 20}
[02:37:43] start 16/34: runs/varratio/key_lin_cert.py 5  sha256 bebde4f1f76d13cc
[02:37:45] end 16: rc=0, 2s, last line: a=5: Lin coefficients {'CERTIFIED': 6}
[02:37:45] start 17/34: runs/lean_plan/edge_exact.py 60  sha256 5c672d687645c760
[02:37:46] end 17: rc=0, 1s, last line: Qhat: fails at []
[02:37:46] start 18/34: runs/lean_plan/forms_iii_v.py  sha256 ec8d35c58fa468a6
[02:37:50] end 18: rc=0, 4s, last line: generic formulas agree with the exact sequences for 4 <= n <= a <= 13
[02:37:50] start 19/34: runs/lean_plan/window_cert.py  sha256 9d97b37700afe147
[02:37:53] end 19: rc=0, 3s, last line: ALL CERTIFIED
[02:37:53] start 20/34: runs/lean_plan/gen_cubicB.py gen /home/yang/szkraw/runs/verify/r6816468-out/gen/B_gen.lean  sha256 a14373132671fa5a
[02:37:58] end 20: rc=0, 5s, last line: case gen: 93 tail facts
[02:37:58] start 21/34: runs/lean_plan/gen_cubicB.py 2 /home/yang/szkraw/runs/verify/r6816468-out/gen/B_2.lean  sha256 a14373132671fa5a
[02:38:00] end 21: rc=0, 2s, last line: case 2: 67 tail facts
[02:38:00] start 22/34: runs/lean_plan/gen_cubicB.py 3 /home/yang/szkraw/runs/verify/r6816468-out/gen/B_3.lean  sha256 a14373132671fa5a
[02:38:02] end 22: rc=0, 3s, last line: case 3: 94 tail facts
[02:38:03] start 23/34: runs/lean_plan/gen_cubicB.py 4 /home/yang/szkraw/runs/verify/r6816468-out/gen/B_4.lean  sha256 a14373132671fa5a
[02:38:05] end 23: rc=0, 2s, last line: case 4: 102 tail facts
[02:38:05] start 24/34: runs/lean_plan/gen_cubicB.py 5 /home/yang/szkraw/runs/verify/r6816468-out/gen/B_5.lean  sha256 a14373132671fa5a
[02:38:08] end 24: rc=0, 3s, last line: case 5: 121 tail facts
[02:38:08] start 25/34: runs/lean_plan/gen_cubicB.py corner /home/yang/szkraw/runs/verify/r6816468-out/gen/B_corner.lean  sha256 a14373132671fa5a
[02:38:09] end 25: rc=0, 1s, last line: case corner: 46 tail facts
[02:38:09] start 26/34: runs/lean_plan/gen_cubicE.py gen /home/yang/szkraw/runs/verify/r6816468-out/gen/E_gen.lean  sha256 f3d0db86e107626c
[02:38:13] end 26: rc=0, 4s, last line: case gen: 92 tail facts
[02:38:13] start 27/34: runs/lean_plan/gen_cubicE.py 3 /home/yang/szkraw/runs/verify/r6816468-out/gen/E_3.lean  sha256 f3d0db86e107626c
[02:38:14] end 27: rc=0, 1s, last line: case 3: 62 tail facts
[02:38:14] start 28/34: runs/lean_plan/gen_cubicE.py 4 /home/yang/szkraw/runs/verify/r6816468-out/gen/E_4.lean  sha256 f3d0db86e107626c
[02:38:15] end 28: rc=0, 1s, last line: case 4: 77 tail facts
[02:38:15] start 29/34: runs/lean_plan/gen_cubicE.py 5 /home/yang/szkraw/runs/verify/r6816468-out/gen/E_5.lean  sha256 f3d0db86e107626c
[02:38:16] end 29: rc=0, 1s, last line: case 5: 88 tail facts
[02:38:16] start 30/34: runs/lean_plan/gen_cubicE.py 6 /home/yang/szkraw/runs/verify/r6816468-out/gen/E_6.lean  sha256 f3d0db86e107626c
[02:38:17] end 30: rc=0, 1s, last line: case 6: 92 tail facts
[02:38:17] start 31/34: runs/lean_plan/phi3_edge.py 40  sha256 9977f63f232e1e89
[02:38:18] end 31: rc=0, 1s, last line: done
[02:38:18] start 32/34: runs/lean_plan/phi3_generic.py  sha256 0e2fd112c023b819
[02:38:21] end 32: rc=0, 3s, last line: generic formulas agree with the exact coefficients for 4 <= n <= a <= 15
[02:38:21] start 33/34: runs/lean_plan/p3_numeric_witnesses.py  sha256 f16727cce76173f5
[02:38:22] end 33: rc=0, 1s, last line: terminal r=1/3 N=120 e=-2/125: g(N,N;N) < 0: True
[02:38:22] start 34/34: runs/lean_plan/lambda_n.py 10  sha256 88951c89fad2f145
[02:38:22] end 34: rc=0, 0s, last line: 10 165 (2, 2, 3)
[02:38:22] all done
```

## Revision 681ab21 (2026-10-24)

Clone of https://github.com/skypher/szkraw at `681ab218a86cbe1b0bad645a49adb8457b60c8dd` (the revision cited as \bibitem{code} in the three papers). The same 34 scripts as in the c95705c run were run unmodified with python3 by `run_certs.sh` (local clone and outputs, not committed). All 34 exit with code 0; their SHA-256 prefixes and last lines are identical to those of the c95705c run. This revision adds `lean/Szkraw/OperatorM.lean` (`Szkraw.opM_negative_entry`, `Szkraw.opM_has_negative_entry`; Lean fidelity round 35, PASS). The Lean development builds with `make lean`; its axiom audit is `lean/axioms.log` (396 lines, only propext, Classical.choice, Quot.sound), and rerunning the audit on a working tree equal to this revision, with no untracked files under `lean/`, reproduces it byte for byte.

```
[02:01:43] start 01/34: runs/cubic/bdetour_cert.py  sha256 c1234cd3a53edc5c
[02:04:03] end 01: rc=0, 140s, last line: ALL CERTIFIED (349 polynomial and sign checks)
[02:04:03] start 02/34: runs/cubic/corner_cert.py  sha256 1af8fb16d3039cc2
[02:04:06] end 02: rc=0, 3s, last line: CERTIFIED: corner repair (12 phi_2(0) + 8 phi_3(0)) phi_2(1) >= 8 c_1 phi_4(0) under r sigma <= t tau
[02:04:06] start 03/34: runs/cubic/edetour_cert.py 3  sha256 1e37a310894c7d23
[02:06:20] end 03: rc=0, 134s, last line: CERTIFIED: E detour with constant 3 (124 checks)
[02:06:20] start 04/34: runs/cubic/phi2loc_cert.py  sha256 631bdcff8c7ca0ef
[02:06:23] end 04: rc=0, 3s, last line: CERTIFIED: Phi2loc >= 0 for all a >= 3
[02:06:23] start 05/34: runs/cubic/phi3loc_cert.py  sha256 96e033c94690a1de
[02:06:27] end 05: rc=0, 4s, last line: CERTIFIED (with chain check)
[02:06:27] start 06/34: runs/cubic/bdetour_u.py 7/4  sha256 0c25196c8b57dcc2
[02:06:47] end 06: rc=0, 20s, last line: ALL CERTIFIED for kappa_ttau + 7/4 kappa_rs (51 checks)
[02:06:47] start 07/34: runs/cubic/edetour_u.py 3 7/4  sha256 6c895068baa1a1bb
[02:06:59] end 07: rc=0, 12s, last line: CERTIFIED: E detour, constant 3, kappa_ttau + 7/4 kappa_rs (18 checks)
[02:06:59] start 08/34: runs/sharp/lc_violation_cert.py 6 1/10 11/10  sha256 a580479d73aee4e4
[02:07:00] end 08: rc=0, 1s, last line: CERTIFIED: (P) for every r in [0,1]
[02:07:00] start 09/34: runs/sharp/lc_violation_cert.py 8 1/10 11/10  sha256 a580479d73aee4e4
[02:07:01] end 09: rc=0, 1s, last line: CERTIFIED: (P) for every r in [0,1]
[02:07:01] start 10/34: runs/sharp/lc_violation_cert.py 10 1/10 11/10  sha256 a580479d73aee4e4
[02:07:02] end 10: rc=0, 1s, last line: CERTIFIED: (P) for every r in [0,1]
[02:07:02] start 11/34: runs/sharp/lc_violation_cert.py 12 1/10 11/10  sha256 a580479d73aee4e4
[02:07:03] end 11: rc=0, 1s, last line: CERTIFIED: (P) for every r in [0,1]
[02:07:03] start 12/34: runs/sharp/lc_violation_cert.py 6 1/100 11/10  sha256 a580479d73aee4e4
[02:07:03] end 12: rc=0, 0s, last line: FAILS: g(6, 6, 6) = -11421689396209222100480371/11282159504913398311706203653864919 < 0 at r = 1 (exact)
[02:07:03] start 13/34: runs/varratio/key_weight_cert.py  sha256 98cdfd094853b19a
[02:07:08] end 13: rc=0, 5s, last line: all small-weight checks pass: True
[02:07:08] start 14/34: runs/varratio/key_weight_closed.py  sha256 104ff8b35eb2f33f
[02:07:09] end 14: rc=0, 1s, last line: closed-form mismatches: 0
[02:07:09] start 15/34: runs/varratio/key_phi_ustep.py 5  sha256 0e1e48daf8f7eb9b
[02:07:18] end 15: rc=0, 9s, last line: a=5: central sums {'CERTIFIED': 20}
[02:07:18] start 16/34: runs/varratio/key_lin_cert.py 5  sha256 bebde4f1f76d13cc
[02:07:21] end 16: rc=0, 3s, last line: a=5: Lin coefficients {'CERTIFIED': 6}
[02:07:21] start 17/34: runs/lean_plan/edge_exact.py 60  sha256 5c672d687645c760
[02:07:21] end 17: rc=0, 0s, last line: Qhat: fails at []
[02:07:21] start 18/34: runs/lean_plan/forms_iii_v.py  sha256 ec8d35c58fa468a6
[02:07:26] end 18: rc=0, 5s, last line: generic formulas agree with the exact sequences for 4 <= n <= a <= 13
[02:07:26] start 19/34: runs/lean_plan/window_cert.py  sha256 9d97b37700afe147
[02:07:29] end 19: rc=0, 3s, last line: ALL CERTIFIED
[02:07:29] start 20/34: runs/lean_plan/gen_cubicB.py gen /home/yang/szkraw/runs/verify/r6816468-out/gen/B_gen.lean  sha256 a14373132671fa5a
[02:07:33] end 20: rc=0, 4s, last line: case gen: 93 tail facts
[02:07:34] start 21/34: runs/lean_plan/gen_cubicB.py 2 /home/yang/szkraw/runs/verify/r6816468-out/gen/B_2.lean  sha256 a14373132671fa5a
[02:07:36] end 21: rc=0, 3s, last line: case 2: 67 tail facts
[02:07:36] start 22/34: runs/lean_plan/gen_cubicB.py 3 /home/yang/szkraw/runs/verify/r6816468-out/gen/B_3.lean  sha256 a14373132671fa5a
[02:07:38] end 22: rc=0, 2s, last line: case 3: 94 tail facts
[02:07:39] start 23/34: runs/lean_plan/gen_cubicB.py 4 /home/yang/szkraw/runs/verify/r6816468-out/gen/B_4.lean  sha256 a14373132671fa5a
[02:07:41] end 23: rc=0, 2s, last line: case 4: 102 tail facts
[02:07:41] start 24/34: runs/lean_plan/gen_cubicB.py 5 /home/yang/szkraw/runs/verify/r6816468-out/gen/B_5.lean  sha256 a14373132671fa5a
[02:07:44] end 24: rc=0, 3s, last line: case 5: 121 tail facts
[02:07:44] start 25/34: runs/lean_plan/gen_cubicB.py corner /home/yang/szkraw/runs/verify/r6816468-out/gen/B_corner.lean  sha256 a14373132671fa5a
[02:07:45] end 25: rc=0, 1s, last line: case corner: 46 tail facts
[02:07:45] start 26/34: runs/lean_plan/gen_cubicE.py gen /home/yang/szkraw/runs/verify/r6816468-out/gen/E_gen.lean  sha256 f3d0db86e107626c
[02:07:49] end 26: rc=0, 4s, last line: case gen: 92 tail facts
[02:07:49] start 27/34: runs/lean_plan/gen_cubicE.py 3 /home/yang/szkraw/runs/verify/r6816468-out/gen/E_3.lean  sha256 f3d0db86e107626c
[02:07:50] end 27: rc=0, 1s, last line: case 3: 62 tail facts
[02:07:50] start 28/34: runs/lean_plan/gen_cubicE.py 4 /home/yang/szkraw/runs/verify/r6816468-out/gen/E_4.lean  sha256 f3d0db86e107626c
[02:07:51] end 28: rc=0, 1s, last line: case 4: 77 tail facts
[02:07:51] start 29/34: runs/lean_plan/gen_cubicE.py 5 /home/yang/szkraw/runs/verify/r6816468-out/gen/E_5.lean  sha256 f3d0db86e107626c
[02:07:52] end 29: rc=0, 1s, last line: case 5: 88 tail facts
[02:07:52] start 30/34: runs/lean_plan/gen_cubicE.py 6 /home/yang/szkraw/runs/verify/r6816468-out/gen/E_6.lean  sha256 f3d0db86e107626c
[02:07:53] end 30: rc=0, 1s, last line: case 6: 92 tail facts
[02:07:53] start 31/34: runs/lean_plan/phi3_edge.py 40  sha256 9977f63f232e1e89
[02:07:53] end 31: rc=0, 0s, last line: done
[02:07:53] start 32/34: runs/lean_plan/phi3_generic.py  sha256 0e2fd112c023b819
[02:07:56] end 32: rc=0, 3s, last line: generic formulas agree with the exact coefficients for 4 <= n <= a <= 15
[02:07:56] start 33/34: runs/lean_plan/p3_numeric_witnesses.py  sha256 f16727cce76173f5
[02:07:57] end 33: rc=0, 1s, last line: terminal r=1/3 N=120 e=-2/125: g(N,N;N) < 0: True
[02:07:57] start 34/34: runs/lean_plan/lambda_n.py 10  sha256 88951c89fad2f145
[02:07:58] end 34: rc=0, 1s, last line: 10 165 (2, 2, 3)
[02:07:58] all done
```

## Revision c95705c (2026-10-24)

Clone of https://github.com/skypher/szkraw at `c95705cd8c0b67144b04fb9414662e866e6eacdd` (the revision cited as \bibitem{code} in the three papers). The same 34 scripts as in the 6816468 run were run unmodified with python3 by `run_certs.sh` (local clone and outputs, not committed). All 34 exit with code 0; their SHA-256 prefixes and last lines are identical to those of the 6816468 run. This revision adds no script; it adds `lean/Szkraw/RaiseDirection.lean` (`Szkraw.raise_direction`, `Szkraw.raise_not_uniform`) and restates `Szkraw.direction_not_uniform` (Lean fidelity round 34, PASS). The Lean development builds with `make lean`; its axiom audit is `lean/axioms.log` (389 lines, only propext, Classical.choice, Quot.sound), and rerunning the audit on a working tree equal to this revision, with no untracked files under `lean/`, reproduces it byte for byte.

```
[01:11:16] start 01/34: runs/cubic/bdetour_cert.py  sha256 c1234cd3a53edc5c
[01:13:33] end 01: rc=0, 137s, last line: ALL CERTIFIED (349 polynomial and sign checks)
[01:13:33] start 02/34: runs/cubic/corner_cert.py  sha256 1af8fb16d3039cc2
[01:13:36] end 02: rc=0, 3s, last line: CERTIFIED: corner repair (12 phi_2(0) + 8 phi_3(0)) phi_2(1) >= 8 c_1 phi_4(0) under r sigma <= t tau
[01:13:36] start 03/34: runs/cubic/edetour_cert.py 3  sha256 1e37a310894c7d23
[01:15:47] end 03: rc=0, 131s, last line: CERTIFIED: E detour with constant 3 (124 checks)
[01:15:47] start 04/34: runs/cubic/phi2loc_cert.py  sha256 631bdcff8c7ca0ef
[01:15:50] end 04: rc=0, 3s, last line: CERTIFIED: Phi2loc >= 0 for all a >= 3
[01:15:50] start 05/34: runs/cubic/phi3loc_cert.py  sha256 96e033c94690a1de
[01:15:54] end 05: rc=0, 4s, last line: CERTIFIED (with chain check)
[01:15:54] start 06/34: runs/cubic/bdetour_u.py 7/4  sha256 0c25196c8b57dcc2
[01:16:14] end 06: rc=0, 20s, last line: ALL CERTIFIED for kappa_ttau + 7/4 kappa_rs (51 checks)
[01:16:14] start 07/34: runs/cubic/edetour_u.py 3 7/4  sha256 6c895068baa1a1bb
[01:16:26] end 07: rc=0, 12s, last line: CERTIFIED: E detour, constant 3, kappa_ttau + 7/4 kappa_rs (18 checks)
[01:16:26] start 08/34: runs/sharp/lc_violation_cert.py 6 1/10 11/10  sha256 a580479d73aee4e4
[01:16:26] end 08: rc=0, 0s, last line: CERTIFIED: (P) for every r in [0,1]
[01:16:26] start 09/34: runs/sharp/lc_violation_cert.py 8 1/10 11/10  sha256 a580479d73aee4e4
[01:16:27] end 09: rc=0, 1s, last line: CERTIFIED: (P) for every r in [0,1]
[01:16:27] start 10/34: runs/sharp/lc_violation_cert.py 10 1/10 11/10  sha256 a580479d73aee4e4
[01:16:28] end 10: rc=0, 1s, last line: CERTIFIED: (P) for every r in [0,1]
[01:16:28] start 11/34: runs/sharp/lc_violation_cert.py 12 1/10 11/10  sha256 a580479d73aee4e4
[01:16:29] end 11: rc=0, 1s, last line: CERTIFIED: (P) for every r in [0,1]
[01:16:29] start 12/34: runs/sharp/lc_violation_cert.py 6 1/100 11/10  sha256 a580479d73aee4e4
[01:16:29] end 12: rc=0, 0s, last line: FAILS: g(6, 6, 6) = -11421689396209222100480371/11282159504913398311706203653864919 < 0 at r = 1 (exact)
[01:16:29] start 13/34: runs/varratio/key_weight_cert.py  sha256 98cdfd094853b19a
[01:16:33] end 13: rc=0, 4s, last line: all small-weight checks pass: True
[01:16:33] start 14/34: runs/varratio/key_weight_closed.py  sha256 104ff8b35eb2f33f
[01:16:34] end 14: rc=0, 1s, last line: closed-form mismatches: 0
[01:16:34] start 15/34: runs/varratio/key_phi_ustep.py 5  sha256 0e1e48daf8f7eb9b
[01:16:43] end 15: rc=0, 9s, last line: a=5: central sums {'CERTIFIED': 20}
[01:16:43] start 16/34: runs/varratio/key_lin_cert.py 5  sha256 bebde4f1f76d13cc
[01:16:45] end 16: rc=0, 2s, last line: a=5: Lin coefficients {'CERTIFIED': 6}
[01:16:45] start 17/34: runs/lean_plan/edge_exact.py 60  sha256 5c672d687645c760
[01:16:45] end 17: rc=0, 0s, last line: Qhat: fails at []
[01:16:45] start 18/34: runs/lean_plan/forms_iii_v.py  sha256 ec8d35c58fa468a6
[01:16:49] end 18: rc=0, 4s, last line: generic formulas agree with the exact sequences for 4 <= n <= a <= 13
[01:16:49] start 19/34: runs/lean_plan/window_cert.py  sha256 9d97b37700afe147
[01:16:52] end 19: rc=0, 3s, last line: ALL CERTIFIED
[01:16:52] start 20/34: runs/lean_plan/gen_cubicB.py gen /home/yang/szkraw/runs/verify/r6816468-out/gen/B_gen.lean  sha256 a14373132671fa5a
[01:16:56] end 20: rc=0, 5s, last line: case gen: 93 tail facts
[01:16:57] start 21/34: runs/lean_plan/gen_cubicB.py 2 /home/yang/szkraw/runs/verify/r6816468-out/gen/B_2.lean  sha256 a14373132671fa5a
[01:16:59] end 21: rc=0, 2s, last line: case 2: 67 tail facts
[01:16:59] start 22/34: runs/lean_plan/gen_cubicB.py 3 /home/yang/szkraw/runs/verify/r6816468-out/gen/B_3.lean  sha256 a14373132671fa5a
[01:17:01] end 22: rc=0, 2s, last line: case 3: 94 tail facts
[01:17:01] start 23/34: runs/lean_plan/gen_cubicB.py 4 /home/yang/szkraw/runs/verify/r6816468-out/gen/B_4.lean  sha256 a14373132671fa5a
[01:17:04] end 23: rc=0, 3s, last line: case 4: 102 tail facts
[01:17:04] start 24/34: runs/lean_plan/gen_cubicB.py 5 /home/yang/szkraw/runs/verify/r6816468-out/gen/B_5.lean  sha256 a14373132671fa5a
[01:17:06] end 24: rc=0, 2s, last line: case 5: 121 tail facts
[01:17:06] start 25/34: runs/lean_plan/gen_cubicB.py corner /home/yang/szkraw/runs/verify/r6816468-out/gen/B_corner.lean  sha256 a14373132671fa5a
[01:17:07] end 25: rc=0, 1s, last line: case corner: 46 tail facts
[01:17:07] start 26/34: runs/lean_plan/gen_cubicE.py gen /home/yang/szkraw/runs/verify/r6816468-out/gen/E_gen.lean  sha256 f3d0db86e107626c
[01:17:11] end 26: rc=0, 4s, last line: case gen: 92 tail facts
[01:17:11] start 27/34: runs/lean_plan/gen_cubicE.py 3 /home/yang/szkraw/runs/verify/r6816468-out/gen/E_3.lean  sha256 f3d0db86e107626c
[01:17:12] end 27: rc=0, 1s, last line: case 3: 62 tail facts
[01:17:12] start 28/34: runs/lean_plan/gen_cubicE.py 4 /home/yang/szkraw/runs/verify/r6816468-out/gen/E_4.lean  sha256 f3d0db86e107626c
[01:17:13] end 28: rc=0, 1s, last line: case 4: 77 tail facts
[01:17:13] start 29/34: runs/lean_plan/gen_cubicE.py 5 /home/yang/szkraw/runs/verify/r6816468-out/gen/E_5.lean  sha256 f3d0db86e107626c
[01:17:14] end 29: rc=0, 1s, last line: case 5: 88 tail facts
[01:17:14] start 30/34: runs/lean_plan/gen_cubicE.py 6 /home/yang/szkraw/runs/verify/r6816468-out/gen/E_6.lean  sha256 f3d0db86e107626c
[01:17:15] end 30: rc=0, 1s, last line: case 6: 92 tail facts
[01:17:15] start 31/34: runs/lean_plan/phi3_edge.py 40  sha256 9977f63f232e1e89
[01:17:15] end 31: rc=0, 0s, last line: done
[01:17:15] start 32/34: runs/lean_plan/phi3_generic.py  sha256 0e2fd112c023b819
[01:17:18] end 32: rc=0, 3s, last line: generic formulas agree with the exact coefficients for 4 <= n <= a <= 15
[01:17:18] start 33/34: runs/lean_plan/p3_numeric_witnesses.py  sha256 f16727cce76173f5
[01:17:19] end 33: rc=0, 1s, last line: terminal r=1/3 N=120 e=-2/125: g(N,N;N) < 0: True
[01:17:19] start 34/34: runs/lean_plan/lambda_n.py 10  sha256 88951c89fad2f145
[01:17:19] end 34: rc=0, 0s, last line: 10 165 (2, 2, 3)
[01:17:19] all done
```

## Revision 6816468 (2026-10-24)

Clone of https://github.com/skypher/szkraw at `681646854f660f24ada3fb18f5bd8a8cc08ba0a9` (the revision cited as \bibitem{code} in the three papers). The 33 scripts of the earlier runs, plus `runs/lean_plan/lambda_n.py 10` (the values Λ_N of P3, Section 9, formalized as `Szkraw.lambda_values`), were run unmodified with python3 by `run_certs.sh` (local clone and outputs, not committed). All 34 exit with code 0. The first 33 last lines are identical to those of the 14b4fa2 run, and `lambda_n.py` prints Λ_N = 4, 10, 18, 28, 52, 90, 165 for N = 4, …, 10. The Lean files written by the generators occur verbatim in `lean/Szkraw/CubicB.lean` and `lean/Szkraw/CubicE.lean`. The Lean development builds with `make lean`; its axiom audit is `lean/axioms.log` (386 lines, only propext, Classical.choice, Quot.sound), produced from a working tree equal to this revision with no untracked files under `lean/`.

```
[00:26:38] start 01/34: runs/cubic/bdetour_cert.py  sha256 c1234cd3a53edc5c
[00:28:56] end 01: rc=0, 138s, last line: ALL CERTIFIED (349 polynomial and sign checks)
[00:28:56] start 02/34: runs/cubic/corner_cert.py  sha256 1af8fb16d3039cc2
[00:28:58] end 02: rc=0, 2s, last line: CERTIFIED: corner repair (12 phi_2(0) + 8 phi_3(0)) phi_2(1) >= 8 c_1 phi_4(0) under r sigma <= t tau
[00:28:58] start 03/34: runs/cubic/edetour_cert.py 3  sha256 1e37a310894c7d23
[00:31:11] end 03: rc=0, 133s, last line: CERTIFIED: E detour with constant 3 (124 checks)
[00:31:11] start 04/34: runs/cubic/phi2loc_cert.py  sha256 631bdcff8c7ca0ef
[00:31:14] end 04: rc=0, 3s, last line: CERTIFIED: Phi2loc >= 0 for all a >= 3
[00:31:14] start 05/34: runs/cubic/phi3loc_cert.py  sha256 96e033c94690a1de
[00:31:18] end 05: rc=0, 4s, last line: CERTIFIED (with chain check)
[00:31:18] start 06/34: runs/cubic/bdetour_u.py 7/4  sha256 0c25196c8b57dcc2
[00:31:37] end 06: rc=0, 19s, last line: ALL CERTIFIED for kappa_ttau + 7/4 kappa_rs (51 checks)
[00:31:37] start 07/34: runs/cubic/edetour_u.py 3 7/4  sha256 6c895068baa1a1bb
[00:31:50] end 07: rc=0, 13s, last line: CERTIFIED: E detour, constant 3, kappa_ttau + 7/4 kappa_rs (18 checks)
[00:31:50] start 08/34: runs/sharp/lc_violation_cert.py 6 1/10 11/10  sha256 a580479d73aee4e4
[00:31:51] end 08: rc=0, 1s, last line: CERTIFIED: (P) for every r in [0,1]
[00:31:51] start 09/34: runs/sharp/lc_violation_cert.py 8 1/10 11/10  sha256 a580479d73aee4e4
[00:31:51] end 09: rc=0, 0s, last line: CERTIFIED: (P) for every r in [0,1]
[00:31:51] start 10/34: runs/sharp/lc_violation_cert.py 10 1/10 11/10  sha256 a580479d73aee4e4
[00:31:52] end 10: rc=0, 1s, last line: CERTIFIED: (P) for every r in [0,1]
[00:31:52] start 11/34: runs/sharp/lc_violation_cert.py 12 1/10 11/10  sha256 a580479d73aee4e4
[00:31:53] end 11: rc=0, 1s, last line: CERTIFIED: (P) for every r in [0,1]
[00:31:53] start 12/34: runs/sharp/lc_violation_cert.py 6 1/100 11/10  sha256 a580479d73aee4e4
[00:31:54] end 12: rc=0, 1s, last line: FAILS: g(6, 6, 6) = -11421689396209222100480371/11282159504913398311706203653864919 < 0 at r = 1 (exact)
[00:31:54] start 13/34: runs/varratio/key_weight_cert.py  sha256 98cdfd094853b19a
[00:31:58] end 13: rc=0, 4s, last line: all small-weight checks pass: True
[00:31:58] start 14/34: runs/varratio/key_weight_closed.py  sha256 104ff8b35eb2f33f
[00:31:59] end 14: rc=0, 1s, last line: closed-form mismatches: 0
[00:31:59] start 15/34: runs/varratio/key_phi_ustep.py 5  sha256 0e1e48daf8f7eb9b
[00:32:07] end 15: rc=0, 8s, last line: a=5: central sums {'CERTIFIED': 20}
[00:32:07] start 16/34: runs/varratio/key_lin_cert.py 5  sha256 bebde4f1f76d13cc
[00:32:10] end 16: rc=0, 3s, last line: a=5: Lin coefficients {'CERTIFIED': 6}
[00:32:10] start 17/34: runs/lean_plan/edge_exact.py 60  sha256 5c672d687645c760
[00:32:10] end 17: rc=0, 0s, last line: Qhat: fails at []
[00:32:10] start 18/34: runs/lean_plan/forms_iii_v.py  sha256 ec8d35c58fa468a6
[00:32:14] end 18: rc=0, 4s, last line: generic formulas agree with the exact sequences for 4 <= n <= a <= 13
[00:32:14] start 19/34: runs/lean_plan/window_cert.py  sha256 9d97b37700afe147
[00:32:17] end 19: rc=0, 3s, last line: ALL CERTIFIED
[00:32:17] start 20/34: runs/lean_plan/gen_cubicB.py gen /home/yang/szkraw/runs/verify/r6816468-out/gen/B_gen.lean  sha256 a14373132671fa5a
[00:32:21] end 20: rc=0, 4s, last line: case gen: 93 tail facts
[00:32:21] start 21/34: runs/lean_plan/gen_cubicB.py 2 /home/yang/szkraw/runs/verify/r6816468-out/gen/B_2.lean  sha256 a14373132671fa5a
[00:32:24] end 21: rc=0, 3s, last line: case 2: 67 tail facts
[00:32:24] start 22/34: runs/lean_plan/gen_cubicB.py 3 /home/yang/szkraw/runs/verify/r6816468-out/gen/B_3.lean  sha256 a14373132671fa5a
[00:32:26] end 22: rc=0, 2s, last line: case 3: 94 tail facts
[00:32:26] start 23/34: runs/lean_plan/gen_cubicB.py 4 /home/yang/szkraw/runs/verify/r6816468-out/gen/B_4.lean  sha256 a14373132671fa5a
[00:32:29] end 23: rc=0, 3s, last line: case 4: 102 tail facts
[00:32:29] start 24/34: runs/lean_plan/gen_cubicB.py 5 /home/yang/szkraw/runs/verify/r6816468-out/gen/B_5.lean  sha256 a14373132671fa5a
[00:32:32] end 24: rc=0, 3s, last line: case 5: 121 tail facts
[00:32:32] start 25/34: runs/lean_plan/gen_cubicB.py corner /home/yang/szkraw/runs/verify/r6816468-out/gen/B_corner.lean  sha256 a14373132671fa5a
[00:32:32] end 25: rc=0, 0s, last line: case corner: 46 tail facts
[00:32:32] start 26/34: runs/lean_plan/gen_cubicE.py gen /home/yang/szkraw/runs/verify/r6816468-out/gen/E_gen.lean  sha256 f3d0db86e107626c
[00:32:37] end 26: rc=0, 5s, last line: case gen: 92 tail facts
[00:32:37] start 27/34: runs/lean_plan/gen_cubicE.py 3 /home/yang/szkraw/runs/verify/r6816468-out/gen/E_3.lean  sha256 f3d0db86e107626c
[00:32:38] end 27: rc=0, 1s, last line: case 3: 62 tail facts
[00:32:38] start 28/34: runs/lean_plan/gen_cubicE.py 4 /home/yang/szkraw/runs/verify/r6816468-out/gen/E_4.lean  sha256 f3d0db86e107626c
[00:32:39] end 28: rc=0, 1s, last line: case 4: 77 tail facts
[00:32:39] start 29/34: runs/lean_plan/gen_cubicE.py 5 /home/yang/szkraw/runs/verify/r6816468-out/gen/E_5.lean  sha256 f3d0db86e107626c
[00:32:40] end 29: rc=0, 1s, last line: case 5: 88 tail facts
[00:32:40] start 30/34: runs/lean_plan/gen_cubicE.py 6 /home/yang/szkraw/runs/verify/r6816468-out/gen/E_6.lean  sha256 f3d0db86e107626c
[00:32:41] end 30: rc=0, 1s, last line: case 6: 92 tail facts
[00:32:41] start 31/34: runs/lean_plan/phi3_edge.py 40  sha256 9977f63f232e1e89
[00:32:41] end 31: rc=0, 0s, last line: done
[00:32:41] start 32/34: runs/lean_plan/phi3_generic.py  sha256 0e2fd112c023b819
[00:32:43] end 32: rc=0, 2s, last line: generic formulas agree with the exact coefficients for 4 <= n <= a <= 15
[00:32:43] start 33/34: runs/lean_plan/p3_numeric_witnesses.py  sha256 f16727cce76173f5
[00:32:44] end 33: rc=0, 1s, last line: terminal r=1/3 N=120 e=-2/125: g(N,N;N) < 0: True
[00:32:44] start 34/34: runs/lean_plan/lambda_n.py 10  sha256 88951c89fad2f145
[00:32:45] end 34: rc=0, 1s, last line: 10 165 (2, 2, 3)
[00:32:45] all done
```

## Revision 14b4fa2 (2026-10-23)

Clone of https://github.com/skypher/szkraw at `14b4fa228f89ea1805289001743aadb7939b2b72` (the revision cited as \bibitem{code} in the three papers), the same 33 scripts as in the run at a25bf9a below, run unmodified with python3 by `run_certs.sh` (local clone and outputs, not committed). All 33 exit with code 0, and their last output lines are identical to those of the a25bf9a run. The Lean files written by the generators occur verbatim in `lean/Szkraw/CubicB.lean` and `lean/Szkraw/CubicE.lean` at this revision. The Lean development at this revision builds with `make lean`; its axiom audit is `lean/axioms.log` (381 lines, only propext, Classical.choice, Quot.sound), produced from a working tree equal to this revision with no untracked files under `lean/`.

```
[23:45:11] start 01/33: runs/cubic/bdetour_cert.py  sha256 c1234cd3a53edc5c
[23:47:27] end 01: rc=0, 136s, last line: ALL CERTIFIED (349 polynomial and sign checks)
[23:47:27] start 02/33: runs/cubic/corner_cert.py  sha256 1af8fb16d3039cc2
[23:47:29] end 02: rc=0, 2s, last line: CERTIFIED: corner repair (12 phi_2(0) + 8 phi_3(0)) phi_2(1) >= 8 c_1 phi_4(0) under r sigma <= t tau
[23:47:29] start 03/33: runs/cubic/edetour_cert.py 3  sha256 1e37a310894c7d23
[23:49:38] end 03: rc=0, 129s, last line: CERTIFIED: E detour with constant 3 (124 checks)
[23:49:38] start 04/33: runs/cubic/phi2loc_cert.py  sha256 631bdcff8c7ca0ef
[23:49:42] end 04: rc=0, 4s, last line: CERTIFIED: Phi2loc >= 0 for all a >= 3
[23:49:42] start 05/33: runs/cubic/phi3loc_cert.py  sha256 96e033c94690a1de
[23:49:45] end 05: rc=0, 4s, last line: CERTIFIED (with chain check)
[23:49:46] start 06/33: runs/cubic/bdetour_u.py 7/4  sha256 0c25196c8b57dcc2
[23:50:05] end 06: rc=0, 19s, last line: ALL CERTIFIED for kappa_ttau + 7/4 kappa_rs (51 checks)
[23:50:05] start 07/33: runs/cubic/edetour_u.py 3 7/4  sha256 6c895068baa1a1bb
[23:50:17] end 07: rc=0, 12s, last line: CERTIFIED: E detour, constant 3, kappa_ttau + 7/4 kappa_rs (18 checks)
[23:50:17] start 08/33: runs/sharp/lc_violation_cert.py 6 1/10 11/10  sha256 a580479d73aee4e4
[23:50:17] end 08: rc=0, 0s, last line: CERTIFIED: (P) for every r in [0,1]
[23:50:17] start 09/33: runs/sharp/lc_violation_cert.py 8 1/10 11/10  sha256 a580479d73aee4e4
[23:50:18] end 09: rc=0, 1s, last line: CERTIFIED: (P) for every r in [0,1]
[23:50:18] start 10/33: runs/sharp/lc_violation_cert.py 10 1/10 11/10  sha256 a580479d73aee4e4
[23:50:19] end 10: rc=0, 1s, last line: CERTIFIED: (P) for every r in [0,1]
[23:50:19] start 11/33: runs/sharp/lc_violation_cert.py 12 1/10 11/10  sha256 a580479d73aee4e4
[23:50:20] end 11: rc=0, 1s, last line: CERTIFIED: (P) for every r in [0,1]
[23:50:20] start 12/33: runs/sharp/lc_violation_cert.py 6 1/100 11/10  sha256 a580479d73aee4e4
[23:50:20] end 12: rc=0, 0s, last line: FAILS: g(6, 6, 6) = -11421689396209222100480371/11282159504913398311706203653864919 < 0 at r = 1 (exact)
[23:50:20] start 13/33: runs/varratio/key_weight_cert.py  sha256 98cdfd094853b19a
[23:50:25] end 13: rc=0, 5s, last line: all small-weight checks pass: True
[23:50:25] start 14/33: runs/varratio/key_weight_closed.py  sha256 104ff8b35eb2f33f
[23:50:26] end 14: rc=0, 1s, last line: closed-form mismatches: 0
[23:50:26] start 15/33: runs/varratio/key_phi_ustep.py 5  sha256 0e1e48daf8f7eb9b
[23:50:35] end 15: rc=0, 9s, last line: a=5: central sums {'CERTIFIED': 20}
[23:50:35] start 16/33: runs/varratio/key_lin_cert.py 5  sha256 bebde4f1f76d13cc
[23:50:37] end 16: rc=0, 2s, last line: a=5: Lin coefficients {'CERTIFIED': 6}
[23:50:37] start 17/33: runs/lean_plan/edge_exact.py 60  sha256 5c672d687645c760
[23:50:37] end 17: rc=0, 0s, last line: Qhat: fails at []
[23:50:37] start 18/33: runs/lean_plan/forms_iii_v.py  sha256 ec8d35c58fa468a6
[23:50:42] end 18: rc=0, 5s, last line: generic formulas agree with the exact sequences for 4 <= n <= a <= 13
[23:50:42] start 19/33: runs/lean_plan/window_cert.py  sha256 9d97b37700afe147
[23:50:45] end 19: rc=0, 3s, last line: ALL CERTIFIED
[23:50:45] start 20/33: runs/lean_plan/gen_cubicB.py gen /home/yang/szkraw/runs/verify/r14b4fa2-out/gen/B_gen.lean  sha256 a14373132671fa5a
[23:50:49] end 20: rc=0, 4s, last line: case gen: 93 tail facts
[23:50:49] start 21/33: runs/lean_plan/gen_cubicB.py 2 /home/yang/szkraw/runs/verify/r14b4fa2-out/gen/B_2.lean  sha256 a14373132671fa5a
[23:50:51] end 21: rc=0, 2s, last line: case 2: 67 tail facts
[23:50:51] start 22/33: runs/lean_plan/gen_cubicB.py 3 /home/yang/szkraw/runs/verify/r14b4fa2-out/gen/B_3.lean  sha256 a14373132671fa5a
[23:50:54] end 22: rc=0, 3s, last line: case 3: 94 tail facts
[23:50:54] start 23/33: runs/lean_plan/gen_cubicB.py 4 /home/yang/szkraw/runs/verify/r14b4fa2-out/gen/B_4.lean  sha256 a14373132671fa5a
[23:50:56] end 23: rc=0, 2s, last line: case 4: 102 tail facts
[23:50:56] start 24/33: runs/lean_plan/gen_cubicB.py 5 /home/yang/szkraw/runs/verify/r14b4fa2-out/gen/B_5.lean  sha256 a14373132671fa5a
[23:50:59] end 24: rc=0, 3s, last line: case 5: 121 tail facts
[23:50:59] start 25/33: runs/lean_plan/gen_cubicB.py corner /home/yang/szkraw/runs/verify/r14b4fa2-out/gen/B_corner.lean  sha256 a14373132671fa5a
[23:50:59] end 25: rc=0, 0s, last line: case corner: 46 tail facts
[23:50:59] start 26/33: runs/lean_plan/gen_cubicE.py gen /home/yang/szkraw/runs/verify/r14b4fa2-out/gen/E_gen.lean  sha256 f3d0db86e107626c
[23:51:04] end 26: rc=0, 5s, last line: case gen: 92 tail facts
[23:51:04] start 27/33: runs/lean_plan/gen_cubicE.py 3 /home/yang/szkraw/runs/verify/r14b4fa2-out/gen/E_3.lean  sha256 f3d0db86e107626c
[23:51:05] end 27: rc=0, 1s, last line: case 3: 62 tail facts
[23:51:05] start 28/33: runs/lean_plan/gen_cubicE.py 4 /home/yang/szkraw/runs/verify/r14b4fa2-out/gen/E_4.lean  sha256 f3d0db86e107626c
[23:51:06] end 28: rc=0, 1s, last line: case 4: 77 tail facts
[23:51:06] start 29/33: runs/lean_plan/gen_cubicE.py 5 /home/yang/szkraw/runs/verify/r14b4fa2-out/gen/E_5.lean  sha256 f3d0db86e107626c
[23:51:07] end 29: rc=0, 1s, last line: case 5: 88 tail facts
[23:51:07] start 30/33: runs/lean_plan/gen_cubicE.py 6 /home/yang/szkraw/runs/verify/r14b4fa2-out/gen/E_6.lean  sha256 f3d0db86e107626c
[23:51:08] end 30: rc=0, 1s, last line: case 6: 92 tail facts
[23:51:08] start 31/33: runs/lean_plan/phi3_edge.py 40  sha256 9977f63f232e1e89
[23:51:08] end 31: rc=0, 0s, last line: done
[23:51:08] start 32/33: runs/lean_plan/phi3_generic.py  sha256 0e2fd112c023b819
[23:51:11] end 32: rc=0, 3s, last line: generic formulas agree with the exact coefficients for 4 <= n <= a <= 15
[23:51:11] start 33/33: runs/lean_plan/p3_numeric_witnesses.py  sha256 f16727cce76173f5
[23:51:12] end 33: rc=0, 1s, last line: terminal r=1/3 N=120 e=-2/125: g(N,N;N) < 0: True
[23:51:12] all done
```

## Revision a25bf9a (2026-10-23)

Clone of https://github.com/skypher/szkraw at `a25bf9a148047a6d909ae752e1ed1f8452aea394` (the revision cited as \bibitem{code} in the three papers), scripts run unmodified with python3 by `run_certs.sh` (local clone and outputs, not committed). Items 1-16 are the certificate scripts of the earlier run below; items 17-33 are the scripts of the Lean route cited in P2 (edge bounds, forms of step (v), small windows, the generators of the cubic B and E detour certificates, the Phi_3 edge forms) and the witness recomputation for the P3 rule and terminal-row statements. Each line gives the exit code, the run time and the last output line. All 33 exit with code 0 and print the expected verdicts. `edge_exact.py 60` fails exactly for R2 at a <= 5 and K_a at a <= 4, as stated in P2.

The Lean files written by the generators (items 20-30) occur verbatim in `lean/Szkraw/CubicB.lean` and `lean/Szkraw/CubicE.lean` at this revision. The Lean development at this revision builds with `make lean`; its axiom audit is `lean/axioms.log` (343 lines, only propext, Classical.choice, Quot.sound), produced from a working tree equal to this revision with no untracked files under `lean/`.

```
[21:57:24] start 01/33: runs/cubic/bdetour_cert.py  sha256 c1234cd3a53edc5c
[21:59:39] end 01: rc=0, 135s, last line: ALL CERTIFIED (349 polynomial and sign checks)
[21:59:39] start 02/33: runs/cubic/corner_cert.py  sha256 1af8fb16d3039cc2
[21:59:42] end 02: rc=0, 3s, last line: CERTIFIED: corner repair (12 phi_2(0) + 8 phi_3(0)) phi_2(1) >= 8 c_1 phi_4(0) under r sigma <= t tau
[21:59:42] start 03/33: runs/cubic/edetour_cert.py 3  sha256 1e37a310894c7d23
[22:01:51] end 03: rc=0, 129s, last line: CERTIFIED: E detour with constant 3 (124 checks)
[22:01:51] start 04/33: runs/cubic/phi2loc_cert.py  sha256 631bdcff8c7ca0ef
[22:01:54] end 04: rc=0, 3s, last line: CERTIFIED: Phi2loc >= 0 for all a >= 3
[22:01:54] start 05/33: runs/cubic/phi3loc_cert.py  sha256 96e033c94690a1de
[22:01:58] end 05: rc=0, 4s, last line: CERTIFIED (with chain check)
[22:01:58] start 06/33: runs/cubic/bdetour_u.py 7/4  sha256 0c25196c8b57dcc2
[22:02:17] end 06: rc=0, 19s, last line: ALL CERTIFIED for kappa_ttau + 7/4 kappa_rs (51 checks)
[22:02:17] start 07/33: runs/cubic/edetour_u.py 3 7/4  sha256 6c895068baa1a1bb
[22:02:28] end 07: rc=0, 11s, last line: CERTIFIED: E detour, constant 3, kappa_ttau + 7/4 kappa_rs (18 checks)
[22:02:28] start 08/33: runs/sharp/lc_violation_cert.py 6 1/10 11/10  sha256 a580479d73aee4e4
[22:02:29] end 08: rc=0, 1s, last line: CERTIFIED: (P) for every r in [0,1]
[22:02:29] start 09/33: runs/sharp/lc_violation_cert.py 8 1/10 11/10  sha256 a580479d73aee4e4
[22:02:29] end 09: rc=0, 0s, last line: CERTIFIED: (P) for every r in [0,1]
[22:02:29] start 10/33: runs/sharp/lc_violation_cert.py 10 1/10 11/10  sha256 a580479d73aee4e4
[22:02:30] end 10: rc=0, 1s, last line: CERTIFIED: (P) for every r in [0,1]
[22:02:30] start 11/33: runs/sharp/lc_violation_cert.py 12 1/10 11/10  sha256 a580479d73aee4e4
[22:02:31] end 11: rc=0, 1s, last line: CERTIFIED: (P) for every r in [0,1]
[22:02:31] start 12/33: runs/sharp/lc_violation_cert.py 6 1/100 11/10  sha256 a580479d73aee4e4
[22:02:32] end 12: rc=0, 1s, last line: FAILS: g(6, 6, 6) = -11421689396209222100480371/11282159504913398311706203653864919 < 0 at r = 1 (exact)
[22:02:32] start 13/33: runs/varratio/key_weight_cert.py  sha256 98cdfd094853b19a
[22:02:36] end 13: rc=0, 4s, last line: all small-weight checks pass: True
[22:02:36] start 14/33: runs/varratio/key_weight_closed.py  sha256 104ff8b35eb2f33f
[22:02:37] end 14: rc=0, 1s, last line: closed-form mismatches: 0
[22:02:37] start 15/33: runs/varratio/key_phi_ustep.py 5  sha256 0e1e48daf8f7eb9b
[22:02:45] end 15: rc=0, 8s, last line: a=5: central sums {'CERTIFIED': 20}
[22:02:45] start 16/33: runs/varratio/key_lin_cert.py 5  sha256 bebde4f1f76d13cc
[22:02:47] end 16: rc=0, 2s, last line: a=5: Lin coefficients {'CERTIFIED': 6}
[22:02:47] start 17/33: runs/lean_plan/edge_exact.py 60  sha256 5c672d687645c760
[22:02:48] end 17: rc=0, 1s, last line: Qhat: fails at []
[22:02:48] start 18/33: runs/lean_plan/forms_iii_v.py  sha256 ec8d35c58fa468a6
[22:02:52] end 18: rc=0, 4s, last line: generic formulas agree with the exact sequences for 4 <= n <= a <= 13
[22:02:52] start 19/33: runs/lean_plan/window_cert.py  sha256 9d97b37700afe147
[22:02:55] end 19: rc=0, 3s, last line: ALL CERTIFIED
[22:02:55] start 20/33: runs/lean_plan/gen_cubicB.py gen /home/yang/szkraw/runs/verify/ra25bf9a-out/gen/B_gen.lean  sha256 a14373132671fa5a
[22:02:59] end 20: rc=0, 4s, last line: case gen: 93 tail facts
[22:02:59] start 21/33: runs/lean_plan/gen_cubicB.py 2 /home/yang/szkraw/runs/verify/ra25bf9a-out/gen/B_2.lean  sha256 a14373132671fa5a
[22:03:02] end 21: rc=0, 3s, last line: case 2: 67 tail facts
[22:03:02] start 22/33: runs/lean_plan/gen_cubicB.py 3 /home/yang/szkraw/runs/verify/ra25bf9a-out/gen/B_3.lean  sha256 a14373132671fa5a
[22:03:05] end 22: rc=0, 3s, last line: case 3: 94 tail facts
[22:03:05] start 23/33: runs/lean_plan/gen_cubicB.py 4 /home/yang/szkraw/runs/verify/ra25bf9a-out/gen/B_4.lean  sha256 a14373132671fa5a
[22:03:08] end 23: rc=0, 3s, last line: case 4: 102 tail facts
[22:03:08] start 24/33: runs/lean_plan/gen_cubicB.py 5 /home/yang/szkraw/runs/verify/ra25bf9a-out/gen/B_5.lean  sha256 a14373132671fa5a
[22:03:10] end 24: rc=0, 2s, last line: case 5: 121 tail facts
[22:03:10] start 25/33: runs/lean_plan/gen_cubicB.py corner /home/yang/szkraw/runs/verify/ra25bf9a-out/gen/B_corner.lean  sha256 a14373132671fa5a
[22:03:11] end 25: rc=0, 1s, last line: case corner: 46 tail facts
[22:03:11] start 26/33: runs/lean_plan/gen_cubicE.py gen /home/yang/szkraw/runs/verify/ra25bf9a-out/gen/E_gen.lean  sha256 f3d0db86e107626c
[22:03:15] end 26: rc=0, 4s, last line: case gen: 92 tail facts
[22:03:15] start 27/33: runs/lean_plan/gen_cubicE.py 3 /home/yang/szkraw/runs/verify/ra25bf9a-out/gen/E_3.lean  sha256 f3d0db86e107626c
[22:03:16] end 27: rc=0, 1s, last line: case 3: 62 tail facts
[22:03:16] start 28/33: runs/lean_plan/gen_cubicE.py 4 /home/yang/szkraw/runs/verify/ra25bf9a-out/gen/E_4.lean  sha256 f3d0db86e107626c
[22:03:17] end 28: rc=0, 1s, last line: case 4: 77 tail facts
[22:03:17] start 29/33: runs/lean_plan/gen_cubicE.py 5 /home/yang/szkraw/runs/verify/ra25bf9a-out/gen/E_5.lean  sha256 f3d0db86e107626c
[22:03:18] end 29: rc=0, 1s, last line: case 5: 88 tail facts
[22:03:18] start 30/33: runs/lean_plan/gen_cubicE.py 6 /home/yang/szkraw/runs/verify/ra25bf9a-out/gen/E_6.lean  sha256 f3d0db86e107626c
[22:03:19] end 30: rc=0, 1s, last line: case 6: 92 tail facts
[22:03:19] start 31/33: runs/lean_plan/phi3_edge.py 40  sha256 9977f63f232e1e89
[22:03:19] end 31: rc=0, 0s, last line: done
[22:03:19] start 32/33: runs/lean_plan/phi3_generic.py  sha256 0e2fd112c023b819
[22:03:21] end 32: rc=0, 2s, last line: generic formulas agree with the exact coefficients for 4 <= n <= a <= 15
[22:03:21] start 33/33: runs/lean_plan/p3_numeric_witnesses.py  sha256 f16727cce76173f5
[22:03:23] end 33: rc=0, 2s, last line: terminal r=1/3 N=120 e=-2/125: g(N,N;N) < 0: True
[22:03:23] all done
```

## Earlier run: revision 4f739c3 (2026-10-23)

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
