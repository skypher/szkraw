# Independent review, round 26: additions after round 25 (Theorem 8.17 extension; sharpness of log-concavity)

Repository: github.com/skypher/szkraw, commit 19b0346 (paper.tex; scripts under runs/cubic/ and runs/sharp/). Round 25 reviewed Theorem 8.17 (`thm:lc-cubic`) at commit faaa5a0 and returned PASS WITH MINOR FIXES; its answer is reviews/round25-answer.md. Please review only the following, completely and independently. This is a mathematics review, not a Lean review. Verify every citation of a paper or book in its PDF; mark any citation you cannot open as unverified.

1. **Round-25 fixes.** Check that the five fixes in REVIEW.md ("Review round 25") are applied correctly in the proof of Theorem 8.17 and in the remark after it.
2. **Extension to rσ ≤ (7/4)tτ** (remark after the proof of Theorem 8.17).
   - Is it right that the condition enters the proof only through κ_tτ + κ_rσ ≥ 0 in (8.11) and (8.10)? Check also the corner (8.12), the key inequality (8.13) (whose polarization bound uses no trade) and the B decomposition with the Theorem 8.11 part.
   - Is it right that, with rσ ≤ u·tτ, it suffices that κ_tτ + u·κ_rσ ≥ 0 together with κ_tτ ≥ 0?
   - Do runs/cubic/bdetour_u.py 7/4 and runs/cubic/edetour_u.py 3 7/4 prove κ_tτ + (7/4)κ_rσ ≥ 0 in every case that bdetour_cert.py and edetour_cert.py cover for u = 1 (n symbolic, the low-n cases, all z-regimes)? Rerun them if you can.
   - Is the statement "Theorem 8.17 holds with rσ ≤ (7/4)tτ" then fully justified?
3. **Section 10, paragraph "How sharp is log-concavity?"**
   - The claims about Section 9 (the uniform-radius statement for fixed r ∈ (0,1)).
   - The Newton coefficients of D(i) = (1−μ)i + μ[i]_q and the quotient ν₁ν₃/ν₂² = 1/μ.
   - The exact all-r certificate runs/sharp/lc_violation_cert.py. Every g(m,n;k) is a polynomial in r because the recurrence divides only by a_m = 1 − d_m. A nonnegative Bernstein form on [0,1] then gives (P) for every r. Check the recurrence against probe.py and the paper's definitions, and rerun for N = 6, 8, 10, 12 with μ = 1/10, q = 11/10, plus the control μ = 1/100 at N = 6.
   - Whether the wording about the grid searches (r1_grid.py, r1_trend.py) is accurate and not overstated.
4. Whether the AI-use disclosure and the open problem in Section 10 now describe all of this accurately.

Answer format: PASS / PASS WITH MINOR FIXES / FAIL, every defect with an exact fix, and your independent checks. Be terse.
