# runs/sharp: archived commands and outputs (2026-10-23)

These are the searches cited in Section 10 of paper.tex ("How sharp is log-concavity?"). All are at r = 1 unless stated. The grid results are the smallest failures found, not thresholds.

## r1_grid.py: float64 screening, mpmath confirmation (60 digits) of up to 20 candidates per N; one-jump family, K = 2..N-1

    python3 r1_grid.py 4,6,8,10 0.5
    N=4: 116 failing grid points; min B/A = 10^2.50 at log A = -3.5, log B = -1.0, K = 2, entry (4, 4, 4) = -1.42e-7 (confirmed)
    N=6: 119 failing grid points; min B/A = 10^2.00 at log A = -3.0, log B = -1.0, K = 2, entry (6, 6, 6) = -1.01e-9 (confirmed)
    N=8: 144 failing grid points; min B/A = 10^2.00 at log A = -2.5, log B = -0.5, K = 2, entry (8, 8, 6) = -1.83e-5 (confirmed)
    N=10: 152 failing grid points; min B/A = 10^2.00 at log A = -3.0, log B = -1.0, K = 2, entry (10, 10, 8) = -8.2e-9 (confirmed)
    python3 r1_grid.py 14,20,30,40 0.5
    N=14: 170 failing grid points; min B/A = 10^2.00 at log A = -3.0, log B = -1.0, K = 2, entry (14, 14, 8) = -4.19e-7 (confirmed)
    N=20: 182 failing grid points; min B/A = 10^2.00 at log A = -3.0, log B = -1.0, K = 2, entry (20, 20, 10) = -1.55e-6 (confirmed)
    N=30: 3902 failing grid points; none confirmed   (float64 noise at this size; not used)
    N=40: 5338 failing grid points; none confirmed   (float64 noise at this size; not used)
    python3 r1_grid.py 6,10,14,20 0.5 0.9   -> min B/A 10^2.5, 10^2.5, 10^2.0, 10^2.5 (all confirmed)
    python3 r1_grid.py 6,10,14,20 0.5 0.7   -> none, 10^3.0, 10^4.0, 10^3.0
    python3 r1_grid.py 6,10,14,20 0.5 0.5   -> no failing grid point

## r1_large.py: mpmath, K in {2, 3}, log A in {-5,-4,-3.5,-3,-2.5,-2}, v = log10(B/A) in {0.5,1,1.5,2,2.5}

    python3 r1_large.py 20,30,40 1 60
    N=20: min B/A = 10^2 (log A = -3.5, K = 2, min entry -4.4e-13)
    N=30: min B/A = 10^2 (log A = -4, K = 2, min entry -8.85e-30)
    N=40: min B/A = 10^1.5 (log A = -3, K = 2, min entry -9.41e-31)
    The N = 30 and N = 40 values are identical at 80 and 140 digits; v = 1.0 at N = 40 gives only rounding noise (1e-71 at 80 digits, 1e-130 at 140 digits).

## r1_trend.py: mpmath at 160 digits, K = 2, v in {0.75, 1, 1.25, 1.5} (sorted), log A in {-4,-3.5,-3,-2.5,-2}

    python3 r1_trend.py 60,80 0.75,1,1.25,1.5 -4,-3.5,-3,-2.5,-2 160
    N=60: v = 0.75, 1, 1.25: no failure (min entries of order -1e-145, rounding noise); v = 1.5 FAILS at log A = -3.0
    N=80: v = 0.75, 1, 1.25: no failure (rounding noise only); v = 1.5 FAILS at log A = -3.5 (min entry -8.0e-75 at (80, 80, 78))

## random_violation.py: N = 12, 30,000 random LC sequences with 1-3 upward bumps, violations up to 10^3, r in {1, 0.9, 0.7}

    python3 random_violation.py 12 30000 3 1,0.9,0.7 1   -> 0 float failures
    The random sampler did not reach the narrow failing windows that the grid search found at nearby sizes, so this says little.

## lc_violation_cert.py: exact, every r in [0, 1]

    python3 lc_violation_cert.py N 1/10 11/10   (N = 6, 8, 10, 12) -> CERTIFIED (every entry has a nonnegative Bernstein form)
    python3 lc_violation_cert.py 6 1/100 11/10  -> FAILS: g(6,6,6) = -11421689396209222100480371/11282159504913398311706203653864919 at r = 1
