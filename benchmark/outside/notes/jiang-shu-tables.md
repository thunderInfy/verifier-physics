# The original smoothness measurement (2.20) of jiang_shu_1995_weno: order, and the report's tables

Reconstruction v2, loose end A. The question: `reconstruction_order_p` finds the original measurement (2.20) fifth
order where f' != 0 with eps -> 0 (one reconstruction and the flux difference), and p. 7 of the report says it
"can only give 4th order accuracy". What do the report's own numerical tables show, and why?

Nothing here changes `items.jsonl`, `ERRATA.md` or an expected value. Script: `js_tables.py` (this folder's parent);
full output: `js_tables_output.md`.

## 1. Which tables

The brief calls them Tables 1-2. In the ICASE report (the version we read, `SOURCES.md`) Tables 1 and 2 are the
coefficient tables (candidate coefficients, optimal weights C_k^r); the numerical tests are **Tables 3 and 4**
(pp. 11-12), the ones p. 7 cites ("see Table 3 and 4"). Setup, p. 10: u_t + u_x = 0 on [-1, 1], periodic, errors
at t = 1; Table 3: u0 = sin(pi x), N = 10 .. 320; Table 4: u0 = sin^4(pi x), N = 20 .. 640; RK4 with
dt ~ dx^(5/4); eps = 10^-6 (p. 6); WENO-RF-4 is r = 3 with the original measurement, WENO-RF-5 with the new one
(3.2)-(3.4); L_inf and L1 errors and orders (L1 is the mean of |e_j|: the CENTRAL-5 rows of Table 3 have
L1/L_inf = 2/pi).

**Our replica reproduces the printed numbers** (float64, RK4, dt = dx^(5/4)/2, the constant being our choice).
Table 3, WENO-RF-4, L_inf: 1.32e-2, 3.01e-3, 4.28e-4, 5.17e-5, 4.98e-6, 3.44e-7 against the printed 1.31e-2,
3.00e-3, 4.27e-4, 5.17e-5, 4.99e-6, 3.44e-7; orders 2.13, 2.81, 3.05, 3.37, 3.86 on both sides. Table 4,
WENO-RF-4, L_inf: 7.27e-2, 2.48e-2, 4.60e-3, 3.59e-4, 2.12e-5, 1.51e-6 against 7.31e-2, 2.48e-2, 4.60e-3,
3.59e-4, 2.12e-5, 1.51e-6. The L1 columns agree to 1-2 digits except at N = 10 (8.59e-3 against 7.93e-3), and
WENO-RF-5 on sin^4 differs from N = 80 on (our 6.81e-5, 1.76e-6, 2.87e-8 against 1.22e-4, 4.37e-6, 9.79e-8),
probably the time step (theirs is not given beyond dx^(5/4)). So the setup is theirs.

## 2. The reconstruction alone

At t = 0, in 50-digit mpmath: the face error h^_{j+1/2} - h(x_{j+1/2}) (h the exact primitive of the flux form)
and the flux-difference error (h^_{j+1/2} - h^_{j-1/2})/dx - u'(x_j), at every grid point, for N up to 5120
(sin^4: 5120), eps = 10^-6 and eps = 0. The columns: L_inf and L1 orders, where the largest error sits (in cells
from the nearest critical point of u0) and the L1 error over the points farther than 0.1 from every critical point
("away"). Critical points: x = +-1/2 for sin (f' = 0, f'' != 0); x = +-1/2 (first order) and x = 0, +-1
(f' = f'' = f''' = 0) for sin^4.

Original measurement, sin, flux difference (orders between successive N):

| N | eps = 10^-6: L_inf | L1 | away | max at | eps = 0: L_inf | L1 | away | max at |
|---|---|---|---|---|---|---|---|---|
| 20 | 2.13 | 3.15 | 2.95 | 2.0 | 2.13 | 3.15 | 2.95 | 2.0 |
| 40 | 2.72 | 3.45 | 4.17 | 2.0 | 2.72 | 3.45 | 4.17 | 2.0 |
| 80 | 2.95 | 3.83 | 4.02 | 2.0 | 2.93 | 3.83 | 4.02 | 2.0 |
| 160 | 3.21 | 4.00 | 4.71 | 2.0 | 2.98 | 3.94 | 4.69 | 2.0 |
| 320 | 4.91 | 4.79 | 4.98 | 3.0 | 3.00 | 3.98 | 4.90 | 2.0 |
| 640 | 6.25 | 5.84 | 5.30 | 1.0 | 3.00 | 3.99 | 4.96 | 2.0 |
| 1280 | 6.93 | 6.11 | 5.94 | 1.0 | 3.00 | 4.00 | 4.98 | 2.0 |
| 5120 | 6.95 | 6.48 | 6.18 | 1.0 | 3.00 | 4.00 | 5.00 | 2.0 |

(`js_tables_output.md` has every row, the errors themselves and both data.) For the face value:
eps = 0 gives L_inf order 4.00 (max 3.5 cells from x = +-1/2), L1 4.81 at N = 5120 and still rising, and 5.00
away from the critical points; eps = 10^-6 gives 5.18 at N = 320 and above 6 from N = 640. sin^4 behaves the
same way (eps = 0: difference L_inf 3.00, L1 4.00, away 5.00; face L_inf 4.00, away 5.00).

## 3. What the tables' orders come from

- **Not mainly from the generic points.** Asymptotically, away from the critical points the original measurement
  is fifth order, for the face value and for the difference (eps = 0: "away" orders 4.99-5.00 for both data at
  N = 2560-5120). This is the numerical side of the exact result: with eps -> 0 and f' != 0,
  `reconstruction_order_p` gives leading order 5 at a grid point, for one reconstruction (form `point`, the face
  x_{i+1/2}) and for the flux difference (form `flux_difference`, at x_i), as identities in the Taylor jet. On the
  tables' grids the away part is itself pre-asymptotic (orders 2.95, 4.17, 4.02, 4.71 for N = 20 .. 160: the dx^5
  coefficient grows with f''/f', which is about 10 at 0.1 from x = +-1/2), but it carries a minority
  of the L1 error from N = 40 on, and none of the largest errors.
- **From the critical points of the data.** Within O(dx) of x = +-1/2 the indicators (2.23)-(2.25) differ at
  leading order (p. 7 says so: "only 3rd order accurate at these points"), so the difference error is O(dx^3)
  there: L_inf order 3, and L1 order 4 because those O(1) cells have weight dx in the mean. The largest error
  sits 2 cells from x = +-1/2 on every grid of the tables, and the share of the L1 error within 0.1 of a
  critical point grows from 0.4 to 0.8 over N = 20 .. 320.
- **On pre-asymptotic grids in eps.** With eps = 10^-6 fixed, the orders on the tables' grids are those of eps = 0
  (identical to 2-3 digits up to N = 160), because near x = +-1/2 the indicators, about 2 (f'' dx^2)^2 with f'' = pi^2
  for sin, run from about 10^-2 at N = 20 to 5 10^-6 at N = 160 and are not yet small against eps. Once they are (N >= 320 for sin),
  the weights there approach the optimal ones and every order rises to 5 and beyond (transient orders 6-7 while
  the error falls from the eps = 0 curve to the linear scheme's). So the eventual fixed-eps order is 5, the
  eps -> 0 order is 3 in L_inf and 4 in L1 (both from the critical points), and the printed orders (L_inf 2.13 ..
  3.86, L1 2.59 .. 4.65 in Table 3; L1 5.00 at N = 640 in Table 4) are the transition between them.

In short: the tables' sub-fifth orders are a critical-point effect seen on grids where eps = 10^-6 does not yet
dominate the indicators near the critical points. They are consistent with fifth order at generic points. The
eps -> 0 reading of p. 7 ("can only give 4th order" for smooth monotone regions, f' != 0) is REFUTED by
`reconstruction_order_p` (VERIFIED for p = 5, both forms); the tables do not bear on that reading, because their
errors are dominated by the critical points of sin and sin^4.

## 4. Why fifth order where f' != 0: the cancellation

From the module's own series (`tests/test_reconstruction_zm.py::test_original_measurement_cancellation_identity`):

- (2.20) expands as IS_k = (f' h)^2 + 2(k - 1) f' f'' h^3 + O(h^4), k = 0, 1, 2 (the O(h) relative terms of
  (2.23)-(2.25)).
- With eps = 0 and the power 2, alpha_k is proportional to d_k (1 - 4(k - 1) r h), r = f''/f', and since
  sum_k d_k (k - 1) = 1/5, omega_k = d_k + d_k (4/5 - 4(k - 1)) r h + O(h^2) = d_k + (12/25, 12/25, -24/25) r h
  + O(h^2). The source's argument asks for omega_k - d_k = O(h^2) ((2.14), (2.17)), a sufficient condition; here it
  is only O(h).
- The candidate errors at x_{i+1/2} are q_k - h = A_k f''' h^3 + O(h^4), A = (-1/4, 1/12, -1/12).
- The O(h^4) part of the face error, sum_k (omega_k - d_k) A_k f''' h^3, has coefficient
  (12/25)(-1/4) + (12/25)(1/12) + (-24/25)(-1/12) = -3/25 + 1/25 + 2/25 = 0. This holds because the weight error
  is d_k times a linear function of k and A satisfies both sum_k d_k A_k = 0 (the optimal combination is fifth
  order) and sum_k k d_k A_k = 0.
- So the face error is C(x_i) h^5 + O(h^6) with C smooth wherever f' != 0, and the flux difference
  (C(x_i) - C(x_{i-1})) h^5 / h + O(h^5) = O(h^5).

The identity is checked exactly in the test (the IS_k coefficients and A are read from the series, not typed in);
the weight expansion in the second step is the two-line derivation written there. The same weight-error shape
d_k (4/5 - 4(k - 1)) appears for the new measurement at a first-order critical point (README, Reconstructions),
where it cancels for the same reason.
