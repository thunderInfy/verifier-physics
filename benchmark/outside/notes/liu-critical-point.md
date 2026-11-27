# The r = 3 WENO of Liu, Osher and Chan at a first-order critical point: order 2 or 3?

The question: `reconstruction_order_p` finds that the r = 3 scheme with the original smoothness measurement (2.18)/(2.20)
of jiang_shu_1995_weno (spec `specs/jiang-shu-weno5-liu-fd.json`), at a point with f' = 0, f'' != 0 and eps -> 0,
has face-value order 3 and flux-difference order 2. Page 7 of the report says the scheme "is only 3rd order
accurate" at critical points (a hypothesis of dev item `jiang_shu_1995_weno:01`). Which reading of that sentence
does the checker support, and what do the report's Tables 3-4 show?

Nothing here changes `items.jsonl`, `ERRATA.md`, an expected value or a dev score. Script: `liu_critical.py`
(this folder's parent; it reuses `face()` and `u()` of `js_tables.py`). Full output: `liu_critical_output.md`.

## 1. What the source claims

ICASE report 95-73 (the copy in `SOURCES.md`), printed p. 7 (pdf p. 8), after the expansions (2.23)-(2.25) of
IS_k for r = 3:

> We can see that the second order terms are different from stencil to stencil. Thus (2.22) is no longer valid at
> critical points of f(u(x)) which implies that the WENO scheme of Liu et al. for r = 3 is only 3rd order accurate
> at these points. In fact, the weights computed from the smoothness measurement (2.18) diverge far away from the
> optimal weights near critical points (see Figure 1 in the next section) on coarse grids (10 to 80 grid points per
> wave). But on fine grids, since the smoothness measurements IS_k for all k are relatively smaller than the
> non-zero constant eps in (2.16), the weights become close to the optimal weights.

What this fixes:

- **The quantity.** The order counting on pp. 5-7 is that of the numerical flux f^_{j+1/2} as an approximation
  of h_{j+1/2}, the face value of the primitive: (2.12) writes f^_{j+1/2} as the (2r-1)th order flux plus
  sum_k (omega_k - C_k)(q_k - h_{j+1/2}) (2.13), and "each term ... can be made O(h^{2r-1}) if
  omega_k = C_k + O(h^{r-1})" (2.14), with q_k - h_{j+1/2} = O(h^r) for each candidate. The same counting gives
  "(r+1)th order" from omega_k = C_k + O(h) (2.22), and "only 3rd" from omega_k - C_k = O(1) at a critical
  point: O(1) times O(h^3). So the derivation is about the face value. The text never states the order of the
  flux difference (2.2) separately; the item's third hypothesis reads the order as "truncation error of the
  spatial operator" (the flux difference), and so does the item's dev reading.
- **The eps regime.** The sentence is about the regime where eps is negligible against IS_k: the next sentences
  say that on fine grids, with eps = 10^-6 fixed, the weights return to the optimal ones. So it is not a claim
  about dx -> 0 with eps fixed.
- **At the points, not as a remark.** "at these points": at the critical points of f(u(x)) themselves, stated as
  a consequence of (2.23)-(2.25).
- **Order in which sense.** p. 10: "We caution the reader that the orders here are in L1 sense", said of the
  scheme names (WENO-X-4 for this scheme), i.e. of measured solution errors in L1.

Three readings follow: (A) the face error h^_{j+1/2} - h(x_{j+1/2}) is O(dx^3), and not better, at a critical
point, eps -> 0; (B) the truncation error of the flux difference (h^_{j+1/2} - h^_{j-1/2})/dx - f'(x_j) at a
critical point x_j is O(dx^3), eps -> 0; (C) the L1 error of the computed solution is third order for data with
critical points.

## 2. What the series says

`reconstruction_order_p`, regime critical, n_cp = 1 (f'(x_i) = 0, f''(x_i) != 0), eps = 0:

| form | p = 2 | p = 3 | p = 4 | leading order |
|---|---|---|---|---|
| point (face x_{i+1/2}) | VERIFIED | VERIFIED | REFUTED: (7/293) dx^3 at f'' = 1, f''' = 1/2 | 3 |
| flux_difference (at x_i) | VERIFIED | REFUTED: (100124/2854113) dx^2 at f'' = 1, f''' = 1/2 | REFUTED | 2 |

With eps fixed (eps = dx^0, c = 1 or c = 10^-6) both forms are VERIFIED at p = 5, leading order 5.

The coefficients, from the module's own series (`liu_critical.py`, section 2; each step is asserted against the
module's `_weights` and `_numerator`):

- With f' = 0, IS_k = c_k (f'' dx^2)^2 + O(dx^5). On the stencils of the face x_{i+1/2} (centred at x_i):
  c = (9/4, 5/4, 9/4), as (2.23)-(2.25) give with f' = 0. On the stencils of x_{i-1/2} (centred at x_{i-1}, where
  f' = -f'' dx, so f' dx and f'' dx^2 are of the same size): c' = (21/4, 9/4, 5/4).
- With eps = 0 and the power 2, omega_k -> (d_k / c_k^2) / sum_j (d_j / c_j^2), a non-zero constant, not d_k:
  omega(x_{i+1/2}) = (25/586, 243/293, 75/586) and omega(x_{i-1/2}) = (75/6494, 1225/3247, 3969/6494), against
  d = (1/10, 3/5, 3/10). The weight error is O(1) on both faces, and different on the two.
- The candidate errors are q_k - h = A_k f''' dx^3 + O(dx^4), A = (-1/4, 1/12, -1/12), with sum_k d_k A_k = 0.
- Face error: sum_k omega_k A_k f''' dx^3 = (14/293) f''' dx^3 at x_{i+1/2} (the checker's 7/293 at f''' = 1/2),
  and (-218/9741) f''' dx^3 at x_{i-1/2}.
- Flux difference: (14/293 + 218/9741) f''' dx^3 / dx = (200248/2854113) f''' dx^2 (about 0.0702 f''' dx^2).

The identity, in the form `jiang-shu-tables.md` used for the generic point: the leading face error is
sum_k omega_k A_k f''' dx^3 = sum_k (omega_k - d_k) A_k f''' dx^3. At a generic point the weight errors are
O(dx) and of the shape d_k (linear in k), which A annihilates, so the dx^4 term cancels and both faces carry the
same smooth dx^5 coefficient: the difference keeps order 5. At a critical point the weight errors are O(1) and
not of that shape (25/586 - 1/10 = -18/293 etc.), so the face error is a dx^3 term; and since the weights on
the two faces differ at O(1), the two dx^3 coefficients differ, 14/293 against -218/9741, and dividing by dx
leaves dx^2. The cancellation that would give the difference one order more than the face, the face error being
a smooth function of the face position, is missing: next to a critical point the error coefficient changes by
O(1) from one face to the next.

When also f''' = 0 (a symmetric extremum, like every critical point of sin(pi x) and sin^4(pi x)), the next terms
are: face (7/1465) f'''' dx^4, difference (21950/951371) f'''' dx^3. So such data show 4 and 3.

## 3. What the numerics say

mpmath, 50 digits, eps = 0 and 10^-6, N = 10 .. 5120 on [-1, 1]; errors at the 13 grid points and 14 faces
nearest the critical point x_c, on a grid with a point at x_c ("aligned") and on a grid shifted by dx/3
("offset"). Two data: sin(pi x) at x_c = 1/2 (f''' = 0) and g(x) = sin(pi x) + sin(2 pi x)/2 at x_c = 1/3
(f'' = -(3 sqrt 3/2) pi^2, f''' = (3/2) pi^3 != 0, a generic first-order critical point). Orders of the max
over that window:

| datum, grid | eps | face, N = 160 / 640 / 5120 | difference, N = 160 / 640 / 5120 |
|---|---|---|---|
| sin, aligned | 0 | 3.96 / 4.00 / 4.00 | 2.98 / 3.00 / 3.00 |
| sin, offset | 0 | 3.95 / 4.00 / 4.00 | 2.98 / 3.00 / 3.00 |
| sin, aligned | 10^-6 | 4.15 / 6.53 / 7.95 | 3.21 / 6.25 / 6.95 |
| g, aligned | 0 | 3.07 / 3.05 / 3.01 | 2.08 / 1.95 / 1.99 |
| g, offset | 0 | 3.10 / 3.06 / 3.01 | 2.00 / 2.02 / 2.00 |
| g, aligned | 10^-6 | 3.12 / 5.87 / 6.95 | 2.13 / 5.44 / 7.59 |

At the aligned point the scaled errors approach the series: for g, face/dx^3 = 2.2232 at N = 5120 against
(14/293) f''' = 2.2223, difference/dx^2 = 3.2735 against 3.2632; for sin, face/dx^4 and difference/dx^3 at
N = 5120 give 0.4654 and 2.247 against (7/1465) pi^4 = 0.4654 and (21950/951371) pi^4 = 2.247. The offset grid
gives the same orders (2 for the difference of g), so order 2 is not an artefact of a grid point sitting exactly
on x_c. With eps = 10^-6 the orders on fine grids rise past 5 (transient 6-8) once IS_k, about (f'' dx^2)^2, falls
below eps: from N of about 320 for sin and 640 for g.

**The report's Tables 3 and 4.** Their data are sin(pi x) and sin^4(pi x), N = 10 .. 320 and 20 .. 640,
eps = 10^-6. Every first-order critical point of both has f''' = 0 (sin^4 also has x = 0, +-1, where f' = f'' =
f''' = 0), so they sit in the symmetric sub-case: difference 3, face 4. On their grids the local difference error
near x = 1/2 (sin, eps = 10^-6, aligned) has orders 1.88, 2.72, 2.95, 3.21, 4.91 for N = 20 .. 320, close to the
printed WENO-RF-4 L_inf orders 2.13, 2.81, 3.05, 3.37, 3.86; `jiang-shu-tables.md` showed these errors dominate
the tables. So the tables agree with "3rd order" near the critical points, pre-asymptotically in eps (at fixed
eps = 10^-6 the order eventually exceeds 5). But the 3 they show is the difference order at a symmetric extremum.
It does not test a generic critical point. There the difference order is 2.

What a generic critical point does to the quantity the tables print (the solution error at t = 1; `liu_critical.py`
section 4, g, float64, RK4, dt = dx^(5/4)/2): with eps = 0, L_inf orders 2.35, 2.38, 2.41, 2.46, 2.48, 2.46 and L1
orders 3.03, 3.19, 3.24, 3.27, 3.28, 3.30 for N = 160 .. 5120; with eps = 10^-6, L_inf 1.71, 2.31, 4.03, 2.78 and
L1 2.28, 2.75, 4.17, 3.99 for N = 40 .. 320, then 4.38 and 5.44 at N = 640 and above 6 after. We measured these and do not have a derivation: the
L_inf solution order near 2.5 lies between the truncation order 2 and the face order 3, and we do not claim an
asymptotic value.

## 4. Verdicts on the readings of p. 7

- **(A) face value, eps -> 0, at a critical point: third order, not better.** Consistent with
  `reconstruction_order_p` (point, n_cp = 1, eps = 0: VERIFIED at p = 3, REFUTED at p = 4, leading order exactly 3
  with coefficient (14/293) f'''). This is the reading the derivation (2.12)-(2.14) supports.
- **(B) the truncation error of the flux difference at a critical point, eps -> 0: third order.** REFUTED by
  `reconstruction_order_p` (flux_difference, n_cp = 1, eps = 0, p = 3): leading order 2, coefficient
  (200248/2854113) f''' dx^2, non-zero whenever f''' != 0. Confirmed numerically (g, both grids, order 2.00 at
  N = 5120). Third order holds only when also f''' = 0.
- **(B') the same at fixed eps = 10^-6, dx -> 0.** Not the source's claim (it says the weights return to optimal on
  fine grids); the checker gives order 5 for both forms.
- **(C) the L1 solution error.** Not decided by the checker. For the report's data the tables are consistent with
  third order on their grids, pre-asymptotically. For a generic critical point we measured L1 orders near 3.3 and
  L_inf near 2.5 at eps = 0.

The report's tables are consistent with readings A and C on its own data, and do not bear on reading B, because
sin and sin^4 have f''' = 0 at their critical points.

For `jiang_shu_1995_weno:01`: the expected values do not depend on which reading is used (alone FALSE needs only
some order below 4 at a critical point, 2 and 3 both qualify; with hypotheses TRUE concerns f' != 0). The
hypothesis text "only 3rd order accurate" is right for the face value and too high for the flux difference that
the item's third hypothesis names. A wording proposal is in `ERRATA_PROPOSED.md`.
