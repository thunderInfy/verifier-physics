# Cell-average bench (reconstruction v3)

Committed with its expected verdicts before the checker supports it.

A spec describes one step of a cell-average scheme fed by polynomials of degree at most k, one per cell, in the
local coordinate y in [-1/2, 1/2] of each cell. `values` names linear functionals of those polynomials:
[c, y] is the value of p_c at y, and [c, "avg"] is the cell average of p_c. `update` is the new average of cell
0, linear in the named values, with coefficients polynomial in lam = dt/dx. `hypotheses` lists linear
combinations of the named values that are assumed to lie in [m, M].

- `cell_average_max_principle` (lam = [lo, hi]): for every lam in [lo, hi], all polynomials of degree <= k and
  all m <= M, if every hypothesis lies in [m, M] then so does the update.

The specs narrow the sources' general flux to f(u) = u with the Lax–Friedrichs flux, a linear update. Degrees
k <= 3 use the 3-point Gauss–Lobatto rule (Simpson; 2 points for k = 1), whose points are rational.
