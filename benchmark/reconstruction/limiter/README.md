# Scaling-limiter bench

Committed with its expected verdicts before the checker supports it.

The bound-preserving (scaling) limiter of Zhang and Shu (J. Comput. Phys. 229 (2010), (2.8)-(2.11); Proc. R. Soc.
A 467 (2011), (2.9)-(2.10)). A spec gives a polynomial p of degree at most k in the local coordinate y in
[-1/2, 1/2] of a cell, the centre c of the scaling (`center`: `"avg"`, the cell average ubar, as in the sources,
or a point y0, a typo variant), the set S where M_x = max_S p and m_x = min_S p are taken (`extrema_over`:
`"cell"` or a list of points), and the terms of theta (`theta`, a subset of `1`, `upper`, `lower`):

    upper = |M - c| / |M_x - c|,  lower = |m - c| / |m_x - c|,  theta = min of the terms,
    p~(y) = c + theta (p(y) - c).

A ratio term whose denominator is zero is left out of the min (the sources do not say; then p is constant on S at
the value c), and theta = 1 if no term is left.

Claims, each for every p of degree <= k and all m <= M, with c in [m, M] unless `average_in_bounds` is false:

- `limiter_keeps_average`: avg(p~) = avg(p).
- `limiter_bounds` (on: `"cell"` or points): m <= p~(y) <= M at every y of `on`.
- `limiter_accuracy`: there is a constant C (depending on the spec only) with
  max_cell |p~ - p| <= C * max_cell dist(p(y), [m, M]). The right side is at most max |p - u| for every u with
  values in [m, M], so a (k+1)-th order accurate p gives a (k+1)-th order accurate p~: the sources' "(k+1)-th order
  accurate limiter" (the accuracy of p is part of that notion, as the items' justifications say).

The deliberately false specs: theta without the 1 (`typo-no-one-k2`), without the lower term (`typo-no-lower-k2`),
scaled about p(0) instead of the average (`typo-centre-value-k2`), extrema over the cell ends only
(`edges-only-k2`), and in `zs-cell-*` the bounds without the hypothesis ubar in [m, M]. `zs-gl-k2`, `zs-gl-k3`
claim the bounds on the whole cell for the Gauss-Lobatto limiter, which only bounds the points.
