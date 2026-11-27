# ENO bench (reconstruction v3)

Committed with its expected verdicts before the checker supports it.

A spec gives the order k of an ENO interpolation of point values w_j and its stencil selection: `"eno"` with a
tie rule, or `{"fixed": r}`, the linear reconstruction on the stencil {i - r, ..., i - r + k - 1} of every cell.
ENO grows the stencil of cell i from {i} one point at a time, to the side whose undivided difference of the next
order is smaller in absolute value; on equal values the tie rule decides. w^+_i is the interpolant of cell i at
x_{i+1/2}, and w^-_{i+1} that of cell i + 1 at the same point. The jump is J = w^-_{i+1} - w^+_i and the
difference is D = w_{i+1} - w_i.

- `eno_sign_property`: for all data, J D >= 0, and J = 0 where D = 0. This is the weak form. The strict reading,
  sign(J) = sign(D) with sign(0) = 0, fails for every reconstruction that is exact on linear data and has k >= 2,
  since there J = 0 and D != 0.
- `eno_jump_ratio_at_most` (c): for all data with D != 0, J / D <= c.

Both quantify over every real data vector (w_{i-k+1}, ..., w_{i+k}); nothing is sampled.
