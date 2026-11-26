# verifier-physics

A checker for physical theories that only rejects a theory when it can prove the theory wrong.
It may let a false theory through, but a rejection always comes with a certificate that a small
trusted checker (usually the Lean kernel) has verified, plus the list of assumptions it rests on.

AI has improved fastest in code and math, where answers can be checked cheaply and reliably.
Physics has no such checker because the final judge is experiment. This project covers what a
machine can check: unit consistency, agreement with published measurements, and whether a force
law can produce the orbits we observe.

```
$ uv run python -m physverify theories/power-law-2.1.json data/trajectory-mercury-10d.json
## Power-law gravity f = GM/r^2 · (r/1 au)^(-1/10)  (i.e. r^-2.1): REFUTED
- [REFUTED] (enclosure, validated-numeric) no trajectory from trajectory-mercury-10d's initial box
  is inside the observed box {'x': 'x1', 'y': 'y1', 'z': 'z1'} at t = 864000
    assumes: hard bounds of trajectory-mercury-10d contain the true values (JPL Horizons DE440 ...)
    assumes: well-posedness: Safe on every step box ⇒ unique solutions (PhysVerify.wellPosed_exists / wellPosed_unique)
    assumes: mpmath interval arithmetic is correctly outward-rounded
    replayed 200 steps: x(t_obs) ∈ [-5.70789e+10, -5.70727e+10], observed [-5.89517e+10, -5.89507e+10]
```

Mercury ends up about 1.9 million km from where an inverse-2.1 force would put it after 10 days,
while the allowed error is 500 km. Newtonian gravity passes the same check.

## How it decides

A theory is a JSON file: symbols with their dimensions, laws, an optional central force, optional
equations of motion, and the regime where the theory claims to hold. Evidence is a JSON file of
measurements with their sources.

Untrusted tools search for a refutation and hand the judge a proof. The tools only name what
they claim to have shown (for example "law `kepler3` fails everywhere inside evidence
`kepler-earth`"). The judge writes the exact statement and its assumption list itself, so a tool
can't swap in an easier claim or drop an assumption. If a proof fails, times out, or Lean isn't
installed, the result is `UNKNOWN` and the theory is not rejected.

| Piece | Trusted | Where |
|---|---|---|
| Theory and evidence format | yes | `physverify/theory.py` |
| Obligations: statement, guarantee, assumptions | yes | `physverify/obligations.py` |
| Judge | yes | `physverify/judge.py` |
| Lean definitions and theorems | kernel-checked | `lean/PhysVerify/` |
| Interval replay checker for trajectories | validated numerics | `physverify/tools/enclosure.py` |
| Tools and planner that search for proofs | no | `physverify/tools/`, `physverify/planner.py` |

## Checks

| Check | Guarantee | Lean result it relies on |
|---|---|---|
| Dimensional consistency of each law | proven | `Law.dimMismatch_refutes`: a law whose sides have different units can't hold in every unit system |
| Law against measured bounds | proven | `Bnd.*` interval lemmas |
| Well-posedness of the equations of motion | proven theorem, checked on each box | `wellPosed_exists`, `wellPosed_unique` (Picard-Lindelöf) |
| Trajectory against an observed position | validated numerics | Taylor enclosures replayed by the judge; uses well-posedness |
| Orbit existence | proven | `EccentricExcluded.refutes`: if r³f(r) is smaller at aphelion than at perihelion, no orbit has both |

The orbit check is a weak form of the anthropic principle: planets and comets have a closest and
a farthest point, and some force laws can't produce that.

Possible outcomes are `REFUTED` (proven, under the listed assumptions), `EXCLUDED` (statistical,
see below), `NOT_REFUTED`, `UNKNOWN`, `OUT_OF_REGIME` (the theory makes no claim about this data)
and `MALFORMED` (the input breaks the format, which says nothing about the physics).

## Statistical evidence

Most measurements come as a value and an error bar, not a hard bound. `physverify/registry.py`
turns every value ± σ in a family of measurements into the box value ± zσ, with
z = Φ⁻¹(1 − α/2K) and K the number of measurements in the whole family on disk (Bonferroni,
rounded up). If each reported σ is a correct Gaussian error, all the true values sit inside their
boxes with probability at least 1 − α. On that event no true theory is excluded, however many
theories you test. The usual checks then run on the boxes, and a hit is reported as `EXCLUDED`
at level α, kept separate from `REFUTED`. Set α with `--alpha=` (default 0.01).

## Data

Everything in `data/` is rebuilt from primary sources by `uv run python tools/fetch_data.py`.
Each file records the published values, the source URL, the retrieval date, and how each bound
was derived.

| Files | Source | Used for |
|---|---|---|
| `kepler-<planet>.json` | NASA NSSDCA fact sheets, JPL DE440 GM☉ | Kepler's third law |
| `orbit-<planet>.json`, `orbit-halley.json` | NASA fact sheets, JPL small-body database | orbit existence |
| `trajectory-mercury-10d.json` | JPL Horizons state vectors | trajectory checks |
| `ppn-will2014.json` | Will, Living Rev. Relativ. 17, 4 (2014) | post-Newtonian gravity parameters |
| `sme-photon-kappa-em.json` | Kostelecký and Russell, Data Tables for Lorentz and CPT Violation (2026) | Lorentz violation in electrodynamics |
| `synthetic/` | generated and labelled synthetic | tests only |

Margins come from independent physical estimates, not from fitting the theory being tested.
Kepler periods get ±1% because the other planets shift a planet's two-body period by up to 0.6%.
Mercury's position after 10 days gets ±500 km, about ten times the pull of Venus over that time.
Will's table of post-Newtonian limits gives no confidence level, so those limits are read as 1σ;
the file says so. Ephemeris data are fitted with general-relativistic N-body models, so they are
not fully independent of gravitational theory.

## Example theories

`theories/` has true theories that must never be rejected (Newtonian gravity, the nonlinear
pendulum, general relativity, Brans-Dicke with ω ≥ 40000, Lorentz-invariant electrodynamics) and
false ones that should be: Kepler's law with a² or 2π², a 1/r⁴ force, a 1/r²·¹ force, the linear
pendulum at 90°, Brans-Dicke with ω ≤ 1000, Nordström's scalar gravity, and an anisotropic
vacuum. The linear pendulum restricted to small angles is reported as `OUT_OF_REGIME` for the
90° data rather than rejected.

## Discrete schemes

A numerical scheme is a theory of a discrete universe, so claims about it can be checked the
same way. `physverify/schemes/` takes a 1D scalar conservation law u_t + f(u)_x = 0 and a
three-point scheme, given either as a numerical flux F(uL, uR) or as an update
u_i^{n+1} = H(u_{i-1}, u_i, u_{i+1}, dt/dx), written in the same expression language as
theories. Examples are in `schemes/`, the broken ones prefixed `broken-`. Stencils up to five
points wide (`um2`, `up2`, and fluxes F(uLL, uL, uR, uRR)) and limiters (`abs`, `min`, `max`,
`minmod`) are covered too; see "Limited schemes on five-point stencils" below and `schemes/limiters/`.

```
$ uv run python -m physverify.schemes schemes/broken-advection-lax-friedrichs-wide-cfl.json
## BROKEN: Lax-Friedrichs claimed positive and monotone up to nu = 1.1: FAILS positive_under_cfl, monotone_under_cfl
claims (judged by the table in claims.py):
...
- [REFUTED] (positive_under_cfl, exact) the linear update is a non-negative combination of u_{i-1}, u_i, u_{i+1} on the claimed CFL range
    evidence: positivity EQUIVALENT REFUTED -> REFUTED
- [REFUTED] (monotone_under_cfl, exact) H is non-decreasing in each argument for states with lam*|f'(u)| <= c
    evidence: monotonicity EQUIVALENT REFUTED -> REFUTED
checks (raw evidence):
...
- [REFUTED] (positivity, exact ...) positivity: every coefficient c_k(nu) >= 0 for nu = a*dt/dx in [0, 11/10]
    coefficient of up1 = -1/2*nu + 1/2 is -1/20 < 0 at nu = 11/10
- [REFUTED] (monotonicity, exact ...) monotone: H(um1, u0, up1) is non-decreasing in each argument for lam > 0 and states with lam*|f'(u)| <= 11/10
    H decreases from -1 to -1201/1200 when up1 increases by 1/60 at lam = 11/10, state ['-1', '-1', '-1']
```

The claim verdicts come first; the raw checks underneath are the evidence (see "Checks vs claims"
below for how one becomes the other).

| Check | Guarantee | Witness |
|---|---|---|
| Consistency F(u, u) = f(u) | exact: normal form of the residual is 0, or an exact rational point where it isn't | normal form, or counterexample u |
| Conservation on a periodic grid | exact: the update telescopes as -(dt/dx)(F_{i+1/2} - F_{i-1/2}), or an exact periodic state whose total changes | recovered flux, or counterexample state |
| Positivity of linear schemes on a claimed CFL range | exact: Bernstein coefficients of every c_k(nu) are >= 0 on the interval (endpoint values when c_k is affine in nu), or an exact nu where some c_k < 0 | coefficient list, or offending coefficient and nu |
| Convergence order (combined, space, time; or one norm, L1 or Linf, for the combined study) | empirical only | L1 and Linf error tables |
| Truncation order of linear schemes | exact: the Taylor coefficients e_j(nu) of the local truncation error vanish identically for j <= p, or an exact nu where some e_j != 0 | every e_j, the leading modified-equation term and its kind (diffusive, anti-diffusive, dispersive) |
| Von Neumann stability of linear schemes on a claimed CFL range | exact: 1 - \|g\|^2 >= 0 on nu x cos(theta) by tensor Bernstein coefficients after stripping (1 - z), (1 + z), or an exact (nu, cos(theta)) with \|g\|^2 > 1 | \|g\|^2, the factorisation, the boxes and their Bernstein coefficients; or the point |
| Shock speed on Riemann problems | empirical only | late-window speed at three crossing levels against the exact Rankine-Hugoniot speed, per grid |
| Entropy stability (Tadmor), semi-discrete | exact for the semi-discrete inequality only, not the time stepping: Q = -[v](F - F*) >= 0 certified on sign cells, or an exact rational point with Q < 0 | F*, Q, per-cell D = Q/(uR - uL)^2 with a change of variables that makes it non-negative by form, or counterexample (uL, uR) |
| Convergence to the rarefaction fan | empirical only | L1 error tables against u = (x - x0)/t, at two incommensurate dt/dx |
| Steady non-entropy step (fully discrete) | exact refutation only: the four stencils of a step uL < uR with f'(uL) < f'(uR) (f'' >= 0 by form) are fixed, as normal forms in lam; a failed search is `UNKNOWN`, never `VERIFIED` | (uL, uR), how it was found (candidate or search), f'(uL), f'(uR), f(uL), f(uR) |
| TVD of limited schemes (linear advection) on a claimed CFL range | exact both ways: Harten's incremental form certified on every sign cell by Farkas identities with multipliers polynomial in nu (sufficient), or an exact periodic state whose total variation grows (necessary) | per cell and half-cell: the identities, their nu-pieces and Bernstein minima, cell counts; or the state, nu and both total variations |
| Truncation order of limited schemes, per branch and on smooth data | exact: the truncation order of the linear scheme on each sign cell (sufficient when all are >= p), or an exact polynomial solution and grid placement whose local truncation error is a lower power of dx (necessary) | the branch table (slopes, order, leading e_j); or U(x), the placement, the cell and tau(dx) |
| Monotonicity of the fully discrete update on a claimed CFL bound | exact: every partial of H(u_{i-1}, u_i, u_{i+1}) is >= 0 on every sign cell within lam*\|f'(u)\| <= c, or two exact states, one argument raised, with H lower | per cell: H, the three partials, and a certificate (by form, a Farkas identity in w = lam*u, or Bernstein in lam); or the decreasing pair |

The exact checks use `Fraction` arithmetic and never decide on a float. Their verdicts are not
Lean-checked yet; each returns the witness a Lean certificate would need. The flux recovery is
complete for three-point stencils: if the update is in flux form at all, the flux it finds is
the only one up to a constant. Square roots (so |u| = sqrt(u^2)) and division by monomials such
as dt/dx are supported. Anything else (sin, division by a sum) gives `UNKNOWN`, and so does a
non-zero normal form with no exact counterexample found.

The convergence check runs refinement studies against exact solutions: an advected sine, and
Burgers before shock formation, solved along characteristics by Newton's method to round-off.
It reports which study it ran: *combined* (fixed dt/dx), *space* (method of lines with RK4 at
small dt) or *time* (forward Euler on a fixed grid, compared with the same-grid RK4 solution so
the spatial error cancels). Space and time are only separated when the update is linear in
dt/dx. A claim of order p is `NOT_REFUTED` when the observed orders of the last two refinements
are within 0.2 of p, `REFUTED_EMPIRICALLY` when one is below, and `SUSPICIOUS` when one is above
(superconvergence on a test is not a pass). This is evidence from float64 runs on one problem,
not a proof of order.

The shock-speed check runs a Riemann problem (a step from uL down to uR) on [0, 1] with
transmissive boundaries, stopping before the waves reach them. It locates the shock where u
crosses uR + l(uL - uR) and compares its speed with the Rankine-Hugoniot speed
s = (f(uL) - f(uR))/(uL - uR), which it computes exactly from the PDE flux. Two things move the
crossing. The step first relaxes into a discrete profile a few cells wide, which shifts the
crossing by O(dx) once; after that the profile translates. So the speed (x_s(T) - x_s(0))/T
carries an O(dx) start-up offset, and its sign depends on the level. On (2, 1/2) at N = 400 the
[0, T] error is +4.3e-3, 0 and -4.3e-3 at levels 0.2, 0.5 and 0.8 for Engquist-Osher, which is
±0.69 cells of offset (±0.9 for Rusanov, ±2 for Lax-Friedrichs). Engquist-Osher's 0 at level 0.5
comes from the profile's symmetry, not from accuracy.

The verdict therefore uses the late-window speed: the least-squares slope of the crossing over
every step in [T/2, T], at levels 0.2, 0.5 and 0.8. The table still shows the [0, T] number,
labelled "includes start-up offset", and the plain endpoint difference over [T/2, T]. We use the
slope rather than the endpoints because a translating discrete profile, read off its samples,
wobbles by a fraction of a cell as its phase against the grid changes. In a scan over dt/dx the
endpoint difference was off by up to 0.2 cells over the window for Engquist-Osher and Rusanov and
0.7 cells for Lax-Friedrichs. The slope was off by at most 0.015 and 0.33 cells (0.07 at
N = 800). The endpoint difference is at round-off whenever the window moves the profile a whole
number of cells. In the spec cases s·T/2 is 0, 1/16 or 1/4, so it comes out at round-off on most
grids.

The claim is `NOT_REFUTED` when the late-window speed is within half a cell of displacement over
the window, d = dx/(2(T - T/2)) ≈ dx/T, at all three levels on the last two grids, and the levels
agree with each other to within d. Agreement across levels means the profile is translating
rigidly; if the speeds are within d but the levels disagree, the result is `UNKNOWN` (not
settled). It is `REFUTED_EMPIRICALLY` when the error exceeds d at every level on the last two
grids and has changed by under 10% between them. Half a cell covers the worst wobble we measured
(0.33 cells, Lax-Friedrichs at N = 200), and is still 320 times smaller than the smallest
refuted error (0.25) at N = 3200. The output also shows the estimator
x0 + (∫u(T) - ∫u(0))/(uL - uR), but the verdict doesn't use it: for a conservative scheme it
returns s from the boundary fluxes alone, wherever the shock is.

A correct late-window speed is a consequence of conservation, not independent evidence. Between
the far fields the total of u grows at f(uL) - f(uR) per unit time. For a profile that translates
at speed c, it grows at c(uL - uR). So a conservative scheme's translating profile must move at
exactly s. The test is only a *necessary* condition. A non-conservative scheme can get the speed
right for one state pair by accident, which is why each spec has several state pairs. Our
non-conservative scheme does exactly that on (1, -1). The step is a fixed point of its update, so
it measures 0, the right speed. On (1, -1/2) the step is again a fixed point, and 0 is wrong
(s = 1/4).

One structural fact, conservation, seen three ways. `broken-burgers-nonconservative`
discretises u_t + u u_x = 0 directly with upwinding.
- The exact conservation check decides it in one shot: the update does not telescope, and an
  exact periodic state's total changes.
- The shock-speed test sees the consequence (Lax-Wendroff and Hou-LeFloch theorems), but only on
  discontinuous data and only with the right estimator. Over [0, T] the start-up offset makes
  every scheme look O(dx) wrong, a speed error that is not there.
- The smooth convergence study can't see it at all: the scheme converges at order 1 to smooth
  solutions.

Numbers from `uv run python -m physverify.schemes schemes/*burgers*.json`. Each shock entry is
the late-window speed error at N = 3200, taken as the largest over the three levels:

| Scheme | Conservation (exact) | Smooth order, last refinement to N = 400 (L1, Linf) | (1, 0), s = 1/2 | (2, 1/2), s = 5/4 | (1, -1), s = 0 | (1, -1/2), s = 1/4 | Shock speed verdict |
|---|---|---|---|---|---|---|---|
| non-conservative upwind | REFUTED | 0.99, 0.97: NOT_REFUTED | -0.5 (speed 0) | -0.267 (speed 0.983) | 2e-16 (by accident) | -0.25 (speed 0) | REFUTED_EMPIRICALLY |
| Lax-Friedrichs | VERIFIED | 0.98, 0.95: NOT_REFUTED | 4.7e-7 | 1.6e-6 | 8e-16 | 3.1e-6 | NOT_REFUTED |
| Engquist-Osher | VERIFIED | 0.99, 0.98: NOT_REFUTED | 5.6e-8 | 3e-15 | 3e-16 | 6.7e-7 | NOT_REFUTED |
| Rusanov | VERIFIED | 1.01, 1.00: NOT_REFUTED | 1.8e-8 | 1e-15 | 4e-16 | 9.5e-7 | NOT_REFUTED |

The tolerance d at N = 3200 is 3.1e-4 for (1, 0), 7.8e-4 for (2, 1/2) and 6.3e-4 for the two
transonic cases. Where the conservative errors are not round-off, they fall by about 4 per
halving of dx. We read that as leftover phase wobble in the slope plus Lax-Friedrichs' slow
settling, not a speed error; we have not separated the two. The [0, T] errors at level 0.5 for
comparison, (1, 0) and (2, 1/2) at N = 3200:
Lax-Friedrichs -7.6e-6 and -2.8e-5, Engquist-Osher +1.3e-6 and 0, Rusanov +1.8e-5 and +3.8e-5.
These halve with dx, as an offset divided by T should. On the transonic cases every conservative
scheme settles to a profile moving at the right speed (stationary for (1, -1)). Lax-Friedrichs on
(1, -1) at N = 200 still has three crossings (an odd-even oscillation) and a -5e-3 [0, T] error;
it has settled to round-off by N = 800. Only the conservation check is a proof; the other two
are float64 evidence on chosen data.

### The ladder: consistency, conservation, entropy

Each rung is necessary for the next and none is sufficient alone.
1. Consistency (F(u, u) = f(u)): the scheme approximates the right PDE.
2. Conservation (flux form): by the Lax-Wendroff theorem, limits are weak solutions.
3. Entropy: weak solutions are not unique, and the limit must be the physical one.

The benchmark for the third rung is `broken-burgers-roe-no-entropy-fix`, the Roe (Murman) flux
F = (f(uL) + f(uR))/2 - |a|(uR - uL)/2 with a = (uL + uR)/2. It is consistent and conservative
(both VERIFIED), converges at order 1 on smooth data and gets every shock speed right. On the
rarefaction data (-1, 1) it computes a = 0 and F = 1/2 at every interface, so the step is a fixed
point: a stationary expansion shock, a weak solution, but not the entropy one.

**Exact rung: semi-discrete entropy stability, after Tadmor.** With an entropy pair (eta, q),
entropy variable v = eta'(u) and potential psi = v f - q, the entropy-conservative flux is
F* = [psi]/[v] ([.] = right minus left). For Burgers with eta = u^2/2 this is
F* = (uL^2 + uL uR + uR^2)/6. An interface produces entropy [v]F - [psi] = [v](F - F*), so the
semi-discrete scheme du_i/dt = -(F_{i+1/2} - F_{i-1/2})/dx is entropy stable iff
Q = -[v](F - F*) >= 0 for all states. The check computes F* by exact polynomial division, which
needs [v]/(uR - uL) to be a constant, so a quadratic entropy; anything else is `UNKNOWN`. A spec
may declare (eta, q); for Burgers the default is (u^2/2, u^3/3). The check verifies q' = eta' f'
exactly. It then certifies Q >= 0, either globally, as Q = (uR - uL)^2 D with D non-negative by its
form, or cell by cell. For cells it splits every |x| = sqrt(x^2) into the cases x >= 0 and x <= 0,
divides each cell's Q by (uR - uL)^2 where that is exact, and looks for a linear change of variables
to two of the cell's constraints that makes the result a positive combination of monomials. Every
cell's identity and change of variables is in the witness, ready for a Lean certificate. If some
cell fails, it searches small rationals for a point with Q < 0 (`REFUTED`). If none turns up, the
verdict is `UNKNOWN`.

This certifies the *semi-discrete* inequality only. The time discretisation is not covered:
forward Euler can produce entropy, so this check does not certify the fully discrete scheme (the
monotonicity rung below does). The output says so in the guarantee line.

| Scheme | Entropy stability (exact, semi-discrete) | Witness |
|---|---|---|
| Engquist-Osher | VERIFIED | 4 sign cells; e.g. on uL, uR >= 0, D = uL/3 + uR/6; on uL >= 0 >= uR, Q itself is positive in (uL, -uR) |
| Rusanov | VERIFIED | 8 sign cells (the nested abs(abs(uL) - abs(uR)) splits each quadrant) |
| Lax-Friedrichs | VERIFIED under lam·\|u\| <= 1 | D = 1/(2 lam) - (uR - uL)/12 = (4 + s + t)/(12 lam) with s = 1 + lam uL, t = 1 - lam uR |
| Roe, no fix | REFUTED | (uL, uR) = (-1, 1): F = 1/2, F* = 1/6, Q = -2/3, entropy production 2/3 > 0 |

Lax-Friedrichs needs its bound because its viscosity is fixed at dx/(2 dt). D >= 0 iff
lam(uR - uL) <= 6, so the check is VERIFIED with lam·|u| <= 3, and REFUTED with lam·|u| <= 4 or with
no bound (at lam = 2, (-2, 2)). Harten's entropy fix, phi(a) = |a| if |a| >= delta and
(a^2 + delta^2)/(2 delta) otherwise, fits the expression language as
|a| + max(0, delta - |a|)^2/(2 delta) with max(0, z) = (z + |z|)/2. With delta = 1/2 it still fails
Tadmor's inequality at (-1, 1) (Q = -1/6): its sonic viscosity delta/2 is below (uR - uL)/6. Yet it
converges to the rarefaction (below). Entropy stability for eta = u^2/2 is sufficient, not
necessary, so `burgers-roe-harten-fix` does not claim it: it claims only that it selects the entropy
solution, and Tadmor's failure there is not a refutation (see "Checks vs claims").

**Empirical rung: convergence to the rarefaction fan.** For uL < uR the entropy solution is
u = clip((x - x0)/t, uL, uR). The study runs the scheme on [0, 1] with the jump at x0 = 1/2 and
transmissive boundaries, and measures the L1 error at T = 1/4 under refinement. An
entropy-satisfying scheme's error falls; a scheme that keeps a jump has an error that settles at a
non-zero value. Verdict on the last two grids: `NOT_REFUTED` at observed order >= 0.3,
`REFUTED_EMPIRICALLY` if the error changed by under 10%, `UNKNOWN` otherwise. Each case runs at
dt/dx = 2/5 and at the deliberately incommensurate 37/100, so an error that looks exact (a fixed
point) must survive a step that does not line up with the grid. L1 errors at N = 1600 (dt/dx = 2/5,
then 37/100), with the observed order of the last halving:

| Scheme | (-1, 1) | (-1/2, 1) | Verdict |
|---|---|---|---|
| Roe, no fix | 0.25, 0.25 (order 0.00; exactly T, the area between step and fan) | 0.0639, 0.0640 (0.02) | REFUTED_EMPIRICALLY |
| Roe + Harten fix | 2.44e-3, 2.52e-3 (0.79) | 1.66e-3, 1.71e-3 (0.78) | NOT_REFUTED |
| Engquist-Osher | 3.19e-3, 3.27e-3 (0.79) | 2.39e-3, 2.44e-3 (0.78) | NOT_REFUTED |
| Rusanov | 2.94e-3, 3.01e-3 (0.79) | 2.17e-3, 2.21e-3 (0.78) | NOT_REFUTED |
| Lax-Friedrichs | 8.47e-3, 9.06e-3 (0.81) | 7.61e-3, 8.13e-3 (0.79) | NOT_REFUTED |

Roe's 0.25 is the same at both dt/dx and on every grid: the step is an exact fixed point of the
update, not a round-off coincidence. On (-1/2, 1), Roe keeps a stationary jump from -1/2 to 1/2
(a = 0 across it) with a fan above it. That limit's L1 error is T/4 = 1/16 = 0.0625, which the
measured error approaches from above (largest jump between neighbouring cells 1.0). The
entropy-satisfying schemes converge at observed order about 0.8, still rising at N = 1600; we have
not pinned down the asymptotic rate (the fan's corners limit first-order schemes). Tadmor's rung
is a proof of the semi-discrete inequality only. The rarefaction study is float64 evidence on two
state pairs. The proof for the fully discrete scheme is monotonicity (see "Checks vs claims").

**Exact refutation for the fully discrete scheme: a steady non-entropy step.** Roe's 0.25 has an
exact cause. Put uL for i < j and uR for i >= j, with the jump at a cell interface, so the same step
sits on every grid. Only four stencils occur. If H(uL, uL, uL) = uL, H(uR, uR, uR) = uR,
H(uL, uL, uR) = uL and H(uL, uR, uR) = uR, then u^n = u^0 for every n and every dx at fixed dt/dx,
so the discrete solutions converge, trivially, to the stationary step. For convex f with
f'(uL) < f'(uR), the entropy solution of that Riemann problem is the rarefaction fan, not the step,
so the scheme does not select the entropy solution. The check (`steady_nonentropy_step`) needs
f'' >= 0 by form and f'(uL) < f'(uR) in exact arithmetic. It checks the four identities as normal
forms in lam, so they hold at every dt/dx. The candidate pairs are the spec's rarefaction cases,
then (-1, 1), (-1/2, 1), (0, 1), then a search labelled as such over pairs of small rationals. No
grid study is involved. It does not require conservation. The limit is the step whatever the
conservation status, though only a conservative scheme with f(uL) = f(uR) makes the step a weak
solution (an expansion shock), and the witness says which case holds. Roe without a fix has a
steady step at (-1, 1) at every dt/dx, and so does Lax-Wendroff for Burgers
(`benchmark/scheme-claims/specs/burgers-lax-wendroff.json`), whose flux is 1/2 = f(±1) whenever
uL + uR = 0. Both become `REFUTED` (exact) on `selects_entropy_solution`. Harten's fix leaves the
straddling stencils off by ∓lam·delta/2, so it has no steady step at (-1, 1). Engquist-Osher,
Lax-Friedrichs and Rusanov have none in the search, which is what Crandall-Majda requires. A failed
search proves nothing, so on those schemes the check is `UNKNOWN`, and it never verifies.

The same check has a semi-discrete instantiation (`steady_nonentropy_step_semidiscrete`) for the
method of lines du_i/dt = -(F_{i+1/2} - F_{i-1/2})/dx with the declared numerical flux. On the
same step only three interface fluxes occur, F(uL, uL), F(uL, uR) and F(uR, uR). If they are
equal, every cell's right-hand side is 0 and the step is a steady state for every dx. The check
uses that condition as it stands, so it does not need consistency. Roe without a fix has
F = 1/2 at all three at (-1, 1), so `selects_entropy_solution_semidiscrete` is now `REFUTED`
(exact) for it, where it was `UNKNOWN` (Tadmor fails, and a failed sufficient condition says
nothing). The two rows cannot contradict each other on a consistent flux. A steady step has
F = f(uL) = f(uR), so Tadmor's Q reduces to -[q], and an expansion shock has [q] > 0 for a strictly
convex entropy. A test checks this on every spec.

**Exact rung for the fully discrete scheme: monotonicity.** The update u_i^{n+1} = H(u_{i-1}, u_i,
u_{i+1}) is monotone if H is non-decreasing in each argument. The check splits every |x| in H into
sign cells. On each closed cell H is a polynomial, and the check certifies its three partial
derivatives >= 0 on the cell within the claimed CFL region lam*|f'(u)| <= c. In w = lam*u the
partials and cell boundaries are affine for these fluxes, so the certificate is an exact Farkas
identity p = r + sum mu_j a_j with mu_j, r >= 0 over the cell's atoms. H is continuous and
Lipschitz, so if it is non-decreasing on each closed piece of a cover of a segment, it is
non-decreasing along the whole segment; the kinks are finitely many points and don't matter. A
refutation is two exact states in the region, differing in one argument, where raising that
argument lowers H. The CFL bounds in the specs are sharp: each scheme is `REFUTED` just above its
bound.

| Scheme | Monotone for | Just above |
|---|---|---|
| Upwind, Lax-Friedrichs (advection, a = 1) | dt/dx <= 1 (the same range as positivity) | REFUTED at 11/10 |
| Lax-Friedrichs, Engquist-Osher (Burgers) | lam*\|u\| <= 1 | REFUTED at 101/100 |
| Rusanov (Burgers) | lam*\|u\| <= 1/3 | REFUTED at 334/1000, 1/2 and 1 (`broken-burgers-rusanov-wide-cfl`) |
| Lax-Wendroff | never on (0, 1): the up1 coefficient is -lam(1 - lam)/2 | REFUTED |
| Roe, no fix | under no bound: a transonic expansion breaks it | REFUTED at 1 and at 1/10 |
| Roe + Harten fix (delta = 1/2) | not at any bound we tried down to 1/10 | REFUTED at 1, 1/2, 1/4, 1/10; UNKNOWN at 1/100 |
| Non-conservative upwind (Burgers) | lam*\|u\| <= 1/3 | REFUTED at 334/1000 |

Rusanov's 1/3 is not a typo. The dissipation alpha = max(|uL|, |uR|) depends on the states, and
differentiating it adds to dH/du_i: on the cell where |u_i| >= |u_{i+1}|, u_i >= 0, the partial is
1 - 2 w_i + (w_{i-1} + w_{i+1})/2, which reaches 1 - 3c. Roe fails at a transonic expansion
(u_{i-1} < 0 < u_i, where dH/du_{i-1} = lam*u_{i-1} < 0) under any CFL bound. Harten's fix is not
monotone at the bounds we tried, so its entropy claim still rests on the study alone. Its cells are
cubic, so there is no Farkas certificate, and at 1/100 the search's dt/dx values keep the states
well below delta, which is why it returns `UNKNOWN` there. delta is a fixed state scale, so a
smaller dt/dx reaches the failing states (|u| near 0.3) under any c. We expect it is never
monotone, but the check has not shown this.

**Exact order of accuracy for linear schemes.** For u_t + a u_x = 0 and a linear update
u_i^{n+1} = sum_k c_k(nu) u_{i+k}^n (nu = a dt/dx), the order is polynomial algebra. Expanding the
exact solution, the local truncation error at fixed dt/dx is tau = sum_j e_j(nu) dx^(j-1) u^(j) with
e_j = a/(nu j!)((-nu)^j - sum_k c_k k^j), and the scheme is consistent of order p iff e_0..e_p vanish
identically in nu. The first non-zero e_j is the leading term of the modified equation. Stability is
von Neumann's condition: with z = cos(theta), |g|^2 is a polynomial in nu and z, and the check
certifies 1 - |g|^2 >= 0 on the claimed range of nu and z in [-1, 1]. For a consistent scheme
1 - |g|^2 always vanishes at z = 1, so the check strips the factors (1 - z) and (1 + z) and
certifies the rest by tensor Bernstein coefficients, bisecting the box when needed. A refutation is
an exact rational (nu, z) with |g|^2 > 1. The tests replay every witness from the spec's update
directly (e_q from the truncation error on u = x^q; |g|^2 from Re g and Im g).

| Scheme (a = 1) | Order (exact) | Leading term of the modified equation | Von Neumann (exact) |
|---|---|---|---|
| Upwind | 1 | (1 - nu)/2 · a dx u_xx, diffusive | VERIFIED on [0, 1]: 1 - \|g\|^2 = 2 nu(1 - nu)(1 - z) |
| Lax-Friedrichs | 1 | (1 - nu^2)/(2 nu) · a dx u_xx, diffusive | VERIFIED on [-1, 1]: (1 - z^2)(1 - nu^2); REFUTED on [0, 11/10] at nu = 11/10, z = 0 |
| Lax-Wendroff | 2 | -(1 - nu^2)/6 · a dx^2 u_xxx, dispersive | VERIFIED on [-1, 1]: nu^2 (1 - nu^2)(1 - z)^2 |
| Lax-Wendroff with the diffusion halved | 1, REFUTED as 2 (e_2 = nu/4) | -nu/4 · dx u_xx, anti-diffusive | REFUTED for every nu != 0 |
| FTCS | 1 | -nu/2 · dx u_xx, anti-diffusive | REFUTED for every nu != 0: 1 - \|g\|^2 = -nu^2 (1 - z^2) |

The halved Lax-Wendroff spec was written as an order test, but the exact check shows it is also
unstable: at z = 0, |g|^2 = 1 + nu^4/4.

"Stable for sufficiently small time steps" is a different claim, `stable_for_small_cfl`: some
nu0 > 0 has |g| <= 1 for all theta and all nu in (0, nu0]. Its check (`von_neumann_small_cfl`)
writes 1 - |g|^2 = sum_k q_k(z) nu^k and looks at the lowest non-zero q_k. If q_k(z0) < 0 at a
rational z0, then 1 - |g|^2 < 0 at z0 for every nu in (0, nu1], with nu1 = c/(c + 2M) explicit
(c = -q_k(z0), M the largest |q_j(z0)| above k) and exact spot values: `REFUTED`. Otherwise it tries
the Bernstein certificate on [0, nu1] for nu1 = 1, 1/2, ..., 2^-10: `VERIFIED` with the first that
works, `UNKNOWN` if none does. A lowest term that is >= 0 but has zeros in z settles nothing, and
the check does not treat it as settling anything. FTCS is `REFUTED` (q_2 = -(1 - z^2), z0 = 0,
nu1 = 1). Upwind, Lax-Friedrichs and Lax-Wendroff are `VERIFIED` with nu0 = 1. The refutation also
holds in the max norm. On a periodic grid the Fourier modes are eigenvectors of the update, so
|g| > 1 on an open set of theta means growth in every norm once the grid has a mode there.

The Lax-Richtmyer equivalence theorem turns the two into a convergence order. For a linear
constant-coefficient scheme on a periodic grid, consistency of order p plus stability gives
convergence of order p for smooth initial data. That is a `sufficient` row for `converges_order_p`,
with two preconditions that must be exactly `VERIFIED`: `von_neumann`, and `lax_richtmyer_scope`.
The second is a structural check: the update is linear with coefficients depending on dt/dx only,
the claimed study is the combined one (refining dx at fixed dt/dx, which is what the theorem is
about) at the claimed consistency order, the study's dt/dx is inside the certified range, and the
test data are smooth. It returns `NOT_APPLICABLE` otherwise, so the row cannot fire for a
nonlinear update (a test claims all of it for Burgers Lax-Friedrichs: the three checks are
`NOT_APPLICABLE`, the row gives `UNKNOWN`, and `converges_order_p` stays `NOT_REFUTED` from the study).

So claims of order are now exactly verifiable for Lax-Friedrichs and Lax-Wendroff (`VERIFIED`, where
they were `NOT_REFUTED`). Upwind's stays `NOT_REFUTED`: it also claims space (method of lines) and
time (forward Euler on a fixed grid) orders, which this theorem does not cover. For FTCS the row is
silent (stability fails) and the study decides. At dt/dx = 4/5 round-off in the unstable modes
grows to 1e11 by N = 400 (`REFUTED_EMPIRICALLY`). At dt/dx = 1/2 to T = 1/4 it does not grow
enough: the study shows order 1.00 and says `NOT_REFUTED`, and only the exact check sees the
instability. The judge never says `INCONSISTENT` on any of these. For nonlinear schemes (Burgers)
nothing here applies, and the empirical study remains the only evidence of order. For limited
schemes of linear advection the truncation order is exact branch by branch (see "Limited schemes on
five-point stencils" below), but the global order is still only empirical.

Lax-Richtmyer is asymptotic. It says the error is O(dx^p) as dx -> 0, nothing about the constant or
about when the asymptotic regime starts, and "order p" here means at least p: a scheme that happens
to be more accurate on the test data is not contradicted. The truncation expansion assumes enough
smooth derivatives; for data with a kink or a shock the order is lower, and the theorem says
nothing.

### Limited schemes on five-point stencils

A spec may use `um2` and `up2` (u_{i-2}, u_{i+2}), and a numerical flux may take four arguments,
F(uLL, uL, uR, uRR) = F_{i+1/2}(u_{i-1}, u_i, u_{i+1}, u_{i+2}). The expression language has
`abs(x)`, `min(a, b)`, `max(a, b)` and `minmod(a, b)`. They are written with |x| = sqrt(x^2)
(max(a, b) = (a + b + |a - b|)/2, minmod(a, b) = max(0, min(a, b)) + min(0, max(a, b))), so the AST
and its Lean mirror get no new node. Three-point specs are parsed and reported exactly as before. The
flux recovery (`telescoping_wide`) and the consistency, truncation, von Neumann and positivity checks
work on the wider stencil. Monotonicity and the steady-step check are still three-point only and give
`UNKNOWN` on wider stencils. The examples are in `schemes/limiters/`, in Sweby's flux-limiter form
for u_t + u_x = 0: u_i^{n+1} = u_i - nu (F_{i+1/2} - F_{i-1/2}) with
F_{i+1/2} = u_i + (1 - nu)/2 * L(Delta_{i+1/2}, Delta_{i-1/2}) and Delta_{i+1/2} = u_{i+1} - u_i. The
slope L is a polynomial with min and max, so no ratio r appears. Minmod is L = minmod(Delta_{i+1/2},
Delta_{i-1/2}). Superbee is maxmod(minmod(2 Delta_{i+1/2}, Delta_{i-1/2}), minmod(Delta_{i+1/2},
2 Delta_{i-1/2})), with maxmod written as max(0, max(m1, m2)) + min(0, min(m1, m2)). That equals it
because the two minmods never have opposite signs.

**Sign cells and why they cover everything** (`limiters.cells`). Every |x| is split into the closed
cells x >= 0 and x <= 0, and on each cell the update is a polynomial (here linear in the u's). The
split is lazy: |x| is split only when the normal form needs its sign, and atoms are scaled to a
canonical form so that |2x| and |x| share one split. A cell is dropped only with a certificate that
it lies in a hyperplane: an atom a with -a = sum_j mu_j a_j and mu_j >= 0 (an identity replayed in the
normal form), so a = 0 on the cell. An exact phase-1 simplex in `Fraction` arithmetic finds the
multipliers (Gordan's alternative). The retained cells still cover the state space. Every split
covers its parent, so the retained and dropped cells together cover everything. The union of the
retained closed cells is closed, and its complement is an open set inside the finitely many
hyperplanes of the dropped cells, so it is empty. A verdict over all states therefore never rests on
"the branches we happened to enumerate". Past `MAX_CELLS` (4000 explored cells) the checks give
`UNKNOWN`.

Where two retained cells overlap, their polynomials must agree, and the code asserts it. It checks
first on the subspace where the atoms of opposite sign vanish. If the polynomials differ there, it
checks on the overlap's linear span, which repeated Gordan LPs find exactly (a polynomial that
vanishes on a cone vanishes on its span). A disagreement would be a bug in the split and gives
`UNKNOWN`. Minmod's update has 18 full-dimensional cells (8 lower-dimensional ones dropped, 43
split-tree nodes, all 153 pairs checked). Superbee's has 50 (36 dropped, 135 nodes, 1225 pairs). The
tests also sample random rational states and confirm that each lies in a retained cell whose
polynomial gives H's exact value there.

**TVD, exact both ways** (`tvd_under_cfl`). Harten's lemma: if
u_i^{n+1} = u_i - C_{i-1/2} Delta_{i-1/2} + D_{i+1/2} Delta_{i+1/2} with C, D >= 0 and
C_{i+1/2} + D_{i+1/2} <= 1, the scheme is TVD. For a > 0 the check takes D = 0 and
C = -(H - u_i)/Delta_{i-1/2}. With N = H - u_i, each cell is split once more by the sign s of
Delta_{i-1/2}. On s*Delta_{i-1/2} >= 0 the check certifies -s*N >= 0 (that is, C*Delta^2 >= 0) and
s*(N + Delta_{i-1/2}) >= 0 (that is, (1 - C)*Delta^2 >= 0), so it never divides by Delta. Both are
linear in the u's with coefficients polynomial in nu. Each is certified as an identity
p = sum_j mu_j(nu) a_j over the cell's atoms, where every mu_j(nu) has non-negative Bernstein
coefficients on a piece of the nu-range (`farkas_in_nu`). The pieces come from bisection, and the
atoms from an exact LP at sample values of nu, with a full subset search as the fallback. Where
Delta_{i-1/2} = 0 the two certificates force N = 0, so the form holds there too. Harten's form is not
unique, so this row is `sufficient`. Refutation is a separate `necessary` check, `tv_increase`: an
explicit periodic rational state and a rational nu in the claimed range whose total variation grows
in one step, in `Fraction` arithmetic. The same certificate gives a local maximum principle for free,
since u_i^{n+1} = (1 - C) u_i + C u_{i-1} with C in [0, 1]. That is the claim
`local_max_principle_under_cfl`, refuted by `max_principle_violation` (an exact state with
u_i^{n+1} outside its stencil's range).

| Spec | consistent, conservative | `tvd_under_cfl` | Witness |
|---|---|---|---|
| `advection-minmod`, nu in [0, 1] | VERIFIED | VERIFIED (Harten) | 18 cells, 18 half-cells certified (18 lower-dimensional halves dropped); the local maximum principle is VERIFIED too |
| `advection-superbee`, nu in [0, 1] | VERIFIED | VERIFIED (Harten) | 50 cells, 50 half-cells certified |
| `broken-advection-lw-flux-form-tvd` (L = Delta_{i+1/2}: unlimited Lax-Wendroff), [0, 1] | VERIFIED | REFUTED | periodic u = (0, 0, 0, 0, 0, 1) at nu = 1/4: TV goes from 2 to 33/16. At nu = 1/2, u_4^{n+1} = -1/8 < 0 breaks the maximum principle |
| `broken-advection-superbee-wide-cfl`, [0, 3/2] | not claimed | REFUTED | the same state at nu = 3/2: TV goes from 2 to 4 (u^{n+1} = (3/2, 0, 0, 0, 0, -1/2)). Harten fails on 58 conditions, which alone would give only `UNKNOWN` |

The exact checks agree with the literature range (Sweby 1984; LeVeque 2002, ch. 6). Both limiters
are TVD for 0 <= nu <= 1, and superbee is not TVD on [0, 3/2] (a test also finds a TV increase at
nu = 9/8). The range is not hard-coded anywhere: the certificate was searched for on the claimed
interval, and the refutation came from the search.

**Truncation order per branch.** On each cell the update is a linear scheme, so the exact truncation
expansion of `linear.py` applies to each branch. Minmod has nine distinct branches over its 18 cells.
The slope columns say what minmod picks at each interface, and e_j is the leading coefficient in
tau = sum_j e_j dx^(j-1) d^j u/dx^j (the modified equation's term is -e_j):

| slope at i+1/2 | slope at i-1/2 | Branch | Truncation order | Leading e_j |
|---|---|---|---|---|
| Delta_{i+1/2} | Delta_{i-1/2} | Lax-Wendroff | 2 | e_3 = (1 - nu^2)/6 |
| Delta_{i-1/2} | Delta_{i-3/2} | Beam-Warming | 2 | e_3 = -(1 - nu)(2 - nu)/6 |
| 0 | 0 | upwind (both slopes clipped) | 1 | e_2 = -(1 - nu)/2 |
| Delta_{i-1/2} | Delta_{i-1/2} | upwind (the two limited terms cancel) | 1 | e_2 = -(1 - nu)/2 |
| Delta_{i+1/2} | Delta_{i-3/2} | mixed | 1 | e_2 = (1 - nu)/2 |
| Delta_{i+1/2} | 0 | mixed | 0 | e_1 = (1 - nu)/2 |
| Delta_{i-1/2} | 0 | mixed | 0 | e_1 = (1 - nu)/2 |
| 0 | Delta_{i-1/2} | mixed | 0 | e_1 = -(1 - nu)/2 |
| 0 | Delta_{i-3/2} | mixed | 0 | e_1 = -(1 - nu)/2 |

The mixed branches with one slope clipped are not even consistent as linear schemes:
tau = e_1 u_x + O(dx). Smooth data reach them only next to an extremum, where the two slopes have
opposite signs and u_x = O(dx), so there they contribute O(dx). That is why the claim "truncation order
2 at every stencil of smooth data" (`truncation_order_smooth_data`) is refuted exactly. Its
`sufficient` row, "every branch has order >= p", gives `UNKNOWN` here (7 of 9 branches are below 2);
it verifies only schemes whose every branch is order p, such as a linear scheme. The `necessary`
check computes tau exactly at explicit data. Take u = U(x - t) with U(x) = 1 - x^2/2 (cos x to second
order; a polynomial, so the exact solution is smooth and known) and x_i = 0. Every stencil atom is a
single power of dx, so the stencil lies in one cell for every dx > 0: the cell with slope 0 at i+1/2
and Delta_{i-1/2} at i-1/2. There tau(dx) = (1 - nu)/4 * dx exactly, which is O(dx) and not O(dx^2)
for every nu != 1. For cos(x) itself the stencil signs are the same, and a float check gives
tau/dx -> (1 - nu)/4. Superbee happens to be exact at this order at x_i = 0 (its clipped slope is
2 Delta_{i-1/2}), but it is refuted at x_i = dx/2. All of this is about the local truncation error only.

**Global order, with the norm named.** A nonlinear scheme has no Lax-Richtmyer theorem and can damp
local errors, so the exact truncation order above says nothing about the global order. The global
claims are separate and empirical: `converges_order_p_linf` (max norm) and `converges_order_p_l1`
(discrete L1). Each reads only its own column of the combined refinement study (`claims.order_linf`,
`claims.order_l1`). Minmod, a = 1, observed orders between successive grids:

| Data | dt/dx, T | L1 order (N = 100..1600) | L∞ order (N = 100..1600) | Verdict |
|---|---|---|---|---|
| sine (periodic, with extrema) | 1/2, 1/4 | 1.91, 1.89, 1.92, 1.93, 1.95 | 1.28, 1.29, 1.30, 1.30, 1.31 | L∞ order 2: REFUTED_EMPIRICALLY; L1 order 2: NOT_REFUTED |
| sine | 0.37, 0.2371 (incommensurate) | 1.89, 1.90, 1.91, 1.94, 1.94 | 1.23, 1.31, 1.27, 1.31, 1.31 | the same |
| sine | 0.9, 1/4 | 1.88, 1.94, 1.92, 2.00, 1.98 | 1.24, 1.25, 1.27, 1.32, 1.31 | the same |
| C-infinity monotone step, constant ends, transmissive boundaries (no extrema) | 1/2, 1/4 | 1.82, 1.99, 2.00, 2.00, 2.00 | 1.53, 1.70, 1.94, 2.01, 2.00 | L1 order 2: NOT_REFUTED (the spec runs N = 50..800) |
| the same | 0.37, 0.2371 | 1.84, 1.97, 2.01, 2.00, 2.00 | 1.39, 1.67, 1.90, 2.01, 2.00 | the same |

With extrema the max-norm order is about 1.3, not 1. Clipping costs O(dx) locally, but only in a few
cells near each extremum, and we have not derived the rate. It stays at 1.3 at an incommensurate dt/dx
and final time, so it is not a commensurability artefact. The L1 order on sine data is about 1.9 and
still rising at N = 1600. We do not know whether it tends to 2, so the benchmark records that reading
as unsettled. Without extrema both norms reach 2.0 once N >= 400. On coarser grids the max norm is
still pre-asymptotic, which is why the extrema-free spec runs N = 50..800.

Limits: one space dimension, scalar laws, three-point stencils for the entropy, monotonicity and
steady-step checks (five points for the rest), limiter checks for linear advection only, periodic grids (the shock-speed and
rarefaction studies use transmissive boundaries), Riemann data with a single shock or a single fan.
The exact entropy check needs a quadratic entropy, and the rarefaction study's exact fan is for
Burgers only. Positivity of
nonlinear schemes (Burgers) is out of scope in v0; monotonicity, its nonlinear counterpart, is
covered for fluxes whose cells give affine partials in w = lam*u (Harten's cubic cells are not). Consistency with an inconsistent flux shows
up in the order study only weakly when the defect is small (the 1.01-scaled flux still shows
order about 0.8 at N = 400); the exact check is what catches it. A non-conservative scheme can
converge at the right order on smooth data, as `broken-burgers-nonconservative` does; only the
conservation check catches it exactly, and the shock-speed study shows the effect. The Burgers tests use data without sonic points, where
Rusanov's L∞ order is still pre-asymptotic at these grid sizes.

### Checks vs claims

A check is evidence about a claim, and checks differ in how strongly they bear on one. A spec
lists the named claims it makes (`named_claims`), and a small trusted table in
`physverify/schemes/claims.py` says, for each claim, which checks bear on it and how. The checks
never decide what their result means for a claim. The table also fixes each check's guarantee,
exact or empirical. An empirical study that returned `VERIFIED` would still count as empirical,
and an empirical pass never verifies a claim, whatever relation the table gives it: it only fails
to refute.

| Claim | Check | Relation | Guarantee |
|---|---|---|---|
| `consistent` | consistency | equivalent | exact |
| `conservative` | conservation (telescoping) | equivalent | exact |
| | shock_speed (late window) | necessary | empirical |
| `positive_under_cfl` | positivity (Bernstein) | equivalent | exact |
| `entropy_stable_tadmor` | entropy_stability (Tadmor) | equivalent | exact (semi-discrete) |
| `selects_entropy_solution_semidiscrete` | entropy_stability (Tadmor) | sufficient | exact (semi-discrete) |
| | steady_nonentropy_step_semidiscrete (F(uL, uL) = F(uL, uR) = F(uR, uR), uL < uR, f'(uL) < f'(uR), f convex) | necessary | exact |
| `monotone_under_cfl` | monotonicity | equivalent | exact |
| `selects_entropy_solution` | entropy_rarefaction | necessary | empirical |
| | steady_nonentropy_step (a steady step uL < uR with f'(uL) < f'(uR), f convex) | necessary | exact |
| | monotonicity (Crandall-Majda), only if conservation and consistency are VERIFIED | sufficient | exact |
| `consistent_order_p` | truncation_order | equivalent | exact |
| `von_neumann_stable_under_cfl` | von_neumann | equivalent | exact |
| `stable_for_small_cfl` | von_neumann_small_cfl (lowest term in nu; Bernstein on [0, 2^-k]) | equivalent | exact |
| `converges_order_p` | order/combined, order/space, order/time | necessary | empirical |
| | truncation_order (Lax-Richtmyer), only if von_neumann and lax_richtmyer_scope are VERIFIED | sufficient | exact |
| `correct_shock_speed` | shock_speed | necessary | empirical |
| `tvd_under_cfl` | tvd_harten (Harten's incremental form on sign cells) | sufficient | exact |
| | tv_increase (an explicit periodic state whose TV grows) | necessary | exact |
| `local_max_principle_under_cfl` | tvd_harten (a convex combination of two stencil values) | sufficient | exact |
| | max_principle_violation (an explicit state outside its stencil's range) | necessary | exact |
| `truncation_order_smooth_data` | truncation_branches (every branch's linear scheme has order >= p) | sufficient | exact |
| | truncation_smooth_data (an explicit polynomial solution with a lower-order tau) | necessary | exact |
| `converges_order_p_l1` | order_l1/combined | necessary | empirical |
| `converges_order_p_linf` | order_linf/combined | necessary | empirical |
| `hyperbolic` (systems) | hyperbolicity (discriminant of the 2x2 Jacobian) | equivalent | exact |
| `positive_depth_under_cfl` (systems) | depth_positivity (Riemann runs) | necessary | empirical |
| | depth_positivity_exact (induction step on the stencil) | equivalent | exact |
| `converges_to_riemann_solution` (systems) | riemann_l1 (against the exact Riemann solution) | necessary | empirical |

Tadmor's inequality is about the method of lines and says nothing about time stepping, so it
bears only on the semi-discrete claim. For the fully discrete scheme, monotonicity verifies the
claim honestly. By Crandall and Majda (1980), a conservative, consistent, monotone scheme
converges to the entropy solution (initial data in L1 ∩ BV). The same theorem gives a discrete
entropy inequality for every Kruzkov entropy, the maximum principle and TVD. The theorem needs
all three properties, so the row carries a precondition in the table: it counts only when the
conservation and consistency checks are exactly `VERIFIED` on the same spec, and otherwise it
gives `UNKNOWN`. `broken-burgers-nonconservative` shows why the precondition is there. That update
is monotone for lam*|u| <= 1/3 (`VERIFIED`), yet it moves shocks at the wrong speed, and its
`selects_entropy_solution` stays `UNKNOWN` ("requires conservation: REFUTED"). The CFL bound is part
of the result. The maximum principle keeps the states inside it if the initial data start there.

The cost is order. By Godunov's theorem a monotone scheme is at most first order, so this route
never verifies the entropy claim for Lax-Wendroff or any other second-order scheme (Lax-Wendroff
claiming monotone is `REFUTED`). That is the No Free Lunch trade in one line: a proof that the limit
is the entropy solution costs the order of accuracy. For non-monotone schemes, such as Roe with
Harten's fix, the claim still rests on the rarefaction study and can reach only `NOT_REFUTED`.

A passing exact sufficient or equivalent check verifies the claim, and a failing necessary or
equivalent check refutes it. A passing necessary check only fails to refute it, and a failing
sufficient check says nothing (`UNKNOWN`). With the guarantee this gives `VERIFIED`/`REFUTED` from
exact checks and `NOT_REFUTED`/`REFUTED_EMPIRICALLY` from empirical ones. When several checks bear
on one claim, any refutation refutes and any verification verifies. If both happen the verdict is
`INCONSISTENT`. That means a checker, a spec or the table is wrong, not that the physics is: the
CLI marks it `!!!` and exits with code 3, and the tests fail on it. The verdict lists the premises
of the relation it used as assumptions. For Tadmor as a sufficient condition these are: the
inequality is semi-discrete only, the scheme must converge, and for a convex scalar flux one
strictly convex entropy singles out the entropy solution.

Roe with Harten's fix is the case the table exists for. Tadmor's check fails on it exactly (at
(-1, 1), Q = -1/6), yet its limit on the rarefaction data is the fan. A failed sufficient
condition proves nothing, so Harten's fix is `UNKNOWN` on the semi-discrete claim. Roe without a
fix is refuted exactly on `entropy_stable_tadmor`, and on the semi-discrete claim by its steady step.

| Spec | Tadmor (raw) | Monotonicity (raw) | Rarefaction (raw) | `entropy_stable_tadmor` | `selects_entropy_solution_semidiscrete` | `selects_entropy_solution` |
|---|---|---|---|---|---|---|
| Roe + Harten fix | REFUTED | not run | NOT_REFUTED | not claimed | UNKNOWN | NOT_REFUTED (empirical, rarefaction) |
| Roe, no fix | REFUTED | REFUTED (c = 1) | REFUTED_EMPIRICALLY | REFUTED (exact) | REFUTED (exact, steady step at (-1, 1)) | REFUTED (exact, steady step at (-1, 1)) |
| Engquist-Osher, Lax-Friedrichs (c = 1), Rusanov (c = 1/3) | VERIFIED | VERIFIED | NOT_REFUTED | VERIFIED | VERIFIED (exact, under the premises above) | VERIFIED (exact, monotonicity + Crandall-Majda) |
| Non-conservative upwind | not run | VERIFIED (c = 1/3) | not run | not claimed | not claimed | UNKNOWN (precondition: conservation REFUTED) |

Roe without a fix is the cross-check. If the monotonicity check had certified it while the
rarefaction study refutes it, the judge would report `INCONSISTENT`. It doesn't: monotonicity fails
exactly at the transonic expansion, the same place the scheme keeps its expansion shock.

Reported as the verdict on "the claim", the raw `REFUTED` would have said Harten's fix picks the
wrong solution. Likewise for `broken-burgers-nonconservative` the exact conservation check
decides `conservative`. The shock-speed study is only a necessary condition: it agrees there, but
on the conservative schemes its pass adds nothing to the proof. This is the same issue as tracking
the polarity of each tool's answer (delta-sat in dReal is only sound in one direction).

### Claims as papers write them

`benchmark/scheme-claims/` has 22 sentences phrased the way papers phrase them ("Lax–Wendroff is
TVD", "our upwind scheme is unconditionally stable", "the minmod MUSCL scheme is second order").
Each reading of each sentence is formalized into the named claims above, with an expected truth
and a citation. `uv run python -m physverify.schemes.bench benchmark/scheme-claims/` prints
expected against actual. It fails on a decisive verdict that contradicts the expectation and lists
non-decisive results as gaps. Now: 30 of 40 readings decided correctly, 9 gaps, 1 unscored
(expected truth unsettled), none wrong. Before the limiter checks it was 24 of 34 with 10 gaps
(the monotonicity check settles the Rusanov and Engquist–Osher monotonicity claims, and the exact
order and von Neumann checks settle the truncation and global orders of Lax–Wendroff and upwind and
refute "upwind is unconditionally L2-stable"; the steady-step check makes the Roe and Lax–Wendroff
entropy refutations exact, and its semi-discrete form refutes "Roe's method of lines converges to
the entropy solution"; the small-CFL check refutes "FTCS is stable for sufficiently small time
steps"). The limiter checks added six matches: minmod and superbee TVD on [0, 1] (VERIFIED),
superbee TVD on [0, 3/2] and Lax–Wendroff in flux-limiter form TVD (REFUTED, exact), minmod's pointwise
truncation order 2 at smooth extrema (REFUTED, exact), and its max-norm order 2 on sine data
(REFUTED_EMPIRICALLY, at two dt/dx). "Order 2 in L1 without extrema" stays a gap (NOT_REFUTED: no
theorem turns a refinement study into a proof). `GAPS.md` there ranks the gaps. The largest
remaining ones are order of accuracy and entropy claims for nonlinear schemes, and stability claims
that need a global parameter or a regime the spec cannot state.

### Systems

`physverify/schemes/systems.py` takes systems q_t + f(q)_x = 0. The first one is shallow water,
q = (h, m) with m = h u and f(q) = (m, m^2/h + g h^2/2). A system spec lists the state components,
a flux per component, positive parameters and a state domain:

```
"pde": {"state": ["h", "m"], "flux": ["m", "m^2/h + g*h^2/2"],
        "parameters": {"g": "positive"}, "domain": {"h": "positive"}}
```

The numerical flux is a list in hL, hR, mL, mR, and an update is a list in hm1, h0, hp1, mm1, m0,
mp1. A scalar spec is the 1-component case with state u. On all 17 scalar specs the system code
returns the same consistency and conservation verdicts as the scalar checks, and the scalar specs
still go through the scalar code, so no scalar verdict changes. Specs are in `schemes/systems/`.

| Spec | `hyperbolic` | `conservative` | `consistent` | `positive_depth_under_cfl` | `converges_to_riemann_solution` |
|---|---|---|---|---|---|
| Lax-Friedrichs | VERIFIED | VERIFIED | VERIFIED | VERIFIED | NOT_REFUTED |
| Rusanov, wave speed max(\|u\| + sqrt(g h)) | VERIFIED | VERIFIED | VERIFIED | VERIFIED | NOT_REFUTED |
| BROKEN: pressure sign flipped, f2 = m^2/h - g h^2/2 | REFUTED (discriminant -4 at g = h = 1) | VERIFIED | VERIFIED | not claimed | not claimed |
| BROKEN: m_t + u m_x + h (u u_x + g h_x) = 0, LxF averaging | VERIFIED | REFUTED (exact periodic state) | UNKNOWN (no flux form) | VERIFIED (LxF depth update) | UNKNOWN |

**Hyperbolicity.** We compute the Jacobian A(q) = df/dq symbolically. A real 2x2 matrix has real,
distinct eigenvalues exactly when tr(A)^2 - 4 det(A) > 0, so the check is equivalent to "strictly
hyperbolic on the stated domain". For shallow water the discriminant is 4 g h. It is a polynomial,
so no square root is needed, and it is certified positive by form with g, h > 0. The eigenvalues
u ± sqrt(g h) are reported for information only. A refutation is an exact domain point where the
discriminant is <= 0. **Limit:** the test is for n = 2 only. A cubic's discriminant would still
decide n = 3, but from n = 4 on a positive discriminant also allows two complex pairs. For n > 2
the check returns UNKNOWN.

**Conservation and consistency** work componentwise with the scalar telescoping argument. The base
state is h = 1, since h = 0 is outside the domain and 1/h is undefined there. `poly.py` handles 1/h
as a Laurent monomial. Division by a sum is still outside the fragment, and any check that reaches
it reports UNKNOWN. One trap showed up on the way: the centred quasi-linear terms
u_i (m_{i+1} - m_{i-1}) + m_i (u_{i+1} - u_{i-1}) telescope (a discrete product rule), so that
"non-conservative" update is in flux form and verifies. The broken spec uses
h_i ((u^2)_{i+1} - (u^2)_{i-1}) instead, which does not telescope.

**Rusanov and sqrt(g h).** We extended `poly.py` rather than return UNKNOWN. A caller may declare
variables positive on its domain. Then sqrt(p) is accepted when p is non-negative by form with
those variables at any power, so sqrt(g hL) and |uL| = sqrt(mL^2/hL^2) qualify. This is sound on
the domain, where p >= 0 and sqrt(p)^2 = p, and only there, so every system verdict lists
"g > 0, h > 0 in every cell" as an assumption. The maximum wave speed is written as
max(a, b) = (a + b + sqrt((a - b)^2))/2. With h not declared positive, Rusanov's consistency and
conservation return UNKNOWN (tested).

**Depth positivity and the Riemann solution (empirical, necessary).** Two Riemann problems on
[0, 1] with transmissive boundaries and g = 1. One is the dam break h = 2 | 1, u = 0. The other is
a near-dry double rarefaction, h = 1, u = -3/2 | 3/2, whose exact middle depth is 1/16. Each runs at
two dt/dx values, one deliberately incommensurate (2/5 and 37/100; 1/3 and 3/10 for the faster near-dry
case), on N = 100 to 800. The exact solution comes from the exact Riemann solver: a
rarefaction or a shock on each side of the star state. For the dam break that is the Stoker
solution, h* = 1.45384, u* = 0.41692, with the shock at speed 1.3356. depth_positivity requires
min h > 0 at every step with the observed CFL number lam·max(|u| + sqrt(g h)) at most the claimed 0.9.
A run that goes past the bound is outside the claim and counts as UNKNOWN. riemann_l1 requires the
L1 error of (h, m) on the last two grids to fall at observed order >= 0.3, as in the scalar
rarefaction study.

| Scheme, case, dt/dx | L1(h) + L1(m), N = 400 | N = 800 | order | min h | max CFL |
|---|---|---|---|---|---|
| LxF, dam break, 2/5 | 3.07e-2 | 1.78e-2 | 0.79 | 1 | 0.649 |
| LxF, dam break, 37/100 | 3.35e-2 | 1.97e-2 | 0.77 | 1 | 0.599 |
| LxF, near-dry, 1/3 | 3.97e-2 | 2.47e-2 | 0.69 | 0.046 | 0.833 |
| LxF, near-dry, 3/10 | 4.74e-2 | 2.95e-2 | 0.68 | 0.047 | 0.750 |
| Rusanov, dam break, 2/5 | 1.66e-2 | 9.56e-3 | 0.79 | 1 | 0.649 |
| Rusanov, dam break, 37/100 | 1.72e-2 | 9.92e-3 | 0.80 | 1 | 0.600 |
| Rusanov, near-dry, 1/3 | 2.34e-2 | 1.37e-2 | 0.77 | 0.037 | 0.833 |
| Rusanov, near-dry, 3/10 | 2.65e-2 | 1.57e-2 | 0.75 | 0.034 | 0.750 |

This is evidence and not a proof. The dam break never comes near h = 0, so only the near-dry case
tests positivity. The exact check below proves it. The
non-conservative scheme goes past the CFL bound and blows up on the near-dry case, so both of its
studies are UNKNOWN. On the dam break alone its observed order falls from 0.52 to 0.23 between
N = 800 and 3200 (LxF stays near 0.78), which looks like convergence to the wrong shock, but the
error has not settled by the 10% rule.

**Depth positivity (exact, `depth_positivity_exact`).** The check proves one induction step: if
g > 0, h_j^n > 0 and lam(|u_j| + sqrt(g h_j)) <= c at the three stencil cells, then h_i^{n+1} > 0.
Induction over n gives h > 0 at every step from positive initial data, as long as the CFL condition
holds at each step. The hypothesis covers the stencil only, which is weaker than a bound on the whole
grid, so the theorem is stronger. h^n > 0 and g > 0 are the only uses of the domain. `positive=`
only ever sees g, the step-n depths and lam (a test spies on every call), and h^{n+1} is never
declared positive: an update sqrt(X)^2 with X = h^{n+1} stays UNKNOWN.

The method. With h_j > 0, write m_j = h_j u_j. Split every |x| into sign cells (32 for Rusanov,
where the cells also resolve max(|u| + sqrt(g h)) at each interface; 1 for LxF). Keep sqrt(g h_j) as
a variable and forget z_j^2 = lam^2 g h_j, keeping only z_j = lam sqrt(g h_j) > 0. That is a weaker
hypothesis, so a certificate over the relaxed variables still proves the claim. On each cell,
h_i^{n+1} = sum_j c_j h_j, with each c_j affine in w_j = lam u_j and z_j. Each c_j >= 0 on the cell
within the CFL region c -+ w_j - z_j >= 0 is certified by an affine Farkas identity. An exact LP
finds the identity and the normal form replays it, so the solver is not trusted. One c_j >= eps z_j
(or >= eps) makes the sum strictly positive. For LxF the cell is
h_i^{n+1} = (1/2) h_{i-1}(1 + w_{i-1}) + (1/2) h_{i+1}(1 - w_{i+1}). REFUTED needs an exact positive
stencil state a | b | c within the bound whose step gives h <= 0. In the grid a, ..., a, b, c, ..., c
that is positive data within the bound whose first step has h <= 0, so the row is EQUIVALENT. A
domain that does not state h > 0 (wet/dry) is NOT_APPLICABLE.

| Scheme | c = 1/2 | c = 9/10 (claimed) | c = 1 | c = 101/100 | c = 1001/1000 | c = 10001/10000 |
|---|---|---|---|---|---|---|
| LxF | VERIFIED | VERIFIED | VERIFIED | REFUTED | REFUTED | UNKNOWN (search grid too coarse) |
| Rusanov | VERIFIED | VERIFIED | VERIFIED | REFUTED | REFUTED | REFUTED |

A certificate at c = 1 covers every c <= 1, because the region only shrinks. So with this CFL
number, lam·max(|u| + sqrt(g h)), the sharp bound for both schemes is 1, not 1/2. The Rusanov
counterexample at c = 101/100 (lam = g = 1) is a deep middle cell, h_i = 10201/10000 at rest,
between two shallow neighbours. The middle coefficient 1 - lam(a_{i-1/2} + a_{i+1/2})/2 = 1 - c is
then negative. For LxF a neighbour moving out at lam|u| > 1 with a small sqrt(g h) does the same.
The non-conservative spec has the LxF depth update, so its depth positivity also verifies. Its
momentum update is irrelevant to the induction step.

**What carries over from scalar 1D, and what doesn't.** Consistency and conservation carry over
componentwise, with the same exact witnesses. Tadmor's entropy test needs entropy variables
v = eta'(q), a vector, and an entropy-conservative flux defined by a line integral, so it is not
ported. Monotonicity has no direct analogue: a system update is not monotone in each argument
even for good schemes, and the scalar route through Crandall-Majda does not apply. Invariant
domains (positivity of h, Riemann-invariant bounds) take its place. Positivity of h is now proved
exactly (above); the Riemann-invariant bounds are not checked yet. The eigenvalues need square roots. We report them, but no check depends on
them.

## Setup

Python 3.11+ and [uv](https://docs.astral.sh/uv/):

```
uv sync
uv run pytest tests/test_fast.py tests/test_schemes.py tests/test_claims_bench.py tests/test_entropy_steady.py tests/test_systems.py tests/test_steady_smallnu.py
```

The Lean checks need [elan](https://github.com/leanprover/elan) and a built Mathlib (Lean
v4.30.0-rc1, Mathlib pinned in `lean/lakefile.toml`). The prebuilt cache avoids compiling
Mathlib but still needs several GB of disk:

```
cd lean && lake exe cache get && lake build && cd ..
uv run pytest tests/test_lean.py      # about 10 minutes
```

To check certificates on a remote GCP machine instead, set `PHYSVERIFY_LEAN=vm` and see
`tools/vm.sh` for the variables it reads.

## Limits

- Interval certificates assume non-negative quantities under `*`, `/` and powers. Theories that
  use `sin`, `exp` or non-integer powers are only checked by the trajectory tool.
- The statistical channel takes value ± σ error bars only. Full likelihoods with correlations,
  such as those on HEPData, are not supported yet.
- The hyperbolicity check for systems decides 2x2 systems only (the discriminant tr^2 - 4 det).
  For n > 2 it returns UNKNOWN.
- The orbit check is deliberately weak. A 1/r³ force, the borderline case, is not rejected.
- Two steps are assumptions rather than Lean proofs: the radial equation of motion for a central
  force, and the translation from a theory file to the Lean expression. Both are listed on every
  result that depends on them.

## License

MIT
