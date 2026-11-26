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
theories. Examples are in `schemes/`, the broken ones prefixed `broken-`.

```
$ uv run python -m physverify.schemes schemes/broken-advection-lax-friedrichs-wide-cfl.json
- [REFUTED] (positivity, exact ...) positivity: every coefficient c_k(nu) >= 0 for nu = a*dt/dx in [0, 11/10]
    coefficient of up1 = -1/2*nu + 1/2 is -1/20 < 0 at nu = 11/10
```

| Check | Guarantee | Witness |
|---|---|---|
| Consistency F(u, u) = f(u) | exact: normal form of the residual is 0, or an exact rational point where it isn't | normal form, or counterexample u |
| Conservation on a periodic grid | exact: the update telescopes as -(dt/dx)(F_{i+1/2} - F_{i-1/2}), or an exact periodic state whose total changes | recovered flux, or counterexample state |
| Positivity of linear schemes on a claimed CFL range | exact: Bernstein coefficients of every c_k(nu) are >= 0 on the interval (endpoint values when c_k is affine in nu), or an exact nu where some c_k < 0 | coefficient list, or offending coefficient and nu |
| Convergence order (combined, space, time) | empirical only | L1 and Linf error tables |
| Shock speed on Riemann problems | empirical only | measured speed against the exact Rankine-Hugoniot speed, per grid |

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
crosses (uL + uR)/2 and compares the measured speed with the Rankine-Hugoniot speed
s = (f(uL) - f(uR))/(uL - uR), which it computes exactly from the PDE flux. The claim is
`NOT_REFUTED` when the error is within 4 dx/T on the last two grids, and `REFUTED_EMPIRICALLY`
when it stays above that and has stopped changing. The output also shows the estimator
x0 + (∫u(T) - ∫u(0))/(uL - uR), but the verdict doesn't use it: for a conservative scheme it
returns s from the boundary fluxes alone, wherever the shock is.

One claim, three checkers. `broken-burgers-nonconservative` discretises u_t + u u_x = 0 directly
with upwinding. An empirical convergence study passed this structurally wrong scheme. The exact
conservation check caught it, and a Riemann problem shows the consequence: the wrong shock speed
(Lax-Wendroff and Hou-LeFloch theorems). Numbers from
`uv run python -m physverify.schemes schemes/*burgers*.json`:

| Scheme | Conservation (exact) | Smooth order, last refinement to N = 400 (L1, Linf) | Shock-speed error (1, 0), s = 1/2, N = 200 → 3200 | Shock-speed error (2, 1/2), s = 5/4, N = 200 → 3200 | Shock speed verdict |
|---|---|---|---|---|---|
| non-conservative upwind | REFUTED | 0.99, 0.97: NOT_REFUTED | -0.5 → -0.5 (measured speed 0) | -0.274 → -0.268 (measured speed 0.976 → 0.982) | REFUTED_EMPIRICALLY |
| Lax-Friedrichs | VERIFIED | 0.98, 0.95: NOT_REFUTED | -1.2e-4 → -7.6e-6 | -4.4e-4 → -2.8e-5 | NOT_REFUTED |
| Engquist-Osher | VERIFIED | 0.99, 0.98: NOT_REFUTED | +2.0e-5 → +1.3e-6 | round-off (2e-16 → 0) | NOT_REFUTED |
| Rusanov | VERIFIED | 1.01, 1.00: NOT_REFUTED | +2.9e-4 → +1.8e-5 | +6.1e-4 → +3.8e-5 | NOT_REFUTED |

The tolerance 4 dx/T is 0.0013 and 0.0031 at N = 3200. For the conservative schemes the error
falls like dx (a factor 16 over four halvings). Engquist-Osher (plain upwinding for these
non-negative data) measures the (2, 1/2) speed exactly to round-off; we have not worked out why. For the non-conservative scheme
the error doesn't shrink. In the (1, 0) case u = 0 is a fixed point of the update, so the step
never moves; in the (2, 1/2) case the speed settles near 0.98. Only the conservation check is a
proof; the other two are float64 evidence on chosen data.

Limits: one space dimension, scalar laws, three-point stencils, periodic grids (the shock-speed study alone uses
transmissive boundaries), Riemann data with a single shock and no sonic point. Positivity of
nonlinear schemes (Burgers) is out of scope in v0. Consistency with an inconsistent flux shows
up in the order study only weakly when the defect is small (the 1.01-scaled flux still shows
order about 0.8 at N = 400); the exact check is what catches it. A non-conservative scheme can
converge at the right order on smooth data, as `broken-burgers-nonconservative` does; only the
conservation check catches it exactly, and the shock-speed study shows the effect. The Burgers tests use data without sonic points, where
Rusanov's L∞ order is still pre-asymptotic at these grid sizes.

## Setup

Python 3.11+ and [uv](https://docs.astral.sh/uv/):

```
uv sync
uv run pytest tests/test_fast.py tests/test_schemes.py
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
- The orbit check is deliberately weak. A 1/r³ force, the borderline case, is not rejected.
- Two steps are assumptions rather than Lean proofs: the radial equation of motion for a central
  force, and the translation from a theory file to the Lean expression. Both are listed on every
  result that depends on them.

## License

MIT
