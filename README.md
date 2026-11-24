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

## Setup

Python 3.11+ and [uv](https://docs.astral.sh/uv/):

```
uv sync
uv run pytest tests/test_fast.py
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
