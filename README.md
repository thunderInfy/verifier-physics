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
| Class theorems (Harten's lemma, monotone ⇒ TVD) | proven in Lean; not yet used by the verdict path | `lean/PhysVerify/Harten.lean` |
| Scheme statements for Lean (from the spec) | yes | `physverify/schemes/lean_cert.py` |
| Scheme proofs for Lean (from the witness) | no | `physverify/schemes/lean_planner.py` |
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

## Derivation checking: Euler–Lagrange equations

The checks above can only reject. For derivations we also want a positive answer: a claim
"these equations of motion are the Euler–Lagrange equations of this Lagrangian" is
`VERIFIED` only with a kernel-checked proof, `REFUTED` only with a kernel-checked
counterexample, and `UNKNOWN` otherwise (failed search, timeout, no Lean).

```
$ uv run python -m physverify.claims claims/
| double-pendulum            | true  | VERIFIED | VERIFIED | ok       |    10s |
| kepler-missing-factor-2    | false | REFUTED  | REFUTED  | ok       |    10s |
| pendulum-empty-domain      | ill   | UNKNOWN  | UNKNOWN  | ok       |     0s |
...
23 claims: 10 VERIFIED, 8 REFUTED, 5 UNKNOWN, 0 wrong
```

A claim file (`claims/*.json`, format in `physverify/derivation.py`) gives coordinates, symbols
with dimensions, a Lagrangian, a domain such as `l > 0`, and one equation per coordinate,
either `qddot = rhs` or any `lhs = rhs`. The domain is a list of atoms `a > b`, `a < b` or
`a != b`. The parser rejects atoms that mention an acceleration, and atoms whose sides are
not continuous everywhere (division other than by a constant, negative powers, `sqrt`,
`log`, real powers). So `D` is an open set of `(q, q̇, parameters)`, cut out by strict
inequalities of continuous functions, and puts no condition on `q̈`. The judge writes two
Lean statements:

* `Verified n L D cs`: `D` has a point, and on `D` the Euler–Lagrange system holds at a jet
  `(q, q̇, q̈)` iff the claimed equations do. The statement also asserts `dimsOK` (both sides
  of each equation have one dimension; `0` has every dimension), the side conditions of
  differentiation on `D`, and `PhysOK` on `D`. `PhysOK` says that in `L` and in both sides
  of every claimed equation, every denominator is non-zero, every power with a negative
  exponent (integer or rational) has a non-zero base, every `sqrt` and `log` argument is
  positive, and so is the base of every non-integer power. Lean's functions are total
  (`x / 0 = 0`, `0 ^ (-1) = 0`, `Real.sqrt x = 0` and `Real.log x = log |x|` for `x < 0`,
  and a real power of a negative base is not the real power), so without `PhysOK` an
  identity could hold in Lean only through these junk values. The differentiation side
  conditions already exclude them in `L` and its derivatives; `PhysOK` is what excludes
  them in the claimed equations. Finally the statement contains `DomainForm`: `D` is the
  conjunction of the listed atoms, each in the continuous fragment `Expr.contOK` and free of
  accelerations. The judge proves it with `Iff.rfl` and `decide`.
* `Refuted n L D cs`: a jet in `D`, with `PhysOK`, where the two disagree.

The point of `D` in `Verified` comes from the judge, not the planner: it searches for a
rational point that satisfies every atom exactly, and Lean checks it with `norm_num`. If it
finds none, the verdict is `UNKNOWN` without calling Lean. Before this, `r > 0, r < 0` would
have made any equations `VERIFIED`, because the statement was a `∀` over an empty set.

The untrusted planner (`physverify/tools/eulerlagrange.py`) proposes tactics. For a
plausible claim it uses the certificate `EL = C · (lhs − rhs)` with `det C ≠ 0`, which
covers non-diagonal mass matrices (the double pendulum). For a false claim it uses a
rational counterexample, closed exactly or with Mathlib's bounds on `sin` and `cos`.

What is proven in Lean (`lean/PhysVerify/Deriv.lean`, `EulerLagrange.lean`):

* `Expr.hasDerivAt_deriv`: the symbolic partial derivative is the real one wherever
  `Expr.diffOK` holds (non-zero denominators and `log`/`sqrt` arguments, non-zero bases of
  negative powers). The side condition is always a hypothesis, never dropped.
* `Expr.hasDerivAt_dir`: the chain rule along curves, used for the total time derivative.
* `EL_bridge`, for any number of degrees of freedom: along any trajectory twice
  differentiable at `t`, the symbolic `EL n k L` on the jet equals the real
  `d/dt (∂L/∂q̇_k) − ∂L/∂q_k`, computed with Mathlib derivatives.
* `verified_meaning`: from a `Verified` certificate, every such trajectory whose jet stays
  in `D` near `t` satisfies the real Euler–Lagrange equations at `t` iff it satisfies the
  claimed equations at `t`.
* `verified_meaning_at`: the same with the jet in `D` at `t` only, given `DomainForm`
  (which every `VERIFIED` statement contains). This is now a Lean theorem, not an argument
  from the parser: `Expr.continuous_eval_of_contOK` shows that expressions in the fragment
  (no division except by a non-zero constant, no negative powers, no `sqrt`, `log` or real
  powers) are continuous on `ℕ → ℝ` with the product topology, so `DomainForm.isOpen` shows
  `D` is open. Along a trajectory twice differentiable at `t`, positions and velocities are
  continuous at `t`, so a jet in `D` at `t` stays in `D` near `t` (`Domain.eventually`).
  Accelerations need not be continuous, which is why `Atom.ok` (and the parser) forbids them
  in the domain: a condition on `q̈` could fail at every `s ≠ t`.
  The parser's continuity check (`_discontinuous` in `physverify/derivation.py`) is now only
  a convenience: if it let through an atom outside the fragment, `decide` would fail on
  `DomainForm` and the verdict would be `UNKNOWN`.
* `verified_nonempty`: a `Verified` certificate gives a point of `D` where `PhysOK` holds.
  `Refuted` also requires `PhysOK` at its counterexample jet, so a counterexample cannot
  come from a junk value either.
* `refuted_meaning`: from a `Refuted` certificate, on the quadratic trajectory through the
  counterexample jet, at `t = 0`, the real Euler–Lagrange equations and the claimed
  equations disagree.

What is assumed, not proven:

* The claim file is translated to Lean by literal serialization (`physverify/expr.py`), as
  for theories.
* That the Euler–Lagrange equations are the physics (Hamilton's principle) is the input of
  the check, not something it shows.
* `REFUTED` is a statement about jets: the claimed equation fails along one smooth
  trajectory at one time. To conclude that the claimed ODE has different solutions, you
  also need an Euler–Lagrange solution through that jet. Picard–Lindelöf gives one when
  the mass matrix is invertible, but that step is not instantiated here.

Benchmark (`claims/`, regenerated by `tools/gen_claims.py`): the true claims are the simple
pendulum (also rearranged and rescaled), Kepler in polar coordinates (also rescaled, with
the angular equation as `d/dt(r²θ̇) = 0`), a charged particle in uniform E and B fields,
two coupled oscillators (also reordered, which needs an anti-diagonal certificate), and the
double pendulum. The false ones are a centrifugal sign error, a missing factor 2 in
`2ṙθ̇`, `cos` for `sin`, a dropped coupling, a swapped mass, a halved Lorentz force (both
dimensionally consistent), the small-angle law claimed for all angles, and a
dimensionally wrong pendulum. The textbook double-pendulum form with double angles is true
but comes out `UNKNOWN`, because our tactics don't try double-angle identities. A
particle in the potential `k x^(1/2)` on `x > 0` is true. Four claims are ill-posed and
must come out `UNKNOWN`: the small-angle law on an empty domain (`θ > 1/2` and
`θ < −1/2`), the same `k x^(1/2)` potential on `x ≠ 0`, where Lean's `x^(1/2) = 0` for
`x < 0` let the planner's certificate prove the old statement, an oscillator written
with `ω = sqrt(k/m)` without `k > 0`, where Lean's `sqrt(k/m) = 0` for `k < 0` gave a
counterexample to the old `Refuted`, and the pendulum `θ̈ = −(g/l) sin θ` with `l > 0` left
out of the domain. At `l = 0` the Euler–Lagrange equation is `0 = 0` and Lean's `g/0 = 0`
turns the claim into `θ̈ = 0`, so `θ̈ = 1` was a counterexample to the old `Refuted`; with
`g/l` covered by `PhysOK`, both statements are provably false (`tests/test_lean.py`). A verdict is wrong if a true claim is `REFUTED`, a
false one `VERIFIED`, or an ill-posed one anything but `UNKNOWN`. The runner exits non-zero
if that happens.

### Conserved quantities

A second claim type says "`Q` is constant along every solution of the Euler–Lagrange
equations of `L` that stays in `D`". The file (`claims/conserved/*.json`, `"kind":
"conserved"`, format in `physverify/conserved.py`) has the same coordinates, symbols,
Lagrangian and domain as an EOM claim, and a `quantity` `Q(q, q̇, parameters)` in place of
the equations. The same runner checks both kinds:
`uv run python -m physverify.claims claims/conserved/`.

The judge writes two Lean statements (`lean/PhysVerify/Conserved.lean`):

* `VERIFIED`: `L` and `Q` are well-dimensioned, `L` and `Q` mention no accelerations,
  `DomainForm`, and `∃ λs, λs.length = n ∧ (∀ l ∈ λs, NoAccel n l) ∧ ConservedVerified n L D Q λs`.
  `ConservedVerified` says `D` has a point, and at every jet in `D`: the differentiation side
  conditions of `L` (as for EOM claims), `L.physOK`, `Q.diffOK`, `Q.physOK`, `diffOK` and
  `physOK` of every `λ_k`, and Noether's identity in characteristic form,
  `dt n Q = Σ_k λ_k · EL n k L`, as an identity in `(q, q̇, q̈)`. The multipliers are
  existentially quantified, so the statement does not depend on the planner.
* `REFUTED`: `NoAccel` of `L` and `Q`, and `ConservedRefuted n L D Q`: a jet in `D` with the
  side conditions and `PhysOK` of `L` and `Q`, where the Euler–Lagrange system holds, the
  velocity Hessian `∂²L/∂q̇_i∂q̇_j` has non-zero determinant (`Regular`), and `dt n Q ≠ 0`.

What the certificates mean, proven in Lean:

* `conserved_meaning`: take a `VERIFIED` statement and a trajectory `q` that is twice
  differentiable on an open interval `(a, b)`, with its jet in `D` and the real Euler–Lagrange
  equations (`realEL`, as in `verified_meaning`) holding at every time in `(a, b)`. Then
  `deriv (fun s => Q.eval (trajEnv n q p s)) t = 0` on `(a, b)`, and `Q` takes the same value
  at any two times in `(a, b)`. The proof is the chain rule (`dt_hasDerivAt`), `EL_bridge` for
  each `EL_k`, and `IsOpen.is_const_of_deriv_eq_zero`. `D` only has to hold along the
  trajectory pointwise, because `DomainForm` makes it open.
* `conserved_refuted_meaning`: at the certificate's jet, every trajectory twice
  differentiable at `t` with that jet at `t` satisfies the real Euler–Lagrange equations at
  `t`, and `s ↦ Q` has derivative `dt n Q ≠ 0` at `t`. The quadratic `jetTraj` through the jet
  is one such trajectory.

The value of `λ_k` does not matter for soundness: on a solution, `Σ λ_k · 0 = 0` for any reals.
We still require `diffOK` and `physOK` of the multipliers, so a certificate that uses a junk
`λ_k` (say `g/0`) somewhere in `D` is rejected (`test_junk_multiplier_rejected` in `tests/test_lean.py`).

The untrusted planner (`physverify/tools/conserved.py`): for a regular `L`, `dt Q` and every
`EL_k` are affine in `q̈`, so matching the `q̈` coefficients gives `λ = H⁻¹ ∂Q/∂q̇`, with `H`
the velocity Hessian. If the remaining identity holds at random points, it emits tactics
(`field_simp; ring`). Otherwise it looks for a counterexample jet with rational `q`, `q̇` and
parameters, and `q̈` solving the linear EL system. When every value is rational (coordinates
at 0 for trigonometric Lagrangians) `q̈` is a rational number. When it is not (the pendulum
with `+ m g l cos θ`, where `dQ/dt = −2 m g l θ̇ sin θ` vanishes at `θ = 0`), `q̈` is the exact
real number given by Cramer's rule as an `Expr` evaluated at the point, and `dQ/dt ≠ 0` is
closed with Mathlib's bounds on `sin` and `cos`. Nothing is approximated.

What is assumed, not proven:

* `REFUTED` is a statement about one jet. To conclude that `Q` changes along some *solution*,
  you also need a solution of the Euler–Lagrange equations through that jet. For a regular
  `L` that is smooth near the jet, Picard–Lindelöf gives one (`q̈ = H⁻¹(…)` is a C¹ ODE), but
  we have not instantiated it. This is why `Regular` is part of the statement: for a
  degenerate `L`, a jet can satisfy the EL system with no solution through it. The benchmark
  has an example: `L = m ẋ²/2 + λ(x − a)`, where `EL_λ` is the constraint `x = a`. `x` is
  constant on every solution, but the jet `x = a`, `ẋ = 1` satisfies the EL system and has
  `dx/dt = 1`. The statement without `Regular` is provable there, and the one with it is not
  (`test_degenerate_lagrangian_cannot_be_refuted` in `tests/test_lean.py`).
* As for EOM claims: literal serialization of the claim file, and the Euler–Lagrange equations
  as the input physics.

Benchmark (`claims/conserved/`, regenerated by `tools/gen_conserved_claims.py`; expected
verdicts written before the first run): pendulum energy (true) and with the potential's sign
flipped (false); Kepler angular momentum `m r² θ̇` (true) and `m r θ̇` (false); Kepler energy
(true) and with `+ GM m / r` (false); the x component of the Laplace–Runge–Lenz vector in polar
coordinates (true); a charged particle in a uniform `B` in the gauge `L = m(ẋ² + ẏ²)/2 − q B y ẋ`,
with the canonical momentum `m ẋ − q B y` (true) and the kinetic momentum `m ẋ` (false, refuted
at a rational jet on the EL surface); coupled oscillators, total energy (true) and the energy of
one oscillator (false); the constraint example above (true, expected `UNKNOWN`); and the pendulum
energy divided by `l` with `l` left out of the domain (ill-posed, `UNKNOWN`: at `l = 0` Lean's
`x/0 = 0` would make `dQ/dt = 0`).

```
$ uv run python -m physverify.claims claims/conserved/
|  constraint-multiplier-position         |  true   |  UNKNOWN   |  UNKNOWN   |   0s |
|  coupled-oscillators-energy             |  true   |  VERIFIED  |  VERIFIED  |  14s |
|  coupled-oscillators-one-energy         |  false  |  REFUTED   |  REFUTED   |  17s |
|  kepler-angular-momentum-wrong-power    |  false  |  REFUTED   |  REFUTED   |  13s |
|  kepler-angular-momentum                |  true   |  VERIFIED  |  VERIFIED  |  11s |
|  kepler-energy-wrong-potential-sign     |  false  |  REFUTED   |  REFUTED   |  15s |
|  kepler-energy                          |  true   |  VERIFIED  |  VERIFIED  |  13s |
|  kepler-lrl-x                           |  true   |  VERIFIED  |  VERIFIED  |  13s |
|  magnetic-canonical-momentum            |  true   |  VERIFIED  |  VERIFIED  |  11s |
|  magnetic-kinetic-momentum              |  false  |  REFUTED   |  REFUTED   |  14s |
|  pendulum-energy-over-length            |  ill    |  UNKNOWN   |  UNKNOWN   |  16s |
|  pendulum-energy-wrong-sign             |  false  |  REFUTED   |  REFUTED   |  18s |
|  pendulum-energy                        |  true   |  VERIFIED  |  VERIFIED  |  30s |

13 claims: 6 VERIFIED, 5 REFUTED, 2 UNKNOWN, 0 wrong
```

Measured on our 2-CPU / 7–8 GB VMs, with other jobs running alongside:

| Step | Time |
|---|---|
| `import Mathlib`, cold (about 5 GB of `.olean` and `.olean.private`) | did not finish in 20 min, twice |
| build `PhysVerify.EulerLagrange` from the Mathlib cache (narrow imports) | 3 min 10 s first time; 56 s to rebuild `EulerLagrange` alone |
| full `lake build` (all of `PhysVerify`, no `import Mathlib` left), cold: fresh Mathlib cache, nothing in the page cache | 7 min 32 s (5 min 16 s of it in `Expr`, the first module to map Mathlib) |
| same, warm: our build outputs deleted, Mathlib in the page cache | 1 min 29 s |
| `lake build` with nothing to rebuild (hashes 2679 jobs) | 1 min 3 s |
| one derivation certificate (`import PhysVerify.EulerLagrange`), warm | 6–28 s, typically about 10 s |
| one conserved-quantity certificate (`import PhysVerify.Conserved`), warm | 6–30 s, typically 8–15 s |
| same, after the page cache was evicted | 80–103 s |
| whole benchmark (23 claims), warm | 4 min 24 s to 7 min |
| conserved-quantity benchmark (13 claims), warm | about 3 min |
| `pytest tests/test_lean.py` (50 tests), warm | 19–20 min; the 17 conserved-quantity tests added since take about 4 min more |

The difference between the first two rows is why no module imports all of Mathlib any more
(`Expr`, `Deriv`, `Interval`, `Orbit` and `WellPosed` import only the modules they use),
and why certificates import a single module.

### Variational integrators

A discrete Lagrangian `L_d(q0, q1; h)` approximates the action over one step, and its discrete
Euler–Lagrange equations `DEL = D2 L_d(q_{k-1}, q_k) + D1 L_d(q_k, q_{k+1}) = 0` define the
integrator (Marsden and West, Acta Numerica 2001). A claim file (`benchmark/variational/*.json`,
`"kind": "variational"`, format in `physverify/variational.py`) gives one integrator: the
coordinates, `L_d` over levels `x_0, x_1`, the continuous `L` in the jet names of the
derivation checker (`x`, `x_dot`), a domain `D` over levels `x_0, x_1, x_2`, `h` and the
parameters (`h > 0` is always added to `D`), and claims of four kinds:

* `del_equations`: the claimed update (`lhs = rhs` per coordinate) is the DEL of `L_d`.
* `discrete_momentum_conserved`: `J(q0, q1)` is constant along DEL solutions, exactly. The
  name is historical: the check certifies *any* `J` with `J(q1, q2) − J(q0, q1)` in the ideal
  generated by the DEL expressions (on `D`), Noether momentum or not. The midpoint
  oscillator's quadratic invariant below is such a `J` and is not a Noether momentum.
* `consistent_order_p`: the DEL is consistent with the continuous EL of `L` with order **at
  least** `p`, the usual reading and the one the scheme layer uses (`consistent_order_p` under
  "Exact order of accuracy for linear schemes").
* `exact_order_p`: order at least `p` and not at least `p + 1`.

Run: `uv run python -m physverify.variational benchmark/variational/`.

What is proven in Lean (`lean/PhysVerify/Discrete.lean`, on top of `Expr`, `Deriv` and
`EulerLagrange`; no `sorry`, `native_decide` or new axioms: the meaning theorems use only
`propext`, `Classical.choice`, `Quot.sound`):

* `DEL_bridge`: where `L_d` is differentiable at `(q_k, q_{k+1})` and `(q_{k+1}, q_{k+2})`
  (`StepOK`), the symbolic `DEL` equals `realDEL`, built from Mathlib derivatives of the
  function `L_d` along a discrete trajectory.
* `del_equations`, `VERIFIED` (`DELVerified`, certificate `DEL = C · (lhs − rhs)` with
  `det C ≠ 0`, as for EOM claims): `del_verified_meaning`, at every step whose triple is in `D`
  the real DEL equations hold iff the claimed update holds. `REFUTED` (`DELRefuted`):
  `del_refuted_meaning`, a rational triple in `D` where one holds and the other does not.
* `discrete_momentum_conserved`, `VERIFIED` (`DMomentumVerified`): on `D`,
  `J(q1, q2) − J(q0, q1) = Σ_k μ_k · DEL_k` as an identity, with the multipliers `μ_k`
  existentially quantified (the planner's are `−ξ(q1)` for a symmetry generator `ξ`, or a
  synthetic division in `q2` for a quadratic invariant of a linear step). `dmomentum_meaning`
  (discrete Noether, certificate form): along every discrete trajectory `q_0 … q_{N+1}` whose
  triples all lie in `D` and satisfy the real DEL equations, `J(q_N, q_{N+1}) = J(q_0, q_1)`
  for every `N`, with no `O(h^p)` error. **`D` is chosen by the claim's author**, and the
  theorem covers only trajectories that stay in `D`; `h > 0` is always part of `D`.
  `L_d`, `J` and every `μ_k` must be junk-free (`physOK`) on all of `D`, and `D` must have a
  rational point.
* `discrete_momentum_conserved`, `REFUTED` (`DMomentumRefuted`): `dmomentum_refuted_meaning`, a
  rational triple `(q0, q1, q2)` in `D` satisfying the real DEL equations, with `RegularStep`
  (`∂DEL/∂q2` is a real derivative with non-zero determinant there, checked exactly), on which
  `J(q1, q2) ≠ J(q0, q1)`.

What is exact Python (labelled `exact (Python)`): the order check. With the sign convention
`DEL ≈ −h·EL` (`EL = d/dt ∂L/∂q̇ − ∂L/∂q`; derived in the module docstring), it substitutes
`q_j = q(t + (j − 1)h)`, a Taylor polynomial in `h` with jet coefficients, centred on the middle
level, and expands `(1/h)·DEL + EL` exactly in rationals. `consistent_order_p` is `VERIFIED`
when the coefficients of `h^0 … h^{p−1}` vanish identically (the verdict also reports the `h^p`
coefficient); `exact_order_p` also needs the `h^p` coefficient not to vanish. `REFUTED` reports
the first nonzero coefficient below `h^p` with a rational point where it is nonzero, or, for
`exact_order_p`, that every coefficient up to `h^p` vanishes.
Only polynomial `L_d` and `L` (division by monomials allowed) are in v1; `sqrt` gives `UNKNOWN`.

What is assumed, not proven:

* `RegularStep` says `q2` is the step taken from `(q0, q1)`. That `q2` is then locally unique
  is the implicit function theorem, which is **not formalised** here. A `REFUTED` momentum is a
  statement about one regular three-level trajectory.
* The order argument: for polynomial `L_d` and `L`, the Taylor expansion of a smooth trajectory
  to the needed degree gives the coefficients of `h^0 … h^p` exactly, and the remainder is
  `O(h^{p+1})`. We compute those coefficients exactly but have not proven this Taylor step in
  Lean (a Lean replay of the coefficient identities is future work).
* The domain `D` is the author's choice (see above), and, as for EOM claims, the claim file is
  serialized literally.

Not in scope: energy. `L_d` has no time-translation symmetry, so energy conservation is not a
Noether claim here. The midpoint oscillator's quadratic form is `VERIFIED` only because the
linear step has determinant 1 (division multiplier, not Noether); the same claim for the
nonlinear trapezoidal quartic oscillator is `REFUTED`. Energy of an explicit map is in scope
for `update_conserves` below.

**Explicit update maps: `update_conserves`.** Most integrators, and most simulation codes, are
not given as a DEL but as an explicit map `z' = Φ(z; h, params)` on the state `z = (q, p)`. A
claim file with `"kind": "update_map"` (same directory, same `Expr` syntax, format in the
"explicit update maps" section of `physverify/variational.py`) gives the state, the update as
a list of steps (each a simultaneous assignment; later steps read what earlier ones wrote, as
code does), a domain `D` over the state, `h` and the parameters (`h > 0` always added), and
claims of two kinds:

* `update_conserves`: `J(Φ(z)) = J(z)` on `D`. No variational structure is assumed.
* `update_conserves_order_p`: `J(Φ(z)) − J(z) = O(h^{p+1})` per step, i.e. the coefficients
  of `h^0 … h^p` vanish identically (order at least `p`, as for `consistent_order_p`).

What is proven in Lean (`lean/PhysVerify/Update.lean`, imports only `PhysVerify.Deriv` and
five tactic modules; no `sorry`, `native_decide` or new axioms):

* `updateStep Phi env` writes `Φ_k(env)` into state coordinate `k` and leaves `h` and the
  parameters alone (`updateStep_of_ge`).
* `VERIFIED` (`UpdateVerified`, plus `Φ` of length `n`, `J` well-dimensioned and every `Φ_k`
  of the dimension of `z_k`, by `decide`): on `D`, `J(Φ(z)) = J(z)` as an identity (planner:
  `simp` then `ring1`, or `field_simp` for a rational map), with `Φ` and `J` junk-free
  (`physOK`) at `z` and `J` also at `Φ(z)`, and a rational point in `D` (the same witness rule
  as above). `update_conserves_meaning`: along every orbit `z_{k+1} = Φ(z_k)` whose points
  `z_0 … z_{N−1}` lie in `D`, `J(z_N) = J(z_0)` exactly.
* `REFUTED` (`UpdateRefuted`): a rational `z ∈ D` (so `h > 0`) with `J(Φ(z)) ≠ J(z)`, checked by
  `norm_num`. `update_refuted_meaning`: the orbit of that point changes `J` at its first step.
  Because `Φ` is explicit, every point starts an orbit, so unlike a `REFUTED` discrete
  momentum this needs no regularity condition and no implicit function theorem.

The order claim (`lean/PhysVerify/UpdateOrder.lean`, also free of `sorry`,
`native_decide` and new axioms) is decided in exact
Python first: the `h`-coefficients of the polynomial `J(Φ(z)) − J(z)` (a map that divides by a
non-monomial, like the midpoint map below, gives `UNKNOWN`). Lean then replays the verdict; a
replay changes the label from `exact (Python)` to `proven (Lean)`, never the verdict.

* `VERIFIED` (`UpdateOrderVerified`, plus the dimension checks and `Expr.isPoly R`, by
  `decide`): the judge divides the drift by `h^{p+1}` exactly and puts the quotient `R(z, h)`,
  a polynomial, in the statement; Lean proves `J(Φ(z)) − J(z) = h^{p+1}·R` as an identity on
  `D` (`simp` then `ring1`), with `Φ`, `J` and `R` junk-free and a witness point in `D`. A wrong
  `R` does not check. `update_order_meaning` (per step): on every set where `|R| ≤ M`,
  `|J(Φ(z)) − J(z)| ≤ M·|h|^{p+1}`; `order_drift_compact`: `R` is continuous, so some `M` works
  on every compact set.
* `REFUTED` (`UpdateOrderRefuted`): a rational state and parameters `z`, a `k ≤ p` and a
  polynomial `S(t)` with `S(0) ≠ 0`, such that for every `t ∈ (0, 1)`, `z` with `h := t` is in
  `D`, junk-free, and `J(Φ(z)) − J(z) = t^k·S(t)` (`ring1` on rationals). `S(0)` is the
  `h^k` coefficient at `z`. `update_order_refuted_meaning`: at that `z` the drift is not
  `O(h^{p+1})` as `h → 0⁺` (`order_refuted_lower` gives `|drift| ≥ c·h^k` with `c > 0` for
  small `h`).

Nothing is proven about orbits. A drift bound after `N = T/h` steps would need the whole orbit
to stay in a set where `R` is bounded, which Lean does not know for these maps, so the theorem
is per step only. Not replayed (label stays `exact (Python)`): an `R` with a negative power of a
variable (from a map dividing by a state variable; `Expr.isPoly` fails) and a `REFUTED` claim
whose domain has an atom other than `h > 0` that mentions `h`. No bench row is in either case.

What is exact Python: the routing (the planner computes `J(Φ(z)) − J(z)` as an exact rational
function and checks whether its numerator is the zero polynomial; outside the rational
fragment it tries both certificates) and the order decision itself, which Lean replays as above. What is assumed: the judge composes the steps into one simultaneous `Φ` by
substitution in Python, and Lean sees only `Φ`, so that composition is trusted, like the
literal serialization of the claim file (`tests/test_update_conserves.py` checks it against
running the steps one by one on rational numbers). `D` is the author's choice, as above. The
kernels below remove this trusted composition for `update_conserves`.

The update-map bench uses a central potential with an exactly polynomial gradient,
`V = k|q|⁴/4`, `∇V = k|q|² q ∥ q`, and the angular momentum `L = x p_y − y p_x` (unit mass).
Explicit Euler changes `L` by `−h² p × ∇V(q)` (refuted at a rational point; conserved to order
1, not 2). Symplectic Euler and Störmer–Verlet (half kick, drift, half kick at `q'`) conserve
it exactly (verified; the Verlet identity is a degree-12 polynomial in six variables, closed by
`ring1`); `L` with one sign flipped is refuted. For the oscillator `H = (p² + w²q²)/2`,
symplectic Euler changes `H` by `h²w²(p² − w²q²)/2 + O(h³)` (refuted; order 1 verified, order 2
refuted) and conserves the modified energy `H − h w² p q/2` exactly (verified). The implicit
midpoint rule, solved by hand for the linear case, is the explicit rational map
`q' = ((4 − h²w²)q + 4hp)/(4 + h²w²)`, `p' = ((4 − h²w²)p − 4hw²q)/(4 + h²w²)`; it conserves `H`
(verified by `field_simp` with `4 + h²w² ≠ 0` from `positivity`), and the test suite checks
that this map solves `z' − z = hA(z + z')/2` exactly.

Bench (`benchmark/variational/`, 9 integrators with 24 claims and 5 update maps with 14). The traps: an explicit-Euler update
claimed as the DEL of the rectangle rule (refuted at a rational point); the wrong-sign cross
product and linear momentum under a central potential (refuted on regular steps); a rotation
invariant `L` with an `L_d` that breaks the symmetry (mixed quadrature: angular momentum
refuted); *exact* order 1 claimed for the Störmer–Verlet DEL of the rectangle rule (exact
order 2: the `h^1` coefficient vanishes identically, so the claim is refuted, while
`consistent_order_p` 1, order at least 1, is verified); order 2 claimed for the
rectangle rule with a position-dependent mass (the `h^1` coefficient is nonzero). The
rectangle rule for a constant-mass oscillator is *not* a first-order trap: its two-step DEL is
Störmer–Verlet, centred and second order.

```
$ uv run python -m physverify.variational benchmark/variational/
| integrator | claim | expected | verdict | guarantee |
|---|---|---|---|---|
| anharmonic-trapezoid | discrete_momentum_conserved | REFUTED | REFUTED | proven (Lean) |
| anharmonic-trapezoid | consistent_order_p 2 | VERIFIED | VERIFIED | exact (Python) |
| central-quartic-explicit-euler | update_conserves | REFUTED | REFUTED | proven (Lean) |
| central-quartic-explicit-euler | update_conserves_order_p 1 | VERIFIED | VERIFIED | proven (Lean) |
| central-quartic-explicit-euler | update_conserves_order_p 2 | REFUTED | REFUTED | proven (Lean) |
| central-quartic-symplectic-euler | update_conserves | VERIFIED | VERIFIED | proven (Lean) |
| central-quartic-symplectic-euler | update_conserves | REFUTED | REFUTED | proven (Lean) |
| central-quartic-trapezoid | discrete_momentum_conserved | VERIFIED | VERIFIED | proven (Lean) |
| central-quartic-trapezoid | discrete_momentum_conserved | REFUTED | REFUTED | proven (Lean) |
| central-quartic-trapezoid | discrete_momentum_conserved | REFUTED | REFUTED | proven (Lean) |
| central-quartic-trapezoid | consistent_order_p 2 | VERIFIED | VERIFIED | exact (Python) |
| central-quartic-verlet | update_conserves | VERIFIED | VERIFIED | proven (Lean) |
| central-quartic-verlet | update_conserves_order_p 5 | VERIFIED | VERIFIED | proven (Lean) |
| free-particle-2d | discrete_momentum_conserved | VERIFIED | VERIFIED | proven (Lean) |
| free-particle-2d | discrete_momentum_conserved | VERIFIED | VERIFIED | proven (Lean) |
| free-particle-2d | consistent_order_p 2 | VERIFIED | VERIFIED | exact (Python) |
| isotropic-oscillator-mixed-quadrature | discrete_momentum_conserved | REFUTED | REFUTED | proven (Lean) |
| isotropic-oscillator-mixed-quadrature | consistent_order_p 2 | VERIFIED | VERIFIED | exact (Python) |
| kepler-trapezoid | discrete_momentum_conserved | VERIFIED | VERIFIED | proven (Lean) |
| kepler-trapezoid | consistent_order_p 2 | UNKNOWN | UNKNOWN | none |
| oscillator-implicit-midpoint-map | update_conserves | VERIFIED | VERIFIED | proven (Lean) |
| oscillator-implicit-midpoint-map | update_conserves | REFUTED | REFUTED | proven (Lean) |
| oscillator-implicit-midpoint-map | update_conserves_order_p 2 | UNKNOWN | UNKNOWN | none |
| oscillator-midpoint | del_equations | VERIFIED | VERIFIED | proven (Lean) |
| oscillator-midpoint | consistent_order_p 2 | VERIFIED | VERIFIED | exact (Python) |
| oscillator-midpoint | discrete_momentum_conserved | VERIFIED | VERIFIED | proven (Lean) |
| oscillator-rectangle-rule | del_equations | VERIFIED | VERIFIED | proven (Lean) |
| oscillator-rectangle-rule | del_equations | REFUTED | REFUTED | proven (Lean) |
| oscillator-rectangle-rule | consistent_order_p 2 | VERIFIED | VERIFIED | exact (Python) |
| oscillator-rectangle-rule | exact_order_p 1 | REFUTED | REFUTED | exact (Python) |
| oscillator-rectangle-rule | consistent_order_p 1 | VERIFIED | VERIFIED | exact (Python) |
| oscillator-symplectic-euler-map | update_conserves | REFUTED | REFUTED | proven (Lean) |
| oscillator-symplectic-euler-map | update_conserves | VERIFIED | VERIFIED | proven (Lean) |
| oscillator-symplectic-euler-map | update_conserves_order_p 1 | VERIFIED | VERIFIED | proven (Lean) |
| oscillator-symplectic-euler-map | update_conserves_order_p 2 | REFUTED | REFUTED | proven (Lean) |
| position-dependent-mass-midpoint | consistent_order_p 2 | VERIFIED | VERIFIED | exact (Python) |
| position-dependent-mass-rectangle | consistent_order_p 2 | REFUTED | REFUTED | exact (Python) |
| position-dependent-mass-rectangle | consistent_order_p 1 | VERIFIED | VERIFIED | exact (Python) |

38 claims: 23 VERIFIED, 13 REFUTED, 2 UNKNOWN, 0 not as expected; 138s
```

Tests: `tests/test_variational.py` (no Lean: loader, layout, Python DEL against finite
differences, the sign convention, exact orders by hand, refutation points regular, a corrupted
multiplier breaking the identity). In `tests/test_lean.py`: the bench, `dmomentum_meaning`
applied to a generated statement, a corrupted multiplier and a junk `1/(m − m)` multiplier
rejected, a Kepler-like `L_d` with `1/sqrt` at the origin or `sqrt` of a negative left in `D`
not `VERIFIED`, and planner tricks rejected.

Update maps: `tests/test_update_conserves.py` (no Lean: loader, layout, step composition against
running the steps on rational numbers, Φ and the defects written out by hand, the midpoint map
solving the midpoint rule, the exact routing of every bench claim, refutation points in `D`, a
corrupted `L` with one sign flipped refuted, at-least order semantics, dimension mismatches).
In `tests/test_lean.py`: the bench (the same `test_variational_bench`), `update_conserves_meaning`
and `update_refuted_meaning` applied to generated statements, the sign-flipped `L` refuted at a
replayed rational point (and the true claim's certificate rejected for it), a junk
`J = H + 1/(w − w)` not `VERIFIED` although the identity holds in Lean, and planner tricks
rejected.

Order claims: `tests/test_update_order.py` (no Lean: `R` exact, drift = `h^{p+1}·R` as polynomials
and against exact runs of every bench item in both forms, kernels run assignment by assignment;
the `REFUTED` point's `h^k` coefficient non-zero and the drift there `t^k·S(t)`; a replay moves
only the label). In `tests/test_lean.py`, `-k update_order`: every decided bench row replays, a
wrong `R` is rejected, `REFUTED` certificates replay and give the meaning theorem (and fail with
`k > p` or a wrong `S`), and a `VERIFIED` statement gives the per-step and compact-set bounds.

Timings on the same 2-CPU VM, a fresh worktree:

| Step | Time |
|---|---|
| `lake exe cache get` (fresh clone of Mathlib and its cache) | 7 min 16 s |
| full `lake build` right after it, cold (our modules from scratch; `Discrete` alone 9.4 s) | 3 min 58 s |
| `lake build PhysVerify.Discrete`, warm, nothing to rebuild | 57 s |
| variational bench (23 claims, 12 Lean certificates in one batch per integrator), warm | 2 min 36 s |
| variational bench with the update maps (38 claims, 20 Lean certificates in one batch per file), warm | 2 min 18 s |
| `lake build`, cold after `lake exe cache get`: `PhysVerify.Update` alone | 4.0 s |
| `pytest tests/test_lean.py -k update` (5 tests), warm | 1 min 41 s |
| `lake build PhysVerify.UpdateOrder`, with every other module built | 1 min 7 s (mostly loading) |
| `pytest tests/test_lean.py -k update_order` (14 tests, both forms), warm | 2 min 28 s |
| `pytest tests/test_lean.py -k "variational or discrete or Discrete or dmomentum or update"` (25 tests, both file kinds), warm | 6 min 13 s |
| `pytest tests/test_lean.py -k "variational or discrete or Discrete or dmomentum"` (15 tests), warm | about 4 min 20 s |

### Kernels

An integrator with several sub-steps (Verlet: kick, drift, kick) is a few lines of code. A
*kernel* is that code, written once as a straight-line program: an ordered list of assignments
`x := e`, where `x` is a state variable or a temporary and `e` is an expression over the current
values. There are no loops, branches, arrays or pointers, and one program is one time step.
Claim files have `"kind": "kernel"` (`benchmark/kernels/`, format in `physverify/kernel.py`):

```json
"program": [{"set": "px", "to": "px - h/2*k*(x^2 + y^2)*x"}, ...,
            {"set": "x",  "to": "x + h*px"}, ...]
```

The same program is (1) serialised node for node into Lean, where its meaning is `exec`, and
(2) printed as C by `physverify/kernel_c.py`: `static inline void step(double *restrict z,
const double *restrict par)`, one C statement per assignment, in order, with temporaries as
locals. The claims are those of update maps, `update_conserves` and `update_conserves_order_p`.

What is proven in Lean (`lean/PhysVerify/Kernel.lean`, imports only `PhysVerify.Update`; no
`sorry`, `native_decide` or new axioms):

* `exec prog env` runs the assignments in order, each evaluated in the environment the previous
  ones produced, and leaves every variable no assignment writes (`h`, the parameters)
  unchanged (`exec_of_not_mem`). The sub-steps are composed by Lean, not by Python.
* `VERIFIED` (`KernelVerified`, plus `J` well-dimensioned and every assignment of the dimension
  of the variable it writes, `ProgDims`, by `decide`): on `D`, `J(exec prog z) = J(z)` as an
  identity (planner: `simp` unfolds `exec`, then `ring1` or `field_simp`), with a rational point
  in `D`. Junk-freeness is stated per step (`ExecOK`): every assigned expression is `physOK` in
  the environment where it runs. A dead temporary `t := 1/(w − w)` disappears from the composed
  map but not from `ExecOK`, so such a kernel is never `VERIFIED` (tested).
  `kernel_conserves_meaning`: along every orbit `z_{k+1} = exec prog z_k` whose points
  `z_0 … z_{N−1}` lie in `D`, `J(z_N) = J(z_0)` exactly.
* `REFUTED` (`KernelRefuted`): a rational `z ∈ D` where every assignment is junk-free and
  `J(exec prog z) ≠ J(z)`. `kernel_refuted_meaning`: its orbit changes `J` at the first step.

What is exact Python: the routing (as for update maps) and the order decision, which runs on the
map composed by substitution (`kernel.compose`). The Lean replay (`KernelOrderVerified`,
`KernelOrderRefuted`, `kernel_order_meaning`, `kernel_order_refuted_meaning`) checks the
identity `J(exec prog z) − J(z) = h^{p+1}·R` against `exec` itself, so the composition only
proposes `R` and is no longer trusted for a replayed row. Tests also check the composition
against `exec`: on rational points in Python, and in Lean for two kernels (`exec prog =
updateStep Φ` on the state).

What is trusted, or only tested:

| Piece | Status |
|---|---|
| `exec` semantics and conservation along orbits | proven (Lean) |
| order claims: the per-step drift identity, against `exec` | proven (Lean) |
| order claims over a time T (orbits) | not claimed |
| JSON-to-Lean serialisation of the program, `D` and `J` | trusted (literal printer, as for every claim file) |
| C path: the printer `kernel_c.py`, the C compiler, IEEE double arithmetic | empirical (differential test; C compiler and float semantics untrusted) |

Lean proves the semantics of the program, not of the compiled C. A `VERIFIED` kernel says the
real-number program conserves `J` exactly. It says nothing about the doubles the C computes,
which conserve `J` only up to rounding.

The differential test (`tests/test_kernel.py`; skipped cleanly without `cc`) compiles the
emitted step with `cc -O2 -std=c99 -ffp-contract=off` and runs N steps (N = 8 for the quartic
kernels, whose exact rationals triple in size every step; N = 200 for the linear ones) from
dyadic start values and parameters, which are exact doubles. It checks two things. (1) Every
step is bit for bit equal to a Python double evaluation with the same operations in the same
order (`kernel.run_float`: integer powers as a multiplication loop, literals as `n.0 / d.0`).
(2) After N steps the C state is within a norm-wise relative error of 1e-12 of the exact
rational orbit (`kernel.run`). Only double rounding separates the two: about 10 to 30 roundings
of relative size 2⁻⁵³ ≈ 1.1e-16 per step, carried by maps close to the identity (`h ≤ 1/16`),
so we expect at most about N·30·1.1e-16 ≈ 7e-13. Measured: 3e-17 to 2e-16 for the quartic
kernels, 4.6e-16 to 1.4e-15 for the oscillators. A printer that swaps the two assignments of
symplectic Euler is caught at the first step (tested).

Bench: the five update-map integrators ported to program form, with every verdict unchanged,
and two kernels for the step-semantics trap:

* Symplectic Euler is two assignments per coordinate, `p := p − h∇V(q); q := q + h p`, and the
  drift reads the NEW `p`.
* Explicit Euler is a simultaneous update. Written as straight-line code it needs temporaries:
  `t := q; q := q + h p; p := p − h∇V(t)`. `L` is still `REFUTED`.
* The trap is the symplectic Euler assignments in the other order, `q := q + h p;
  p := p − h∇V(q)`. It looks like explicit Euler written sequentially, but the kick reads the
  new `q`, so it is the adjoint symplectic Euler method. By hand: `q' × p' = q' × (p −
  hk|q'|²q') = q' × p = (q + hp) × p = q × p`. So `L` is conserved (`VERIFIED`), where explicit
  Euler's `L` is `REFUTED`. For the oscillator the same swap changes the exact invariant from
  `H − h w² p q/2` to `H + h w² p q/2`. By hand: `p'² + w²q'² + h w² p'q' = p² − h w² p q' +
  w²q'² = p² + w²q² + h w² p q`. The symplectic Euler invariant is `REFUTED` for the swapped
  kernel.

Map form (`benchmark/variational/`) against program form (`benchmark/kernels/`), from
`uv run python -m physverify.variational benchmark/kernels benchmark/variational/<the five maps>`:

| integrator | claim | expected | map form | program form | guarantee |
|---|---|---|---|---|---|
| central-quartic-explicit-euler | update_conserves L | REFUTED | REFUTED | REFUTED | proven (Lean) |
| central-quartic-explicit-euler | update_conserves_order_p 1 | VERIFIED | VERIFIED | VERIFIED | proven (Lean) |
| central-quartic-explicit-euler | update_conserves_order_p 2 | REFUTED | REFUTED | REFUTED | proven (Lean) |
| central-quartic-symplectic-euler | update_conserves L | VERIFIED | VERIFIED | VERIFIED | proven (Lean) |
| central-quartic-symplectic-euler | update_conserves L, sign flipped | REFUTED | REFUTED | REFUTED | proven (Lean) |
| central-quartic-verlet | update_conserves L | VERIFIED | VERIFIED | VERIFIED | proven (Lean) |
| central-quartic-verlet | update_conserves_order_p 5 | VERIFIED | VERIFIED | VERIFIED | proven (Lean) |
| oscillator-symplectic-euler | update_conserves H | REFUTED | REFUTED | REFUTED | proven (Lean) |
| oscillator-symplectic-euler | update_conserves H − h w² p q/2 | VERIFIED | VERIFIED | VERIFIED | proven (Lean) |
| oscillator-symplectic-euler | update_conserves_order_p 1 | VERIFIED | VERIFIED | VERIFIED | proven (Lean) |
| oscillator-symplectic-euler | update_conserves_order_p 2 | REFUTED | REFUTED | REFUTED | proven (Lean) |
| oscillator-implicit-midpoint | update_conserves H | VERIFIED | VERIFIED | VERIFIED | proven (Lean) |
| oscillator-implicit-midpoint | update_conserves L-sign energy | REFUTED | REFUTED | REFUTED | proven (Lean) |
| oscillator-implicit-midpoint | update_conserves_order_p 2 | UNKNOWN | UNKNOWN | UNKNOWN | none |
| central-quartic-adjoint-symplectic-euler | update_conserves L | VERIFIED | | VERIFIED | proven (Lean) |
| central-quartic-adjoint-symplectic-euler | update_conserves L, sign flipped | REFUTED | | REFUTED | proven (Lean) |
| central-quartic-adjoint-symplectic-euler | update_conserves_order_p 3 | VERIFIED | | VERIFIED | proven (Lean) |
| oscillator-adjoint-symplectic-euler | update_conserves H − h w² p q/2 | REFUTED | | REFUTED | proven (Lean) |
| oscillator-adjoint-symplectic-euler | update_conserves H + h w² p q/2 | VERIFIED | | VERIFIED | proven (Lean) |

33 claims (19 kernel, 14 map), 0 not as expected, 1 min 46 s warm.

Tests: `tests/test_kernel.py` (no Lean, 37 tests, about 4 s: loader, layout, `run` against
`compose`, each port composing to the old map's Φ with the same routing, sequential semantics
and the trap defects by hand, per-step junk, dimension mismatches, the C differential test and
its mutation check). In `tests/test_lean.py`, `-k "kernel or exec_equals"` (14 tests): the
kernel bench, both meaning theorems on generated statements, `exec = updateStep Φ` for two
kernels, the assignment order visible in Lean, a junk step rejected although the identity holds,
and planner tricks rejected.

| Step (same 2-CPU VM, fresh worktree) | Time |
|---|---|
| `lake build PhysVerify.Kernel`, with every other module built | 1 min 26 s (mostly loading) |
| kernel bench alone (19 claims, 12 Lean certificates in one batch per file), warm | 1 min 31 s |
| `pytest tests/test_lean.py -k "kernel or exec_equals"` (14 tests), warm | 3 min 23 s to 4 min 5 s (two runs) |

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
| Positivity of linear schemes on a claimed CFL range | exact: Bernstein coefficients of every c_k(nu) are >= 0 on the interval (endpoint values when c_k is affine in nu); where they are not, an exact decision (`univariate.py`): square-free decomposition c_k = c f_1 f_2^2 ..., no root of the odd-multiplicity part in the open interval (Sturm count) and c_k > 0 at a sample point, which certifies interior double roots that no Bernstein subdivision can; or an exact nu where some c_k < 0 | coefficient list, Bernstein coefficients, the decomposition, Sturm counts and sample point; or offending coefficient and nu |
| Convergence order (combined, space, time; or one norm, L1 or Linf, for the combined study) | empirical only | L1 and Linf error tables |
| Truncation order of linear schemes | exact: the Taylor coefficients e_j(nu) of the local truncation error vanish identically for j <= p, or an exact nu where some e_j != 0 | every e_j, the leading modified-equation term and its kind (diffusive, anti-diffusive, dispersive) |
| Von Neumann stability of linear schemes on a claimed CFL range | exact: 1 - \|g\|^2 >= 0 on nu x cos(theta) by tensor Bernstein coefficients after stripping (1 - z), (1 + z), or an exact (nu, cos(theta)) with \|g\|^2 > 1 | \|g\|^2, the factorisation, the boxes and their Bernstein coefficients; or the point |
| Shock speed on Riemann problems | empirical only | late-window speed at three crossing levels against the exact Rankine-Hugoniot speed, per grid |
| Entropy stability (Tadmor), semi-discrete | exact for the semi-discrete inequality only, not the time stepping: Q = -[v](F - F*) >= 0 certified on sign cells, or an exact rational point with Q < 0 | F*, Q, per-cell D = Q/(uR - uL)^2 with a change of variables that makes it non-negative by form, or counterexample (uL, uR) |
| Convergence to the rarefaction fan | empirical only | L1 error tables against u = (x - x0)/t, at two incommensurate dt/dx |
| Steady non-entropy step (fully discrete) | exact refutation only: the four stencils of a step uL < uR with f'(uL) < f'(uR) (f'' >= 0 by form) are fixed, as normal forms in lam; a failed search is `UNKNOWN`, never `VERIFIED` | (uL, uR), how it was found (candidate or search), f'(uL), f'(uR), f(uL), f(uR) |
| TVD of linear schemes on a claimed CFL range | exact, equivalent: with sum_k c_k = 1, TVD for all data iff every c_k(nu) >= 0 (decided as for positivity); a refutation is the box data u = 1 on w cells of a periodic grid of 2w cells (w the stencil width), stepped with the scheme's own update | the coefficients and their nonnegativity certificates; or the negative c_k(nu), the box data and both total variations |
| TVD of limited schemes (linear advection) on a claimed CFL range | exact both ways: Harten's incremental form certified on every sign cell by Farkas identities with multipliers polynomial in nu (sufficient), or an exact periodic state whose total variation grows (necessary) | per cell and half-cell: the identities, their nu-pieces and Bernstein minima, cell counts; or the state, nu and both total variations |
| Truncation order of limited schemes, per branch and on smooth data | exact: the truncation order of the linear scheme on each sign cell (sufficient when all are >= p), or an exact polynomial solution and grid placement whose local truncation error is a lower power of dx (necessary) | the branch table (slopes, order, leading e_j); or U(x), the placement, the cell and tau(dx) |
| Monotonicity of the fully discrete update on a claimed CFL bound | exact: every partial of H(u_{i-1}, u_i, u_{i+1}) is >= 0 on every sign cell within lam*\|f'(u)\| <= c, or two exact states, one argument raised, with H lower | per cell: H, the three partials, and a certificate (by form, a Farkas identity in w = lam*u, or Bernstein in lam); or the decreasing pair |

The exact checks use `Fraction` arithmetic and never decide on a float. Each returns a witness,
and with `--lean` most of their verdicts are replayed in the Lean kernel (next section). The flux recovery is
complete for three-point stencils: if the update is in flux form at all, the flux it finds is
the only one up to a constant. Square roots (so |u| = sqrt(u^2)) and division by monomials such
as dt/dx are supported. Anything else (sin, division by a sum) gives `UNKNOWN`, and so does a
non-zero normal form with no exact counterexample found.

### Lean certificates for the exact scheme checks

```
uv run python -m physverify.schemes schemes/*.json schemes/*/*.json --lean
```

runs the checks, then kernel-checks their exact verdicts in one Lean run and upgrades the guarantee
of each verdict whose theorems are all accepted. Lean never changes a verdict. If Lean is missing or
a proof fails, the verdict keeps `exact (Python Fraction arithmetic; Lean certificate pending)`.
The judge (`physverify/schemes/lean_cert.py`, trusted) writes every statement from the spec,
serializing the update, the numerical flux and the PDE flux node for node as real expressions. The
planner (`lean_planner.py`, untrusted) writes only the tactics, from the check's witness. The
general theorems live in `lean/PhysVerify/Scheme.lean`, which imports only the Mathlib modules it
needs; the generated file imports only `PhysVerify.Scheme`.
A claim verdict's guarantee carries the caveats of every check it rests on, on both paths: the Roe
entropy verdicts read `proven (Lean); semi-discrete inequality only, time stepping not certified`
(or `exact; semi-discrete ...` without Lean), never a bare `proven (Lean)`.

| Verdict | Lean statement | Guarantee |
|---|---|---|
| conservation VERIFIED / REFUTED | `Conserves D (H - u_i)` on every periodic grid `Fin (n+1)`, n >= 0, every component of a system, cells in the domain D (h > 0 for shallow water), for every lam > 0 and positive parameter; or its negation | proven (Lean) |
| consistency VERIFIED / REFUTED | `F(q, q, q, q) = f(q)` for every state in the domain, per component; or its negation | proven (Lean) |
| positivity VERIFIED / REFUTED | `NonnegComb H` (a non-negative combination of the stencil) for every lam > 0 with nu = a lam in [lo, hi]; or its negation | proven (Lean) |
| monotonicity, tvd_harten, depth_positivity_exact VERIFIED | per sign cell, every fact the check certifies: `p >= 0` on `{a_j >= 0}` | proven (Lean, per cell; cover in exact Python) |
| tv_increase, max_principle_violation, monotonicity, entropy_stability REFUTED | the negated claim (`TVD`, `LocalMaxPrinciple`, `MonotoneOn3` or `MonotoneVec`, `Q >= 0`) | proven (Lean) |
| steady_nonentropy_step (both forms) REFUTED | the step identities H(window) = centre value (or equal interface fluxes) for every lam > 0, and uL < uR, f'(uL) < f'(uR) | proven (Lean) |

What carries the weight, proven once in `Scheme.lean`:
- `conserves_of_telescoping`: if `H(a, b, c, d, e) - c = Phi(b, c, d, e) - Phi(a, b, c, d)` on the
  domain, the total is conserved on every periodic grid of any length. A certificate supplies Phi
  (for a declared flux, `-lam F`) and proves the pointwise identity with `ring` or `field_simp`.
- `NonnegComb.nonneg`, `.step_nonneg`, `.max_principle`: a non-negative combination keeps u >= 0, and
  with weights summing to 1 it satisfies the local maximum principle. `not_nonnegComb` refutes from
  one negative weight.
- `farkas`: atoms `a_j >= 0`, multipliers `mu_j >= 0`, `r >= 0` and the identity `p = r + sum mu_j a_j`
  give `p >= 0`. Rational multipliers are checked by `norm_num`. For the multipliers `mu_j(nu)` of
  `tvd_harten`, the proof splits the nu-range into the check's pieces (`le_total`), and on each piece
  proves `mu_j >= 0` with `nonneg_of_bernstein` (a polynomial with non-negative Bernstein coefficients
  on [lo, hi] is >= 0 there; the certificate proves the Bernstein identity by `ring`) when the degree
  is 2 or more, and by `linarith` from the endpoints when it is affine. The nu-cover of [lo, hi] is
  therefore kernel-checked too.
- Refutations are concrete: a periodic rational state, a stencil, a pair of states or a point, and
  `norm_num` evaluates both sides (square roots of rational squares included).

What stays trusted, exact Python:
- **The cell decomposition and its cover.** For a cell-based check, "proven (Lean, per cell; cover
  in exact Python)" means that every cell fact is kernel-checked and the case split covering the
  state space is checked in exact Python. The judge re-derives each cell's polynomial p and its atoms
  with the check's own code (sign cells, partial derivatives, the scaling w = lam u, Harten's N and
  Delta), so those derivations are trusted too, as is the argument from cell facts to the claim
  (piecewise-polynomial H with non-negative partials on closed covering cells is non-decreasing,
  Harten's lemma, the depth induction step). The pruned lower-dimensional cells are pruned in Python.
- **Relaxations.** Depth positivity quantifies over `z_j = lam sqrt(g h_j)` with only `z_j >= 0`, and
  forgets `z_j^2 = lam^2 g h_j`. Its statements are therefore weaker hypotheses over more variables,
  and so sound.
- **The step from identities to a claim.** A steady-step refutation proves the identities in Lean;
  that they make the step a steady state, and that this rules out entropy selection, is the argument
  in `checks.steady_nonentropy_step`, carried as the claim row's premise.
- **Statement generation itself** (the serializer `lean_cert.real`, the binders, the domain), as for
  the derivation checker.

Junk values: Lean has `x/0 = 0` and `sqrt(x) = 0` for `x < 0`. A statement is written only if every
denominator is a monomial in variables it assumes `> 0` (lam, the positive parameters, the positive
state components). A division by anything else, a state difference say, makes the verdict keep its
Python label. Every statement with square roots comes with a second theorem, `<name>_sqrt`, that
each argument is `>= 0` on the statement's domain (proved by `positivity`). The two together are
what upgrades the verdict.

Not yet certified (the verdicts keep the exact-Python label): consistency of a flux recovered from an
update (no spec in the corpus needs it), the cells of the five-point monotonicity check
(`limiters.monotonicity_wide`, nothing in the corpus is VERIFIED there), the entropy check's
VERIFIED cells, and the other exact checks (truncation order, von Neumann, hyperbolicity, the
shock-study scope checks).

Costs of a full pass (`python -m physverify.schemes schemes/*.json schemes/*/*.json --lean`, 30 specs,
one Lean file) on a 2-CPU, 8 GB machine shared with other jobs, so the numbers are indicative:

| run | load at start | wall | Lean | Python | theorems accepted | theorems/s (Lean) | peak RSS (Lean) |
|---|---|---|---|---|---|---|---|
| first after build | 3.2 | 799 s | 745 s | 54 s | 532 / 532 | 0.71 | 3.5 GB |
| warm repeat | 2.5 | 638 s | 562 s | 76 s | 532 / 532 | 0.95 | 3.7 GB |

Python is the exact checks (49 to 71 s) plus writing the statements and proofs (about 5 s). The
Python process itself peaks at about 45 MB.

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
identically in nu: `consistent_order_p` means order at least p, here and for variational integrators
(where `exact_order_p` adds that the next term does not vanish). The first non-zero e_j is the leading term of the modified equation. Stability is
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
work on the wider stencil, and so do monotonicity (linear advection only) and the steady-step checks
(see "Monotonicity and the steady step on five points" below). The examples are in `schemes/limiters/`, in Sweby's flux-limiter form
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

For linear schemes the two claims are decided exactly, both ways, by `tvd_linear` and
`max_principle_linear` (`linear.py`). If u_i^{n+1} = sum_k c_k(nu) u_{i+k} with sum_k c_k = 1, the
differences Delta_{i+1/2} evolve by the same convolution, whose l1 norm on zero-sum vectors is
sum_k |c_k|; with sum_k c_k = 1 that is <= 1 iff every c_k >= 0. So TVD for all data is equivalent to
positivity of the coefficients on the claimed range, and so is the local maximum principle (a negative
c_j gives u_i^{n+1} = c_j < 0 for the data 1 at i + j, 0 elsewhere). The nonnegativity is decided as
for `positivity`, including the exact square-free/Sturm step. The TVD refutation steps the box data
u = 1 on cells 1..w, 0 elsewhere, on a periodic grid of N = 2w cells (w the stencil width), with the
scheme's own update: its differences e_0 - e_w have non-overlapping images, so TV goes from 2 to
2 sum_k |c_k(nu)|. The TVD direction holds on every periodic grid and on the line; the refutation needs
N >= 2w (or the line), which the row states. Lax-Wendroff on [0, 1]: c_1 = (nu^2 - nu)/2 = -3/32 at
nu = 1/4, and TV goes from 2 to 19/8. Harten's three-point scheme with Q(x) = x^2 + 1/4 (the outside
benchmark's `harten_1982_highres:05`) has c_{+1} = (nu - 1/2)^2/2, with a double root inside
[0, 433/500]: Bernstein on the whole interval fails, the exact decision certifies it, and the scheme is
TVD there, though `tvd_harten` (upwind split, D = 0) has no certificate for this centred scheme.

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

**Monotonicity and the steady step on five points** (`limiters.monotonicity_wide`, the wide branch of
`checks.steady_nonentropy_step`). On each sign cell the limited update of u_t + a u_x = 0 is linear in
the u's, so dH/du_k is a polynomial c_k(nu). It is certified >= 0 on [0, c] by Bernstein coefficients
(with bisection). Otherwise the check looks for a real violation: two states u <= v, differing in one
argument and both strictly inside one full-dimensional cell (every atom > 0, checked exactly), with
H(u) > H(v) at a rational nu in the claimed range. The pair is replayed by evaluating the scheme's own
expression, and only the pair counts as a refutation; a negative derivative at a kink is not evidence.
Minmod and superbee are TVD on [0, 1] but not monotone, as Godunov's theorem (Harten, Hyman and Lax
for nonlinear schemes) says they cannot be:

| Spec, claim nu <= 1 | `monotone_under_cfl` | Witness (a = 1) |
|---|---|---|
| `broken-advection-minmod-monotone` | REFUTED | nu = 1/2: H(0, 4, 7, 8, 0) = 23/4 > H(0, 4, 7, 33/4, 0) = 183/32 (18 cells) |
| `broken-advection-superbee-monotone` | REFUTED | nu = 1/2: H(0, 12, 17, 18, 0) = 31/2 > H(0, 12, 17, 73/4, 0) = 247/16 (50 cells) |
| upwind with um2, up2 as unused arguments | VERIFIED | partials 0, nu, 1 - nu, 0, 0 |
| Lax-Wendroff in flux-limiter form | REFUTED | nu = 1/2: H(0, 6, 0, -6, -2) = 3 > H(0, 6, 0, -11/2, -2) = 47/16 |

Both witnesses sit in the Lax-Wendroff cell, where dH/du_{i+1} = -nu(1 - nu)/2. At nu = 1 minmod is
upwind and every partial is >= 0, so the refutation needs nu < 1. Failing monotonicity decides nothing
about `selects_entropy_solution`, whose monotonicity row is `sufficient`: for minmod that claim stays
`UNKNOWN`. For Burgers the five-point monotonicity check is `UNKNOWN` (the sign cells are not linear).

The steady non-entropy step works on all six windows of a five-point update across the jump,
H(uL, uL, uL, uL, uL), H(uL, uL, uL, uL, uR), ..., H(uR, uR, uR, uR, uR), and on the five interface
fluxes F(LLLL), ..., F(RRRR) for the method of lines. Minmod slopes vanish next to a step, so a MUSCL
scheme keeps the steady steps of its two-point flux. With the Roe flux and no entropy fix
(`broken-burgers-muscl-minmod-roe-no-entropy-fix`) the expansion shock -1 | 1 is exact (every
interface flux is 1/2): both entropy claims are REFUTED. With the Rusanov flux
(`burgers-muscl-minmod-rusanov`) no steady step is found and both claims stay `UNKNOWN`. Tadmor's check
is for two-point fluxes and says `UNKNOWN` for four-point ones.

Limits: one space dimension, scalar laws, three-point stencils for the entropy check (five points for the
rest), limiter checks (TVD, monotonicity, truncation) for linear advection only, periodic grids (the shock-speed and
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
| `positive_under_cfl` | positivity (Bernstein; square-free decomposition + Sturm where Bernstein fails) | equivalent | exact |
| `entropy_stable_tadmor` | entropy_stability (Tadmor) | equivalent | exact (semi-discrete) |
| `selects_entropy_solution_semidiscrete` | entropy_stability (Tadmor) | sufficient | exact (semi-discrete) |
| | steady_nonentropy_step_semidiscrete (F(uL, uL) = F(uL, uR) = F(uR, uR), uL < uR, f'(uL) < f'(uR), f convex) | necessary | exact |
| `monotone_under_cfl` | monotonicity | equivalent | exact |
| `selects_entropy_solution` | entropy_rarefaction | necessary | empirical |
| | steady_nonentropy_step (a steady step uL < uR with f'(uL) < f'(uR), f convex) | necessary | exact |
| | monotonicity (Crandall-Majda), only if conservation and consistency are VERIFIED | sufficient | exact |
| | stationary_rh_violation (a fixed-point jump uL \| uR with f(uL) != f(uR), shock or expansion) | necessary | exact |
| `consistent_order_p` | truncation_order | equivalent | exact |
| `von_neumann_stable_under_cfl` | von_neumann | equivalent | exact |
| `stable_for_small_cfl` | von_neumann_small_cfl (lowest term in nu; Bernstein on [0, 2^-k]) | equivalent | exact |
| `converges_order_p` | order/combined, order/space, order/time | necessary | empirical |
| | truncation_order (Lax-Richtmyer), only if von_neumann and lax_richtmyer_scope are VERIFIED | sufficient | exact |
| `correct_shock_speed` | shock_speed | necessary | empirical |
| | monotonicity (Crandall-Majda), only if conservation, consistency, flux_lipschitz and shock_scope_monotone are VERIFIED | sufficient | exact |
| | tvd_harten (Helly + Lax-Wendroff, a subsequence), only if conservation, consistency, flux_lipschitz and shock_scope_tvd are VERIFIED | sufficient | exact |
| | stationary_shock_rh_violation (a fixed-point jump uL \| uR with f(uL) != f(uR) that is a Lax shock: f'' >= 0 on [uR, uL], f'(uL) > f'(uR)) | necessary | exact |
| `limit_is_weak_solution` | conservation (Lax-Wendroff theorem), only if consistency and flux_lipschitz are VERIFIED | sufficient | exact |
| | stationary_rh_violation (a fixed-point jump uL \| uR with f(uL) != f(uR)) | necessary | exact |
| `tvd_under_cfl` | tvd_harten (Harten's incremental form on sign cells) | sufficient | exact |
| | tv_increase (an explicit periodic state whose TV grows) | necessary | exact |
| | tvd_linear (linear schemes with sum_k c_k = 1: TVD iff every c_k >= 0; the refutation needs a periodic grid of N >= 2w cells, or the line) | equivalent | exact |
| `local_max_principle_under_cfl` | tvd_harten (a convex combination of two stencil values) | sufficient | exact |
| | max_principle_violation (an explicit state outside its stencil's range) | necessary | exact |
| | max_principle_linear (linear schemes with sum_k c_k = 1: the principle iff every c_k >= 0) | equivalent | exact |
| `truncation_order_smooth_data` | truncation_branches (every branch's linear scheme has order >= p) | sufficient | exact |
| | truncation_smooth_data (an explicit polynomial solution with a lower-order tau) | necessary | exact |
| `converges_order_p_l1` | order_l1/combined | necessary | empirical |
| `converges_order_p_linf` | order_linf/combined | necessary | empirical |
| `hyperbolic` (systems) | hyperbolicity (discriminant of the 2x2 Jacobian) | equivalent | exact |
| `positive_depth_under_cfl` (systems) | depth_positivity (Riemann runs) | necessary | empirical |
| | depth_positivity_exact (induction step on the stencil) | equivalent | exact |
| `converges_to_riemann_solution` (systems) | riemann_l1 (against the exact Riemann solution) | necessary | empirical |
| `stated_identity` | stated_identity (LHS - RHS as a rational function; a rational witness point) | equivalent | exact Python (the poly.py normal form is trusted); no Lean meaning |

Tadmor's inequality is about the method of lines and says nothing about time stepping, so it
bears only on the semi-discrete claim. For the fully discrete scheme, monotonicity verifies the
claim honestly. By Crandall and Majda (1980), a conservative, consistent, monotone scheme
converges to the entropy solution (initial data in L1 ∩ BV). The same theorem gives a discrete
entropy inequality for every Kruzkov entropy, the maximum principle and TVD. The theorem needs
all three properties, so the row carries a precondition in the table: it counts only when the
conservation and consistency checks are exactly `VERIFIED` on the same spec, and otherwise it
gives `UNKNOWN`. `broken-burgers-nonconservative` shows why the precondition is there. That update
is monotone for lam*|u| <= 1/3 (`VERIFIED`), yet it moves shocks at the wrong speed, and the
Crandall–Majda row gives `UNKNOWN` ("requires conservation: REFUTED"). Its `selects_entropy_solution`
is `REFUTED` instead, by the frozen jump 1 | 0 (see the stationary-jump rows below). The CFL bound is part
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
| Non-conservative upwind | not run | VERIFIED (c = 1/3) | not run | not claimed | not claimed | REFUTED (exact, frozen jump 1 \| 0; Crandall-Majda UNKNOWN: conservation REFUTED) |

Roe without a fix is the cross-check. If the monotonicity check had certified it while the
rarefaction study refutes it, the judge would report `INCONSISTENT`. It doesn't: monotonicity fails
exactly at the transonic expansion, the same place the scheme keeps its expansion shock.

**Shock speed and weak limits** (`physverify/schemes/shockspeed.py`). Three rows turn exact checks
into statements about the limit dx -> 0 at fixed dt/dx, for scalar 1D conservation laws:
- `limit_is_weak_solution` is the Lax–Wendroff theorem (1960): for a conservative scheme with a
  consistent, locally Lipschitz numerical flux, every bounded a.e. limit is a weak solution, so its
  discontinuities move at the Rankine–Hugoniot speed. It is conditional: it does not say the scheme
  converges, and the limit may be a non-entropy weak solution.
- `correct_shock_speed` from monotonicity (Crandall–Majda): the whole sequence converges to the
  entropy solution, whose shocks satisfy Rankine–Hugoniot. The row also needs `shock_scope_monotone`:
  every (uL, uR, dt/dx) of the spec's shock study has dt/dx * max|f'| inside the certified monotone
  bound. Lax–Friedrichs and Engquist–Osher on Burgers are VERIFIED this way; Rusanov is certified only
  up to 1/3 while its study runs at 4/5, so it stays `NOT_REFUTED`.
- `correct_shock_speed` from exact TVD (Helly + Lax–Wendroff): TVD bounds plus L1-Lipschitz
  continuity in time give a convergent subsequence, and its limit is a weak solution. Subsequence
  only: the limit may contain an entropy-violating discontinuity that still moves at the RH speed,
  and the row says nothing about uniqueness or entropy. It needs `shock_scope_tvd` (each study nu in
  the claimed TVD range). TVD is exact only for linear advection today, where the only
  discontinuities are contacts moving at speed a. The row is correct there but weak, and it becomes
  useful once there is a TVD check for nonlinear fluxes.

`flux_lipschitz` checks the numerical flux by form: polynomials, |.| (so min, max and minmod) and
factors in dt/dx only are locally Lipschitz, and local is enough because the maximum principle or
TVD bounds the states. A square root of anything other than an even power, a division by the states,
or sin, exp and so on give `UNKNOWN`. Without a declared flux it checks a three-point update H, whose
flux (if it is conservative and consistent) is F(a, b) = f(a) + (a - H(a, a, b))/lam.

Both claims, and `selects_entropy_solution`, also have an exact necessary row from `fixedjump.py`,
which works on the update as written and so covers non-conservative schemes. It looks for Riemann
data uL | uR, jump at a cell interface, that the update returns unchanged at every stencil position
(the far-field constants and every window across the jump, three- or five-point) as an identity in
dt/dx, with f(uL) != f(uR). Then the numerical solution is that jump at every dx, its limit is the
stationary jump, and a stationary jump is a weak solution only if f(uL) = f(uR). So the limit is
not a weak solution, and not the entropy solution either (`stationary_rh_violation`, any such pair).
For `correct_shock_speed` that is not enough: if uL | uR is an expansion, the exact solution is a
rarefaction with no shock in it, and a frozen expansion shows a wrong limit, not a shock at a wrong
speed. That row uses `stationary_shock_rh_violation`, the same search restricted to Lax shocks:
f'' >= 0 on [uR, uL] (non-negative Bernstein coefficients) and f'(uL) > f'(uR). Then the entropy
solution is the single shock uL | uR at the RH speed, which is not 0, while the scheme's jump stays
put. Without such a certificate the row is `NOT_APPLICABLE`. The candidates are the spec's
shock-study pairs and a small grid; each hit is replayed by evaluating H and f in exact rationals.
For the quasilinear upwind scheme on Burgers, 1 | 0 is such a jump (H(1, 1, 0) = 1, H(1, 0, 0) = 0,
f(1) = 1/2) and a Lax shock, so all three claims are `REFUTED` exactly. A test scheme that freezes
exactly the expansions (0 | 1 among them) is refuted on the weak-limit and entropy claims and not on
the shock speed. A conservative consistent scheme is never refuted
this way: a fixed jump there forces F(uL, uL) = F(uL, uR) = F(uR, uR), so f(uL) = f(uR). Roe without a
fix freezes -1 | 1, but f(-1) = f(1), so that frozen step is a (non-entropy) weak solution and these
rows say nothing; the entropy row's steady-step check catches it. No pair found gives
`NOT_APPLICABLE`, which decides nothing.

Reported as the verdict on "the claim", the raw `REFUTED` would have said Harten's fix picks the
wrong solution. Likewise for `broken-burgers-nonconservative` the exact conservation check
decides `conservative`. The shock-speed study is only a necessary condition: it agrees there, but
on the conservative schemes its pass adds nothing to the proof. This is the same issue as tracking
the polarity of each tool's answer (delta-sat in dReal is only sound in one direction).

### Claims as papers write them

`benchmark/scheme-claims/` has 23 sentences phrased the way papers phrase them ("Lax–Wendroff is
TVD", "our upwind scheme is unconditionally stable", "the minmod MUSCL scheme is second order").
Each reading of each sentence is formalized into the named claims above, with an expected truth
and a citation. `uv run python -m physverify.schemes.bench benchmark/scheme-claims/` prints
expected against actual. It fails on a decisive verdict that contradicts the expectation and lists
non-decisive results as gaps. Now: 34 of 44 readings decided correctly, 9 gaps, 1 unscored
(expected truth unsettled), none wrong. The stationary-jump row closed C13's conditional reading
(REFUTED, exact) and made its unconditional one exact (REFUTED_EMPIRICALLY to REFUTED); before it
the count was 33 of 44 with 10 gaps. Five-point monotonicity added C23 (one match, below); before
it the count was 32 of 43. The shock-speed rows split C12's shock clause into a
conditional reading (every bounded limit is a weak solution) and an unconditional one (the scheme's
shocks move at the RH speed), both VERIFIED for Lax–Friedrichs on Burgers, and added C13's
conditional reading, a gap (see `GAPS.md`); before them it was 30 of 40 with 9 gaps. Before the limiter checks it was 24 of 34 with 10 gaps
(the monotonicity check settles the Rusanov and Engquist–Osher monotonicity claims, and the exact
order and von Neumann checks settle the truncation and global orders of Lax–Wendroff and upwind and
refute "upwind is unconditionally L2-stable"; the steady-step check makes the Roe and Lax–Wendroff
entropy refutations exact, and its semi-discrete form refutes "Roe's method of lines converges to
the entropy solution"; the small-CFL check refutes "FTCS is stable for sufficiently small time
steps"). The limiter checks added six matches: minmod and superbee TVD on [0, 1] (VERIFIED),
superbee TVD on [0, 3/2] and Lax–Wendroff in flux-limiter form TVD (REFUTED, exact), minmod's pointwise
truncation order 2 at smooth extrema (REFUTED, exact), and its max-norm order 2 on sine data
(REFUTED_EMPIRICALLY, at two dt/dx). Five-point monotonicity added a seventh: "the minmod-limited
scheme is monotone under nu <= 1" (C23) is REFUTED exactly. "Order 2 in L1 without extrema" stays a gap (NOT_REFUTED: no
theorem turns a refinement study into a proof). `GAPS.md` there ranks the gaps. The largest
remaining ones are order of accuracy and entropy claims for nonlinear schemes, and stability claims
that need a global parameter or a regime the spec cannot state.

### Printed formulas: stated identities

The other checks decide properties of a scheme. They say nothing about whether a formula a paper
prints is right: a paper can print its numerical entropy flux with a wrong sign while the scheme
is entropy stable all the same. `stated_identity` (`physverify/schemes/identity.py`) checks the
printed object. A spec gives the printed expressions in `claims.stated_identity` and picks the
identity they must satisfy (`form`):

| form | identity (scalar 1D) | stated keys |
|---|---|---|
| `entropy_balance` | eta'(u_i) (-(F_{i+1/2} - F_{i-1/2})) = -(Qh_{i+1/2} - Qh_{i-1/2}) + D on the 3-point stencil (the semi-discrete entropy balance times dx; D defaults to 0, entropy conservation) | `eta`, `entropy_flux` (Qh in uL, uR), `dissipation` (D in um1, u0, up1) |
| `entropy_pair` | q'(u) = eta'(u) f'(u) | `eta`, `q` |
| `viscosity_form` | F(uL, uR) = (f(uL) + f(uR))/2 - Q (uR - uL)/2 | `Q` (in uL, uR, lam; `nu` = lam*a for a linear f) |
| `amplification` | the stated g equals the symbol sum_k c_k(nu) z^k of a linear update, z = e^{i theta} | `g` (in nu, z) |

`let` names subexpressions (the paper's ~F, ~Q, v-bar, ...), and `domain` lists conditions
`p > 0` or `p >= 0`. LHS - RHS is brought to N/Dn over the normal form of `poly.py`. Division by a
sum is allowed here, and the identity then holds wherever every denominator is non-zero. VERIFIED
means N normalises to 0. REFUTED means an exact rational point in the domain, with Dn != 0, where
N/Dn != 0. For `amplification` that point is a rational nu and a rational point
((1 - t^2) + 2ti)/(1 + t^2) on the unit circle, evaluated in exact complex rationals. Everything
else is UNKNOWN: exp, log, non-integer powers, or a non-zero N with no witness found. No verdict
comes from floating-point sampling. So the check decides polynomial and rational identities only: an
entropy pair with a log term (the physical entropy of the Euler equations, the logarithmic mean in
entropy-conservative fluxes) or with exp comes out UNKNOWN, never REFUTED, even when the pair is true
(rows `entropy-pair-burgers-log` and `entropy-pair-burgers-exp`). The rows are in `schemes/identity/` and
`tests/test_stated_identity.py`.
In `benchmark/outside`, the identity (3.3) of `fjordholm_mishra_tadmor_2012_tecno:04` as
transcribed is REFUTED (residual (up1^2 - 2 u0^2 + um1^2)/2, the difference across the cell of
v-bar [v]), and it is VERIFIED with the minus sign that the paper's Lemma 3.2 uses.

Not covered: systems (matrix D, vector entropy variables), fully discrete identities (energy
identities summed over the grid, such as E^{n+1} = E^n + ...), stencils wider than three points for
the balance form, and non-rational entropies (exp, log).

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

### Reconstructions: the order of WENO weights, critical points included

`physverify/reconstruction.py` decides `reconstruction_order_p`: a WENO-type reconstruction, written as
expressions over the stencil values (candidates q_k, linear weights d_k, indicators beta_k,
alpha_k = d_k/(eps + beta_k)^q; or WENO-Z, alpha_k = d_k (1 + (tau/(eps + beta_k))^q) with
tau = |beta_i - beta_j|; or WENO-M, the Jiang–Shu weights through Henrick's mapping), has error O(dx^p) for
every smooth f in a regime: f' != 0, or a critical
point of order n_cp (f' = ... = f^(n_cp) = 0 at x_i). The claim names eps = c dx^m (rational m) or eps = 0, and
a form: one reconstruction at x_i + s dx, or the conservative difference (R - T at i+1/2 minus R - T at i-1/2,
over dx). Data are point values (target f, or the primitive h of the finite-difference flux form) or cell averages.

The error is a power series in dx^(1/L), with coefficients that are polynomials in the Taylor jet (exact
`Fraction`s). The weights' denominators are cleared. Their leading terms must be positive for every jet in the
regime, which is shown by form; otherwise the answer is UNKNOWN. VERIFIED means every coefficient below dx^p is
the zero polynomial; no jet is sampled. REFUTED gives a rational jet, the order k < p and the exact dx^k
coefficient. Tests re-check every REFUTED witness, and every eps = 0 VERIFIED row on sampled jets, by evaluating
the formulas directly at rational dx.

`uv run python -m physverify.reconstruction` runs `benchmark/reconstruction/` (70 claims, expected verdicts
committed before the checker supported them: 43 for v1, 27 WENO-Z/M rows for v2; all 70 agree, including the 7
marked unsure). Leading orders for WENO5-JS (Jiang–Shu indicators), flux
form:

| form | regime | eps | leading order |
|---|---|---|---|
| point or difference | f' != 0 | 10^-6, dx^2 or 0 | 5 |
| difference | f' = 0, f'' != 0 | 0 or dx^4 | **3** (the drop Henrick, Aslam and Powers found) |
| difference | f' = 0, f'' != 0 | dx^2 or 10^-6 fixed | 5 |
| point (one reconstruction) | f' = 0, f'' != 0 | 0 | 5 |
| point / difference | f' = f'' = 0 | 0 | 3 / 2 |

The drop at a critical point is a property of the difference. At x_{i+1/2} alone the O(dx) weight errors
d_k (f'''/f'')(4/5 - 4(k-1)) dx cancel against the candidate errors (1/4, -1/12, 1/12) f''' dx^3. At x_{i-1/2}
(f' = -f'' dx there) they do not. With a fixed eps the order is 5 at critical points too, because IS_k = O(dx^4)
is eventually small against eps. Other rows: WENO3-JS drops to 1 at critical points (eps = 0), the linear
weights give 5 everywhere, and a typo of 1/3 for 1/4 in beta_1 is invisible with fixed eps but gives order 3
with eps = 0 where f' != 0.

**WENO-Z and WENO-M** (same candidates and Jiang–Shu indicators, flux form, leading orders):

| weights | f' != 0, eps = 0 | n_cp = 1, eps = 0 | n_cp = 1, other eps | n_cp = 2, eps = 0 |
|---|---|---|---|---|
| WENO-M (Henrick, Aslam and Powers) | 5 | 5 (one reconstruction 5) | 5 for eps = dx^4 | 2 (one reconstruction 3) |
| WENO-Z, q = 1 (Borges, Carmona, Costa and Don) | 5 | **4** (one reconstruction 5) | 5 for dx^3 and 10^-6; 4 for dx^4 | 2 (one reconstruction 4) |
| WENO-Z, q = 2 | 5 | 5 | | 2 |

These match the papers' statements: Henrick et al. read directly (5 at n_cp = 1, p. 557; rate 2 at n_cp = 2 for
r = 3, eq. (60) and Table 10); Borges et al. (q = 1 gives 4 at n_cp = 1, q = 2 gives 5) and Don and Borges's eps
range (eps of order at least dx^3 for q = 1) only through secondary sources, as the paper was not accessible to us.

The map is rational in the weights, so WENO-M needs no new mechanism: the mapped weights are cleared the same way,
and their denominator is positive because each g_k is a positive-definite form in (omega, 1) for 0 < d_k < 4/5.
WENO-Z needs one: tau = |beta_i - beta_j| is not a power series. For one f, beta_i - beta_j has the sign of its
first non-zero term for all small dx, so |beta_i - beta_j| = sigma (beta_i - beta_j) with sigma = +1 or -1. The
checker decides every sign branch (two for one reconstruction, four for the difference), dropping only branches the
leading term rules out by form; VERIFIED needs every branch, and no branch is picked by sampling. A REFUTED jet is
checked exactly to lie in its branch. This needs tau of order at least every eps + beta_k (true for WENO5-Z in
every regime above: beta_0 - beta_2 = dx^5 (-13/3 f'' f''' + f' f'''' + ...)), and an even q needs no split. At
n_cp = 1 the sign of -13/3 f'' f''' is open, and all four branches give 4; at n_cp = 2 the shifted stencil's
leading term 13/3 f'''^2 dx^6 is positive by form, which removes two branches, and it is of the same order as the
indicators there, which is why WENO-Z also falls to 2.

The original Jiang–Shu measurement (2.20) is fifth order where f' != 0 (v1). Why, and what the report's numerical
tables show, is in `benchmark/outside/notes/jiang-shu-tables.md`: the O(h) weight errors d_k (4/5 - 4(k-1))
(f''/f') h cancel against the candidate errors at O(h^4), and the tables' sub-fifth orders come from the critical
points of their data on grids where eps = 10^-6 does not yet dominate the indicators there.

### Cell-average steps and ENO jumps (reconstruction v3)

Two more claim kinds in the same layer. We chose them by how many outside dev items they cover
(`benchmark/outside/notes/reconstruction-survey.md`), so the dev readings that use them are made with a checker
tuned on those items. Their bench specs and expected verdicts were committed first
(`benchmark/reconstruction/cell-average/`, `benchmark/reconstruction/eno/`, each with a README).

`cell_average_max_principle` (`physverify/cellaverage.py`): one step of a cell-average scheme fed by polynomials of
degree <= k keeps the new average in [m, M] whenever stated linear functionals of the polynomials (point values,
averages) lie in [m, M], for every lam = dt/dx in a range. If the update and the hypotheses are 1 on constant data,
this holds iff the update is a convex combination of the hypotheses, and with independent hypotheses the weights
mu_i(lam) are unique polynomials. VERIFIED means they are >= 0 on the range (exact: square-free part and Sturm
count). REFUTED comes with polynomials whose hypotheses lie in [0, 1] and whose update does not, checked by
evaluation. A hypothesis that is a non-negative combination of earlier ones is dropped (the average, as
Simpson's combination of the Gauss–Lobatto values, for k <= 3); a dependent set otherwise is UNKNOWN (a linear
programme, not done). Zhang and Shu's Gauss–Lobatto condition comes out exactly. With f(u) = u and the
Lax–Friedrichs flux the bound is lam <= min w_alpha (1/2 for k = 1, 1/6 for k = 2, 3). It fails for k = 4 with 3
points, and it fails without the interior point value (their Remark 2.3).

| spec | lam | verdict |
|---|---|---|
| k = 1, 2-point GL | [0, 1/2] / [0, 1] | VERIFIED / REFUTED |
| k = 2, 3, 3-point GL | [0, 1/6] / [0, 1/5], [0, 1/4] | VERIFIED / REFUTED |
| k = 2, Lax–Friedrichs with a = 2 | [0, 1/9] / [0, 1/6] | VERIFIED / REFUTED |
| k = 2, p(x*) form (survey (5.1)) | [0, 1/6] / [0, 1/3] | VERIFIED / REFUTED |
| k = 2, edge values only | [0, 1/6] | REFUTED |
| k = 4, 3-point GL | [0, 1/12] | REFUTED |

`eno_sign_property`, `eno_jump_ratio_at_most` (`physverify/eno.py`): for ENO interpolation of point values of order
k, with a tie rule, or a fixed stencil, over all real data: the jump J = w^-_{i+1} - w^+_i has the sign of
D = w_{i+1} - w_i in the weak sense (J D >= 0, and J = 0 where D = 0; the strict sign fails on linear data for
k >= 2), and J / D <= c. The selection splits the data space into finitely many polyhedral branches (|A| <= |B|
is a union of two cones). On each branch, J and D are linear, so a failure is a feasible system of strict and
non-strict linear inequalities, decided by Fourier–Motzkin elimination over the rationals. A REFUTED witness is
a rational solution, re-checked by recomputing the ENO choices directly. Results: the sign property holds for
k = 1, 2, 3 with either tie rule and fails for the linear stencils {i-1, i} and {i-1, i, i+1}. The exact supremum
of J / D is 1, 2 and 7/2 for k = 1, 2, 3. k >= 4 is UNKNOWN: 4^6 branch pairs, and the elimination takes minutes.

### The scaling limiter

Zhang and Shu's bound-preserving limiter p~ = ubar + theta (p - ubar), theta = min(1, |M - ubar|/|M_x - ubar|,
|m - ubar|/|m_x - ubar|), with M_x, m_x the extrema of p over the cell or over the Gauss–Lobatto points. This was
the next mechanism in the same dev survey's ranking, so its readings are tuned on the dev items too. The bench
(`benchmark/reconstruction/limiter/`, committed first) also has typo variants: theta without the 1 or without the
lower term, scaling about p(0), and too few points. `physverify/limiter.py` decides three claims for every
polynomial of degree k <= 3 and all m <= M:

- `limiter_keeps_average`: an identity when the centre is the average functional.
- `limiter_bounds` (on a set of points or the cell): VERIFIED when theta has both ratio terms, ubar is in
  [m, M] and the set is dominated by the extrema set at degree k (for k >= 2: a subset of it, or S is the cell;
  -(y - y')^2 peaks off the points otherwise).
- `limiter_accuracy`: max |p~ - p| <= C max dist(p, [m, M]). VERIFIED when the 1 is in theta and the average is a
  non-negative combination of the values on S. C is a bound on K_k = sup max |q| / max q over zero-mean q of degree
  k. The first bound came from the k + 1 Newton–Cotes nodes, C <= max_a max L_a / w_a - 1, with each max certified
  by Sturm: 1, 5, 7 for k = 1, 2, 3 (still computed, as `newton_cotes_K`). The checker now uses a sharper one:
  K_k <= 1/w - 1 whenever avg P >= w P(y0) for every y0 in the cell and every P >= 0 on the cell of degree k. By the
  Markov–Lukács representation of such P, that holds when 1 x 1 and 2 x 2 Hankel matrices of avg - w delta_y0 are
  positive semidefinite, which is a set of polynomial inequalities in y0 certified by Sturm.

  | k | certified upper bound (`C`) | lower bound (`C_lower`), witness q | Newton–Cotes bound |
  |---|---|---|---|
  | 1 | 1 | 1, q = y | 1 |
  | 2 | 3 | 3, q = 1/9 - (y - 1/6)^2 (max 1/9 at y = 1/6, min -1/3 at y = -1/2) | 5 |
  | 3 | 5 | 5, q = 1/24 - y^2/2 - y^3 (max 1/24 at y = -1/2 and 0, min -5/24 at y = 1/2) | 7 |

  Upper and lower bounds agree, so 1, 3, 5 are the exact suprema (attained). A numerical search over zero-mean
  polynomials found the same values before they were certified.

Each REFUTED verdict comes with a datum (p, m, M) from a fixed list of simple candidates. The datum is checked by
exact evaluation, and for accuracy, d = 0 is certified by Sturm while theta != 1. When no candidate works the
verdict is UNKNOWN. Results: every Zhang–Shu claim is VERIFIED for k = 1, 2, 3 (cell and Gauss–Lobatto). The bounds
fail without ubar in [m, M]. The Gauss–Lobatto limiter bounds the points but not the whole cell for k = 2, 3 (it
does for k = 1). Dropping the 1 breaks the accuracy, dropping the lower term breaks the bounds, scaling about p(0)
breaks the average, and the two cell ends alone break the accuracy for k = 2. The accuracy clause does not need
ubar in [m, M], which the sources assume.

## Class theorems

The checks above decide a property of one concrete scheme. A theorem about every scheme with a
property needs the scheme's coefficients as variables, so it is a Lean theorem, not a check.
`lean/PhysVerify/Harten.lean` has the first ones. They are proven (no `sorry`, standard axioms
only), but no verdict calls them yet, so `tvd_under_cfl` still has no Lean meaning.

Setting: the periodic grid `ZMod N`, any `N ≥ 1` (`[NeZero N]`), values in any linearly ordered
field (`ℚ` and `ℝ` both work), `TV u = Σ_i |u (i+1) - u i|`. Both coefficients of the interface
j + 1/2 carry the index `j`: `hartenStep u C D i = u i + C i (u(i+1) - u i) - D(i-1) (u i - u(i-1))`.

| Theorem | Hypotheses | Conclusion |
|---|---|---|
| `harten_tvd` | `∀ j, 0 ≤ C j`, `∀ j, 0 ≤ D j`, `∀ j, C j + D j ≤ 1` | `TV (hartenStep u C D) ≤ TV u` |
| `harten_tvd_of_form` | `∀ u i, H u i = hartenStep u (C u) (D u) i`, and the three bounds on `C u`, `D u` for this `u` | `TV (H u) ≤ TV u` |
| `linear_tvd` | `v i = a u(i-1) + b u i + c u(i+1)`, `a, b, c ≥ 0`, `a + b + c = 1` (`C = c`, `D = a`) | `TV v ≤ TV u` |
| `upwind_tvd` | `v i = u i - ν (u i - u(i-1))`, `0 ≤ ν ≤ 1` | `TV v ≤ TV u` |
| `monotone_tvd` | `v i = H(u(i-1), u i, u(i+1))`, `H(a, b, c) = b - λF(b, c) + λF(a, b)` nondecreasing in each argument (`Monotone3 F λ`) | `TV v ≤ TV u` |

`monotone_tvd` goes through the incremental form, with `C` and `D` difference quotients of the
flux (`x / 0 = 0` where the data are flat). It needs no Lipschitz bound and no separate CFL
hypothesis: on a finite grid the quotients are just numbers, and monotonicity already gives the
three bounds. The converse of `linear_tvd` (TVD only if `a, b, c ≥ 0`) needs box data and is
decided in Python by `physverify/schemes/linear.py::tvd_linear`, not proven here. All of these
are periodic; the whole-line versions in the literature (finite TV on ℤ) are not formalised.

## Claim kinds

Every claim name has one reading, shared by every layer that uses it, in
`physverify/claimkinds.py`. Each layer keeps its own table of which checks decide a claim; only the
names and their meaning are shared, and each layer checks its names against the registry when it
is imported. The table below is generated (`uv run python -m physverify.claimkinds --write`), and
`tests/test_claimkinds.py` fails if it drifts, if a name in a layer or a bench file is missing from
the registry, if an entry is unused, or if a Lean meaning theorem does not exist. It also checks
each param's key: the layer's code reads it, and every spec (and every benchmark component, with
its override) that names the claim declares it, unless the key is marked optional.

<!-- claim-kinds:begin -->
Kinds with a Lean meaning theorem have a proven semantics; the rest have a gloss only (a reading a person chose, checked by review).

Params gives where each layer reads a parameter (see `params` in the module docstring; `?` marks an optional key).

| Name | Gloss | Quantifier | Layers | Params | Lean meaning |
|---|---|---|---|---|---|
| `consistent` | the numerical flux is consistent with the PDE flux | for all states u: F(u, ..., u) = f(u), as an identity | schemes | none | gloss only |
| `conservative` | the update is in flux form, so the total of u (of each component) is conserved on periodic grids | for every periodic grid of any size and every state in the domain: sum_i (u_i^{n+1} - u_i^n) = 0 | schemes | none | `conserves_of_telescoping` |
| `positive_under_cfl` | the linear update is a non-negative combination of its stencil values, so non-negative data stay non-negative | for all nu = a*dt/dx in the claimed range: every stencil weight is >= 0 | schemes | nu_range: `claims.positive_cfl` | `NonnegComb.step_nonneg` |
| `entropy_stable_tadmor` | entropy stable in Tadmor's semi-discrete sense for the declared entropy pair (by default u^2/2, u^3/3 when the flux is Burgers' u^2/2) | for all states uL, uR: Q = -[v](F - F*) >= 0, with v = eta'(u) | schemes | eta: `claims.entropy_stability.eta?`; q: `claims.entropy_stability.q?` | gloss only |
| `selects_entropy_solution_semidiscrete` | the method-of-lines scheme's limit is the entropy solution | for all admissible data: the dx -> 0 limit of the semi-discrete solution is the entropy solution | schemes | none | gloss only |
| `monotone_under_cfl` | the update H is non-decreasing in each stencil value under the claimed CFL bound | for all states with lam*\|f'(u)\| <= c: H is non-decreasing in each argument | schemes | c: `claims.monotone_cfl` | gloss only |
| `selects_entropy_solution` | the limit of the fully discrete scheme is the entropy solution, not another weak solution | for all admissible data: the dx -> 0 limit at fixed dt/dx is the entropy solution | schemes | none | gloss only |
| `consistent_order_p` | the discrete equations are consistent with the continuous ones to order at least p in the step (dx at fixed dt/dx for a linear scheme, h for a variational integrator) | for all smooth solutions: truncation error = O(dx^p) (schemes), (1/h)·DEL + EL = O(h^p) (variational); at least p, so a higher order also verifies | schemes, variational | p: `claims.consistent_order` (schemes), `claims[].p` (variational) | gloss only |
| `exact_order_p` | the DEL is consistent with the continuous EL equations to order exactly p | exactly p: at least p and not p + 1 (the h^p coefficient of (1/h)·DEL + EL is not identically 0) | variational | p: `claims[].p` | gloss only |
| `von_neumann_stable_under_cfl` | von Neumann (l2) stable on the claimed CFL range (linear constant-coefficient schemes) | for all nu = a*dt/dx in the claimed range and all theta: \|g(theta)\| <= 1 | schemes | nu_range: `claims.von_neumann_cfl` | gloss only |
| `stable_for_small_cfl` | von Neumann stable for every small enough CFL number (linear constant-coefficient schemes) | there is nu0 > 0 such that for all nu in (0, nu0] and all theta: \|g(theta)\| <= 1 | schemes | none | gloss only |
| `converges_order_p` | the scheme converges to smooth solutions at order at least p, for each claimed refinement study (claims.order maps a study to its p) | for each claimed study (combined, space, time): global error = O(step^p) on smooth data; at least p, but an empirical study above p + TOL is reported SUSPICIOUS, a gap, never a refutation | schemes | p: `claims.order` | gloss only |
| `correct_shock_speed` | shocks move at the Rankine-Hugoniot speed in the limit dx -> 0 at fixed dt/dx | for Riemann data whose entropy solution is a shock: the limit's shock moves at (f(uL) - f(uR))/(uL - uR) | schemes | none | gloss only |
| `limit_is_weak_solution` | every bounded a.e. limit of the scheme as dx -> 0 at fixed dt/dx is a weak solution (conditional on convergence) | for all data and every limit u (bounded, a.e., in L1_loc): u is a weak solution | schemes | none | gloss only |
| `tvd_under_cfl` | one step never increases the total variation, on the claimed CFL range | for every periodic state and every nu = a*dt/dx in the claimed range: TV(u^{n+1}) <= TV(u^n) | schemes | nu_range: `claims.tvd_cfl` | gloss only |
| `local_max_principle_under_cfl` | each new value lies between the smallest and largest values of its stencil, on the claimed CFL range | for every state, every nu = a*dt/dx in the claimed range and every i: min(stencil) <= u_i^{n+1} <= max(stencil) | schemes | nu_range: `claims.tvd_cfl` | gloss only |
| `truncation_order_smooth_data` | pointwise local truncation order at least p at every grid point of every smooth solution, extrema included | for all smooth u and every grid point: local truncation error = O(dx^p) at fixed dt/dx | schemes | p: `claims.smooth_truncation` | gloss only |
| `converges_order_p_l1` | the global error in the discrete L1 norm is O(dx^p) at fixed dt/dx, on the spec's smooth test problem | on the spec's test problem: sum_i \|u_i - u(x_i)\| dx = O(dx^p) as dx -> 0; at least p, but an empirical study above p + TOL is reported SUSPICIOUS, a gap, never a refutation | schemes | p: `claims.order_l1.combined` | gloss only |
| `converges_order_p_linf` | the global error in the max norm is O(dx^p) at fixed dt/dx, on the spec's smooth test problem | on the spec's test problem: max_i \|u_i - u(x_i)\| = O(dx^p) as dx -> 0; at least p, but an empirical study above p + TOL is reported SUSPICIOUS, a gap, never a refutation | schemes | p: `claims.order_linf.combined` | gloss only |
| `hyperbolic` | the system is strictly hyperbolic on the stated domain | for all q in the domain: df/dq has real, distinct eigenvalues | schemes | none | gloss only |
| `positive_depth_under_cfl` | the water depth h stays positive under the claimed CFL number (shallow water) | for all positive data and every step at which the CFL condition holds on every stencil: h_i^{n+1} > 0 | schemes | c: `claims.riemann.cfl` | gloss only |
| `converges_to_riemann_solution` | the scheme converges in L1 to the exact (entropy) Riemann solution | on the spec's Riemann data: \|\|u_dx - u_exact\|\|_L1 -> 0 as dx -> 0 at fixed dt/dx | schemes | none | gloss only |
| `stated_identity` | a formula the source prints (numerical entropy flux, entropy pair, viscosity coefficient Q, amplification factor g) satisfies the identity that defines it (scalar 1D laws) | for all states (and lam, nu, theta) in the stated domain with every denominator non-zero: LHS - RHS = 0, as a rational function (Laurent polynomial in z = e^{i theta} for g) | schemes | form: `claims.stated_identity.form`; eta: `claims.stated_identity.eta?`; q: `claims.stated_identity.q?`; entropy_flux: `claims.stated_identity.entropy_flux?`; dissipation: `claims.stated_identity.dissipation?`; Q: `claims.stated_identity.Q?`; g: `claims.stated_identity.g?`; let: `claims.stated_identity.let?`; domain: `claims.stated_identity.domain?` | gloss only |
| `del_equations` | the claimed update is the discrete Euler–Lagrange equations of L_d | for every triple (q_k, q_k+1, q_k+2) in D: DEL(L_d) = 0 iff the claimed update holds | variational | none | `del_verified_meaning` |
| `discrete_momentum_conserved` | J(q0, q1) is constant, exactly, along every solution of the DEL equations that stays in D (a Noether momentum or any other such J) | for every N and every discrete trajectory q_0..q_N+1 in D solving the DEL: J(q_N, q_N+1) = J(q_0, q_1) | variational | none | `dmomentum_meaning` |
| `update_conserves` | the explicit update map z' = Phi(z) conserves J exactly (for a straight-line kernel, Phi is exec prog, run by Lean: kernel_conserves_meaning) | for all z in D: J(Phi(z)) = J(z); so along every orbit in D, J(z_N) = J(z_0) | variational | none | `update_conserves_meaning` |
| `update_conserves_order_p` | the explicit update map (or kernel) conserves J to order at least p, per step: the drift of one step is O(h^{p+1}); nothing is claimed about orbits over a time T | for all z in D: J(Phi(z)) - J(z) = h^{p+1} R(z, h) with R a polynomial, so \|J(Phi(z)) - J(z)\| <= M h^{p+1} wherever \|R\| <= M (on every compact set some M works) | variational | p: `claims[].p` | `update_order_meaning` |
| `reconstruction_order_p` | a WENO-type reconstruction (or its conservative difference) is accurate to order at least p, in the stated regime (f' != 0, or a critical point of order n_cp) and for the stated eps = c dx^m | for every smooth f in the regime: reconstruction - exact value = O(dx^p) (form point), or the difference of the errors at x_{i+1/2} and x_{i-1/2}, over dx, = O(dx^p) (form flux_difference); at least p | reconstruction | p: `claims[].p`; form: `claims[].form?`; regime: `claims[].regime`; n_cp: `claims[].n_cp?`; eps: `claims[].eps?` | gloss only |
| `cell_average_max_principle` | one cell-average step fed by polynomials of degree <= k keeps the new average in [m, M] whenever the stated point values (or other linear functionals) of the polynomials lie in [m, M] | for every lam = dt/dx in the claimed range, all polynomials of degree <= k per cell and all m <= M: every hypothesis in [m, M] => the updated average in [m, M] | reconstruction | lam: `claims[].lam` | gloss only |
| `eno_sign_property` | the jump of an ENO interpolation of point values at x_{i+1/2} has the sign of w_{i+1} - w_i (weak form: zero allowed, and zero where the difference is zero) | for all real data w: (w^-_{i+1} - w^+_i)(w_{i+1} - w_i) >= 0, and w^-_{i+1} = w^+_i where w_{i+1} = w_i | reconstruction | none | gloss only |
| `eno_jump_ratio_at_most` | the jump of an ENO interpolation of point values is at most c times the jump of the data | for all real data w with w_{i+1} != w_i: (w^-_{i+1} - w^+_i) / (w_{i+1} - w_i) <= c | reconstruction | c: `claims[].c` | gloss only |
| `limiter_keeps_average` | the scaling limiter p~ = c + theta (p - c) keeps the cell average of a polynomial of degree <= k | for all polynomials p of degree <= k on the cell and all m <= M (c in [m, M] if assumed): avg(p~) = avg(p) | reconstruction | average_in_bounds: `claims[].average_in_bounds?` | gloss only |
| `limiter_bounds` | the scaling limiter puts p~ in [m, M] at the stated points (or on the whole cell) | for all polynomials p of degree <= k and all m <= M (ubar in [m, M] if assumed): m <= p~(y) <= M for every y in `on` | reconstruction | on: `claims[].on`; average_in_bounds: `claims[].average_in_bounds?` | gloss only |
| `limiter_accuracy` | the scaling limiter changes p by at most a constant times its overshoot of [m, M], so a (k+1)-th order accurate p stays (k+1)-th order accurate | there is C such that for all polynomials p of degree <= k and all m <= M (ubar in [m, M] if assumed): max_cell \|p~ - p\| <= C max_cell dist(p(y), [m, M]) | reconstruction | average_in_bounds: `claims[].average_in_bounds?` | gloss only |
| `conserved` | Q is constant along every solution of the Euler–Lagrange equations of L that stays in D | for every trajectory twice differentiable on an open interval, with jet in D and solving the EL equations there: Q is constant on that interval | conserved | none | `conserved_meaning` |
| `el_equations` | the claimed equations of motion are the Euler–Lagrange equations of L on D | for every trajectory twice differentiable at t with jet in D: the EL equations of L hold at t iff the claimed equations hold at t | derivation | none | `verified_meaning_at` |
| `dim_mismatch` | a law of the theory is not dimensionally homogeneous | the two sides of the law have different dimensions under the theory's symbol dimensions | theory | law: `args.law` | `Law.dimMismatch_refutes` |
| `law_vs_evidence` | a law of the theory fails everywhere in the box of a piece of evidence | for all values inside the evidence's hard bounds: the law does not hold | theory | law: `args.law`; evidence: `args.evidence` | gloss only |
| `orbit_excluded` | the central force law admits no orbit with a perihelion and an aphelion in the observed boxes | for every angular momentum and every radial trajectory: no local min of r in the perihelion box together with a local max in the aphelion box | theory | evidence: `args.evidence` | `EccentricExcluded.refutes` |
| `trajectory_vs_evidence` | no trajectory of the theory's dynamics from the evidence's initial box is inside the observed box at the observation time | for all initial states and parameters in the evidence box: the state at t_obs is outside the observed box (validated interval arithmetic, not Lean) | theory | evidence: `args.evidence` | gloss only |
<!-- claim-kinds:end -->

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
- Stated identities (`stated_identity`) are scalar only. Systems with matrix dissipation and
  vector entropy variables are out of scope, as are summed fully discrete identities and entropies
  outside the rational fragment (exp, log).
- The orbit check is deliberately weak. A 1/r³ force, the borderline case, is not rejected.
- Two steps are assumptions rather than Lean proofs: the radial equation of motion for a central
  force, and the translation from a theory file to the Lean expression. Both are listed on every
  result that depends on them.

## License

MIT
