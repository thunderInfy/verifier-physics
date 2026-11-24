"""Theory and evidence formats — the *judge-owned* semantic contract.

The planner may propose certificates, but it never edits these objects: every check
is stated against the theory exactly as submitted, so a tool cannot quietly swap in
an easier statement (cf. FormalScience's scalar-for-vector substitutions).

Theory JSON:
{
  "name": "...",
  "framework": "newtonian-mechanics",           # what the theory claims to be
  "symbols": {"GM": {"dim": "L^3 T^-2", "positive": true},   # every symbol + dimension
              "r0": {"dim": "L", "value": "149597870700"},      # exact theory constant
              "omega": {"dim": "1", "range": ["0", "1000"]}, ...},  # parameter range the theory claims
  "laws": [{"name": "kepler3", "lhs": "T^2", "rhs": "4*pi^2*a^3/GM"}],
  "central_force": {"r": "r", "f": "GM/r^2"},   # optional: attractive accel. magnitude f(r)
  "dynamics": {"time": "t", "state": {"th": "w", "w": "-(g/L)*sin(th)"}},  # optional
  "regime": {"th": [-0.1, 0.1]}                 # optional: where the theory claims validity
}

Evidence JSON, hard bounds:
{"id": "...", "source": "...", "kind": "hard_bounds",
 "quantities": {"T": {"dim": "T", "bounds": ["3.1558e7", "3.1559e7"]}, ...}}

Evidence JSON, statistical (compiled to a simultaneous box by `registry.py`):
{"id": "...", "source": "...", "kind": "gaussian", "family": "registry-2026",
 "quantities": {"gamma": {"dim": "1", "value": "1.000021", "sigma": "0.000023"}, ...}}
"""

from __future__ import annotations

import json
from dataclasses import dataclass, field
from fractions import Fraction
from pathlib import Path

from . import units
from .expr import E, parse, variables


@dataclass
class Law:
    name: str
    lhs: E
    rhs: E


@dataclass
class Theory:
    name: str
    framework: str
    dims: dict[str, units.Dim]
    laws: list[Law] = field(default_factory=list)
    central_force: tuple[str, E] | None = None  # (radius symbol, f(r))
    dynamics: tuple[str, dict[str, E]] | None = None  # (time symbol, {state: rhs})
    regime: dict[str, tuple[Fraction, Fraction]] = field(default_factory=dict)
    positive: set[str] = field(default_factory=set)  # symbols the theory asserts are > 0
    values: dict[str, Fraction] = field(default_factory=dict)  # exact constants fixed by the theory
    ranges: dict[str, tuple[Fraction, Fraction]] = field(default_factory=dict)  # claimed param ranges
    source: dict = field(default_factory=dict)

    def symbols(self) -> list[str]:
        return sorted(self.dims)


@dataclass
class Evidence:
    id: str
    source: str
    kind: str
    dims: dict[str, units.Dim]
    bounds: dict[str, tuple[Fraction, Fraction]]
    extra: dict = field(default_factory=dict)
    gauss: dict[str, tuple[Fraction, Fraction]] = field(default_factory=dict)  # value, sigma
    family: str = ""
    stat: dict = field(default_factory=dict)  # set by registry.compile: alpha, K, z

    @property
    def statistical(self) -> bool:
        return self.kind == "gaussian"


class Malformed(ValueError):
    """The input does not satisfy the contract. This is *not* a refutation."""


def _bounds(pair) -> tuple[Fraction, Fraction]:
    lo, hi = Fraction(str(pair[0])), Fraction(str(pair[1]))
    if lo > hi:
        raise Malformed(f"empty interval {pair}")
    return lo, hi


def load_theory(spec: dict | str | Path) -> Theory:
    if not isinstance(spec, dict):
        spec = json.loads(Path(spec).read_text())
    try:
        dims = {k: units.parse_dim(v["dim"]) for k, v in spec["symbols"].items()}
        laws = [Law(l["name"], parse(l["lhs"]), parse(l["rhs"])) for l in spec.get("laws", [])]
        cf = spec.get("central_force")
        central = (cf["r"], parse(cf["f"])) if cf else None
        dyn = spec.get("dynamics")
        dynamics = (dyn["time"], {k: parse(v) for k, v in dyn["state"].items()}) if dyn else None
        regime = {k: _bounds(v) for k, v in spec.get("regime", {}).items()}
    except (KeyError, ValueError) as ex:
        raise Malformed(f"theory {spec.get('name')!r}: {ex}") from ex
    positive = {k for k, v in spec["symbols"].items() if v.get("positive")}
    values = {k: Fraction(str(v["value"])) for k, v in spec["symbols"].items() if "value" in v}
    ranges = {k: _bounds(v["range"]) for k, v in spec["symbols"].items() if "range" in v}
    th = Theory(spec["name"], spec.get("framework", "unspecified"), dims, laws, central, dynamics,
                regime, positive, values, ranges, spec)
    _check_declared(th)
    return th


def _check_declared(th: Theory) -> None:
    used: set[str] = set()
    for l in th.laws:
        used |= variables(l.lhs) | variables(l.rhs)
    if th.central_force:
        used |= variables(th.central_force[1]) | {th.central_force[0]}
    if th.dynamics:
        t, rhs = th.dynamics
        used |= set(rhs) | {t}
        for e in rhs.values():
            used |= variables(e)
    missing = used - set(th.dims)
    if missing:
        raise Malformed(f"theory {th.name!r}: undeclared symbols {sorted(missing)}")


def load_evidence(spec: dict | str | Path) -> Evidence:
    if not isinstance(spec, dict):
        spec = json.loads(Path(spec).read_text())
    q = spec["quantities"]
    kind = spec.get("kind", "hard_bounds")
    gauss = {k: (Fraction(str(v["value"])), Fraction(str(v["sigma"])))
             for k, v in q.items() if "sigma" in v}
    if kind == "gaussian" and (not gauss or not spec.get("family")):
        raise Malformed(f"evidence {spec['id']}: gaussian evidence needs value/sigma and a family")
    return Evidence(
        id=spec["id"], source=spec.get("source", ""), kind=kind,
        dims={k: units.parse_dim(v["dim"]) for k, v in q.items()},
        bounds={k: _bounds(v["bounds"]) for k, v in q.items() if "bounds" in v},
        extra={k: v for k, v in spec.items() if k not in ("id", "source", "kind", "quantities")},
        gauss=gauss, family=spec.get("family", ""),
    )
