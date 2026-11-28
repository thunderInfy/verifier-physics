"""The orbit tool's pre-filter (untrusted, but it should be exact): h(r) = r³ f(r) at aphelion < at
perihelion, in exact arithmetic for a rational force law."""
from pathlib import Path

from physverify import registry
from physverify.expr import parse
from physverify.theory import load_theory
from physverify.tools import orbit

ROOT = Path(__file__).resolve().parent.parent
EVIDENCE = registry.load(sorted((ROOT / "data").glob("**/*.json")))
ORBITS = [ev for ev in EVIDENCE if ev.extra.get("orbit")]


def proposed(name):
    return orbit.propose(load_theory(ROOT / "theories" / f"{name}.json"), EVIDENCE)


def test_inverse_cube_never_proposed():
    # K/r^3: h = K at every radius, so h(aphelion) < h(perihelion) never holds. In floats r^3 * K / r^3
    # is not always exactly K, and 3 of the 9 orbits got past the filter (Lean then rejected them).
    assert ORBITS
    assert proposed("inverse-cube-force") == []


def test_inverse_square_never_proposed():
    assert proposed("newton-gravity") == []


def test_inverse_fourth_proposed_on_every_orbit():
    assert len(proposed("inverse-fourth-force")) == len(ORBITS)


def test_exact_at_a_float_rounding_point():
    th = load_theory(ROOT / "theories" / "inverse-cube-force.json")
    rsym, _ = th.central_force
    x, y = 8.58, 20.82              # the float version of the filter let K/r^3 through here
    spec = (rsym, parse("K/r^3"), (x, x, y, y), {}, ["K"])
    assert not orbit._promising(th, spec)
    spec = (rsym, parse("K/r^4"), (x, x, y, y), {}, ["K"])
    assert orbit._promising(th, spec)
    spec = (rsym, parse("K/sqrt(r)^6"), (x, x, y, y), {}, ["K"])     # not rational: intervals, can't tell
    assert orbit._promising(th, spec)
