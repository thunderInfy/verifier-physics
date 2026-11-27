"""Bench rows for the `stated_identity` claim kind (physverify/schemes/identity.py). Each expected verdict
was fixed before the checker was run on the spec."""

from fractions import Fraction
from pathlib import Path

import pytest

from physverify.schemes import checks, claims as C, identity, load

S = Path(__file__).resolve().parent.parent / "schemes" / "identity"

EXPECTED = {
    # tecno:04's identity (3.3) with ^Q as transcribed (plus sign), and with the minus sign of Lemma 3.2
    "broken-entropy-balance-zero-flux-printed": C.REFUTED,
    "entropy-balance-zero-flux-corrected": C.VERIFIED,
    "broken-entropy-balance-burgers-printed": C.REFUTED,
    "entropy-balance-burgers-corrected": C.VERIFIED,
    "entropy-conservative-burgers": C.VERIFIED,
    "entropy-pair-burgers": C.VERIFIED,
    "broken-entropy-pair-burgers": C.REFUTED,
    "entropy-pair-burgers-exp": C.UNKNOWN,          # a true pair, but exp is outside the rational fragment
    "entropy-pair-burgers-log": C.UNKNOWN,          # a true pair (eta = u log u), but log is outside it too
    "viscosity-lax-friedrichs": C.VERIFIED,
    "broken-viscosity-lax-friedrichs": C.REFUTED,     # Q = lam*a^2 is Lax-Wendroff's
    "amplification-upwind": C.VERIFIED,
    "broken-amplification-upwind": C.REFUTED,
}


def _verdict(report):
    (v,) = report["claims"]
    return v


@pytest.mark.parametrize("name", EXPECTED)
def test_bench_row(name, checked):
    v = _verdict(checked(load(S / f"{name}.json")))
    assert v["verdict"] == EXPECTED[name], v
    if v["verdict"] in (C.VERIFIED, C.REFUTED):
        assert v["guarantee"].startswith("exact")


def test_every_spec_is_a_row():
    assert sorted(p.stem for p in S.glob("*.json")) == sorted(EXPECTED)


def _check(name, checked):
    return next(r for r in checked(load(S / f"{name}.json"))["checks"] if r["check"] == "stated_identity")


def test_tecno04_witness_and_residual(checked):
    """The item's own witness: f = 0, eta = u^2/2, D = 1, (u_{i-1}, u_i, u_{i+1}) = (0, 0, 1). The scheme gives
    dx * d/dt eta(u_i) = 0, the printed right side -(^Q_{i+1/2} - ^Q_{i-1/2}) + D-term = -1/2."""
    r = _check("broken-entropy-balance-zero-flux-printed", checked)
    assert r["witness"]["counterexample"] == {"point": {"u0": "0", "um1": "0", "up1": "1"}, "LHS - RHS": "1/2"}


def test_residual_is_the_sign_flip(checked):
    """Plus instead of minus adds v_bar*D*[v] = (uR^2 - uL^2)/2 to ^Q, so the residual is its difference across
    the cell, (up1^2 - 2 u0^2 + um1^2)/2, whatever the flux."""
    from physverify.expr import parse
    from physverify.schemes import poly as P
    want = P.show(P.from_expr(parse("(up1^2 - 2*u0^2 + um1^2)/2")))
    for spec in ("broken-entropy-balance-zero-flux-printed", "broken-entropy-balance-burgers-printed"):
        assert _check(spec, checked)["witness"]["residual LHS - RHS"] == want


@pytest.mark.parametrize("name", ["entropy-pair-burgers-exp", "entropy-pair-burgers-log"])
def test_unknown_names_its_reason(name, checked):
    r = _check(name, checked)
    assert r["status"] == C.UNKNOWN and "app" in r["detail"]


def test_amplification_witness_is_on_the_unit_circle(checked):
    w = _check("broken-amplification-upwind", checked)["witness"]["counterexample"]
    re, im = (Fraction(x.strip("()i ")) for x in w["z"].split(" + "))
    assert re * re + im * im == 1


def test_rational_handles_division_by_a_sum():
    from physverify.expr import parse
    from physverify.schemes import poly as P
    n, d = identity.rational(parse("1/(uL + uR) - 1/(uR + uL)"))
    assert not n and d
    n, d = identity.rational(parse("(uL^2 - uR^2)/(uL - uR)"))
    assert P.add(n, P.mul(P.from_expr(parse("uL + uR")), d), -1) == {}


def test_missing_block_is_not_applicable():
    spec = load(S / "entropy-pair-burgers.json")
    del spec["claims"]["stated_identity"]
    assert identity.stated_identity(spec)["status"] == checks.NOT_APPLICABLE
