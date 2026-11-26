"""Fast tests (no Lean)."""
from fractions import Fraction
from pathlib import Path

import pytest

from physverify import units
from physverify.core import Candidate
from physverify.expr import parse, to_str
from physverify.lean_backend import check
from physverify.theory import load_evidence, load_theory
from physverify.tools import algebra, enclosure

ROOT = Path(__file__).resolve().parent.parent
T, D = ROOT / "theories", ROOT / "data"


def test_parse_precedence_and_exponents():
    assert to_str(parse("4*pi^2*a^3/GM")) == "(((4 * (pi)^(2)) * (a)^(3)) / GM)"
    assert parse("x^(1/2)").kind == "rpow" and parse("x^(1/2)").q == Fraction(1, 2)
    assert parse("x^-2.1").q == Fraction(-21, 10)
    assert to_str(parse("-x^2")) == "-((x)^(2))"


def test_dimensions():
    ctx = {"G": units.parse_dim("L^3 M^-1 T^-2"), "m": units.parse_dim("M"), "r": units.parse_dim("L")}
    assert units.dim_of(parse("G*m/r^2"), ctx) == units.parse_dim("L T^-2")
    with pytest.raises(units.DimError):
        units.dim_of(parse("m + r"), ctx)
    with pytest.raises(units.DimError):
        units.dim_of(parse("sin(r)"), ctx)
    assert units.dim_of(parse("sqrt(G*m/r)"), ctx) == units.parse_dim("L T^-1")


def test_sanitizer_blocks_environment_tricks():
    for bad in ["sorry", "native_decide", "set_option maxHeartbeats 0 in simp",
                "#exit", "@[simp] theorem x : True := trivial", "axiom x : False"]:
        r = check("True", bad)
        assert not r.ok and "sanitizer" in r.log


def test_interval_planner_finds_no_certificate_for_true_kepler():
    th = load_theory(T / "newton-gravity.json")
    evs = [load_evidence(p) for p in sorted(D.glob("kepler-*.json"))]
    assert len(evs) == 8 and algebra.propose(th, evs) == []


def test_interval_planner_refutes_wrong_constant_on_every_planet():
    th = load_theory(T / "kepler-wrong-factor.json")
    evs = [load_evidence(p) for p in sorted(D.glob("kepler-*.json"))]
    assert len(algebra.propose(th, evs)) == 8


def _enclosure_cert():
    th = load_theory(T / "pendulum-linear.json")
    ev = load_evidence(D / "synthetic/pendulum-90deg-SYNTHETIC.json")
    (c,) = enclosure.propose(th, [ev])
    return th, ev, c


def test_enclosure_certificate_replays():
    th, ev, c = _enclosure_cert()
    ok, _ = enclosure.check_certificate({"theory": th, "evidence": ev}, c.proof)
    assert ok


def test_enclosure_checker_rejects_tampered_boxes():
    th, ev, c = _enclosure_cert()
    cert = dict(c.proof)
    # shrink one a-priori box to a point: the Picard inclusion must fail
    b = dict(cert["boxes"][10])
    b["th"] = (b["th"][0], b["th"][0])
    cert["boxes"] = cert["boxes"][:10] + [b] + cert["boxes"][11:]
    ok, why = enclosure.check_certificate({"theory": th, "evidence": ev}, cert)
    assert not ok and "Picard" in why
    # wrong step count / step size
    ok, _ = enclosure.check_certificate({"theory": th, "evidence": ev},
                                        {"h": "1/100", "boxes": c.proof["boxes"]})
    assert not ok


def test_true_pendulum_has_no_enclosure_refutation():
    th = load_theory(T / "pendulum-nonlinear.json")
    ev = load_evidence(D / "synthetic/pendulum-90deg-SYNTHETIC.json")
    assert enclosure.propose(th, [ev]) == []


def test_enclosure_is_sound_on_true_dynamics():
    """Replaying any planner boxes for the TRUE dynamics must enclose the true value."""
    th = load_theory(T / "pendulum-nonlinear.json")
    ev = load_evidence(D / "synthetic/pendulum-90deg-SYNTHETIC.json")
    sys_, P, X0, obs, t_obs = enclosure._setup(th, ev)
    h = t_obs / 200
    boxes = enclosure._search(sys_, X0, P, h, 200, {})
    X = enclosure.replay(sys_, X0, P, h, boxes, {})
    true_theta = -1.40456839931977640201487143378  # mpmath odefun, g = 9.805, L = 1
    assert float(X["th"].a) <= true_theta <= float(X["th"].b)


def test_statistical_family_counts_whole_registry():
    from physverify import registry
    ev = registry.load([D / "sme-photon-kappa-em.json"])[0]   # passing one file must not shrink z
    assert ev.stat["K"] == registry.family_size("registry-2026") == 8
    lo, hi = ev.bounds["kappa_em_XY"]
    v, sg = ev.gauss["kappa_em_XY"]
    assert lo < v - 3 * sg and hi > v + 3 * sg                # z ≈ 3.23 at α = 0.01, K = 8


def test_stricter_alpha_widens_boxes():
    from fractions import Fraction
    from physverify import registry
    a = registry.load([D / "ppn-will2014.json"], Fraction(1, 100))[0].bounds["gamma"]
    b = registry.load([D / "ppn-will2014.json"], Fraction(1, 10000))[0].bounds["gamma"]
    assert b[0] < a[0] and b[1] > a[1]


def test_planner_on_ppn_and_sme():
    from physverify import registry
    from physverify.planner import plan
    ev = registry.load(sorted(D.glob("*.json")))
    expect = {"gr-ppn": 0, "brans-dicke-omega-ge-40000": 0, "photon-lorentz-invariant": 0,
              "brans-dicke-omega-le-1000": 1, "nordstrom-scalar": 1, "photon-anisotropic-1e-16": 1}
    for name, n in expect.items():
        cands = [c for c in plan(load_theory(T / f"{name}.json"), ev) if c.kind == "law_vs_evidence"]
        assert len(cands) == n, name


# ---------------------------------------------------------------- derivation claims

def _claims():
    from physverify.derivation import load_claim
    return [load_claim(p) for p in sorted((ROOT / "claims").glob("*.json"))]


def test_claims_load_and_layout():
    from physverify.derivation import load_claim
    c = load_claim(ROOT / "claims/kepler-polar.json")
    idx = c.index()
    assert [idx[s] for s in ("r", "th", "r_dot", "th_dot", "r_ddot", "th_ddot")] == list(range(6))
    assert idx["GM"] == 6 and idx["m"] == 7          # parameters from 3n, sorted
    assert c.dims["r_ddot"] == units.parse_dim("L T^-2")


def test_claim_dimension_mirror():
    from physverify.derivation import dims_ok, load_claim
    assert dims_ok(load_claim(ROOT / "claims/pendulum-rearranged.json"))[0]     # `= 0` is fine
    assert not dims_ok(load_claim(ROOT / "claims/pendulum-wrong-dimension.json"))[0]


def test_claim_rejects_acceleration_dependent_lagrangian():
    from physverify.derivation import load_claim
    spec = {"name": "x", "coordinates": ["x"], "symbols": {"x": {"dim": "L"}},
            "lagrangian": "x*x_ddot", "eom": [{"lhs": "x_ddot", "rhs": "0"}]}
    with pytest.raises(ValueError):
        load_claim(spec)


def test_planner_routes_true_and_false_claims():
    """Untrusted planner: certificate attempts for true claims, counterexamples for false."""
    from physverify.tools import eulerlagrange
    for c in _claims():
        kinds = {k for k, _ in eulerlagrange.propose(c)}
        assert kinds == ({"verified"} if c.source["true"] else {"refuted"}), c.name


def test_failed_certificates_give_unknown():
    from physverify.derivation import UNKNOWN, judge
    from physverify.lean_backend import LeanResult
    from physverify.tools import eulerlagrange
    for c in _claims()[:3]:
        r = judge(c, eulerlagrange.propose(c), check=lambda s, p, **kw: LeanResult(False, set(), "no"))
        assert r.verdict == UNKNOWN


def test_judge_statement_is_independent_of_planner():
    from physverify.derivation import load_claim, statement
    c = load_claim(ROOT / "claims/pendulum.json")
    s = statement("verified", c)
    assert s.startswith("dimsOK ") and "NoAccel 1 " in s and "Verified 1 " in s
    assert "Expr.eval env (.lit (0 : ℚ)) < Expr.eval env (.var 5)" in s   # domain m > 0
