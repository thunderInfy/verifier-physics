"""Fast tests for variational-integrator claims (no Lean): claim format, statements, exact
order, and the rational points the refutations use."""
from fractions import Fraction
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parent.parent
BENCH = sorted((ROOT / "benchmark/variational").glob("*.json"))


def _bench():
    from physverify.variational import load_variational
    return [load_variational(p) for p in BENCH]


def _by_name():
    return {I.name: I for I in _bench()}


def _spec(**kw):
    spec = {"kind": "variational", "name": "t", "coordinates": ["x"],
            "symbols": {"x": {"dim": "L"}, "m": {"dim": "M"}},
            "discrete_lagrangian": "h*m/2*((x_1 - x_0)/h)^2", "lagrangian": "m/2*x_dot^2",
            "domain": ["m > 0"], "claims": [{"claim": "consistent_order_p", "p": 2}]}
    spec.update(kw)
    return spec


def test_bench_has_the_required_cases_and_labels():
    bs = _bench()
    claims = [(I, c) for I in bs for c in I.claims]
    assert len(claims) >= 15
    assert {c.kind for _, c in claims} == {"del_equations", "discrete_momentum_conserved",
                                           "consistent_order_p", "exact_order_p"}
    for I in bs:
        for raw, c in zip(I.source["claims"], I.claims):
            assert (raw["true"], c.expect) in {(True, "VERIFIED"), (False, "REFUTED"), (True, "UNKNOWN")}
    traps = [c for _, c in claims if c.why.startswith("TRAP")]
    assert {c.kind for c in traps} == {"del_equations", "discrete_momentum_conserved", "consistent_order_p",
                                       "exact_order_p"}


def test_loader_rejects_bad_claims():
    from physverify.variational import load_variational
    load_variational(_spec())
    with pytest.raises(ValueError, match="discrete Lagrangian"):
        load_variational(_spec(discrete_lagrangian="h*m/2*((x_2 - x_0)/h)^2"))
    with pytest.raises(ValueError, match="levels 0, 1"):
        load_variational(_spec(claims=[{"claim": "discrete_momentum_conserved", "quantity": "m*x_2"}]))
    with pytest.raises(ValueError, match="update"):
        load_variational(_spec(claims=[{"claim": "del_equations", "update": []}]))
    with pytest.raises(ValueError, match="continuous Lagrangian"):
        load_variational(_spec(lagrangian="m/2*x_1^2"))
    with pytest.raises(ValueError, match="unknown claim kind"):
        load_variational(_spec(claims=[{"claim": "energy"}]))


def test_h_positive_is_always_in_the_domain_and_the_layout():
    from physverify.variational import lean_terms, load_variational
    I = load_variational(_spec())
    assert [(op, repr(a), repr(b)) for op, a, b in I.domain] == [(">", "m", "0"), (">", "h", "0")]
    idx = I.index()
    assert (idx["x_0"], idx["x_1"], idx["x_2"], idx["h"], idx["m"]) == (0, 1, 2, 3, 4)
    assert "(.var 3)" in lean_terms(I)["D"]
    two = _by_name()["free particle in 2D"].index()
    assert [two[s] for s in ("x_0", "y_0", "x_1", "y_1", "x_2", "y_2", "h", "m")] == list(range(8))


def test_statements_parallel_the_continuous_ones():
    from physverify.variational import statement
    I = _by_name()["free particle in 2D"]
    c = I.claims[0]
    v, r = statement("verified", I, c), statement("refuted", I, c)
    assert "∃ mus : List Expr, mus.length = 2 ∧ DMomentumVerified 2" in v
    assert v.startswith("(Expr.dimOf") and "NoAccel 2" in v
    assert r.startswith("NoAccel 2") and "DMomentumRefuted 2" in r
    H = _by_name()["harmonic oscillator, midpoint rule"]
    assert "DELVerified 1" in statement("verified", H, H.claims[0])
    assert "DELRefuted 1" in statement("refuted", H, H.claims[0])


def test_python_del_matches_finite_differences():
    """`del_exprs` (Python mirror of Lean's DEL) against numerical partial derivatives."""
    import mpmath as mp

    from physverify.tools.eulerlagrange import neval
    from physverify.variational import del_exprs
    I = _by_name()["central quartic potential in 2D, trapezoidal rule"]
    env = {"m": mp.mpf(2), "k": mp.mpf(3), "a": mp.mpf(1) / 2, "h": mp.mpf(1) / 3,
           "x_0": mp.mpf("0.3"), "y_0": mp.mpf("-0.7"), "x_1": mp.mpf("0.5"), "y_1": mp.mpf("0.1"),
           "x_2": mp.mpf("-0.2"), "y_2": mp.mpf("0.9")}

    def ld(e, a, b):     # L_d(q_a, q_b)
        return neval(I.ld, {**e, "x_0": e[f"x_{a}"], "y_0": e[f"y_{a}"], "x_1": e[f"x_{b}"], "y_1": e[f"y_{b}"]})

    for k, q in enumerate(I.coords):
        d2 = mp.diff(lambda s: ld({**env, f"{q}_1": s}, 0, 1), env[f"{q}_1"])
        d1 = mp.diff(lambda s: ld({**env, f"{q}_1": s}, 1, 2), env[f"{q}_1"])
        assert abs(neval(del_exprs(I)[k], env) - (d2 + d1)) < mp.mpf(10) ** -20


def test_sign_convention_del_over_h_is_minus_el():
    """h^0 coefficient of (1/h)·DEL + EL vanishes for every bench integrator in the fragment."""
    from physverify.variational import NotPolynomial, truncation
    n = 0
    for I in _bench():
        if I.lagrangian is None:
            continue
        try:
            co = truncation(I, 1)
        except NotPolynomial:
            continue
        assert not any(co.get(0, [])) and all(not any(co[e]) for e in co if e < 0), I.name
        n += 1
    assert n >= 5


@pytest.mark.parametrize("path", BENCH, ids=lambda p: p.stem)
def test_order_verdicts(path):
    from physverify.variational import judge_order, load_variational
    I = load_variational(path)
    for c in I.claims:
        if c.kind in ("consistent_order_p", "exact_order_p"):
            r = judge_order(I, c)
            assert r.verdict == c.expect, (I.name, c.p, r.detail)
            if r.verdict != "UNKNOWN":
                assert r.detail.startswith("exact (Python)")


def test_order_coefficients_by_hand():
    """Midpoint oscillator: (1/h)DEL + EL = -h^2 (m x''''/12 + k x''/4) + O(h^4)."""
    from physverify.variational import truncation
    I = _by_name()["harmonic oscillator, midpoint rule"]
    co = truncation(I, 3)
    assert co[2][0] == {(("m", 1), ("x_d4", 1)): Fraction(-1, 12), (("k", 1), ("x_ddot", 1)): Fraction(-1, 4)}
    assert not any(co.get(1, [])) and not any(co.get(3, []))
    R = _by_name()["position-dependent mass, rectangle rule"]
    h1 = truncation(R, 1)[1][0]
    assert h1 == {(("a", -2), ("m", 1), ("x", 1), ("x_ddot", 1), ("x_dot", 1)): Fraction(3),
                  (("a", -2), ("m", 1), ("x_dot", 3)): Fraction(1)}


def test_empty_domain_is_never_verified():
    """No rational point in D: the judge does not attempt VERIFIED (the check is never called)."""
    from physverify.tools.variational import propose
    from physverify.variational import UNKNOWN, judge, load_variational
    I = load_variational(_spec(domain=["m > 0", "m < 0"],
                               claims=[{"claim": "discrete_momentum_conserved", "quantity": "m*(x_1 - x_0)/h"}]))
    calls = []
    r = judge(I, I.claims[0], [("verified", "trivial")], check=lambda *a, **k: calls.append(a))
    assert r.verdict == UNKNOWN and not calls and "no rational point" in r.detail
    assert propose(I, I.claims[0]) == []         # and the planner finds no sample point either


def test_order_at_least_versus_exact():
    """`consistent_order_p` is order at least p (as in the scheme layer); `exact_order_p` also
    needs the h^p coefficient not to vanish. The rectangle-rule DEL is exactly second order."""
    from physverify.variational import VClaim, judge_order
    I = _by_name()["harmonic oscillator, rectangle rule V(q0)"]
    want = {("consistent_order_p", 1): "VERIFIED", ("consistent_order_p", 2): "VERIFIED",
            ("consistent_order_p", 3): "REFUTED", ("exact_order_p", 1): "REFUTED",
            ("exact_order_p", 2): "VERIFIED", ("exact_order_p", 3): "REFUTED"}
    for (kind, p), v in want.items():
        r = judge_order(I, VClaim(kind, p=p))
        assert r.verdict == v, (kind, p, r.detail)
    r = judge_order(I, VClaim("exact_order_p", p=1))
    assert "vanishes" in r.detail and "at least 2" in r.detail
    r = judge_order(I, VClaim("consistent_order_p", p=3))      # the nonzero h^2 coefficient
    assert "the h^2 coefficient" in r.detail and "order 2 < 3" in r.detail


def test_order_outside_fragment_is_unknown():
    from physverify.variational import judge_order, load_variational
    I = load_variational(_spec(discrete_lagrangian="h*m/2*((x_1 - x_0)/h)^2 - h*m*cos(x_0/x_1)",
                               symbols={"x": {"dim": "1"}, "m": {"dim": "M L^2 T^-2"}},
                               lagrangian="m/2*x_dot^2 - m*cos(1)"))
    assert judge_order(I, I.claims[0]).verdict == "UNKNOWN"


@pytest.mark.parametrize("path", BENCH, ids=lambda p: p.stem)
def test_planner_routes_true_and_false_claims(path):
    from physverify.tools.variational import propose
    from physverify.variational import load_variational
    I = load_variational(path)
    for raw, c in zip(I.source["claims"], I.claims):
        if c.kind in ("consistent_order_p", "exact_order_p"):
            continue
        kinds = [k for k, _ in propose(I, c)]
        assert kinds == (["verified"] if raw["true"] else ["refuted"]), (I.name, c.kind)


def test_refutation_points_are_regular_trajectories():
    """The momentum counterexamples: DEL = 0 exactly, ∂DEL/∂q2 invertible, J changes."""
    from physverify.expr import substitute
    from physverify.tools import variational as P
    from physverify.tools.eulerlagrange import qeval
    from physverify.variational import del_exprs
    n = 0
    for I in _bench():
        for raw, c in zip(I.source["claims"], I.claims):
            if c.kind != "discrete_momentum_conserved" or raw["true"]:
                continue
            w = P.refutation_point(I, c)
            assert w is not None and w["h"] > 0
            assert all(qeval(d, w) == 0 for d in del_exprs(I))
            assert P.regular(I, del_exprs(I), w)
            assert qeval(substitute(c.quantity, I.shift()), w) != qeval(c.quantity, w)
            n += 1
    assert n >= 3


def test_noether_multiplier_is_minus_generator():
    """Rotation-invariant L_d: μ = −ξ(q1) = (y_1, −x_1)."""
    from physverify.tools import variational as P
    from physverify.tools.eulerlagrange import neval
    from physverify.variational import del_exprs
    I = _by_name()["central quartic potential in 2D, trapezoidal rule"]
    mus = P.multipliers(I, I.claims[0], del_exprs(I))
    env = {"m": Fraction(2), "k": Fraction(3), "a": Fraction(1), "h": Fraction(1, 2), "x_0": Fraction(1),
           "y_0": Fraction(2), "x_1": Fraction(3), "y_1": Fraction(-5), "x_2": Fraction(7), "y_2": Fraction(1)}
    assert [neval(m, env) for m in mus] == [-5, -3]


def test_corrupted_multiplier_breaks_the_identity():
    """Python side of the Lean test: a perturbed μ no longer satisfies the identity."""
    import random

    from physverify.expr import E, lit
    from physverify.tools import variational as P
    from physverify.variational import del_exprs
    I = _by_name()["free particle in 2D"]
    c, dels = I.claims[0], del_exprs(I)
    mus = P.multipliers(I, c, dels)
    assert P.looks_conserved(I, c, dels, mus, random.Random(0))
    bad = [E("add", (mus[0], lit(1))), mus[1]]
    assert not P.looks_conserved(I, c, dels, bad, random.Random(0))
