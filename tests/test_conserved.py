"""Fast tests for conserved-quantity claims (no Lean)."""
from fractions import Fraction
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parent.parent
CLAIMS = sorted((ROOT / "claims/conserved").glob("*.json"))


def _claims():
    from physverify.conserved import load_conserved
    return [load_conserved(p) for p in CLAIMS]


def test_benchmark_size_and_labels():
    cs = _claims()
    assert len(cs) >= 10
    labels = {(c.source["true"], c.expect) for c in cs}
    # (True, UNKNOWN): the degenerate Lagrangian, true but outside both certificate forms
    assert labels <= {(True, "VERIFIED"), (False, "REFUTED"), (None, "UNKNOWN"), (True, "UNKNOWN")}
    assert {c.expect for c in cs} == {"VERIFIED", "REFUTED", "UNKNOWN"}


def test_conserved_claims_are_not_eom_claims():
    """The EOM runner globs claims/*.json only; conserved claims live in claims/conserved/
    and carry `kind: conserved`, which the EOM loader's caller dispatches on."""
    import json

    from physverify.conserved import is_conserved
    assert all(is_conserved(json.loads(p.read_text())) for p in CLAIMS)
    assert not any(is_conserved(json.loads(p.read_text())) for p in (ROOT / "claims").glob("*.json"))


def test_quantity_may_not_use_accelerations():
    from physverify.conserved import load_conserved
    spec = {"kind": "conserved", "name": "x", "coordinates": ["x"],
            "symbols": {"x": {"dim": "L"}, "m": {"dim": "M"}}, "lagrangian": "m/2*x_dot^2",
            "domain": ["m > 0"], "quantity": "m*x_ddot"}
    with pytest.raises(ValueError, match="accelerations"):
        load_conserved(spec)
    with pytest.raises(ValueError, match="undeclared"):
        load_conserved({**spec, "quantity": "k*x"})
    load_conserved({**spec, "quantity": "m*x_dot"})


def test_python_dt_matches_numeric_derivative():
    """`dt_expr` (planner mirror of Lean's `dt`) against a finite difference along a curve."""
    import mpmath as mp

    from physverify.tools import conserved as P
    from physverify.tools.eulerlagrange import neval
    c = [c for c in _claims() if c.name == "Kepler Laplace-Runge-Lenz vector, x component"][0]
    dQ = P.dt_expr(c, c.quantity)
    params = {"m": mp.mpf(2), "GM": mp.mpf(3)}

    def jet(s):
        r, th = 1 + s / 3 + s ** 2, mp.mpf(1) / 2 + 2 * s - s ** 2 / 2
        return {**params, "r": r, "th": th, "r_dot": mp.mpf(1) / 3 + 2 * s, "th_dot": 2 - s,
                "r_ddot": mp.mpf(2), "th_ddot": mp.mpf(-1)}
    num = mp.diff(lambda s: neval(c.quantity, jet(s)), 0)
    assert abs(num - neval(dQ, jet(0))) < mp.mpf(10) ** -20


def test_planner_routes_true_and_false_claims():
    from physverify.tools import conserved as P
    for c in _claims():
        if c.expect == "UNKNOWN":       # ill-posed or degenerate: whatever it proposes, Lean must reject
            continue
        kinds = {k for k, _ in P.propose(c)}
        assert kinds == ({"verified"} if c.source["true"] else {"refuted"}), c.name


def test_multipliers_for_textbook_cases():
    from physverify.tools import conserved as P
    from physverify.tools.eulerlagrange import el_exprs, neval
    by = {c.name: c for c in _claims()}
    pt = {"th": Fraction(1, 3), "th_dot": Fraction(5), "m": Fraction(2), "l": Fraction(3),
          "g": Fraction(7), "r": Fraction(2), "r_dot": Fraction(3), "GM": Fraction(1)}
    (lam,) = P.multipliers(by["pendulum energy"], el_exprs(by["pendulum energy"]))
    assert neval(lam, pt) == 5                                  # λ = th_dot
    c = by["Kepler angular momentum"]
    assert [neval(x, pt) for x in P.multipliers(c, el_exprs(c))] == [0, 1]
    c = by["Kepler energy"]
    assert [neval(x, pt) for x in P.multipliers(c, el_exprs(c))] == [3, 5]   # (r_dot, th_dot)


def test_kinetic_momentum_refutation_is_an_exact_rational_jet():
    """The magnetic trap must be REFUTED at a rational jet on the EL surface, not merely
    lack a certificate: m x_ddot = qe B y_dot and m y_ddot = -qe B x_dot, with y_dot != 0."""
    import random

    from physverify.tools import conserved as P
    from physverify.tools.eulerlagrange import el_exprs, qeval
    c = [c for c in _claims() if c.name.endswith("kinetic x momentum")][0]
    els = el_exprs(c)
    kind, w = next(P.jets(c, els, random.Random(0)))
    assert kind == "exact" and all(isinstance(v, Fraction) for v in w.values())
    assert all(qeval(e, w) == 0 for e in els)                              # on the EL surface
    assert w["m"] * w["x_ddot"] == w["qe"] * w["B"] * w["y_dot"] != 0
    assert qeval(P.dt_expr(c, c.quantity), w) == w["m"] * w["x_ddot"]      # dQ/dt = m x_ddot
    ((k, tac),) = P.propose(c)
    assert k == "refuted" and "Expr.eval (fun" not in tac                   # no symbolic q̈


def test_failed_certificates_give_unknown_never_refuted():
    from physverify.conserved import UNKNOWN, judge
    from physverify.lean_backend import LeanResult
    from physverify.tools import conserved as P
    for c in _claims():
        r = judge(c, P.propose(c), check=lambda s, p, **kw: LeanResult(False, set(), "no"))
        assert r.verdict == UNKNOWN
        assert judge(c, []).verdict == UNKNOWN


def test_judge_statement_is_independent_of_planner():
    from physverify.conserved import load_conserved, statement
    c = load_conserved(ROOT / "claims/conserved/pendulum-energy.json")
    s = statement("verified", c)
    assert "∃ lams : List Expr, lams.length = 1 ∧ (∀ l ∈ lams, NoAccel 1 l) ∧ ConservedVerified 1 " in s
    assert "DomainForm 1 " in s and "NoAccel 1 " in s
    r = statement("refuted", c)
    assert r.startswith("NoAccel 1 ") and "ConservedRefuted 1 " in r


def test_ill_posed_claim_has_junk_point_in_domain():
    """Q/l with l unconstrained: l = 0 is in D and Q divides by it (Lean's x/0 = 0)."""
    from physverify.conserved import load_conserved
    from physverify.tools import conserved as P
    c = load_conserved(ROOT / "claims/conserved/pendulum-energy-over-length.json")
    env = {"th": Fraction(0), "th_dot": Fraction(1), "th_ddot": Fraction(0), "g": Fraction(1),
           "l": Fraction(0), "m": Fraction(1)}
    assert not P.in_domain(c, env)
    assert P.in_domain(c, {**env, "l": Fraction(1)})
