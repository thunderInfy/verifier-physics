"""Fast tests for the Lean certificates of `update_conserves_order_p` (no Lean): the remainder R
with J(Φ(z)) − J(z) = h^{p+1}·R, computed exactly, for every bench item in both forms (explicit
maps and straight-line kernels), and the REFUTED point with its non-zero h^k coefficient."""
import json
import random
from fractions import Fraction
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parent.parent
BENCH = sorted(p for d in ("benchmark/variational", "benchmark/kernels") for p in (ROOT / d).glob("*.json")
               if json.loads(p.read_text())["kind"] in ("update_map", "kernel")
               and any(c["claim"] == "update_conserves_order_p" for c in json.loads(p.read_text())["claims"]))


def _order_claims(path):
    from physverify.variational import judge_update_order, load
    U = load(path)
    return U, [(c, judge_update_order(U, c)) for c in U.claims if c.kind == "update_conserves_order_p"]


def _ids(p):
    return f"{p.parent.name}/{p.stem}"


def test_bench_covers_both_forms_and_both_verdicts():
    seen = set()
    for p in BENCH:
        _, rs = _order_claims(p)
        seen |= {(p.parent.name, r.verdict) for _, r in rs}
    assert {("variational", "VERIFIED"), ("variational", "REFUTED"),
            ("kernels", "VERIFIED"), ("kernels", "REFUTED")} <= seen


@pytest.mark.parametrize("path", BENCH, ids=_ids)
def test_drift_is_h_to_the_p_plus_1_times_R(path):
    """For every VERIFIED order claim, drift == h^{p+1}·R as polynomials (exactly), and R is a
    polynomial (so the Lean statement's `Expr.isPoly R` holds)."""
    from physverify.expr import to_lean
    from physverify.variational import (defect_expr, is_polynomial, p_add, p_mul, poly_expr, to_poly,
                                        update_order_remainder)
    U, rs = _order_claims(path)
    for c, r in rs:
        if r.verdict != "VERIFIED":
            continue
        R = update_order_remainder(U, c)
        assert is_polynomial(R)
        drift = to_poly(defect_expr(U, c), {})
        assert not p_add(drift, p_mul({(("h", c.p + 1),): Fraction(1)}, R), -1)
        assert to_poly(poly_expr(R), {}) == R        # the expression the statement prints
        assert "(.var " in to_lean(poly_expr(R), U.index()) or not R


@pytest.mark.parametrize("path", BENCH, ids=_ids)
def test_remainder_against_exact_runs(path):
    """drift = h^{p+1}·R at random rational points, with the step run exactly: for kernels by
    `kernel.run` (the assignments in order, as Lean's `exec`), not the composed map."""
    from physverify.expr import substitute
    from physverify.kernel import Kernel, qvalue, run
    from physverify.variational import p_eval, update_order_remainder
    U, rs = _order_claims(path)
    rng = random.Random(1)
    for c, r in rs:
        if r.verdict != "VERIFIED":
            continue
        R = update_order_remainder(U, c)
        for _ in range(5):
            env = {s: Fraction(rng.choice([-3, -2, -1, 1, 2, 3]), rng.randint(1, 4)) for s in U.declared}
            env["h"] = Fraction(rng.randint(1, 5), rng.randint(2, 7))
            if isinstance(U, Kernel):
                after = run(U.program, {**env, **{t: Fraction(0) for t in U.temps}})
            else:
                after = {**env, **{z: qvalue(e, env) for z, e in zip(U.state, U.phi)}}
            drift = qvalue(c.quantity, after) - qvalue(c.quantity, env)
            assert drift == env["h"] ** (c.p + 1) * p_eval(R, env)
            assert qvalue(substitute(c.quantity, U.new_state()), env) == qvalue(c.quantity, after)


@pytest.mark.parametrize("path", BENCH, ids=_ids)
def test_refuted_point_has_the_claimed_nonzero_coefficient(path):
    """For every REFUTED order claim the planner gives k ≤ p and a point in the h-free domain at
    which the h^k coefficient is non-zero and every lower one is zero; the drift at that point,
    run exactly with h := t, is t^k·S(t) for the S it prints."""
    from physverify.kernel import Kernel, qvalue, run
    from physverify.tools import variational as P
    from physverify.variational import p_eval, update_order_coeffs, update_order_remainder
    U, rs = _order_claims(path)
    for c, r in rs:
        if r.verdict != "REFUTED":
            continue
        with pytest.raises(ValueError):
            update_order_remainder(U, c)
        coeffs = update_order_coeffs(U, c)
        k = min(e for e in coeffs if coeffs[e][0])
        assert k <= c.p
        w = P.update_order_point(U, coeffs[k][0])
        assert w is not None and p_eval(coeffs[k][0], w) != 0
        assert all(qvalue(a, {**w, "h": Fraction(1, 2)}) > qvalue(b, {**w, "h": Fraction(1, 2)})
                   for op, a, b in U.domain)
        S = {e - k: p_eval(q[0], w) for e, q in coeffs.items() if e >= k}
        for t in (Fraction(1, 3), Fraction(1, 7), Fraction(2, 5)):
            env = {**w, "h": t}
            if isinstance(U, Kernel):
                after = run(U.program, {**env, **{x: Fraction(0) for x in U.temps}})
            else:
                after = {**env, **{z: qvalue(e, env) for z, e in zip(U.state, U.phi)}}
            drift = qvalue(c.quantity, after) - qvalue(c.quantity, env)
            assert drift == t ** k * sum(v * t ** j for j, v in S.items())
        kinds = [kind for kind, _ in P.propose(U, c)]
        assert kinds == ["refuted"]


@pytest.mark.parametrize("path", BENCH, ids=_ids)
def test_planner_offers_the_exact_polarity(path):
    from physverify.tools import variational as P
    U, rs = _order_claims(path)
    for c, r in rs:
        kinds = [kind for kind, _ in P.propose(U, c)]
        assert kinds == {"VERIFIED": ["verified"], "REFUTED": ["refuted"], "UNKNOWN": []}[r.verdict]


def test_replay_never_changes_the_verdict():
    """A Lean check that accepts everything, or nothing, only moves the label."""
    from physverify.lean_backend import LeanResult
    from physverify.tools import variational as P
    from physverify.variational import guarantee, judge
    U, rs = _order_claims(ROOT / "benchmark/variational/oscillator-symplectic-euler-map.json")
    for c, r0 in rs:
        cands = P.propose(U, c)
        yes = judge(U, c, cands, check=lambda s, p, module: LeanResult(True, {"propext"}, ""))
        no = judge(U, c, cands, check=lambda s, p, module: LeanResult(False, set(), "no"))
        assert yes.verdict == no.verdict == r0.verdict
        assert guarantee(c, yes) == "proven (Lean)" and "update_order" in yes.detail
        assert guarantee(c, no) == "exact (Python)" and no.detail == r0.detail
        # a certificate of the wrong polarity is never even checked
        flip = [("refuted" if k == "verified" else "verified", t) for k, t in cands]
        w = judge(U, c, flip, check=lambda s, p, module: LeanResult(True, {"propext"}, ""))
        assert w.verdict == r0.verdict and guarantee(c, w) == "exact (Python)"


def test_laurent_remainder_is_not_replayed():
    """R with a negative power of a state variable: exact Python still decides, but the planner
    offers nothing (the statement needs `Expr.isPoly R`)."""
    from physverify.tools import variational as P
    from physverify.variational import is_polynomial, judge_update_order, load_update, update_order_remainder
    U = load_update({"kind": "update_map", "name": "t", "state": ["q", "p"],
                     "symbols": {"q": {"dim": "L"}, "p": {"dim": "L"}},
                     "update": {"q": "q + h^2/p", "p": "p"}, "domain": ["p > 0"],
                     "claims": [{"claim": "update_conserves_order_p", "quantity": "q", "p": 1}]})
    c = U.claims[0]
    assert judge_update_order(U, c).verdict == "VERIFIED"
    assert not is_polynomial(update_order_remainder(U, c))
    assert P.propose(U, c) == []
