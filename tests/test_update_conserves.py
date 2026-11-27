"""Fast tests for `update_conserves` claims on explicit update maps (no Lean): loader, step
composition, exact defects by hand, the bench routing, refutation points and the order check."""
import json
import random
from fractions import Fraction
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parent.parent
BENCH = sorted(p for p in (ROOT / "benchmark/variational").glob("*.json")
               if json.loads(p.read_text())["kind"] == "update_map")
QP = {"x": {"dim": "L"}, "y": {"dim": "L"}, "px": {"dim": "L T^-1"}, "py": {"dim": "L T^-1"},
      "k": {"dim": "L^-2 T^-2"}}


def _load(stem):
    from physverify.variational import load_update
    return load_update(ROOT / f"benchmark/variational/{stem}.json")


def _spec(**kw):
    spec = {"kind": "update_map", "name": "t", "state": ["q", "p"],
            "symbols": {"q": {"dim": "L"}, "p": {"dim": "L T^-1"}, "w": {"dim": "T^-1"}},
            "update": [{"p": "p - h*w^2*q"}, {"q": "q + h*p"}], "domain": ["w > 0"],
            "claims": [{"claim": "update_conserves", "quantity": "(p^2 + w^2*q^2)/2"}]}
    spec.update(kw)
    return spec


def _same(a, b) -> bool:
    """Two expressions are equal as rational functions."""
    from physverify.expr import E
    from physverify.variational import to_ratfn
    return not to_ratfn(E("sub", (a, b)))[0]


def test_bench_has_the_required_cases():
    names = {p.stem for p in BENCH}
    assert {"central-quartic-explicit-euler", "central-quartic-symplectic-euler", "central-quartic-verlet",
            "oscillator-symplectic-euler-map", "oscillator-implicit-midpoint-map"} <= names
    for p in BENCH:
        U = _load(p.stem)
        for raw, c in zip(U.source["claims"], U.claims):
            assert (raw["true"], c.expect) in {(True, "VERIFIED"), (False, "REFUTED"), (True, "UNKNOWN")}
    assert all(c.expect == "VERIFIED" for c in _load("central-quartic-symplectic-euler").claims[:1])


def test_loader_rejects_bad_claims():
    from physverify.variational import load_update
    load_update(_spec())
    with pytest.raises(ValueError, match="not state variables"):
        load_update(_spec(update=[{"w": "2*w"}]))
    with pytest.raises(ValueError, match="update may not mention"):
        load_update(_spec(update={"q": "q + h*v", "p": "p"}))
    with pytest.raises(ValueError, match="quantity may not mention"):
        load_update(_spec(claims=[{"claim": "update_conserves", "quantity": "q_1"}]))
    with pytest.raises(ValueError, match="unknown claim kind"):
        load_update(_spec(claims=[{"claim": "del_equations", "quantity": "q"}]))
    with pytest.raises(ValueError, match="at least 1"):
        load_update(_spec(claims=[{"claim": "update_conserves_order_p", "quantity": "q", "p": 0}]))
    with pytest.raises(ValueError, match="dimension T"):
        load_update(_spec(symbols={"q": {"dim": "L"}, "p": {"dim": "L T^-1"}, "w": {"dim": "T^-1"},
                                   "h": {"dim": "L"}}))
    with pytest.raises(ValueError, match="continuous"):
        load_update(_spec(domain=["1/w > 0"]))


def test_layout_and_h_positive():
    from physverify.variational import update_statement, update_terms
    U = _load("central-quartic-symplectic-euler")
    assert U.index() == {"x": 0, "y": 1, "px": 2, "py": 3, "h": 4, "k": 5}
    assert [(op, repr(a), repr(b)) for op, a, b in U.domain] == [(">", "k", "0"), (">", "h", "0")]
    assert "(.var 4)" in update_terms(U, U.claims[0])["D"]
    v, r = update_statement("verified", U, U.claims[0]), update_statement("refuted", U, U.claims[0])
    assert v.startswith("List.length ([") and ": List Expr) = 4 ∧" in v
    assert "UpdDims [" in v and "UpdateVerified ([" in v
    assert r.startswith("UpdateRefuted ([")


def test_steps_compose_as_sequential_code():
    """`compose_steps` against running the steps one after another on numbers (each step
    simultaneous, each reading what the previous one wrote)."""
    from physverify.tools.eulerlagrange import qeval
    rng = random.Random(1)
    for stem in ("central-quartic-symplectic-euler", "central-quartic-verlet", "central-quartic-explicit-euler"):
        U = _load(stem)
        raw = U.source["update"]
        raw = [raw] if isinstance(raw, dict) else raw
        from physverify.expr import parse
        for _ in range(5):
            env = {s: Fraction(rng.randint(-5, 5), rng.randint(1, 4)) for s in U.index()}
            env["h"] = abs(env["h"]) + 1
            cur = dict(env)
            for st in raw:
                cur.update({v: qeval(parse(rhs), cur) for v, rhs in st.items()})
            assert [qeval(e, env) for e in U.phi] == [cur[z] for z in U.state], stem


def test_maps_by_hand():
    """Φ for symplectic Euler and Störmer–Verlet, written out by hand."""
    from physverify.expr import parse
    U = _load("central-quartic-symplectic-euler")
    px1 = "(px - h*k*(x^2 + y^2)*x)"
    py1 = "(py - h*k*(x^2 + y^2)*y)"
    want = [f"x + h*{px1}", f"y + h*{py1}", px1, py1]
    assert all(_same(a, parse(b)) for a, b in zip(U.phi, want))
    V = _load("central-quartic-verlet")
    ph = ["(px - h/2*k*(x^2 + y^2)*x)", "(py - h/2*k*(x^2 + y^2)*y)"]
    x1, y1 = f"(x + h*{ph[0]})", f"(y + h*{ph[1]})"
    want = [x1, y1, f"{ph[0]} - h/2*k*({x1}^2 + {y1}^2)*{x1}", f"{ph[1]} - h/2*k*({x1}^2 + {y1}^2)*{y1}"]
    assert all(_same(a, parse(b)) for a, b in zip(V.phi, want))


def test_explicit_euler_defect_by_hand():
    """L(Φ(z)) − L(z) = −h² p × ∇V(q) = h² (py ∇V_x − px ∇V_y), ∇V = k |q|² q."""
    from physverify.expr import parse
    from physverify.variational import defect_expr
    U = _load("central-quartic-explicit-euler")
    want = parse("h^2*(py*k*(x^2 + y^2)*x - px*k*(x^2 + y^2)*y)")
    assert _same(defect_expr(U, U.claims[0]), want)


def test_oscillator_defects_by_hand():
    from physverify.expr import parse
    from physverify.variational import defect_expr, update_defect
    U = _load("oscillator-symplectic-euler-map")
    H, Hmod = U.claims[0], U.claims[1]
    want = parse("h^2*w^2*(p^2 - w^2*q^2)/2 - h^3*w^4*p*q + h^4*w^6*q^2/2")
    assert _same(defect_expr(U, H), want)
    assert not update_defect(U, Hmod)[0]
    M = _load("oscillator-implicit-midpoint-map")
    assert not update_defect(M, M.claims[0])[0]
    assert update_defect(M, M.claims[1])[0]


def test_implicit_midpoint_map_solves_the_midpoint_rule():
    """z' − z = h A (z + z')/2 with A = [[0, 1], [−w², 0]], exactly, at rational points."""
    from physverify.tools.eulerlagrange import qeval
    M = _load("oscillator-implicit-midpoint-map")
    rng = random.Random(2)
    for _ in range(10):
        env = {"q": Fraction(rng.randint(-9, 9), 3), "p": Fraction(rng.randint(-9, 9), 2),
               "w": Fraction(rng.randint(1, 9), 4), "h": Fraction(rng.randint(1, 9), 5)}
        q1, p1 = (qeval(e, env) for e in M.phi)
        q, p, w, h = env["q"], env["p"], env["w"], env["h"]
        assert q1 - q == h * (p + p1) / 2
        assert p1 - p == -h * w ** 2 * (q + q1) / 2


@pytest.mark.parametrize("path", BENCH, ids=lambda p: p.stem)
def test_exact_python_routes_every_claim_as_expected(path):
    """The exact decision behind the planner: defect numerator ≡ 0 for the true claims, a
    rational refutation point for the false ones; the order claims judged in exact Python."""
    from physverify.tools import variational as P
    from physverify.variational import ORDER_KINDS, judge_order, update_defect
    U = _load(path.stem)
    for c in U.claims:
        if c.kind in ORDER_KINDS:
            r = judge_order(U, c)
            assert r.verdict == c.expect, (c.kind, c.p, r.detail)
            if r.verdict != "UNKNOWN":
                assert r.detail.startswith("exact (Python)")
            continue
        zero = not update_defect(U, c)[0]
        assert zero == (c.expect == "VERIFIED"), c.quantity
        kinds = [k for k, _ in P.propose(U, c)]
        assert kinds == (["verified"] if zero else ["refuted"])


def test_refutation_points_are_in_the_domain_and_change_J():
    from physverify.expr import substitute
    from physverify.tools import variational as P
    from physverify.tools.eulerlagrange import phys_ok, qeval
    n = 0
    for p in BENCH:
        U = _load(p.stem)
        for c in U.claims:
            if c.kind != "update_conserves" or c.expect != "REFUTED":
                continue
            w = P.update_refutation_point(U, c)
            assert w is not None and w["h"] > 0 and all(qeval(a, w) > qeval(b, w) for op, a, b in U.domain)
            assert all(phys_ok(e, w) for e in U.phi)
            assert qeval(substitute(c.quantity, U.new_state()), w) != qeval(c.quantity, w)
            n += 1
    assert n >= 4


def test_corrupted_claim_sign_flip_is_refuted():
    """L = x py − y px with one sign flipped is not conserved by symplectic Euler; the exact
    defect is nonzero and the planner offers only a refutation, at a point that replays."""
    from physverify.expr import parse, substitute
    from physverify.tools import variational as P
    from physverify.tools.eulerlagrange import qeval
    from physverify.variational import VClaim, update_defect
    U = _load("central-quartic-symplectic-euler")
    good = U.claims[0]
    bad = VClaim("update_conserves", quantity=parse("x*py + y*px"))
    assert not update_defect(U, good)[0] and update_defect(U, bad)[0]
    assert [k for k, _ in P.propose(U, bad)] == ["refuted"]
    w = P.update_refutation_point(U, bad)
    assert qeval(substitute(bad.quantity, U.new_state()), w) != qeval(bad.quantity, w)


def test_order_semantics_is_at_least_p():
    """update_conserves_order_p p: J(Φ(z)) − J(z) = O(h^{p+1}). Exactly conserved J: every p."""
    from physverify.variational import VClaim, judge_update_order
    U = _load("oscillator-symplectic-euler-map")
    H = U.claims[0].quantity
    assert [judge_update_order(U, VClaim("update_conserves_order_p", quantity=H, p=p)).verdict
            for p in (1, 2, 3)] == ["VERIFIED", "REFUTED", "REFUTED"]
    r = judge_update_order(U, VClaim("update_conserves_order_p", quantity=U.claims[1].quantity, p=4))
    assert r.verdict == "VERIFIED" and "vanishes too" in r.detail


def test_dimension_mismatch_reported():
    from physverify.variational import load_update, update_dims_ok
    U = load_update(_spec(update={"q": "q + h*p", "p": "p - h*q"}))
    assert update_dims_ok(U, U.claims[0]).startswith("mismatch")
    U = load_update(_spec())
    assert update_dims_ok(U, U.claims[0]) == "ok"


def test_runner_loads_both_kinds():
    from physverify.variational import Integrator, UpdateMap, load
    kinds = {type(load(p)) for p in (ROOT / "benchmark/variational").glob("*.json")}
    assert kinds == {Integrator, UpdateMap}
