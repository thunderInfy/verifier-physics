"""Exact depth positivity for shallow water (systems.depth_positivity_exact): the induction step
h_j^n > 0 and lam*(|u_j| + sqrt(g h_j)) <= c on the stencil  =>  h_i^{n+1} > 0."""
import copy
import random
from fractions import Fraction
from pathlib import Path

import pytest

from physverify.schemes import checks, claims as C, load, poly as P, systems

S = Path(__file__).resolve().parent.parent / "schemes" / "systems"
LXF, RUS = "shallow-water-lax-friedrichs", "shallow-water-rusanov"


def _spec(name):
    return load(S / f"{name}.json")


def _with_update(h_update, name=LXF):
    spec = copy.deepcopy(_spec(name))
    spec["scheme"] = {"update": [h_update, "m0"]}
    return spec


def _sqrt(q: Fraction) -> Fraction:
    r = P._exact_sqrt(q)
    assert r is not None, q
    return r


def _depth_step(name, st, lam, g):
    """h_i^{n+1} written out by hand in Fractions, independent of the normal form."""
    h = {j: st[f"h{j}"] for j in systems.SLOTS}
    u = {j: st[f"m{j}"] / h[j] for j in systems.SLOTS}
    if name == LXF:
        return (h["m1"] + h["p1"]) / 2 - lam * (h["p1"] * u["p1"] - h["m1"] * u["m1"]) / 2
    a = {j: abs(u[j]) + _sqrt(g * h[j]) for j in systems.SLOTS}
    F = lambda l, r: (h[l] * u[l] + h[r] * u[r]) / 2 - max(a[l], a[r]) * (h[r] - h[l]) / 2
    return h["0"] - lam * (F("0", "p1") - F("m1", "0"))


@pytest.fixture(scope="module")
def claimed():
    return {n: systems.depth_positivity_exact(_spec(n)) for n in (LXF, RUS)}


@pytest.mark.parametrize("name", [LXF, RUS])
def test_verified_at_the_claimed_cfl(claimed, name):
    r = claimed[name]
    assert r["status"] == checks.VERIFIED and r["guarantee"] == checks.EXACT
    assert "9/10" in r["claim"] and any("h_j^n > 0" in a for a in r["assumptions"])


@pytest.mark.parametrize("name", [LXF, RUS])
def test_claim_level_verdict_and_no_inconsistency(name):
    rep = systems.check_all(_spec(name))
    v = C.judge(["positive_depth_under_cfl"], rep)[0]
    assert v["verdict"] == C.VERIFIED and v["guarantee"] == C.EXACT and v["decided_by"] == ["depth_positivity_exact"]
    assert {e["check"]: e["gives"] for e in v["evidence"]} == {"depth_positivity": C.NOT_REFUTED,
                                                                "depth_positivity_exact": C.VERIFIED}
    assert any("induction over n" in a for a in v["assumes"])


def test_lax_friedrichs_coefficients(claimed):
    (cell,) = claimed[LXF]["witness"]["cells"]
    assert cell["cell"] == []
    assert cell["coefficients"] == {"hm1": "1/2*w_m1 + 1/2", "h0": "0", "hp1": "-1/2*w_p1 + 1/2"}


def test_rusanov_needs_the_sign_cells(claimed):
    cells = claimed[RUS]["witness"]["cells"]
    assert len(cells) == 32 and all(len(c["cell"]) == 5 for c in cells)
    assert all("certificates" in c or "empty" in c for c in cells)


# ---------------------------------------------------------------- the sharp CFL range


@pytest.mark.parametrize("name", [LXF, RUS])
@pytest.mark.parametrize("c", ["1/2", "1"])
def test_verified_up_to_cfl_one(name, c):
    assert systems.depth_positivity_exact(_spec(name), c)["status"] == checks.VERIFIED


@pytest.mark.parametrize("name", [LXF, RUS])
@pytest.mark.parametrize("c", ["101/100", "1001/1000"])
def test_refuted_just_above_cfl_one(name, c):
    r = systems.depth_positivity_exact(_spec(name), c)
    assert r["status"] == checks.REFUTED
    hit = r["witness"]["counterexample"]
    st = {k: Fraction(v) for k, v in hit["state"].items()}
    lam, g = st["lam"], st["g"]
    assert g > 0 and lam > 0 and all(st[h] > 0 for h in systems.DEPTH)
    for j in systems.SLOTS:                                    # within the claimed CFL bound, recomputed here
        assert lam * (abs(st[f"m{j}"] / st[f"h{j}"]) + _sqrt(g * st[f"h{j}"])) <= Fraction(c)
    v = _depth_step(name, st, lam, g)
    assert v == Fraction(hit["h_i^{n+1}"]) and v <= 0


def test_refutation_is_exact_at_claim_level():
    r = systems.depth_positivity_exact(_spec(RUS), "101/100")
    v = C.judge(["positive_depth_under_cfl"], [r])[0]
    assert v["verdict"] == C.REFUTED and v["guarantee"] == C.EXACT


def test_draining_update_is_refuted_exactly():
    r = systems.depth_positivity_exact(_with_update("h0 - lam/10"))
    assert r["status"] == checks.REFUTED
    st = {k: Fraction(v) for k, v in r["witness"]["counterexample"]["state"].items()}
    assert st["h0"] - st["lam"] / 10 <= 0 < st["h0"]


def test_centred_depth_update_is_refuted():
    # forward-time centred: h_i^{n+1} = h_i - lam/2 (m_{i+1} - m_{i-1}) loses positivity at any CFL number
    assert systems.depth_positivity_exact(_with_update("h0 - lam*(mp1 - mm1)/2"))["status"] == checks.REFUTED


# ---------------------------------------------------------------- no circularity, wet/dry


def test_conclusion_is_never_assumed_positive():
    # sqrt(X)^2 = X needs X >= 0, i.e. h^{n+1} >= 0: only an assumption on h^{n+1} would admit it
    for upd in ("sqrt(h0 - 2*lam*m0)^2", "sqrt(hm1 - 3*lam*mp1)^2 + 0*h0"):
        r = systems.depth_positivity_exact(_with_update(upd))
        assert r["status"] == checks.UNKNOWN and "non-negative" in r["detail"], upd
    # |h0 - 2 lam m0| >= 0 can be 0, which the claim (h > 0) excludes
    r = systems.depth_positivity_exact(_with_update("sqrt((h0 - 2*lam*m0)^2)"))
    assert r["status"] != checks.VERIFIED


def test_a_variable_outside_step_n_is_not_admitted():
    r = systems.depth_positivity_exact(_with_update("hnext"))
    assert r["status"] == checks.UNKNOWN and "hnext" in r["detail"]


def test_positive_is_only_ever_step_n(monkeypatch):
    seen = []
    for f in ("from_expr", "nonneg_by_form", "positive_by_form"):
        orig = getattr(P, f)

        def spy(*a, _orig=orig, **k):
            seen.append(set(k.get("positive", ())))
            return _orig(*a, **k)
        monkeypatch.setattr(P, f, spy)
    assert systems.depth_positivity_exact(_spec(RUS))["status"] == checks.VERIFIED
    allowed = set(systems.STEP_N) | {"lam"}       # lam > 0 is part of the hypothesis (dt, dx > 0)
    assert seen and all(s <= allowed for s in seen), [s - allowed for s in seen if not s <= allowed]


@pytest.mark.parametrize("name", [LXF, RUS])
def test_wet_dry_is_not_applicable(name):
    spec = copy.deepcopy(_spec(name))
    spec["pde"]["domain"] = {}                    # h = 0 allowed: wet/dry states
    r = systems.depth_positivity_exact(spec)
    assert r["status"] == checks.NOT_APPLICABLE and "wet/dry" in r["detail"]
    assert C.judge(["positive_depth_under_cfl"], [r])[0]["verdict"] == C.UNKNOWN


def test_no_cfl_claimed_is_not_applicable():
    spec = copy.deepcopy(_spec(LXF))
    del spec["claims"]["riemann"]
    assert systems.depth_positivity_exact(spec)["status"] == checks.NOT_APPLICABLE


# ---------------------------------------------------------------- the LP behind the Farkas certificates


def test_lp_farkas_agrees_with_enumeration_on_nonempty_regions():
    rng = random.Random(1)

    def aff():
        p = P.const(rng.randint(-3, 3))
        for x in "xyz":
            p = P.add(p, P.scale(P.var(x), Fraction(rng.randint(-2, 2))))
        return p
    tried = 0
    for _ in range(300):
        atoms, p = [aff() for _ in range(rng.randint(2, 6))], aff()
        if systems._farkas_lp(P.const(-1), atoms):            # empty region: enumeration is not complete there
            continue
        tried += 1
        assert (checks.certify_farkas(p, atoms) is None) == (systems._farkas_lp(p, atoms) is None)
    assert tried > 100


def test_lp_certificate_replays():
    # an empty region: -1 = (-x + z - 2) + (2y - 2z + 3)/2 + (2x - 2y - 1)/2
    atoms = [P.add(P.add(P.scale(P.var("x"), -1), P.var("z")), P.const(-2)),
             P.add(P.add(P.scale(P.var("y"), 2), P.scale(P.var("z"), -2)), P.const(3)),
             P.add(P.add(P.scale(P.var("x"), 2), P.scale(P.var("y"), -2)), P.const(-1))]
    cert = systems._farkas_lp(P.const(-1), atoms)
    assert cert is not None
    total = P.const(Fraction(cert["remainder"]))
    for a in atoms:
        total = P.add(total, P.scale(a, Fraction(cert["multipliers"].get(P.show(a), "0"))))
    assert total == P.const(-1)
