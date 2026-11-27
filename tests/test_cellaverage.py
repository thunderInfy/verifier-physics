"""The cell-average maximum principle (physverify/cellaverage.py): the bench's pre-committed verdicts, every
REFUTED datum re-evaluated by plain substitution, and VERIFIED claims against random polynomial data (a test
oracle only; the verdicts do not sample). Fast."""

import json
import random
from fractions import Fraction as F
from pathlib import Path

import pytest

from physverify import cellaverage as CA, reconstruction
from physverify.expr import parse

BENCH = Path(__file__).resolve().parent.parent / "benchmark" / "reconstruction" / "cell-average"
SPECS = {p.stem: json.loads(p.read_text()) for p in sorted(BENCH.glob("*.json"))}
CASES = [(name, i) for name, s in SPECS.items() for i in range(len(s["claims"]))]
RESULTS = {(name, i): r for name, s in SPECS.items() for i, r in enumerate(CA.check(s)["claims"])}


def _eval(e, env):
    k, a = e.kind, e.args
    if k == "var": return env[e.name]
    if k == "lit": return F(e.q)
    if k == "neg": return -_eval(a[0], env)
    if k == "add": return _eval(a[0], env) + _eval(a[1], env)
    if k == "sub": return _eval(a[0], env) - _eval(a[1], env)
    if k == "mul": return _eval(a[0], env) * _eval(a[1], env)
    if k == "div": return _eval(a[0], env) / _eval(a[1], env)
    raise ValueError(k)


def _values(rec, polys):
    """The named values of the spec for polynomials {cell: [c_0, .., c_k]}, by direct evaluation."""
    out = {}
    for name, (cell, y) in rec["values"].items():
        c = polys[cell]
        if y == "avg":  # exact antiderivative over [-1/2, 1/2]
            out[name] = sum((cn * (F(1, 2) ** (n + 1) - F(-1, 2) ** (n + 1)) / (n + 1) for n, cn in enumerate(c)), F(0))
        else:
            out[name] = sum((cn * F(str(y)) ** n for n, cn in enumerate(c)), F(0))
    return out


def _update_and_hyps(rec, polys, lam):
    env = {**_values(rec, polys), "lam": F(lam)}
    return _eval(parse(rec["update"]), env), [_eval(parse(h), env) for h in rec["hypotheses"]]


@pytest.mark.parametrize("name,i", CASES)
def test_bench_verdicts_are_the_committed_ones(name, i):
    assert RESULTS[name, i]["verdict"] == SPECS[name]["claims"][i]["expect"], RESULTS[name, i]


def test_reconstruction_layer_dispatches_here():
    s = SPECS["gl-k2-lf-advection"]
    assert reconstruction.check_claim(s["reconstruction"], s["claims"][0])["verdict"] == "VERIFIED"


@pytest.mark.parametrize("name,i", [c for c in CASES if RESULTS[c]["verdict"] == "REFUTED"])
def test_refuting_data_break_the_claim_by_substitution(name, i):
    rec, r = SPECS[name]["reconstruction"], RESULTS[name, i]
    k = rec["degree"]
    polys = {}
    for cell, text in r["polynomials"].items():
        coeffs = [F(t.split("*")[0]) for t in text.split(" + ")]
        assert len(coeffs) == k + 1
        polys[int(cell)] = coeffs
    lam = F(r["lam"])
    lo, hi = (F(x) for x in SPECS[name]["claims"][i]["lam"])
    assert lo <= lam <= hi
    u, hs = _update_and_hyps(rec, polys, lam)
    assert all(0 <= h <= 1 for h in hs) and not 0 <= u <= 1


@pytest.mark.parametrize("name,i", [c for c in CASES if RESULTS[c]["verdict"] == "VERIFIED"])
def test_verified_claims_hold_on_random_polynomials(name, i):
    rec = SPECS[name]["reconstruction"]
    lo, hi = (F(x) for x in SPECS[name]["claims"][i]["lam"])
    rnd = random.Random(i)
    cells = sorted({w[0] for w in rec["values"].values()})
    for _ in range(200):
        polys = {c: [F(rnd.randint(-20, 20), rnd.randint(1, 5)) for _ in range(rec["degree"] + 1)] for c in cells}
        lam = lo + (hi - lo) * F(rnd.randint(0, 12), 12)
        u, hs = _update_and_hyps(rec, polys, lam)
        assert min(hs) <= u <= max(hs)


def test_average_functional_is_exact():
    # the average of y^n over [-1/2, 1/2]: 1, 0, 1/12, 0, 1/80
    assert CA.functional([0, "avg"], 4, [0]) == [1, 0, F(1, 12), 0, F(1, 80)]


def test_bad_specs_are_unknown():
    rec = dict(SPECS["gl-k2-lf-advection"]["reconstruction"])
    assert CA.check_claim({**rec, "update": "ubar*u0l"}, {"lam": ["0", "1"]})["verdict"] == "UNKNOWN"
    assert CA.check_claim({**rec, "update": "ubar + 1"}, {"lam": ["0", "1"]})["verdict"] == "UNKNOWN"
    # not consistent: the update is 2 on constant data
    out = CA.check_claim({**rec, "update": "2*ubar"}, {"lam": ["0", "1"]})
    assert out["verdict"] == "UNKNOWN" and "constant data" in out["reason"]
