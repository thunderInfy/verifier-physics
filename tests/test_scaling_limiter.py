"""The scaling limiter (physverify/limiter.py): the bench's pre-committed verdicts, every REFUTED datum re-evaluated
by plain substitution (own extrema, own theta), and VERIFIED claims against random polynomial data whose critical
points are rational (a test oracle only; the verdicts do not sample). Fast."""

import json
import random
from fractions import Fraction as F
from pathlib import Path

import pytest

from physverify import limiter as LIM, reconstruction

BENCH = Path(__file__).resolve().parent.parent / "benchmark" / "reconstruction" / "limiter"
SPECS = {p.stem: json.loads(p.read_text()) for p in sorted(BENCH.glob("*.json"))}
CASES = [(name, i) for name, s in SPECS.items() for i in range(len(s["claims"]))]
RESULTS = {(name, i): r for name, s in SPECS.items() for i, r in enumerate(LIM.check(s)["claims"])}
H = F(1, 2)


def ev(p, y):
    return sum((a * y ** n for n, a in enumerate(p)), F(0))


def avg(p):  # exact antiderivative over [-1/2, 1/2]
    return sum((a * (H ** (n + 1) - (-H) ** (n + 1)) / (n + 1) for n, a in enumerate(p)), F(0))


def parse_poly(text):
    return [F(t.split("*")[0]) for t in text.split(" + ")]


def crit(p):
    """Rational roots of p' in (-1/2, 1/2), by trying the candidates a quadratic or linear p' can have."""
    d = [n * a for n, a in enumerate(p)][1:]
    while d and d[-1] == 0:
        d.pop()
    if len(d) <= 1:
        return []
    if len(d) == 2:
        r = -d[0] / d[1]
        return [r] if -H < r < H else []
    c0, c1, c2 = d
    disc = c1 * c1 - 4 * c2 * c0
    if disc < 0:
        return []
    s = float(disc) ** 0.5
    roots = []
    for r in ((-float(c1) + s) / (2 * float(c2)), (-float(c1) - s) / (2 * float(c2))):
        q = F(r).limit_denominator(10 ** 6)
        assert ev(d, q) == 0 or not -H < r < H, "an irrational extremum in a witness"
        if ev(d, q) == 0 and -H < q < H:
            roots.append(q)
    return roots


def extrema(p, S):
    pts = [-H, H] + crit(p) if S == "cell" else [F(y) for y in S]
    vals = [ev(p, y) for y in pts]
    return max(vals), min(vals)


def limit(rec, p, m, M):
    c = avg(p) if rec.get("center", "avg") == "avg" else ev(p, F(rec["center"]))
    Mx, mx = extrema(p, rec["extrema_over"])
    terms = [F(1)] if "1" in rec["theta"] else []
    if "upper" in rec["theta"] and Mx != c:
        terms.append(abs(M - c) / abs(Mx - c))
    if "lower" in rec["theta"] and mx != c:
        terms.append(abs(m - c) / abs(mx - c))
    th = min(terms) if terms else F(1)
    return [th * a for a in p], c * (1 - th), th, c  # p~ = th p + c (1 - th)


@pytest.mark.parametrize("name,i", CASES)
def test_bench_verdicts_are_the_committed_ones(name, i):
    assert RESULTS[name, i]["verdict"] == SPECS[name]["claims"][i]["expect"], RESULTS[name, i]


def test_reconstruction_layer_dispatches_here():
    s = SPECS["zs-cell-k2"]
    assert reconstruction.check_claim(s["reconstruction"], s["claims"][3])["verdict"] == "VERIFIED"
    assert set(LIM.CLAIMS) <= set(reconstruction.CLAIMS)


@pytest.mark.parametrize("name,i", [c for c in CASES if RESULTS[c]["verdict"] == "REFUTED"])
def test_refuting_data_break_the_claim_by_substitution(name, i):
    rec, claim, w = SPECS[name]["reconstruction"], SPECS[name]["claims"][i], RESULTS[name, i]["witness"]
    p, m, M = parse_poly(w["p"]), F(w["m"]), F(w["M"])
    assert len(p) == rec["degree"] + 1 and m <= M
    lin, const, th, c = limit(rec, p, m, M)
    pt = [a + (const if n == 0 else 0) for n, a in enumerate(lin)]
    assert th == F(w["theta"])
    if claim.get("average_in_bounds", True):
        assert m <= c <= M
    if claim["claim"] == "limiter_keeps_average":
        assert avg(pt) != avg(p)
    elif claim["claim"] == "limiter_bounds":
        y = F(w["y"])
        assert (claim["on"] == "cell" and -H <= y <= H) or y in [F(v) for v in claim["on"]]
        assert not m <= ev(pt, y) <= M
    else:  # accuracy: no overshoot, yet p~ != p
        Mx, mx = extrema(p, "cell")
        assert m <= mx and Mx <= M
        assert pt != p


def _random_poly(rnd, k):
    """A polynomial of degree <= k with rational critical points (so its extrema are exact)."""
    r = lambda: F(rnd.randint(-12, 12), rnd.randint(1, 8))
    a, b = r(), r()
    if k == 1:
        return [b, a]
    r1, r2 = F(rnd.randint(-6, 6), 8), F(rnd.randint(-6, 6), 8)
    if k == 2:
        return [b + a * r1 * r1, -2 * a * r1, a]
    return [b, 3 * a * r1 * r2, -F(3, 2) * a * (r1 + r2), a]


@pytest.mark.parametrize("name,i", [c for c in CASES if RESULTS[c]["verdict"] == "VERIFIED"])
def test_verified_claims_hold_on_random_polynomials(name, i):
    rec, claim, res = SPECS[name]["reconstruction"], SPECS[name]["claims"][i], RESULTS[name, i]
    k = rec["degree"]
    rnd = random.Random(i + 17 * k)
    for _ in range(150):
        p = _random_poly(rnd, k)
        u = avg(p)
        m, M = sorted((u + F(rnd.randint(-8, 8), 4), u + F(rnd.randint(-8, 8), 4)))
        if not claim.get("average_in_bounds", True):
            m, M = sorted((F(rnd.randint(-40, 40), 4), F(rnd.randint(-40, 40), 4)))
        elif not m <= u <= M:
            continue
        lin, const, th, c = limit(rec, p, m, M)
        pt = [a + (const if n == 0 else 0) for n, a in enumerate(lin)]
        if claim["claim"] == "limiter_keeps_average":
            assert avg(pt) == avg(p)
        elif claim["claim"] == "limiter_bounds":
            pts = [-H, H] + crit(p) if claim["on"] == "cell" else [F(y) for y in claim["on"]]
            assert all(m <= ev(pt, y) <= M for y in pts)
        else:
            Mx, mx = extrema(p, "cell")
            d = max(F(0), Mx - M, m - mx)
            diff = [x - y for x, y in zip(pt, p)]  # (th - 1)(p - c): extrema at the ends or critical points of p
            sup = max(abs(ev(diff, y)) for y in [-H, H] + crit(p))
            assert sup <= F(res["C"]) * d


def test_accuracy_constants():
    # k = 1: q = y has max |q| / max q = 1, and the bound is exact
    assert LIM.accuracy_constant(1)["K"] == 1
    # k = 2, 3: the moment certificate gives the supremum, attained by the witnesses 1/9 - (y - 1/6)^2 (max 1/9 at
    # 1/6, min -1/3 at -1/2) and 1/24 - y^2/2 - y^3 (max 1/24 at -1/2 and 0, min -5/24 at 1/2)
    for k, K, nc in ((2, 3, 5), (3, 5, 7)):
        r = LIM.accuracy_constant(k)
        assert r["K"] == r["lower"] == K and r["method"].startswith("moment certificate")
        assert r["newton_cotes_K"] == nc
    assert LIM.abs_max_ratio(LIM.LOWER_WITNESS[2]) == 3 and LIM.abs_max_ratio(LIM.LOWER_WITNESS[3]) == 5
    # the certificate fails just above the supremum (w slightly larger than 1/(K + 1))
    assert LIM._moment_certificate(2, F(1, 4) + F(1, 1000)) is None
    assert LIM._moment_certificate(3, F(1, 6) + F(1, 1000)) is None
    assert LIM.accuracy_constant(2)["weights"] == [F(1, 6), F(2, 3), F(1, 6)]  # Simpson


def test_dominated():
    assert LIM.dominated("cell", [F(-1, 2), F(1, 2)], 1)
    assert not LIM.dominated("cell", [F(-1, 2), F(0), F(1, 2)], 2)
    assert LIM.dominated([F(0)], [F(-1, 2), F(1, 2)], 1)
    assert not LIM.dominated([F(1, 4)], [F(-1, 2), F(0), F(1, 2)], 2)


def test_bad_specs_are_unknown():
    rec = SPECS["zs-cell-k2"]["reconstruction"]
    for bad in ({**rec, "theta": ["2"]}, {**rec, "extrema_over": ["1"]}, {**rec, "degree": -1}):
        assert LIM.check_claim(bad, {"claim": "limiter_accuracy"})["verdict"] == "UNKNOWN"
    assert LIM.check_claim(rec, {"claim": "limiter_bounds"})["verdict"] == "UNKNOWN"  # no `on`
