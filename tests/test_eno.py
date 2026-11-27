"""ENO sign property and jump bound (physverify/eno.py): the bench's pre-committed verdicts, Fourier–Motzkin on
small systems, and the VERIFIED claims against random data (a test oracle only; the verdicts do not sample).
Fast (about 2 s)."""

import json
import random
from fractions import Fraction as F
from pathlib import Path

import pytest

from physverify import eno, reconstruction

BENCH = Path(__file__).resolve().parent.parent / "benchmark" / "reconstruction" / "eno"
SPECS = {p.stem: json.loads(p.read_text()) for p in sorted(BENCH.glob("*.json"))}
CASES = [(name, i) for name, s in SPECS.items() for i in range(len(s["claims"]))]
RESULTS = {(name, i): r for name, s in SPECS.items() for i, r in enumerate(eno.check(s)["claims"])}


@pytest.mark.parametrize("name,i", CASES)
def test_bench_verdicts_are_the_committed_ones(name, i):
    assert RESULTS[name, i]["verdict"] == SPECS[name]["claims"][i]["expect"], RESULTS[name, i]


def test_reconstruction_layer_dispatches_here():
    s = SPECS["eno2-tie-left"]
    assert reconstruction.check_claim(s["reconstruction"], s["claims"][0])["verdict"] == "VERIFIED"


def test_fourier_motzkin_tracks_strictness():
    one = (F(1),)
    assert eno.fm_solve([(one, F(0), True), ((F(-1),), F(0), True)], 1) is None        # x > 0, x < 0
    assert eno.fm_solve([(one, F(0), False), ((F(-1),), F(0), False)], 1) == [0]       # x >= 0, x <= 0
    x = eno.fm_solve([((F(1), F(-1)), F(0), True), ((F(0), F(1)), F(1), False)], 2)     # x > y >= 1
    assert x[0] > x[1] >= 1
    assert eno.fm_max([((F(-1), F(-1)), F(-2), False), ((F(1), F(0)), F(0), False), ((F(0), F(1)), F(0), False)],
                      (F(1), F(0)), 2) == 2                                               # max x on x + y <= 2


def test_strict_sign_fails_on_linear_data():
    """Why the claim is the weak form: on linear data the ENO jump is 0 while the difference is not."""
    w = {j: F(j) for j in range(-2, 4)}
    wp, wm = eno.eno_values(w, 3, "eno", "left")
    assert wm - wp == 0 and w[1] - w[0] == 1


@pytest.mark.parametrize("k,tie", [(2, "left"), (2, "right"), (3, "left")])
def test_verified_claims_hold_on_random_data(k, tie):
    sup = F(eno.sup_ratio(k, "eno", tie))
    rnd = random.Random(k)
    for _ in range(2000):
        w = {j: F(rnd.choice([rnd.randint(-3, 3), rnd.randint(-40, 40)]), rnd.randint(1, 4)) for j in range(-k + 1, k + 1)}
        wp, wm = eno.eno_values(w, k, "eno", tie)
        J, D = wm - wp, w[1] - w[0]
        assert J * D >= 0 and (D != 0 or J == 0)
        if D:
            assert J / D <= sup


def test_refuting_data_are_reported_with_their_jump():
    for (name, i), r in RESULTS.items():
        if r["verdict"] == "REFUTED":
            rec = SPECS[name]["reconstruction"]
            w = {int(k[2:]): F(v) for k, v in r["data"].items()}
            wp, wm = eno.eno_values(w, rec["order"], rec["selection"], rec.get("tie", "left"))
            assert (str(wm - wp), str(w[1] - w[0])) == (r["jump"], r["difference"])


def test_sup_ratios():
    assert [eno.sup_ratio(1, "eno", "left"), eno.sup_ratio(2, "eno", "left"), eno.sup_ratio(3, "eno", "left")] == \
        ["1", "2", "7/2"]


def test_order_four_is_not_attempted():
    out = eno.check_claim({"order": 4, "selection": "eno"}, {"claim": "eno_sign_property"})
    assert out["verdict"] == "UNKNOWN"
