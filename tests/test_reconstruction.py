"""The reconstruction layer (physverify/reconstruction.py): series arithmetic, the bench's
pre-committed verdicts, and every decisive verdict against plain exact evaluation of the formulas.
Fast: no Lean."""

import json
import random
from fractions import Fraction as F
from pathlib import Path

import pytest

from physverify import reconstruction as R
from physverify.expr import parse

BENCH = Path(__file__).resolve().parent.parent / "benchmark" / "reconstruction"
SPECS = {p.stem: json.loads(p.read_text()) for p in sorted(BENCH.glob("*.json"))}
CASES = [(name, i) for name, s in SPECS.items() for i in range(len(s["claims"]))]
RESULTS = {(name, i): r for name, s in SPECS.items() for i, r in enumerate(R.check(s)["claims"])}


def _L(c):
    e = c.get("eps")
    return F(str(e["m"])).denominator if isinstance(e, dict) else 1


# ---------------------------------------------------------------- series arithmetic

def test_primitive_coefficients_are_those_of_z_over_2_sinh():
    # (z/2)/sinh(z/2) = 1 - z^2/24 + 7 z^4/5760 - 31 z^6/967680 + ...
    assert R.primitive_coefficients(3) == [1, F(-1, 24), F(7, 5760), F(-31, 967680)]


def test_data_and_target_weights():
    assert [R.data_weight("cell_averages", 0, n) for n in range(4)] == [1, 0, F(1, 24), 0]
    assert R.data_weight("cell_averages", 1, 1) == 1          # average of y over [1/2, 3/2]
    assert R.data_weight("point_values", -2, 3) == F(-8, 6)
    # h(dx/2) = f + (dx/2) f' + (dx^2/8 - dx^2/24) f'' + ...
    assert R.target_weight("primitive", F(1, 2), 2) == F(1, 8) - F(1, 24)


def test_series_products_and_powers():
    nv, n = 1, 6
    one_plus_t = R.sconst(1, n, nv)
    one_plus_t[1] = {(0,): F(1)}
    cube = R.spow(one_plus_t, 3, n, nv)
    assert [c.get((0,), 0) for c in cube] == [1, 3, 3, 1, 0, 0]
    assert R.sshift(cube, 2, n)[2:] == cube[:4]


def test_beta_1_expansion_at_point_values():
    """beta_1 = (13/12)(v_-1 - 2v_0 + v_1)^2 + (1/4)(v_-1 - v_1)^2 = f1^2 dx^2 + (13/12 f2^2 + 1/3 f1 f3) dx^4 + O(dx^6)."""
    jet = R.Jet("point_values", "value", 1, 0, 7)
    b = R.to_series(parse("13/12*(vm1 - 2*v0 + vp1)^2 + 1/4*(vm1 - vp1)^2"), jet, 0, 7)
    mono = lambda **e: tuple(e.get(f"f{i}", 0) for i in range(jet.nv))
    assert b[:2] == [{}, {}] and b[3] == {} and b[5] == {}
    assert b[2] == {mono(f1=2): 1}
    assert b[4] == {mono(f2=2): F(13, 12), mono(f1=1, f3=1): F(1, 3)}


def test_positive_by_form():
    assert R.positive_by_form({(0, 0, 2): F(13, 12)}, 2)
    assert R.positive_by_form({(0, 0, 0): F(1), (0, 0, 2, 2): F(1)}, 2)
    assert not R.positive_by_form({(0, 0, 2, 2): F(1)}, 2)       # vanishes where f3 = 0
    assert not R.positive_by_form({(0, 1, 1): F(1)}, 2)
    assert not R.positive_by_form({}, 1)


def test_a_bad_spec_is_unknown_not_a_verdict():
    rec = SPECS["weno5-js-fd"]["reconstruction"]
    r = R.check_claim(rec, {"claim": "reconstruction_order_p", "p": 5, "regime": "critical"})
    assert r["verdict"] == R.UNKNOWN and "n_cp" in r["reason"]
    with pytest.raises(ValueError):
        R.decide(R.parse_reconstruction(rec), R.parse_claim({"p": 5, "regime": "generic"}))  # js without eps


# ---------------------------------------------------------------- the bench

@pytest.mark.parametrize("name,i", CASES)
def test_bench_verdicts_are_the_committed_expectations(name, i):
    c = SPECS[name]["claims"][i]
    assert RESULTS[name, i]["verdict"] == c["expect"], (c, RESULTS[name, i])


def test_henrick_aslam_powers_drop_and_its_eps_dependence():
    """The headline rows, by leading order: WENO5-JS difference at f' = 0 is 3 for eps = 0 or c dx^4,
    5 for eps = c dx^2 and for fixed eps; one reconstruction at the critical point stays 5."""
    lead = {(c["form"], c["regime"], c.get("n_cp"), json.dumps(c.get("eps"))): RESULTS["weno5-js-fd", i]["leading_order"]
            for i, c in enumerate(SPECS["weno5-js-fd"]["claims"])}
    assert lead["flux_difference", "critical", 1, '"0"'] == "3"
    assert lead["flux_difference", "critical", 1, '{"c": "1", "m": "4"}'] == "3"
    assert lead["flux_difference", "critical", 1, '{"c": "1", "m": "2"}'] == "5"
    assert lead["flux_difference", "critical", 1, '{"c": "1/1000000", "m": "0"}'] == "5"
    assert lead["point", "critical", 1, '"0"'] == "5"


def test_fractional_eps_exponent_uses_a_series_in_a_root_of_dx():
    rec = SPECS["weno5-js-fd"]["reconstruction"]
    c = {"claim": "reconstruction_order_p", "p": 3, "form": "flux_difference", "regime": "critical", "n_cp": 1,
         "eps": {"c": "1", "m": "7/2"}}
    r = R.check_claim(rec, c)
    assert r["verdict"] == R.VERIFIED
    assert any("dx^7/2" in a for a in r["assumptions"])     # eps dominates beta = O(dx^4)


# ---------------------------------------------------------------- against direct exact evaluation

REFUTED_CASES = [k for k in CASES if RESULTS[k]["verdict"] == R.REFUTED]


@pytest.mark.parametrize("name,i", REFUTED_CASES)
def test_refuted_witness_by_direct_evaluation(name, i):
    """E(dx)/dx^k -> the reported coefficient, for the reported jet (extended by arbitrary higher
    derivatives, which must not matter), with E evaluated from the formulas at rational dx."""
    rec, c, r = SPECS[name]["reconstruction"], SPECS[name]["claims"][i], RESULTS[name, i]
    jet = [F(v) for v in r["jet"].values()] + [F(1, 3), F(-1, 2), F(2), F(1), F(1, 5), F(-1)]
    k, coef, L = F(r["k"]), F(r["coefficient"]), _L(c)
    assert coef != 0 and k < c["p"]
    # a fixed eps = 1e-6 needs beta << eps before the asymptotics show, and WENO-Z at n_cp = 2 (tau and beta
    # of the same order at the shifted stencil) settles only near dx = 2^-13, so smaller dx there
    fixed_eps = isinstance(c.get("eps"), dict) and F(str(c["eps"]["m"])) == 0
    exps = (8, 12, 16) if fixed_eps or SPECS[name]["reconstruction"]["weights"]["kind"] == "z" else (5, 8, 11)
    gaps = [abs(R.direct_error(rec, c, jet, F(1, 2 ** a)) / F(1, 2 ** a) ** (L * k) - coef) for a in exps]
    assert gaps[0] > gaps[1] > gaps[2] and gaps[2] < abs(coef) / 10, (gaps, coef)


VERIFIED_EPS0 = [k for k in CASES if RESULTS[k]["verdict"] == R.VERIFIED
                 and SPECS[k[0]]["claims"][k[1]].get("eps", "0") == "0"]


def _jet_in_regime(c, rnd, size=11):
    ncp = c.get("n_cp", 0) if c["regime"] == "critical" else 0
    vals = [F(x) for x in (-2, -1, F(-1, 2), F(1, 3), 1, 2)]
    jet = [rnd.choice(vals) for _ in range(size)]
    for n in range(1, ncp + 1):
        jet[n] = F(0)
    return jet


@pytest.mark.parametrize("name,i", VERIFIED_EPS0)
def test_verified_with_eps_0_survives_sampled_jets(name, i):
    """A VERIFIED order p with eps = 0 never coexists with a sampled jet whose exact error falls
    off slower than dx^p: |E(dx)|/dx^p must not keep growing as dx halves (order p - 1 would
    double it each halving)."""
    rec, c = SPECS[name]["reconstruction"], SPECS[name]["claims"][i]
    rnd = random.Random(f"{name}:{i}")
    p = c["p"]
    # the mapped and Z weights have pre-asymptotic transients (a sign change of E near dx = 2^-7 for some
    # jets), so they are sampled further out
    exps = (7, 9, 11) if SPECS[name]["reconstruction"]["weights"]["kind"] in ("js", "linear") else (11, 13, 15)
    for _ in range(3):
        jet = _jet_in_regime(c, rnd)
        r = [abs(R.direct_error(rec, c, jet, F(1, 2 ** a))) * 2 ** (a * p) for a in exps]
        assert r[2] <= F(3, 2) * r[1] + F(1, 10 ** 6) and r[1] <= F(3, 2) * r[0] + F(1, 10 ** 6), (jet, r)


def test_original_measurement_is_fifth_order_where_f_prime_is_nonzero():
    """Found by the checker (not a pre-committed bench row; DEV_RESULTS.md §3): the r = 3 measurement (2.20)
    of Liu, Osher and Chan, eps -> 0, f' != 0, is fifth order, not only fourth as Jiang and Shu say on p. 7.
    Confirmed here by direct exact evaluation: E/dx^4 -> 0 and E/dx^5 settles, for two jets."""
    rec = json.loads((BENCH.parent / "outside/specs/jiang-shu-weno5-liu-fd.json").read_text())["reconstruction"]
    for form in ("point", "flux_difference"):
        c = {"claim": "reconstruction_order_p", "p": 5, "form": form, "regime": "generic", "eps": "0"}
        assert R.check_claim(rec, c)["leading_order"] == "5"
        assert R.check_claim(rec, {**c, "p": 6})["verdict"] == R.REFUTED
        for jet in ([F(0), F(1), F(1), F(1, 2), F(-1), F(2), F(1, 3), F(1)],
                    [F(1), F(-1, 2), F(3), F(-2), F(1), F(1, 2), F(-1), F(2)]):
            r5 = [R.direct_error(rec, c, jet, F(1, 2 ** a)) * 2 ** (5 * a) for a in (8, 10, 12)]
            assert abs(r5[2] - r5[1]) < abs(r5[1] - r5[0]) < abs(r5[1]) / 4, r5


def test_series_coefficients_match_direct_evaluation():
    """The leading coefficient of a VERIFIED row is also what direct evaluation converges to."""
    rec = SPECS["weno5-js-fd"]["reconstruction"]
    c = {"claim": "reconstruction_order_p", "p": 6, "form": "point", "regime": "critical", "n_cp": 1, "eps": "0"}
    r = R.check_claim(rec, c)
    assert r["verdict"] == R.REFUTED and r["k"] == "5"
    jet = [F(v) for v in r["jet"].values()] + [F(0)] * 4
    e = R.direct_error(rec, c, jet, F(1, 2 ** 12)) * 2 ** 60
    assert abs(e - F(r["coefficient"])) < abs(F(r["coefficient"])) / 100
