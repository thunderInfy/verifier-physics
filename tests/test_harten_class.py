"""TVD claims about a class of schemes (physverify/schemes/harten_class.py): the flux or the limiter is a
variable. Every outcome of both kinds, the replay of certificates and counterexamples, and the example specs
in schemes/classes. No Lean (the class theorems are in lean/PhysVerify/Harten.lean)."""

from fractions import Fraction
from pathlib import Path

import pytest

from physverify import schemes
from physverify.claimkinds import KINDS
from physverify.schemes import harten_class as H

ROOT = Path(__file__).resolve().parent.parent
STANDARD = ["a_lo >= 0", "a_hi <= L1", "b_lo >= -L2", "b_hi <= 0", "lam >= 0", "lam*(L1 + L2) <= 1"]
SWEBY = [{"on": "(0, 1]", "lo": "0", "hi": "2*r"}, {"on": "[1, inf)", "lo": "0", "hi": "2"}]


def mono(*conditions):
    cfg = {"conditions": list(conditions)}
    return H.monotone_class({"claims": {"tvd_monotone_class": cfg}}), cfg


def lim(**cfg):
    return H.limiter_class({"claims": {"tvd_limiter_class": cfg}}), cfg


# ---------------------------------------------------------------- tvd_monotone_class

def test_monotone_class_verified_with_replayed_certificates():
    r, cfg = mono(*STANDARD)
    assert r["status"] == "VERIFIED" and r["guarantee"]
    certs = r["witness"]["farkas"]
    assert set(certs) == {lab for lab, _ in H.monotone_targets()}
    for label, cert in certs.items():
        assert H.replay_farkas(cfg, label, cert), label


def test_tampered_farkas_certificate_is_rejected():
    r, cfg = mono(*STANDARD)
    label = "lam * (a_hi - b_lo) <= 1"
    cert = r["witness"]["farkas"][label]
    k = next(iter(cert["multipliers"]))
    bad = {**cert, "multipliers": {**cert["multipliers"], k: str(Fraction(cert["multipliers"][k]) + 1)}}
    assert not H.replay_farkas(cfg, label, bad)
    assert not H.replay_farkas(cfg, label, {**cert, "remainder": str(Fraction(cert["remainder"]) + 1)})
    assert not H.replay_farkas(cfg, label, {**cert, "multipliers": {**cert["multipliers"], "lam >= 0 >= 0": "1"}})


def test_monotone_class_refuted_with_recomputed_counterexample():
    """Twice the CFL bound: a linear flux of the class raises TV in one step, recomputed from the witness."""
    r, cfg = mono(*STANDARD[:-1], "lam*(L1 + L2) <= 2")
    assert r["status"] == "REFUTED"
    ce = r["witness"]["counterexample"]
    assert H.replay_counterexample(ce, "monotone")
    x = {k: Fraction(v) for k, v in ce["parameters"].items()}
    assert all(H._holds(*H.parse_condition(t), x) for t in cfg["conditions"])
    assert x["lam"] * (x["a_hi"] - x["b_lo"]) > 1
    assert not H.replay_counterexample({**ce, "p": str(x["a_hi"] + 1)}, "monotone")      # p outside the bounds
    assert not H.replay_counterexample({**ce, "v": ce["u"]}, "monotone")


def test_monotone_class_negative_lower_bound_refuted():
    r, _ = mono("a_lo >= -1", "a_hi <= 1", "b_lo >= -1", "b_hi <= 0", "lam = 1/4")
    assert r["status"] == "REFUTED" and "lam * a_lo >= 0" in r["detail"]
    assert H.replay_counterexample(r["witness"]["counterexample"], "monotone")


@pytest.mark.parametrize("conds,why", [
    ((), "no conditions"),
    (("lam*a_lo*b_hi >= 0",), "no exact counterexample"),
    (("a_lo >= 0", "a_lo <= -1"), "empty"),
    (("sqrt(lam) >= 0",), "sqrt"),
    (("a_lo/lam >= 0",), "not a polynomial"),
    (("lam >= 0 >= a_lo",), "one relation"),
])
def test_monotone_class_unknown(conds, why):
    r, _ = mono(*conds)
    assert r["status"] == "UNKNOWN" and why in r["detail"], r["detail"]


# ---------------------------------------------------------------- tvd_limiter_class

def test_sweby_region_verified_by_sturm_on_every_piece():
    r, _ = lim(pieces=SWEBY, zero_for_nonpositive_r=True, nu_max="1")
    assert r["status"] == "VERIFIED"
    sturm = r["witness"]["sturm"]
    assert len(sturm) == 8 and all("certificate" in c for c in sturm.values())


def test_van_leer_and_the_nu_dependent_region_verify():
    vl, _ = lim(pieces=[{"on": "(0, inf)", "lo": "2*r/(1 + r)", "hi": "2*r/(1 + r)"}], zero_for_nonpositive_r=True,
                nu_max="1")
    assert vl["status"] == "VERIFIED"
    # nu_max = 1/2: phi <= min(4r, 2) suffices (nu phi(r)/r <= 2 and phi <= 2)
    wide, _ = lim(pieces=[{"on": "(0, 1/2]", "lo": "0", "hi": "4*r"}, {"on": "[1/2, inf)", "lo": "0", "hi": "2"}],
                  zero_for_nonpositive_r=True, nu_max="1/2")
    assert wide["status"] == "VERIFIED"
    # the same class at nu_max = 1 is outside Sweby's region on (0, 1)
    assert lim(pieces=[{"on": "(0, 1/2]", "lo": "0", "hi": "4*r"}, {"on": "[1/2, inf)", "lo": "0", "hi": "2"}],
               zero_for_nonpositive_r=True, nu_max="1")[0]["status"] != "VERIFIED"


def test_limiter_class_refuted_with_recomputed_counterexample():
    r, cfg = lim(pieces=[{"on": "(0, 3/2]", "lo": "0", "hi": "2*r"}, {"on": "[3/2, inf)", "lo": "0", "hi": "3"}],
                 zero_for_nonpositive_r=True, nu_max="1")
    assert r["status"] == "REFUTED"
    ce = r["witness"]["counterexample"]
    assert H.replay_counterexample(ce, "limiter", cfg)
    assert Fraction(ce["TV(v)"]) > Fraction(ce["TV(u)"])
    # a value outside the class's bounds, or a different step, is rejected
    k = next(r for r, y in ce["phi at the ratios of the data"].items() if Fraction(y) > 2)
    assert not H.replay_counterexample({**ce, "phi at the ratios of the data": {
        **ce["phi at the ratios of the data"], k: "7"}}, "limiter", cfg)
    assert not H.replay_counterexample({**ce, "v": ce["u"]}, "limiter", cfg)


def test_limiter_unconstrained_on_negative_r_refuted():
    r, cfg = lim(pieces=SWEBY, nu_max="1")
    assert r["status"] == "REFUTED" and "r <= 0" in r["detail"]
    assert H.replay_counterexample(r["witness"]["counterexample"], "limiter", cfg)


def test_outside_sweby_but_not_refuted_is_unknown():
    """phi = 2 on r > 0 leaves Sweby's region on (0, 1) (phi > 2r); Sweby's region is only sufficient, and no
    counterexample is found, so UNKNOWN, never REFUTED."""
    r, _ = lim(pieces=[{"on": "(0, inf)", "lo": "0", "hi": "2"}], zero_for_nonpositive_r=True, nu_max="1")
    assert r["status"] == "UNKNOWN" and "sufficient, not necessary" in r["detail"]
    small, _ = lim(pieces=[{"on": "(0, inf)", "lo": "-1/100", "hi": "0"}], zero_for_nonpositive_r=True, nu_max="1")
    assert small["status"] == "UNKNOWN"


@pytest.mark.parametrize("cfg,why", [
    ({"pieces": [{"on": "(0 1]", "lo": "0"}], "nu_max": "1"}, "malformed"),
    ({"pieces": [{"on": "(0, 1]", "lo": "0", "slope": "1"}], "nu_max": "1"}, "malformed"),
    ({"pieces": [{"on": "(0, 1]", "hi": "r/(r - 1/2)"}], "nu_max": "1"}, "denominator"),
    ({"pieces": [{"on": "(0, 1]", "hi": "sin(r)"}], "nu_max": "1"}, "malformed"),
    ({"pieces": SWEBY}, "malformed"),
    ({"pieces": [{"on": "(0, 1]", "lo": "1", "hi": "0"}], "nu_max": "1"}, "empty"),
    ({"pieces": SWEBY, "zero_for_nonpositive_r": True, "nu_max": "0"}, "nu_max must be > 0"),
])
def test_limiter_class_malformed_or_empty_is_unknown(cfg, why):
    r, _ = lim(**cfg)
    assert r["status"] == "UNKNOWN" and why in r["detail"], r["detail"]


def test_nu_max_above_one_is_not_verified():
    r, _ = lim(pieces=[{"on": "(0, inf)", "lo": "0", "hi": "0"}], zero_for_nonpositive_r=True, nu_max="3/2")
    assert r["status"] == "REFUTED"           # upwind (phi = 0) at nu = 3/2
    assert H.replay_counterexample(r["witness"]["counterexample"], "limiter")


def test_unbounded_nonneg_and_cover():
    inf = H.INF
    assert H.nonneg_on([Fraction(-1), Fraction(0), Fraction(1)], (Fraction(1), True, inf, False))["nonneg"]
    out = H.nonneg_on([Fraction(1), Fraction(-1)], (Fraction(0), True, inf, False))
    assert not out["nonneg"] and U_ev([Fraction(1), Fraction(-1)], out["counterexample"]["x"]) < 0
    out = H.nonneg_on([Fraction(0), Fraction(1)], (inf, False, Fraction(1), True))
    assert not out["nonneg"] and out["counterexample"]["x"] < 0
    pos = (Fraction(0), False, inf, False)
    assert H._covered(pos, [H.parse_interval("(0, 1]"), H.parse_interval("[1, inf)")]) is None
    assert H._covered(pos, [H.parse_interval("(0, 1)"), H.parse_interval("(1, inf)")]) == 1
    assert H._covered(pos, [H.parse_interval("(0, 1]")]) is not None


def U_ev(p, x):
    from physverify.schemes import univariate
    return univariate.ev(p, x)


# ---------------------------------------------------------------- the example specs and the registry

EXPECTED = {"monotone-flux-class": "VERIFIED", "broken-monotone-flux-class-wide-cfl": "REFUTED",
            "sweby-region-class": "VERIFIED", "van-leer-limiter-class": "VERIFIED",
            "broken-limiter-class-above-2": "REFUTED"}


def test_example_specs():
    got = {p.stem: schemes.check(schemes.load(p))["claims"][0]["verdict"]
           for p in sorted((ROOT / "schemes/classes").glob("*.json"))}
    assert got == EXPECTED


def test_registry_meanings_are_the_lean_class_theorems():
    assert KINDS["tvd_monotone_class"]["meaning"] == H.LEAN_MONOTONE.rsplit(".", 1)[1]
    assert KINDS["tvd_limiter_class"]["meaning"] == H.LEAN_LIMITER.rsplit(".", 1)[1]
    lean = (ROOT / "lean/PhysVerify/Harten.lean").read_text()
    for name in (H.LEAN_MONOTONE, H.LEAN_LIMITER):
        assert f"theorem {name.rsplit('.', 1)[1]} " in lean


def test_posthoc_tvd_readings():
    """POST-HOC (benchmark/outside/posthoc_tvd.py): the three 'monotone => TVD' dev items read with
    tvd_monotone_class are VERIFIED as narrowed readings: MATCH without the narrowing rule, GAP with it."""
    import importlib.util
    s = importlib.util.spec_from_file_location("posthoc_tvd", ROOT / "benchmark/outside/posthoc_tvd.py")
    m = importlib.util.module_from_spec(s)
    s.loader.exec_module(m)
    rows = m.table()
    assert [r["id"] for r in rows] == ["mfa_oslo_notes:14", "harten_1982_highres:02", "barsukow_uzh_notes:09"]
    for r in rows:
        assert r["instance verdict"] == "VERIFIED" and r["sentence verdict (rule)"] == "NOT_REFUTED"
        assert set(r["score"].values()) == {"MATCH"} and set(r["score under the narrowing rule"].values()) == {"GAP"}
