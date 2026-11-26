"""Tests for systems (physverify/schemes/systems.py): shallow water as the first 2x2 system."""
import copy
from fractions import Fraction
from pathlib import Path

import numpy as np
import pytest

from physverify.expr import parse
from physverify.schemes import check, checks, claims as C, failed, load, poly as P, render, systems

ROOT = Path(__file__).resolve().parent.parent / "schemes"
S = ROOT / "systems"
EXPECTED = {
    "shallow-water-lax-friedrichs": {"hyperbolic": C.VERIFIED, "conservative": C.VERIFIED, "consistent": C.VERIFIED,
                                     "positive_depth_under_cfl": C.NOT_REFUTED,
                                     "converges_to_riemann_solution": C.NOT_REFUTED},
    "shallow-water-rusanov": {"hyperbolic": C.VERIFIED, "conservative": C.VERIFIED, "consistent": C.VERIFIED,
                              "positive_depth_under_cfl": C.NOT_REFUTED, "converges_to_riemann_solution": C.NOT_REFUTED},
    "broken-shallow-water-elliptic": {"hyperbolic": C.REFUTED, "conservative": C.VERIFIED, "consistent": C.VERIFIED},
    # the PDE is fine; the update of m is not in flux form. It is not in flux form, so it has no numerical flux to
    # check for consistency; it blows up past the CFL bound on the near-dry case, so the studies say nothing.
    "broken-shallow-water-nonconservative": {"hyperbolic": C.VERIFIED, "conservative": C.REFUTED,
                                             "consistent": C.UNKNOWN, "positive_depth_under_cfl": C.UNKNOWN,
                                             "converges_to_riemann_solution": C.UNKNOWN},
}


def _spec(name):
    return load(S / f"{name}.json")


@pytest.fixture(scope="module")
def reports():
    return {name: check(_spec(name)) for name in EXPECTED}


def test_spec_files_match_table():
    assert {p.stem for p in S.glob("*.json")} == set(EXPECTED)


@pytest.mark.parametrize("name", list(EXPECTED))
def test_verdicts(reports, name):
    got = {v["claim"]: v["verdict"] for v in reports[name]["claims"]}
    assert got == EXPECTED[name]
    assert C.INCONSISTENT not in got.values()
    render(_spec(name), reports[name])


def test_check_dispatches_systems():
    spec = _spec("broken-shallow-water-elliptic")
    rep = check(spec)
    assert [r["check"] for r in rep["checks"]] == ["hyperbolicity", "consistency", "conservation"]
    assert {v["claim"]: v["verdict"] for v in rep["claims"]}["hyperbolic"] == C.REFUTED


def test_exact_results_are_exact_and_studies_empirical(reports):
    for rep in reports.values():
        for v in rep["claims"]:
            if v["claim"] in ("positive_depth_under_cfl", "converges_to_riemann_solution"):
                assert v["guarantee"] in ("", C.EMPIRICAL)
            elif v["verdict"] in (C.VERIFIED, C.REFUTED):
                assert v["guarantee"] == C.EXACT


# ---------------------------------------------------------------- the scalar case is the 1-component case

@pytest.mark.parametrize("path", sorted(ROOT.glob("*.json")), ids=lambda p: p.stem)
def test_scalar_specs_agree_with_scalar_checks(path):
    spec = load(path)
    assert not systems.is_system(spec)
    for name in ("consistency", "conservation"):
        assert getattr(systems, name)(spec)["status"] == getattr(checks, name)(spec)["status"], name


# ---------------------------------------------------------------- hyperbolicity

def test_shallow_water_discriminant_is_4gh():
    r = systems.hyperbolicity(_spec("shallow-water-lax-friedrichs"))
    assert r["status"] == checks.VERIFIED
    assert r["witness"]["discriminant tr^2 - 4 det"] == "4*g*h"
    assert r["witness"]["eigenvalues (information only)"] == "(2*h^-1*m)/2 +- sqrt(g*h)"
    assert any("g > 0, h > 0" in a for a in r["assumptions"])


def test_elliptic_counterexample_replays():
    r = systems.hyperbolicity(_spec("broken-shallow-water-elliptic"))
    assert r["status"] == checks.REFUTED
    pt = {k: Fraction(v) for k, v in r["witness"]["point"].items()}
    assert pt["g"] > 0 and pt["h"] > 0
    disc = P.from_expr(parse(r["witness"]["discriminant tr^2 - 4 det"].replace("^-1", "^(-1)")))
    assert P.evaluate(disc, {"m": 0, **pt}) == Fraction(r["witness"]["discriminant_value"]) < 0


def test_hyperbolicity_needs_the_domain():
    # without h > 0 the discriminant 4 g h is not positive by form, and a point with h < 0 refutes it
    spec = copy.deepcopy(_spec("shallow-water-lax-friedrichs"))
    spec["pde"]["domain"] = {}
    r = systems.hyperbolicity(spec)
    assert r["status"] == checks.REFUTED and Fraction(r["witness"]["point"]["h"]) < 0


def test_hyperbolicity_limits():
    one = {"pde": {"state": ["u"], "flux": ["u^2/2"]}, "scheme": {"update": ["u0"]}}
    assert systems.hyperbolicity(one)["status"] == checks.VERIFIED
    three = {"pde": {"state": ["a", "b", "c"], "flux": ["b", "c", "a"]}, "scheme": {"update": ["a0", "b0", "c0"]}}
    r = systems.hyperbolicity(three)
    assert r["status"] == checks.UNKNOWN and "2x2" in r["detail"]
    # repeated eigenvalue: two decoupled advections at the same speed have A = 2 I, discriminant 0
    rep = {"pde": {"state": ["a", "b"], "flux": ["2*a", "2*b"]}, "scheme": {"update": ["a0", "b0"]}}
    r = systems.hyperbolicity(rep)
    assert r["status"] == checks.REFUTED and r["witness"]["discriminant_value"] == "0"


def test_positive_by_form():
    pos = {"g", "h"}
    assert P.positive_by_form(_p("4*g*h"), pos)
    assert P.positive_by_form(_p("g*h + m^2"), pos)
    assert not P.positive_by_form(_p("m^2"), pos)          # vanishes at m = 0
    assert not P.positive_by_form(_p("g*h - m^2"), pos)
    assert not P.positive_by_form(_p("4*g*h"), {"g"})


def _p(s):
    return P.from_expr(parse(s))


# ---------------------------------------------------------------- sqrt atoms over the domain (Rusanov)

def test_sqrt_of_gh_needs_declared_positivity():
    with pytest.raises(P.Undecided):
        P.from_expr(parse("sqrt(g*h)"))
    a = P.from_expr(parse("sqrt(g*h)"), positive={"g", "h"})
    assert P.mul(a, a) == _p("g*h")
    # an odd power of a variable not declared positive is still rejected
    with pytest.raises(P.Undecided):
        P.from_expr(parse("sqrt(g*m)"), positive={"g", "h"})


def test_rusanov_is_decided_only_on_the_domain():
    spec = _spec("shallow-water-rusanov")
    r = systems.consistency(spec)
    assert r["status"] == checks.VERIFIED
    assert any("sqrt(p)^2 = p" in a for a in r["assumptions"]) and any("h > 0" in a for a in r["assumptions"])
    no_domain = copy.deepcopy(spec)
    no_domain["pde"]["domain"] = {}
    for f in (systems.consistency, systems.conservation):
        out = f(no_domain)
        assert out["status"] == checks.UNKNOWN and "non-negative" in out["detail"]


# ---------------------------------------------------------------- conservation

def test_nonconservative_counterexample_replays():
    spec = _spec("broken-shallow-water-nonconservative")
    r = systems.conservation(spec)
    assert r["status"] == checks.REFUTED
    sys = systems.read(spec)
    Hs = [P.from_expr(h, positive=sys["positive"]) for h in sys["update"]]
    w = r["witness"]
    state = [{c: Fraction(v) for c, v in s.items()} for s in w["state"]]
    d = systems._periodic_change(Hs, sys, state, {"lam": Fraction(w["lam"]), "g": Fraction(w["g"])})
    assert d[0] == 0 and d[1] == Fraction(w["sum_change"]["m"]) != 0


def test_centred_product_rule_telescopes():
    # u0*(mp1 - mm1) + m0*(up1 - um1) = G(q0, qp1) - G(qm1, q0) with G(a, b) = u_a m_b + m_a u_b: a centred
    # quasi-linear discretisation can be in flux form, so the broken spec uses h0*((u^2)_{i+1} - (u^2)_{i-1}) instead
    spec = copy.deepcopy(_spec("broken-shallow-water-nonconservative"))
    spec["scheme"]["update"][1] = ("(mm1 + mp1)/2 - lam*(m0/h0*(mp1 - mm1) + m0*(mp1/hp1 - mm1/hm1) "
                                   "+ g*h0*(hp1 - hm1))/2")
    assert systems.conservation(spec)["status"] == checks.VERIFIED


def test_recovered_flux_is_the_declared_one():
    spec = _spec("shallow-water-lax-friedrichs")
    r = systems.conservation(spec)
    sys = systems.read(spec)
    for c, F in zip(sys["state"], sys["nf"]):
        got = P.from_expr(parse(r["witness"]["recovered_flux"][c].replace("^-1", "^(-1)")))
        assert P.add(got, P.from_expr(F), -1) == {}


# ---------------------------------------------------------------- exact Riemann solver

def test_stoker_star_state():
    hs, us = systems.star_state(2, 0, 1, 0, 1)
    # left rarefaction: u + 2c is constant; right shock: Rankine-Hugoniot for h and m
    assert us + 2 * np.sqrt(hs) == pytest.approx(2 * np.sqrt(2), abs=1e-12)
    s = us * hs / (hs - 1)
    assert hs * us * us + hs * hs / 2 - 1 / 2 == pytest.approx(s * hs * us, abs=1e-12)
    assert systems.star_state(1, -1.5, 1, 1.5, 1) == pytest.approx((1 / 16, 0), abs=1e-12)


@pytest.mark.parametrize("case,g", [((2, 0, 1, 0), 1.0), ((1, -1.5, 1, 1.5), 1.0), ((1, 0.5, 3, -0.2), 9.81)])
def test_exact_solution_conserves_mass_and_momentum(case, g):
    # totals on [0, 1] change only by the boundary fluxes while the waves are inside; a 1% error in a shock
    # speed would move them by ~1e-3, the midpoint rule across a jump by at most jump * dx / sub ~ 1e-4
    T, n = 0.05, 4000
    lo, hi = systems.wave_speeds(*case, g)
    assert 0 < 0.5 + lo * T and 0.5 + hi * T < 1
    h, m = systems.cell_averages(n, T, 0.5, case, g, sub=4)
    hL, uL, hR, uR = case
    flux = lambda hh, uu: (hh * uu, hh * uu * uu + g * hh * hh / 2)
    (aL, bL), (aR, bR) = flux(hL, uL), flux(hR, uR)
    assert np.sum(h) / n == pytest.approx((hL + hR) / 2 + T * (aL - aR), abs=1e-4)
    assert np.sum(m) / n == pytest.approx((hL * uL + hR * uR) / 2 + T * (bL - bR), abs=1e-4)


def test_dry_bed_is_rejected():
    with pytest.raises(ValueError):
        systems.star_state(1, -3, 1, 3, 1)


# ---------------------------------------------------------------- empirical studies

def test_two_dt_dx_per_case(reports):
    table = next(r for r in reports["shallow-water-lax-friedrichs"]["checks"] if r["check"] == "riemann_l1")["witness"]["table"]
    heads = [line for line in table if "dt/dx" in line]
    assert any("dam break, dt/dx = 2/5" in x for x in heads) and any("dam break, dt/dx = 37/100" in x for x in heads)
    assert len(heads) == 4


def test_positivity_refuted_by_a_draining_update():
    spec = copy.deepcopy(_spec("shallow-water-lax-friedrichs"))
    spec["scheme"] = {"update": ["h0 - lam/10", "m0"]}
    pos, _ = systems.riemann_studies(spec, (100, 200))
    assert pos["status"] == C.REFUTED_EMPIRICALLY
    assert C.judge(["positive_depth_under_cfl"], [pos])[0]["verdict"] == C.REFUTED_EMPIRICALLY


def test_studies_need_shallow_water():
    spec = copy.deepcopy(_spec("shallow-water-lax-friedrichs"))
    spec["pde"]["flux"] = ["m", "m^2/h + g*h^2"]
    assert {r["status"] for r in systems.riemann_studies(spec, (100,))} == {C.UNKNOWN}


def test_cli_exit_codes(reports):
    assert not failed(reports["shallow-water-lax-friedrichs"])
    assert failed(reports["broken-shallow-water-elliptic"]) == ["hyperbolic"]
    assert failed(reports["broken-shallow-water-nonconservative"]) == ["conservative"]
