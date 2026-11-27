"""Harten's form with general C, D (physverify/schemes/harten.py), without Lean: the class read off the
flux, the exact ranges of phi = L/q and xi = L/p, the two splits, and the verdicts they give. Every
certificate is checked here against the scheme's own formula on random rational data, independently
of the checker."""
import random
from fractions import Fraction as Fr
from pathlib import Path

import pytest

from physverify.schemes import check, checks, harten, limiters as L, linear, load

ROOT = Path(__file__).resolve().parent.parent
S = ROOT / "schemes" / "limiters"
OUT = ROOT / "benchmark" / "outside" / "specs"


def sweby(slope: str, cfl=("0", "1"), name="Sweby") -> dict:
    """F = uL + (1 - lam)/2 * slope (a = 1), the slope in uLL, uL, uR."""
    return {"name": name, "pde": {"flux": "a*u"}, "params": {"a": "1"},
            "scheme": {"numerical_flux": f"a*uL + a/2*(1 - a*lam)*({slope})"}, "claims": {"tvd_cfl": list(cfl)}}


VAN_LEER = ("((uR - uL)*abs(uL - uLL) + abs(uR - uL)*(uL - uLL))/(abs(uL - uLL) + abs(uR - uL))")
STEEP = "minmod(uR - uL, 3*(uL - uLL))"            # phi(r) = min(1, 3r) for r > 0: phi > 2r near 0


def cert(spec):
    return harten.certify(spec, *L._tvd_range(spec))


def step(spec, u, lam):
    """One periodic step evaluated from the spec's numerical flux (Fractions)."""
    return L._step(None, u, lam, checks.numerical_flux(spec))


def tv(u):
    return sum(abs(u[(i + 1) % len(u)] - u[i]) for i in range(len(u)))


def flux(spec, x, y, z, lam):
    return L.evaluate(checks.numerical_flux(spec), {"uLL": x, "uL": y, "uR": z, "lam": lam})


# ---------------------------------------------------------------- the Sweby limiters, upwind split

@pytest.mark.parametrize("spec,sup", [(load(S / "advection-minmod.json"), "1/2"), (load(S / "advection-superbee.json"), "1"),
                                      (sweby(VAN_LEER, name="van Leer"), "1")], ids=["minmod", "superbee", "van-leer"])
def test_sweby_limiters_are_verified_with_the_upwind_split(spec, sup):
    r = L.tvd_harten(spec)
    inc = r["witness"]["incremental_form"]
    assert r["status"] == checks.VERIFIED and inc["verified"] and inc["form"] == "upwind"
    assert inc["A(nu) = lam*alpha"] == "0" and inc["B(nu) = lam*beta"] == "nu + -nu^2"
    # L is the Sweby slope / 2 (G = (lam - lam^2) L / lam), so the ranges are those of phi/2 and phi/(2r):
    # minmod phi, phi/r in [0, 1]; superbee and van Leer [0, 2], the Sweby region's edges
    for fam in ("phi+", "phi-", "xi+", "xi-"):
        assert inc["ranges"][fam] == ["0", sup], (fam, inc["ranges"])


def test_van_leer_ranges_are_attained_only_in_the_limit():
    """phi(r) = 2r/(1 + r) approaches 2 as r -> infinity; the range's sup is that limit (closed bounds)."""
    spec = sweby(VAN_LEER, name="van Leer")
    inc = cert(spec)
    assert inc["verified"] and inc["interface cells"]["retained"] == 4
    phi = lambda r: (r + abs(r)) / (1 + abs(r))
    for r in (Fr(10 ** k) for k in range(1, 6)):
        q = Fr(1)
        val = flux(spec, -r * q, Fr(0), q, Fr(0)) * 2 / q        # lam = 0: F = uL + L_true / 2
        assert val == phi(r) < 2


def test_rational_extremum_inside_a_branch_is_found():
    """phi(r) = 2r/(1 + r^2) for r >= 0 (0 otherwise) has its maximum 1 inside the branch, at r = 1, and
    phi/r = 2/(1 + r^2) <= 2: inside the Sweby region. As a slope, L = (|p| q + p |q|) |q| / (p^2 + q^2)."""
    slope = "(abs(uL - uLL)*(uR - uL) + (uL - uLL)*abs(uR - uL))*abs(uR - uL)/((uL - uLL)^2 + (uR - uL)^2)"
    inc = cert(sweby(slope))
    assert inc["ranges"]["phi+"] == inc["ranges"]["phi-"] == ["0", "1/2"]     # phi/2: the critical point, not an end
    assert inc["ranges"]["xi+"] == ["0", "1"]
    assert inc["verified"]


def test_a_limiter_outside_the_sweby_region_is_not_verified_and_tv_increase_replays():
    spec = sweby(STEEP, name="steep")
    r = L.tvd_harten(spec)
    assert r["status"] == checks.UNKNOWN and not r["witness"]["incremental_form"]["verified"]
    assert r["witness"]["incremental_form"]["ranges"]["xi+"] == ["0", "3/2"]     # phi/r up to 3
    # the scheme really is not TVD there: a state found by a wider search than tv_increase's, replayed
    u = [Fr(x) for x in (6, 0, 0, 1, 6, 6)]
    v = step(spec, u, Fr(9, 10))
    assert tv(u) == 12 and tv(v) == Fr(1207, 100)
    t = L.tv_increase(spec)
    if t["status"] == checks.REFUTED:                         # a witness, replayed with the flux formula
        w = t["witness"]
        u = [Fr(x) for x in w["periodic state u^n"]]
        v = step(spec, u, Fr(w["lam"]))
        assert v == [Fr(x) for x in w["u^{n+1}"]] and tv(v) > tv(u)
    else:
        assert t["status"] == checks.UNKNOWN


def test_superbee_beyond_cfl_one_is_not_verified():
    r = cert(load(S / "broken-advection-superbee-wide-cfl.json"))
    assert not r["verified"] and "nu = 9/8" in r["tried"]["upwind"]


# ---------------------------------------------------------------- centred schemes, flux split

def test_centred_harten_q_scheme_is_verified_with_c_and_d_positive():
    """harten:05: F = (uL + uR)/2 - (nu^2 + 1/4)/(2 lam) (uR - uL). C = (Q - nu)/2, D = (Q + nu)/2 with
    Q = nu^2 + 1/4: both > 0 inside the range, C = 0 at nu = 1/2."""
    spec = load(OUT / "harten-q-quadratic-advection.json")
    r = L.tvd_harten(spec)
    inc = r["witness"]["incremental_form"]
    assert r["status"] == checks.VERIFIED and inc["form"] == "flux"
    assert inc["A(nu) = lam*alpha"] == "-1/8 + (1/2)*nu + (-1/2)*nu^2"         # -C = A = (nu - Q)/2
    assert linear.tvd_linear(spec)["status"] == checks.VERIFIED             # the two certificates agree
    assert inc["tried"]["upwind"].startswith("needs alpha = 0")
    rng = random.Random(1)
    for _ in range(200):
        nu = Fr(rng.randint(0, 433), 500)
        Q = nu * nu + Fr(1, 4)
        C, D = (Q - nu) / 2, (Q + nu) / 2
        assert C >= 0 and D >= 0 and C + D <= 1
        u = [Fr(rng.randint(-9, 9)) for _ in range(rng.choice((4, 5, 7)))]
        if nu:
            v = step(spec, u, nu)
            n = len(u)
            assert v == [u[i] + C * (u[(i + 1) % n] - u[i]) - D * (u[i] - u[i - 1]) for i in range(n)]
            assert tv(v) <= tv(u)


def test_lax_wendroff_in_flux_form_fails_both_splits():
    r = cert(load(S / "broken-advection-lw-flux-form-tvd.json"))
    assert not r["verified"]
    assert "needs alpha = 0" in r["tried"]["upwind"] and "C >= 0" in r["tried"]["flux"]


# ---------------------------------------------------------------- scope and the difference-zero identities

def test_out_of_class_fluxes_are_unknown_not_verdicts():
    four_point = {"name": "four-point", "pde": {"flux": "a*u"}, "params": {"a": "1"},
                  "scheme": {"numerical_flux": "a*uL + a/2*(1 - a*lam)*minmod(uR - uL, uRR - uR)"},
                  "claims": {"tvd_cfl": ["0", "1"]}}
    with pytest.raises(harten.OutOfScope):
        cert(four_point)
    leftward = {**four_point, "params": {"a": "-1"}, "scheme": {"numerical_flux": "a*uR"}, "claims": {"tvd_cfl": ["-1", "0"]}}
    with pytest.raises(harten.OutOfScope):
        cert(leftward)
    two_slopes = sweby("minmod(uR - uL, uL - uLL) + lam*(uR - uL - abs(uL - uLL))")
    with pytest.raises(harten.OutOfScope):
        cert(two_slopes)                                      # rank 2 over the powers of lam
    r = L.tvd_harten(four_point)
    assert r["status"] in (checks.VERIFIED, checks.UNKNOWN)  # the cell path may still decide; never REFUTED


def test_fromm_slope_breaks_the_upwind_difference_zero_identity():
    """Fromm's phi(r) = (1 + r)/2 has phi(0) != 0: G(0, q) != 0, so the upwind split is not even tried, and
    the scheme (not TVD) is not verified."""
    inc = cert(sweby("(uR - uLL)/2"))
    assert inc["G(p, 0) = 0"] and not inc["G(0, q) = 0"] or inc["tried"]["upwind"].startswith("needs alpha")
    assert not inc["verified"]


def test_verdicts_are_unchanged_on_the_limited_specs():
    """tvd_harten's status on every shipped spec with a TVD claim is what it was before general C, D
    (the cell path), except where the new certificate decides an UNKNOWN."""
    before = {"advection-minmod": checks.VERIFIED, "advection-superbee": checks.VERIFIED,
              "broken-advection-lw-flux-form-tvd": checks.UNKNOWN, "broken-advection-superbee-wide-cfl": checks.UNKNOWN}
    for name, status in before.items():
        assert L.tvd_harten(load(S / f"{name}.json"))["status"] == status, name


def test_upwind_split_coefficient_matches_the_scheme_on_random_data():
    """D_{i-1} = -(H - u_i)/(u_i - u_{i-1}) from the spec's own update lies in [0, 1] (the certificate's
    claim for the upwind split), for minmod, superbee and van Leer at nu in [0, 1]."""
    rng = random.Random(3)
    for spec in (load(S / "advection-minmod.json"), load(S / "advection-superbee.json"), sweby(VAN_LEER)):
        for _ in range(120):
            u = [Fr(rng.randint(-9, 9), rng.randint(1, 3)) for _ in range(rng.choice((5, 6, 8)))]
            nu = Fr(rng.randint(1, 20), 20)
            v = step(spec, u, nu)
            if v is None:                                     # van Leer's 0/0 at a flat pair
                continue
            for i in range(len(u)):
                d = u[i] - u[i - 1]
                if d:
                    assert 0 <= -(v[i] - u[i]) / d <= 1
            assert tv(v) <= tv(u)


def test_claim_verdicts_on_harten_q_are_unchanged(checked):
    spec = load(OUT / "harten-q-quadratic-advection.json")
    rep = checked(spec)
    v = {x["claim"]: x for x in rep["claims"]}
    assert v["tvd_under_cfl"]["verdict"] == "VERIFIED"
    assert set(v["tvd_under_cfl"]["decided_by"]) == {"tvd_harten", "tvd_linear"}
