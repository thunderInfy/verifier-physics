"""Exact univariate nonnegativity on an interval (square-free decomposition + Sturm), its use in the
positivity check, and the linear TVD / local maximum principle equivalence. Every counterexample is
re-evaluated here from the polynomial or the scheme's own formula, independently of the checker."""
import random
from fractions import Fraction as Fr
from pathlib import Path

from physverify.schemes import check, checks, claims as C, limiters, linear, load, univariate as U

ROOT = Path(__file__).resolve().parent.parent
HALF = Fr(1, 2)


def decide(p, lo, hi):
    d = U.nonneg_on(p, lo, hi)
    if not d["nonneg"]:
        x, v = d["counterexample"]["x"], d["counterexample"]["p(x)"]
        assert U.ev(p, x) == v < 0 and Fr(lo) <= x <= Fr(hi)
    return d


def test_double_root_inside_is_nonnegative():
    d = decide(U.power([-HALF, 1], 2), 0, 1)
    assert d["nonneg"]
    cert = d["certificate"]
    assert cert["factors"] == [{"multiplicity": 2, "factor": "-1/2 + nu"}] and cert["odd_part"] == "1"
    assert cert["sturm_odd_part"]["roots in (lo, hi)"] == 0 and cert["p(sample)"] > 0
    # the Bernstein test on the whole interval cannot certify it
    assert min(checks.bernstein(U.power([-HALF, 1], 2), Fr(0), Fr(1))) < 0


def test_triple_root_inside_is_refuted_exactly():
    d = decide(U.power([-HALF, 1], 3), 0, 1)
    assert not d["nonneg"] and 0 < d["counterexample"]["x"] < HALF


def test_two_double_roots():
    p = U.mul([0, 0, 1], U.power([-2, 1], 2))           # x^2 (x - 2)^2
    assert decide(p, 0, 3)["nonneg"]
    assert not decide(U.add([], p, -1), 0, 3)["nonneg"]    # its negative


def test_positive_without_real_roots():
    assert decide([1, 0, 1], -5, 5)["nonneg"]            # x^2 + 1
    assert decide([3, -2, 1], -1, 4)["nonneg"]           # (x - 1)^2 + 2


def test_endpoint_roots_and_constants():
    assert decide([0, 1], 0, 1)["nonneg"]                # x on [0, 1]: root at lo
    assert decide([1, -1], 0, 1)["nonneg"]               # 1 - x: root at hi
    assert not decide([0, -1], 0, 1)["nonneg"]           # -x: zero at lo, negative inside
    assert decide([], 0, 1)["nonneg"] and decide([0, 0], -1, 1)["nonneg"]
    assert decide([Fr(2)], 0, 1)["nonneg"] and not decide([Fr(-1)], 0, 1)["nonneg"]
    assert decide([1, -1], 1, 1)["nonneg"] and not decide([-1, 1], 0, 0)["nonneg"]


def test_rational_root_of_the_odd_part():
    assert not decide(U.mul([-HALF, 1], [1, 0, 1]), 0, 1)["nonneg"]     # (x - 1/2)(x^2 + 1)
    assert not decide([-2, 0, 1], 0, 3)["nonneg"]                       # irrational root sqrt(2)


def test_squarefree_decomposition_multiplies_back():
    p = U.mul(U.mul(U.power([-1, 1], 3), U.power([2, 0, 1], 2)), [Fr(-3), Fr(1, 7)])
    c, fs = U.squarefree(p)
    assert sorted(i for i, _ in fs) == [1, 2, 3]
    q = [c]
    for i, f in fs:
        q = U.mul(q, U.power(f, i))
    assert q == U.trim(p)


def test_random_cross_check_against_sampling_and_bernstein():
    """On small random polynomials (products of random linear factors with random multiplicities):
    a VERIFIED never meets a negative value on a dense rational grid, and agrees with Bernstein
    wherever Bernstein certifies; a REFUTED comes with an exact negative value (checked in decide)."""
    rng = random.Random(48)
    seen = {True: 0, False: 0}
    for _ in range(300):
        p = [Fr(rng.choice((-3, -1, 1, 2)), rng.choice((1, 2, 3)))]
        for _ in range(rng.randint(0, 3)):
            root = Fr(rng.randint(-8, 8), rng.choice((2, 3, 4)))
            p = U.mul(p, U.power([-root, 1], rng.randint(1, 3)))
        if rng.random() < 0.3:
            p = U.mul(p, [Fr(rng.randint(1, 3)), 0, 1])                 # a factor with no real root
        lo = Fr(rng.randint(-6, 2), 2)
        hi = lo + Fr(rng.randint(1, 8), 2)
        d = decide(p, lo, hi)
        seen[d["nonneg"]] += 1
        grid = [lo + (hi - lo) * Fr(j, 240) for j in range(241)]
        if d["nonneg"]:
            assert all(U.ev(p, x) >= 0 for x in grid), U.show(p)
        if min(checks.bernstein(list(p), lo, hi)) >= 0:
            assert d["nonneg"], U.show(p)
        if any(U.ev(p, x) < 0 for x in grid):
            assert not d["nonneg"], U.show(p)
    assert seen[True] > 50 and seen[False] > 50


# ---------------------------------------------------------------- the checks that use it

def _report(path, tvd=None):
    spec = load(ROOT / path)
    if tvd is not None:
        spec["claims"] = {**spec.get("claims", {}), "tvd_cfl": tvd}
        spec["named_claims"] = list(dict.fromkeys(spec.get("named_claims", []) + ["tvd_under_cfl",
                                                                                 "local_max_principle_under_cfl"]))
    return spec, check(spec)


def _raw(rep, name):
    return next(r for r in rep["checks"] if r["check"] == name)


def _verdicts(rep):
    return {v["claim"]: v["verdict"] for v in rep["claims"]}


def test_harten_quadratic_viscosity_decides():
    spec, rep = _report("benchmark/outside/specs/harten-q-quadratic-advection.json")
    assert _verdicts(rep) == {"positive_under_cfl": C.VERIFIED, "tvd_under_cfl": C.VERIFIED}
    pos = _raw(rep, "positivity")
    assert list(pos["witness"]["exact_decision"]) == ["up1"]
    assert pos["witness"]["coefficients"]["up1"] and "lean" in pos["witness"]
    assert _raw(rep, "tvd_linear")["status"] == C.VERIFIED
    tvd = _raw(rep, "tvd_harten")                                  # the upwind split does not apply; the flux split does
    assert tvd["status"] == C.VERIFIED and tvd["witness"]["incremental_form"]["form"] == "flux"


def test_linear_tvd_lax_friedrichs_and_upwind():
    for path in ("schemes/advection-lax-friedrichs.json", "schemes/advection-upwind.json"):
        _, rep = _report(path, ["0", "1"])
        assert _raw(rep, "tvd_linear")["status"] == C.VERIFIED, path
        assert _raw(rep, "max_principle_linear")["status"] == C.VERIFIED, path
        v = _verdicts(rep)
        assert v["tvd_under_cfl"] == v["local_max_principle_under_cfl"] == C.VERIFIED, path


def test_linear_tvd_lax_wendroff_refuted_with_box_data():
    spec, rep = _report("schemes/advection-lax-wendroff.json", ["0", "1"])
    r = _raw(rep, "tvd_linear")
    assert r["status"] == C.REFUTED
    box = r["witness"]["counterexample"]
    nu, u = Fr(box["nu"]), [Fr(x) for x in box["periodic state u^n"]]
    assert 0 < nu < 1 and len(u) == 2 * box["stencil width w"]
    # replay with the scheme's own update, independently of the coefficient extraction
    v = limiters._step(checks.update(spec), u, Fr(box["lam"]), checks.numerical_flux(spec))
    tv0, tv1 = limiters.total_variation(u), limiters.total_variation(v)
    assert (str(tv0), str(tv1)) == (box["TV(u^n)"], box["TV(u^{n+1})"]) and tv1 > tv0
    # TV(u^{n+1}) = 2 sum_k |c_k(nu)| on the box data
    (_, c), _ = linear.coefficients(spec, "x", "x")
    assert tv1 == 2 * sum(abs(checks._horner(checks.nu_coefficients(p), nu)) for p in c.values())
    mp = _raw(rep, "max_principle_linear")
    assert mp["status"] == C.REFUTED and Fr(mp["witness"]["counterexample"]["u_i^{n+1}"]) < 0
    v = _verdicts(rep)
    assert v["tvd_under_cfl"] == v["local_max_principle_under_cfl"] == C.REFUTED


def test_linear_rows_stay_out_of_nonlinear_schemes():
    _, rep = _report("schemes/limiters/advection-minmod.json")
    assert _raw(rep, "tvd_linear")["status"] == checks.NOT_APPLICABLE
