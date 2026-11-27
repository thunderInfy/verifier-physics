"""Reconstruction v2: WENO-Z (the absolute value in tau) and WENO-M (the mapping), and the cancellation behind
the fifth order of the original Jiang-Shu measurement (2.20). The bench rows themselves are checked in
test_reconstruction.py. Fast: no Lean."""

import json
from fractions import Fraction as F
from pathlib import Path

from physverify import reconstruction as R
from physverify.expr import parse

BENCH = Path(__file__).resolve().parent.parent / "benchmark" / "reconstruction"
Z = json.loads((BENCH / "weno5-z-fd.json").read_text())["reconstruction"]
Z2 = json.loads((BENCH / "weno5-z2-fd.json").read_text())["reconstruction"]
M = json.loads((BENCH / "weno5-m-fd.json").read_text())["reconstruction"]
LIU = json.loads((BENCH.parent / "outside/specs/jiang-shu-weno5-liu-fd.json").read_text())["reconstruction"]


def claim(**kw):
    return {"claim": "reconstruction_order_p", "eps": "0", **kw}


def _delta_sign(rec, jet, shift, a=14):
    """The sign of beta_0 - beta_2 at the stencil shifted by `shift`, by plain evaluation at dx = 2^-a."""
    Rp, dx = R.parse_reconstruction(rec), F(1, 2 ** a)
    v = {k: sum(jet[n] * R.data_weight("point_values", k + shift, n) * dx ** n for n in range(len(jet)))
         for k in range(-3, 4)}
    b = [R._eval(x, v) for x in Rp["beta"]]
    return 1 if b[0] > b[2] else -1


def test_z_decides_every_sign_branch_of_tau():
    """f' = 0: beta_0 - beta_2 = dx^5 (-13/3 f'' f''' + ...), whose sign the regime leaves open, so the difference
    is decided in all four branches (sign at x_{i+1/2}, sign at x_{i-1/2}), each without sampling."""
    r = R.check_claim(Z, claim(p=4, form="flux_difference", regime="critical", n_cp=1))
    assert r["verdict"] == R.VERIFIED and len(r["branch_orders"]) == 4
    assert set(r["branch_orders"].values()) == {"4"}
    assert any("-13/3*f2*f3" in a for a in r["assumptions"])


def test_z_branch_excluded_by_form():
    """f' = f'' = 0: at x_{i-1/2} the leading term of beta_0 - beta_2 is (13/3) f'''^2 dx^6 > 0 by form, so the
    branch with a negative sign there is empty and is not decided."""
    r = R.check_claim(Z, claim(p=2, form="flux_difference", regime="critical", n_cp=2))
    assert r["verdict"] == R.VERIFIED
    assert sorted(r["branch_orders"]) == sorted(
        f"beta_0 - beta_2 {s} 0 at x_{{i+1/2}}, beta_0 - beta_2 > 0 at x_{{i-1/2}}" for s in "><")


def test_z_even_power_needs_no_split():
    r = R.check_claim(Z2, claim(p=5, form="flux_difference", regime="critical", n_cp=1))
    assert r["verdict"] == R.VERIFIED and "branch_orders" not in r


def test_z_refuted_witness_lies_in_its_branch():
    """The REFUTED jet's branch is the actual one: beta_0 - beta_2 evaluated from the formulas at small dx has the
    signs the branch names, at both stencils."""
    r = R.check_claim(Z, claim(p=5, form="flux_difference", regime="critical", n_cp=1))
    assert r["verdict"] == R.REFUTED and r["k"] == "4"
    jet = [F(v) for v in r["jet"].values()]
    signs = [1 if f"> 0 at x_{{i{s}1/2}}" in r["branch"] else -1 for s in "+-"]
    assert [_delta_sign(Z, jet, 0), _delta_sign(Z, jet, -1)] == signs


def test_z_tau_must_be_small_against_the_indicators():
    """An artificial pair of indicators of different orders at f' = 0, (f'' dx^2 / 2)^2 and (f'' dx^2)^4: tau =
    O(dx^4) is not small against the second, so D(0) > 0 is not shown and the answer is UNKNOWN, not a guess."""
    rec = {**Z, "candidates": ["(-vm1 + 3*v0)/2", "(v0 + vp1)/2"],
           "weights": {"kind": "z", "d": ["1/3", "2/3"], "beta": ["(v0 - vm1)^2", "(vp1 - 2*v0 + vm1)^4"],
                       "tau": [0, 1], "q": 1}}
    r = R.check_claim(rec, claim(p=1, form="point", regime="critical", n_cp=1))
    assert r["verdict"] == R.UNKNOWN and "not small against" in r["reason"]


def test_mapping_fixes_the_linear_weights_to_third_order():
    """g_k(d_k) = d_k and g_k'(d_k) = g_k''(d_k) = 0, so a JS weight error e becomes O(e^3)."""
    for d in (F(1, 10), F(6, 10), F(3, 10)):
        g = lambda w: w * (d + d * d - 3 * d * w + w * w) / (d * d + w * (1 - 2 * d))
        assert g(d) == d
        for h in (F(1, 10 ** 3), F(1, 10 ** 4)):
            assert abs(g(d + h) - d) < 2 * h ** 3 / d ** 2 and abs(g(d - h) - d) < 2 * h ** 3 / d ** 2


def test_mapping_outside_the_positive_definite_range_is_unknown():
    rec = {**M, "weights": {**M["weights"], "d": ["1/20", "17/20", "1/10"]}}
    r = R.check_claim(rec, claim(p=5, form="flux_difference", regime="generic"))
    assert r["verdict"] == R.UNKNOWN and "4/5" in r["reason"]


def test_original_measurement_cancellation_identity():
    """Why (2.20) is fifth order where f' != 0, from the module's own series: IS_k = (f'h)^2 + 2(k-1) f' f'' h^3 + ...,
    so with eps = 0 the weights are omega_k = d_k + d_k (4/5 - 4(k-1)) (f''/f') h + O(h^2), and the candidate errors
    q_k - h at x_{i+1/2} are A_k f''' h^3 with A = (-1/4, 1/12, -1/12). The O(h^4) term sum_k (omega_k - d_k) A_k f''' h^3
    vanishes because sum_k d_k A_k = 0 and sum_k k d_k A_k = 0."""
    Rp = R.parse_reconstruction(LIU)
    jet = R.Jet("point_values", "primitive", 1, 0, 6)
    mono = lambda **e: tuple(e.get(f"f{i}", 0) for i in range(jet.nv))
    for k, beta in enumerate(Rp["beta"]):
        b = R.to_series(beta, jet, 0, 6)
        assert b[2] == {mono(f1=2): 1}
        assert b[3] == ({mono(f1=1, f2=1): F(2 * (k - 1))} if k != 1 else {})
    exact = jet.exact(F(1, 2))
    A = []
    for qk in Rp["q"]:
        err = R.sadd(R.to_series(qk, jet, 0, 6), exact, -1)
        assert err[:3] == [{}, {}, {}] and set(err[3]) == {mono(f3=1)}
        A.append(err[3][mono(f3=1)])
    d = Rp["d"]
    assert A == [F(-1, 4), F(1, 12), F(-1, 12)]
    # the first-order weight error d_k (4/5 - 4(k-1)): from alpha_k ~ d_k (1 - 4(k-1) r h), r = f''/f', normalised
    # with sum_k d_k (k-1) = 1/5
    assert sum(dk * (k - 1) for k, dk in enumerate(d)) == F(1, 5)
    w1 = [dk * (F(4, 5) - 4 * (k - 1)) for k, dk in enumerate(d)]
    assert w1 == [F(12, 25), F(12, 25), F(-24, 25)] and sum(w1) == 0
    assert sum(dk * a for dk, a in zip(d, A)) == 0 and sum(k * dk * a for k, (dk, a) in enumerate(zip(d, A))) == 0
    assert sum(w * a for w, a in zip(w1, A)) == 0
    # and the checker agrees: leading order 5 for one reconstruction and for the difference
    for form in ("point", "flux_difference"):
        assert R.check_claim(LIU, claim(p=5, form=form, regime="generic"))["leading_order"] == "5"


def test_original_measurement_critical_point_coefficients():
    """Pins the leading errors of benchmark/outside/notes/liu-critical-point.md at n_cp = 1 (f' = 0), eps = 0, from
    the module's numerators: face (14/293) f''' dx^3, flux difference (200248/2854113) f''' dx^2, and with f''' = 0
    as well (7/1465) f'''' dx^4 and (21950/951371) f'''' dx^3."""
    Rp = R.parse_reconstruction(LIU)
    jet = R.Jet("point_values", "primitive", 1, 1, 12)
    mono = lambda **e: tuple(e.get(f"f{i}", 0) for i in range(jet.nv))
    n = 6
    Np, Dp = R._numerator(Rp, jet, 0, n, None, 2, [])
    Nm, Dm = R._numerator(Rp, jet, -1, n, None, 2, [])
    want = {"point": (3, F(14, 293), F(7, 1465)), "flux_difference": (2, F(200248, 2854113), F(21950, 951371))}
    for form, (order, c3, c4) in want.items():
        if form == "point":
            N, den = Np, Dp[0]
        else:
            N, den = R.sadd(R.smul(Np, Dm, n), R.smul(Nm, Dp, n), -1), R.pmul(Dp[0], Dm[0])
        (dm, dc), = den.items()
        lead = lambda terms: {tuple(a - b for a, b in zip(m, dm)): c / dc for m, c in terms.items()}
        j0 = R.first_nonzero(N)
        assert j0 - (form == "flux_difference") == order
        assert lead(N[j0]) == {mono(f3=1): c3}
        assert lead({m: c for m, c in N[j0 + 1].items() if m[3] == 0}) == {mono(f4=1): c4}
        r = R.check_claim(LIU, claim(p=order, form=form, regime="critical", n_cp=1))
        assert r["verdict"] == R.VERIFIED and r["leading_order"] == str(order)


def test_parse_rejects_a_bad_tau():
    rec = {**Z, "weights": {**Z["weights"], "tau": [1, 1]}}
    assert R.check_claim(rec, claim(p=5, regime="generic"))["verdict"] == R.UNKNOWN
    assert parse("v0")  # the expression parser is the shared one
