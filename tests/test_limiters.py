"""Limited schemes on five-point stencils: the expression language (abs, min, max, minmod), sign cells
and their cover, Harten TVD certificates, exact TV increases, per-branch truncation order, the exact
truncation error on smooth data, per-norm order studies, and the claims they decide. Every witness is
replayed here from the scheme's own formula, independently of the checker."""
import math
import random
from fractions import Fraction as Fr
from pathlib import Path

import pytest

from physverify.expr import parse
from physverify.schemes import check, checks, claims as C, convergence, limiters as L, linear, load, poly as P

ROOT = Path(__file__).resolve().parent.parent
S = ROOT / "schemes" / "limiters"
NAMES = ["advection-minmod", "advection-superbee", "broken-advection-lw-flux-form-tvd",
         "broken-advection-superbee-wide-cfl", "broken-advection-minmod-second-order"]


@pytest.fixture(scope="module")
def reports():
    return {n: check(load(S / f"{n}.json")) for n in NAMES}


def verdicts(rep):
    return {v["claim"]: v["verdict"] for v in rep["claims"]}


def raw(rep, name):
    return next(r for r in rep["checks"] if r["check"] == name)


# ---------------------------------------------------------------- references, written independently

def minmod(a, b):
    return min(a, b) if a > 0 and b > 0 else max(a, b) if a < 0 and b < 0 else Fr(0)


def superbee_phi(r):
    return max(Fr(0), min(2 * r, Fr(1)), min(r, Fr(2)))


def sweby_step(u, nu, phi):
    """LeVeque (2002) (6.39) form for a = 1: F_{i-1/2} = u_{i-1} + (1 - nu)/2 * phi(theta_{i-1/2}) *
    (u_i - u_{i-1}), theta_{i-1/2} = (u_{i-1} - u_{i-2})/(u_i - u_{i-1}), the slope 0 where the jump is 0."""
    n = len(u)
    d = lambda i: u[i % n] - u[(i - 1) % n]                         # Delta_{i-1/2}
    slope = lambda i: Fr(0) if d(i) == 0 else phi(d(i - 1) / d(i)) * d(i)
    F = [u[(i - 1) % n] + (1 - nu) / 2 * slope(i) for i in range(n)]     # F[i] = F_{i-1/2}
    return [u[i] - nu * (F[(i + 1) % n] - F[i]) for i in range(n)]


def tv(u):
    return sum(abs(u[(i + 1) % len(u)] - u[i]) for i in range(len(u)))


def rand_state(rng, n):
    return [Fr(rng.randint(-9, 9), rng.randint(1, 4)) for _ in range(n)]


def _top_level(s: str, sep: str) -> list:
    out, depth, start, i = [], 0, 0, 0
    while i < len(s):
        depth += {"(": 1, ")": -1}.get(s[i], 0)
        if depth == 0 and s.startswith(sep, i):
            out.append(s[start:i])
            i = start = i + len(sep)
            continue
        i += 1
    return out + [s[start:]]


# ---------------------------------------------------------------- the expression language

def test_piecewise_primitives_match_their_definitions():
    rng = random.Random(0)
    for _ in range(200):
        a, b = Fr(rng.randint(-9, 9), rng.randint(1, 5)), Fr(rng.randint(-9, 9), rng.randint(1, 5))
        env = {"a": a, "b": b}
        for s, want in (("abs(a)", abs(a)), ("min(a, b)", min(a, b)), ("max(a, b)", max(a, b)),
                        ("minmod(a, b)", minmod(a, b)), ("minmod(2*a, b - a)", minmod(2 * a, b - a))):
            e = parse(s)
            assert L.evaluate(e, env) == want == P.evaluate(P.from_expr(e), env), s
    assert parse("min") == parse("min")                  # a bare name is still a variable
    with pytest.raises(ValueError):
        parse("minmod(a)")


def test_minmod_cells_are_the_six_textbook_cases_and_cover_the_plane():
    cs = L.cells(parse("minmod(a, b)"))
    vals = sorted(P.show(c["poly"]) for c in cs["cells"])
    assert vals == ["0", "0", "a", "a", "b", "b"]
    assert len(cs["pruned"]) == 2                          # a >= b >= 0 >= a and its mirror: only a = b = 0
    rng = random.Random(1)
    for _ in range(300):                                   # every point lies in a retained cell with the right value
        pt = {"a": Fr(rng.randint(-5, 5)), "b": Fr(rng.randint(-5, 5))}
        hits = [c for c in cs["cells"] if all(P.evaluate(x, pt) >= 0 for x in c["atoms"])]
        assert hits and all(P.evaluate(c["poly"], pt) == minmod(pt["a"], pt["b"]) for c in hits)


@pytest.mark.parametrize("name", ["advection-minmod", "advection-superbee"])
def test_cells_cover_the_state_space_and_pruned_cells_are_certified(name):
    """The cover is by construction; here it is also sampled: every random rational state lies in a
    retained cell, and every retained cell containing it gives H's exact value there. Each pruned cell
    carries a certificate; its identity is re-parsed and replayed."""
    spec = load(S / f"{name}.json")
    e = checks.update(spec)
    cs = L.cells(e)
    assert cs["overlaps_undecided"] == 0 and cs["overlaps_checked"] == len(cs["cells"]) * (len(cs["cells"]) - 1) // 2
    rng = random.Random(2)
    for _ in range(150):
        pt = {x: Fr(rng.randint(-4, 4)) for x in checks.STENCIL5} | {"lam": Fr(rng.randint(1, 9), 10)}
        hits = [c for c in cs["cells"] if all(P.evaluate(x, pt) >= 0 for x in c["atoms"])]
        assert hits
        assert {P.evaluate(c["poly"], pt) for c in hits} == {L.evaluate(e, pt)}
    for cert in cs["pruned"]:
        lhs, rhs = cert["is <= 0 on the cell"].split(" = ", 1)
        assert P.add(P.from_expr(parse(lhs)), P.from_expr(parse(rhs)), -1) == {}
        assert rhs == "0" or all(Fr(t.split("*(", 1)[0]) > 0 for t in _top_level(rhs, " + "))


def test_cell_cap_gives_unknown_not_a_verdict(monkeypatch):
    spec = load(S / "advection-minmod.json")
    with pytest.raises(L.TooMany):
        L._cells(checks.update(spec), cap=5)
    monkeypatch.setattr(L, "MAX_CELLS", 5)
    L._CACHE.clear()
    try:
        r = L.tvd_harten(spec)
    finally:
        L._CACHE.clear()
    assert r["status"] == checks.UNKNOWN and "giving up" in r["detail"]


def test_overlap_check_catches_disagreeing_cells():
    x, y = P.var("x"), P.var("y")
    key = checks._key(x)
    c1 = {"poly": x, "atoms": [x], "assign": {key: (x, 1)}}
    c2 = {"poly": P.add(x, y), "atoms": [P.scale(x, -1)], "assign": {key: (x, -1)}}
    assert L._agree(c1, c2) is False                       # on x = 0 they differ by y
    c3 = {"poly": P.scale(x, -1), "atoms": [P.scale(x, -1)], "assign": {key: (x, -1)}}
    assert L._agree(c1, c3) is True                        # |x| written as x and -x: equal on x = 0


# ---------------------------------------------------------------- five-point stencils elsewhere

def test_three_point_specs_are_untouched_by_the_wide_stencil():
    for p in sorted((ROOT / "schemes").glob("*.json")):
        H = P.from_expr(checks.update(load(p)))
        assert checks.stencil_of(P.variables(H)) == checks.STENCIL
        phi, res = checks.telescoping(H)
        phi_w, res_w, names = checks.telescoping_wide(checks.update(load(p)))
        assert names == ["uL", "uR"] and bool(res) == bool(res_w)
        if not res:                                        # the same potential, up to the names
            assert P.subst(phi, {"_x": P.var("uL"), "_y": P.var("uR")}) == phi_w


def test_beam_warming_as_a_five_point_linear_update():
    """Beam-Warming (a = 1) uses u_{i-2}: the linear checks see the wider stencil."""
    spec = {"name": "Beam-Warming", "pde": {"flux": "u"},
            "scheme": {"update": "u0 - lam/2*(3*u0 - 4*um1 + um2) + lam^2/2*(u0 - 2*um1 + um2)"},
            "claims": {"consistent_order": 2, "von_neumann_cfl": ["0", "2"], "positive_cfl": ["0", "1"]}}
    assert linear.truncation_order(spec)["status"] == checks.VERIFIED
    assert linear.von_neumann(spec)["status"] == checks.VERIFIED
    pos = checks.positivity(spec)
    assert pos["status"] == checks.REFUTED and pos["witness"]["offending"] == "um2"    # nu(nu - 1)/2 < 0
    assert checks.conservation(spec)["status"] == checks.VERIFIED
    assert checks.consistency(spec)["status"] == checks.VERIFIED


def test_wide_flux_matches_the_update_it_defines():
    spec = load(S / "advection-minmod.json")
    rng = random.Random(3)
    F = checks.numerical_flux(spec)
    for _ in range(50):
        u = rand_state(rng, 7)
        lam = Fr(rng.randint(1, 10), 10)
        step = [L.evaluate(checks.update(spec), {**{x: u[(i + k) % 7] for x, k in checks.OFFSET5.items()}, "lam": lam})
                for i in range(7)]
        assert step == L._step(None, u, lam, F) == sweby_step(u, lam, lambda r: max(Fr(0), min(Fr(1), r)))


# ---------------------------------------------------------------- TVD

def test_tvd_verdicts(reports):
    assert verdicts(reports["advection-minmod"])["tvd_under_cfl"] == C.VERIFIED
    assert verdicts(reports["advection-superbee"])["tvd_under_cfl"] == C.VERIFIED
    assert verdicts(reports["broken-advection-lw-flux-form-tvd"])["tvd_under_cfl"] == C.REFUTED
    assert verdicts(reports["broken-advection-superbee-wide-cfl"])["tvd_under_cfl"] == C.REFUTED
    for n in ("advection-minmod", "advection-superbee"):
        assert raw(reports[n], "tvd_harten")["status"] == checks.VERIFIED
        assert raw(reports[n], "tv_increase")["status"] == checks.UNKNOWN
        counts = raw(reports[n], "tvd_harten")["witness"]["cell_counts"]
        assert counts["retained (full-dimensional)"] == {"advection-minmod": 18, "advection-superbee": 50}[n]


@pytest.mark.parametrize("name,phi", [("broken-advection-lw-flux-form-tvd", lambda r: Fr(1)),
                                      ("broken-advection-superbee-wide-cfl", superbee_phi)])
def test_tv_increase_replays_with_the_textbook_formula(reports, name, phi):
    w = raw(reports[name], "tv_increase")["witness"]
    u, nu = [Fr(x) for x in w["periodic state u^n"]], Fr(w["nu"])
    lo, hi = (Fr(x) for x in load(S / f"{name}.json")["claims"]["tvd_cfl"])
    assert lo <= nu <= hi
    v = sweby_step(u, nu, phi)
    assert v == [Fr(x) for x in w["u^{n+1}"]] and tv(v) > tv(u) == Fr(w["TV(u^n)"])


@pytest.mark.parametrize("name,phi", [("advection-minmod", lambda r: max(Fr(0), min(Fr(1), r))),
                                      ("advection-superbee", superbee_phi)])
def test_harten_coefficient_and_tv_on_random_data(name, phi):
    """Independent of the certificate: C = -(H - u_i)/(u_i - u_{i-1}) is in [0, 1] and TV never grows,
    on random rational periodic data and nu in [0, 1]."""
    rng = random.Random(4)
    for _ in range(150):
        u, nu = rand_state(rng, rng.choice((5, 6, 8))), Fr(rng.randint(0, 20), 20)
        v = sweby_step(u, nu, phi)
        assert tv(v) <= tv(u)
        for i in range(len(u)):
            d = u[i] - u[i - 1]
            if d:
                assert 0 <= -(v[i] - u[i]) / d <= 1


def test_harten_certificates_replay():
    """Each Farkas identity in the minmod witness, p = sum_j mu_j(nu) * a_j, is a polynomial identity;
    every a_j is an atom of its half-cell (so a_j >= 0 there) and every mu_j has non-negative
    Bernstein coefficients on its nu-piece, recomputed here from the printed identity."""
    spec = load(S / "advection-minmod.json")
    r = L.tvd_harten(spec)
    n = 0
    for row in r["witness"]["cells"]:
        for half in row["halves"]:
            atoms = {checks._key(P.from_expr(parse(a.removesuffix(" >= 0")))) for a in row["cell"] + [half["sign"]]}
            for goal in ("C >= 0", "C <= 1"):
                for piece in half[goal]["pieces"]:
                    lhs, rhs = piece["identity"].split(" = ", 1)
                    assert P.add(P.from_expr(parse(lhs)), P.from_expr(parse(rhs)), -1) == {}
                    lo, hi = (Fr(x) for x in piece["nu"])
                    for term in ([] if rhs == "0" else _top_level(rhs, " + ")):
                        mu, atom = _top_level(term, "*")
                        assert checks._key(P.from_expr(parse(atom))) in atoms
                        m = P.from_expr(parse(mu))
                        c = [Fr(0)] * 4
                        for mono, v in m.items():
                            c[dict(mono).get(("v", "nu"), 0)] += v
                        assert min(checks.bernstein(c, lo, hi)) >= 0
                    n += 1
    assert n >= 36


def test_local_maximum_principle(reports):
    """Minmod: VERIFIED through the Harten certificate (a convex combination of u_{i-1} and u_i).
    Lax-Wendroff in flux form: REFUTED by a state replayed here with the textbook formula."""
    assert verdicts(reports["advection-minmod"])["local_max_principle_under_cfl"] == C.VERIFIED
    assert verdicts(reports["broken-advection-lw-flux-form-tvd"])["local_max_principle_under_cfl"] == C.REFUTED
    w = raw(reports["broken-advection-lw-flux-form-tvd"], "max_principle_violation")["witness"]
    u, nu, i = [Fr(x) for x in w["periodic state u^n"]], Fr(w["nu"]), w["i"]
    v = sweby_step(u, nu, lambda r: Fr(1))
    st = [u[(i + k) % len(u)] for k in (-1, 0, 1)]                 # Lax-Wendroff's stencil
    assert v[i] == Fr(w["u_i^{n+1}"]) and not min(st) <= v[i] <= max(st)


def test_superbee_wide_cfl_is_tvd_up_to_one_and_not_beyond():
    """The exact checks agree with the literature range: Harten certifies [0, 1], a TV increase exists
    just above 1 (nu = 9/8, inside the broken claim's range)."""
    spec = load(S / "advection-superbee.json")
    u = [Fr(x) for x in (0, 0, 0, 0, 0, 1)]
    assert tv(sweby_step(u, Fr(9, 8), superbee_phi)) > tv(u)
    assert tv(L._step(None, u, Fr(9, 8), checks.numerical_flux(spec))) > tv(u)


# ---------------------------------------------------------------- truncation order per branch and on smooth data

def test_minmod_branch_table():
    rows, cs, a = L.branch_table(load(S / "advection-minmod.json"))
    by = {(r["slopes"]["i+1/2"], r["slopes"]["i-1/2"]): r for r in rows}
    assert len(rows) == 9
    lw = by["L = Delta_{i+1/2}", "L = Delta_{i-1/2}"]
    bw = by["L = Delta_{i-1/2}", "L = Delta_{i-3/2}"]
    up = by["L = 0", "L = 0"]
    assert (lw["scheme"], lw["order"]) == ("Lax-Wendroff", 2)
    assert (bw["scheme"], bw["order"]) == ("Beam-Warming", 2)
    assert (up["scheme"], up["order"]) == ("upwind", 1)
    assert by["L = Delta_{i-1/2}", "L = Delta_{i-1/2}"]["scheme"] == "upwind"
    assert sorted(r["order"] for r in rows) == [0, 0, 0, 0, 1, 1, 1, 2, 2]


def test_truncation_on_smooth_data_replays():
    """tau at U = 1 - x^2/2, x_i = 0, from the scheme itself at several rational dx: exactly (1 - nu)/4 * dx.
    The same stencil signs hold for cos(x) (Delta_{i+1/2} < 0 < Delta_{i-1/2} < Delta_{i-3/2}), and its
    tau/dx tends to the same (1 - nu)/4 (float check)."""
    spec = load(S / "broken-advection-minmod-second-order.json")
    r = L.truncation_smooth_data(spec)
    assert r["status"] == checks.REFUTED
    row = r["witness"]["rows"][-1]
    assert row["tau(dx)"] == "-1/4*dx*nu + 1/4*dx" and row["holds for"] == "every dx > 0"
    phi = lambda q: max(Fr(0), min(Fr(1), q))
    for nu in (Fr(1, 2), Fr(1, 3)):
        for dx in (Fr(1, 10), Fr(1, 37), Fr(1, 1000)):
            U = lambda x: 1 - x * x / 2
            u = [U(k * dx) for k in range(-3, 4)]               # periodic wrap is far from the centre
            H = sweby_step(u, nu, phi)[3]
            tau = (U(-nu * dx) - H) / (nu * dx)
            assert tau == (1 - nu) / 4 * dx
    for nu in (0.5, 0.3):
        for dx in (1e-2, 1e-3):
            f = [math.cos(k * dx) for k in range(-3, 4)]
            mm = lambda a, b: min(a, b) if a > 0 and b > 0 else max(a, b) if a < 0 and b < 0 else 0.0
            Fp = f[3] + (1 - nu) / 2 * mm(f[4] - f[3], f[3] - f[2])
            Fm = f[2] + (1 - nu) / 2 * mm(f[3] - f[2], f[2] - f[1])
            tau = (math.cos(nu * dx) - (f[3] - nu * (Fp - Fm))) / (nu * dx)
            assert abs(tau / dx - (1 - nu) / 4) < 2 * dx


def test_order_verdicts_and_three_readings(reports):
    v = verdicts(reports["broken-advection-minmod-second-order"])
    assert v["truncation_order_smooth_data"] == C.REFUTED                   # exact, local truncation only
    assert v["converges_order_p_linf"] == C.REFUTED_EMPIRICALLY            # global, max norm, sine data
    assert v["converges_order_p_l1"] == C.NOT_REFUTED                      # global, L1, sine data
    assert raw(reports["broken-advection-minmod-second-order"], "truncation_branches")["status"] == checks.UNKNOWN
    assert verdicts(reports["advection-minmod"])["converges_order_p_l1"] == C.NOT_REFUTED   # no extrema


def test_linf_study_is_not_a_commensurability_artefact():
    """Max-norm order of minmod on the sine at an incommensurate dt/dx and final time: still well below 2."""
    spec = load(S / "broken-advection-minmod-second-order.json")
    rows = convergence.combined(checks.update(spec), spec["test"]["problem"], 0.2371, 0.37)
    linf = [o[1] for o in convergence.orders(rows)[-2:]]
    l1 = [o[0] for o in convergence.orders(rows)[-2:]]
    assert all(1.1 < q < 1.5 for q in linf) and all(q > 1.8 for q in l1)


def test_per_norm_verdict():
    rows = [(25, 1e-2, 1e-1), (50, 2.5e-3, 5e-2), (100, 6.25e-4, 2.5e-2)]
    assert convergence.verdict(rows, 2, 0)[0] == convergence.NOT_REFUTED
    assert convergence.verdict(rows, 2, 1)[0] == convergence.REFUTED_EMPIRICALLY
    assert convergence.verdict(rows, 2)[0] == convergence.REFUTED_EMPIRICALLY


def test_judge_never_inconsistent_on_limited_schemes(reports):
    for n, rep in reports.items():
        assert not [v for v in rep["claims"] if v["verdict"] == C.INCONSISTENT], n
        assert verdicts(rep).get("consistent", C.VERIFIED) == C.VERIFIED
        assert verdicts(rep).get("conservative", C.VERIFIED) == C.VERIFIED
