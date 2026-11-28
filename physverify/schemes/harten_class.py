"""TVD claims about a class of schemes: the flux or the limiter is a variable (exact).

Two checks, one per claim kind. Each decides whether the stated class conditions K imply the
hypotheses of a Lean theorem that quantifies over the class (lean/PhysVerify/Harten.lean); neither
looks at one scheme.

`monotone_class` (claim `tvd_monotone_class`): "every three-point conservative scheme
v_i = u_i - lam (F(u_i, u_i+1) - F(u_i-1, u_i)) whose flux F has difference quotients in
[a_lo, a_hi] (first argument) and [b_lo, b_hi] (second argument) is TVD", for every (lam, a_lo,
a_hi, b_lo, b_hi) meeting K. K is a list of polynomial (in)equalities over lam, a_lo, a_hi, b_lo,
b_hi and any other named parameters (L1, L2, ...). For a differentiable F the bounds are bounds on
dF/da and dF/db (mean value theorem). The theorem, `PhysVerify.Harten.tvd_monotone_class_meaning`,
holds for the class as soon as K implies

    lam >= 0,   lam a_lo >= 0,   lam b_hi <= 0,   lam (a_hi - b_lo) <= 1,

which make the scheme monotone (`monotone3_of_bounds`), so TVD (`monotone_tvd`). The targets
are quadratic, so "K implies it" is decided by a Farkas certificate over the conditions and their
pairwise products (each product of two conditions >= 0 is >= 0), monomials taken as LP variables
(exactlp.py, exact rationals); the certificate is replayed as an identity. That is sound but not
complete for quadratics, so a target with no certificate is not yet refuted: the LP's point gives
parameters, kept only if they meet K exactly (true products) and violate the target, and then the
linear fluxes F(a, b) = p a + q b with p in {a_lo, a_hi}, q in {b_lo, b_hi} (members of the class)
are run on a few periodic rational data vectors in Fractions. REFUTED only when one step raises TV
exactly; else UNKNOWN.

`limiter_class` (claim `tvd_limiter_class`): "every flux-limited scheme for u_t + a u_x = 0, a > 0,
v_i = u_i - (G_i - G_i-1), G_j = nu u_j + nu (1 - nu)/2 phi(r_j) (u_j+1 - u_j), r_j = (u_j - u_j-1) /
(u_j+1 - u_j) (r_j = 0 when u_j+1 = u_j), whose limiter phi meets K is TVD for 0 <= nu <= nu_max". This
is the Sweby form of limiters.py's specs (lam a F = nu u_L + nu (1 - nu)/2 psi with psi = phi(r) Delta).
K is a list of pieces: an interval of r with rational (or infinite) ends, open or closed, and bounds
lo(r) <= phi(r) <= hi(r) (polynomials or quotients of polynomials in r; either may be missing), plus
optionally phi(r) = 0 for r <= 0. The theorem, `PhysVerify.Harten.tvd_limiter_class_meaning`, needs
nu_max <= 1 and

    phi(r) = 0 for r <= 0;   0 <= phi(r) <= 2 and nu_max phi(r) <= 2 r for r > 0,

which is Sweby's region 0 <= phi <= min(2r, 2) at nu_max = 1 (and a larger one for nu_max < 1: the
D-coefficient of Harten's form stays in [0, 1] when nu phi(r)/r <= 2 and phi <= 2). K implies them
when the pieces cover each region and, on every part of a piece in a region, each target inequality
(cleared of its positive denominator) is a polynomial >= 0 there: decided by Sturm sequences
(univariate.py), with a Cauchy root bound for unbounded ends. VERIFIED needs that certificate on
every piece. Sweby's region is SUFFICIENT: a limiter outside it is not thereby non-TVD, so "K does
not imply the targets" is UNKNOWN, never REFUTED by itself. REFUTED needs a member of the class
and rational periodic data whose TV rises after one step, recomputed in Fractions: the member is
any phi meeting K with the stated values at the finitely many ratios of the data (K is checked to
be non-empty at every r, so such phi exists), the values taken at the point Sturm found outside
the targets.

Nothing here samples or uses floats: every VERIFIED and REFUTED is exact. Malformed K (a nonlinear
or unparsable condition, an interval that does not parse, a denominator that is not positive on its
piece) is UNKNOWN, and so is an empty class (the claim is then vacuous).
"""

from __future__ import annotations

from fractions import Fraction
from itertools import product

from ..expr import parse
from . import exactlp, poly as P, univariate as U
from .checks import NOT_APPLICABLE, REFUTED, UNKNOWN, VERIFIED, result

LEAN_MONOTONE = "PhysVerify.Harten.tvd_monotone_class_meaning"
LEAN_LIMITER = "PhysVerify.Harten.tvd_limiter_class_meaning"
RELS = ("<=", ">=", "<", ">", "=")
BOUNDS = ("lam", "a_lo", "a_hi", "b_lo", "b_hi")


# ---------------------------------------------------------------- polynomials with monomials as LP variables

def _mono_name(m: tuple) -> str:
    out = []
    for a, k in m:
        if a[0] != "v" or k < 1:
            raise ValueError("not a polynomial (a square root or a division by a variable)")
        out.append(a[1] + (f"^{k}" if k > 1 else ""))
    return "*".join(sorted(out))


def _lin(p: P.Poly) -> tuple[Fraction, dict]:
    """p as (const, {monomial name: coef}); a polynomial is linear in its monomials."""
    c0, lin = Fraction(0), {}
    for m, c in p.items():
        if not m:
            c0 += c
        else:
            k = _mono_name(m)
            lin[k] = lin.get(k, Fraction(0)) + c
    return c0, {k: v for k, v in lin.items() if v}


def parse_condition(text: str) -> tuple[P.Poly, str]:
    """'lhs REL rhs' -> (p, rel) meaning p rel 0 with rel in >=, >, =. Raises ValueError if it does not parse
    or is not a polynomial."""
    for rel in RELS:
        if rel in text:
            lhs, rhs = text.split(rel, 1)
            if any(r in rhs for r in RELS):
                raise ValueError(f"{text!r}: one relation per condition")
            break
    else:
        raise ValueError(f"{text!r}: no relation (one of {RELS})")
    try:
        diff = P.add(P.from_expr(parse(lhs)), P.from_expr(parse(rhs)), -1)
    except Exception as ex:           # a parse error or a non-polynomial expression
        raise ValueError(f"{text!r}: {ex}") from ex
    if rel in ("<=", "<"):
        diff = P.scale(diff, Fraction(-1))
    _lin(diff)                         # raises unless polynomial
    return diff, {"<=": ">=", "<": ">"}.get(rel, rel)


def _degree(p: P.Poly) -> int:
    return max((sum(k for _, k in m) for m in p), default=0)


def _show(p: P.Poly, rel: str) -> str:
    return f"{P.show(p)} {rel} 0"


def products(conds: list) -> list[tuple[str, P.Poly, str]]:
    """The conditions and the pairwise products of the affine ones, as (label, poly, rel): a product of
    two non-negative quantities is non-negative; an equality times an affine quantity is an equality."""
    out = [(_show(p, r), p, r) for p, r in conds]
    aff = [(p, r) for p, r in conds if _degree(p) <= 1]
    for i, (p, r) in enumerate(aff):
        for q, s in aff[i:]:
            rel = "=" if "=" in (r, s) else ">="
            out.append((f"({P.show(p)}) * ({P.show(q)}) {rel} 0", P.mul(p, q), rel))
    for p, r in aff:                   # an equality times each variable
        if r == "=":
            for v in sorted(set().union(*(P.variables(q) for q, _ in conds))):
                out.append((f"({P.show(p)}) * {v} = 0", P.mul(p, P.var(v)), "="))
    return out


def _value(p: P.Poly, x: dict) -> Fraction:
    v = P.evaluate(p, x)
    if v is None:
        raise ValueError("not evaluable")
    return v


def _holds(p: P.Poly, rel: str, x: dict) -> bool:
    v = _value(p, x)
    return v >= 0 if rel == ">=" else v > 0 if rel == ">" else v == 0


# ---------------------------------------------------------------- tvd_monotone_class

def monotone_targets() -> list[tuple[str, P.Poly]]:
    """(label, p) for the hypotheses of tvd_monotone_class_meaning, each p >= 0."""
    v = {n: P.var(n) for n in BOUNDS}
    lam = v["lam"]
    return [("lam >= 0", lam), ("lam * a_lo >= 0", P.mul(lam, v["a_lo"])),
            ("lam * b_hi <= 0", P.scale(P.mul(lam, v["b_hi"]), -1)),
            ("lam * (a_hi - b_lo) <= 1", P.add(P.const(1), P.mul(lam, P.add(v["a_hi"], v["b_lo"], -1)), -1))]


def cons_step(F, lam: Fraction, u: list) -> list:
    """One step of v_i = u_i - lam (F(u_i, u_i+1) - F(u_i-1, u_i)) on the periodic grid, exactly."""
    n = len(u)
    return [u[i] - lam * (F(u[i], u[(i + 1) % n]) - F(u[i - 1], u[i])) for i in range(n)]


def total_variation(u: list) -> Fraction:
    return sum((abs(u[(i + 1) % len(u)] - u[i]) for i in range(len(u))), Fraction(0))


def _increments_data(incs: list) -> list:
    """The periodic data with these increments u_i+1 - u_i (they sum to 0), starting at 0."""
    assert sum(incs) == 0
    u = [Fraction(0)]
    for d in incs[:-1]:
        u.append(u[-1] + d)
    return u


MONO_DATA = ([0, 0, 1, 0, 0], [0, 0, -1, 0, 0], [0, 0, 1, 1, 0, 0], [0, 1, 0, 1], [0, 0, 1, 2, 2, 0])


def monotone_counterexample(x: dict) -> dict | None:
    """A linear flux in the class at parameters x and periodic data whose TV rises in one step, or None."""
    lam, alo, ahi, blo, bhi = (x[n] for n in BOUNDS)
    if alo > ahi or blo > bhi:
        return None                       # no flux has these bounds
    for p, q in product(dict.fromkeys((alo, ahi)), dict.fromkeys((blo, bhi))):
        F = lambda a, b, p=p, q=q: p * a + q * b
        for data in MONO_DATA:
            u = [Fraction(d) for d in data]
            v = cons_step(F, lam, u)
            if total_variation(v) > total_variation(u):
                return {"parameters": {n: str(x[n]) for n in sorted(x)}, "flux": f"F(a, b) = p*a + q*b",
                        "p": str(p), "q": str(q),
                        "flux difference quotients": f"{p} in [{alo}, {ahi}] (first argument), {q} in [{blo}, {bhi}] "
                                                     "(second argument)",
                        "lam": str(lam), "u": [str(y) for y in u], "v": [str(y) for y in v],
                        "TV(u)": str(total_variation(u)), "TV(v)": str(total_variation(v))}
    return None


def replay_farkas(cfg: dict, label: str, cert: dict) -> bool:
    """Re-check a reported certificate for one target from the claim's own conditions: the multipliers
    (keyed by the rows' labels) must be >= 0 on inequalities and give target = remainder + sum y_j row_j,
    remainder >= 0, as an identity in the monomials."""
    rows = products([parse_condition(t) for t in cfg.get("conditions", [])])
    by_label = {lab: (p, rel) for lab, p, rel in rows}
    (p_t,) = [p for lab, p in monotone_targets() if lab == label]
    if set(cert["multipliers"]) - set(by_label):
        return False
    sel = [by_label[k] for k in cert["multipliers"]]
    lp = [(*_lin(p), rel) for p, rel in sel]
    y = [Fraction(v) for v in cert["multipliers"].values()]
    names = sorted({k for _, lin, _ in lp for k in lin} | set(_lin(p_t)[1]))
    out = exactlp.replay(lp, _lin(p_t), names, y)
    return out is not None and out["remainder"] == Fraction(cert["remainder"])


def replay_counterexample(ce: dict, kind: str, cfg: dict | None = None) -> bool:
    """Recompute a reported counterexample's step and TVs in Fractions from its own fields; for a limiter
    with the claim's cfg, also that each phi value meets K at its ratio."""
    u = [Fraction(x) for x in ce["u"]]
    if kind == "monotone":
        p, q = Fraction(ce["p"]), Fraction(ce["q"])
        x = {k: Fraction(v) for k, v in ce["parameters"].items()}
        if not (x["a_lo"] <= p <= x["a_hi"] and x["b_lo"] <= q <= x["b_hi"] and Fraction(ce["lam"]) == x["lam"]):
            return False
        v = cons_step(lambda a, b: p * a + q * b, Fraction(ce["lam"]), u)
    else:
        table = {Fraction(k): Fraction(x) for k, x in ce["phi at the ratios of the data"].items()}
        if cfg is not None:
            pieces = parse_pieces(cfg)
            for r, y in table.items():
                lo, hi = _admissible(pieces, r)
                if (lo is not None and y < lo) or (hi is not None and y > hi):
                    return False
            if Fraction(ce["nu"]) < 0 or Fraction(ce["nu"]) > Fraction(cfg["nu_max"]):
                return False
        v = lim_step(table.__getitem__, Fraction(ce["nu"]), u)
    return [str(x) for x in v] == ce["v"] and total_variation(v) > total_variation(u) \
        and str(total_variation(v)) == ce["TV(v)"]


def _points_at_lam(conds: list, target: P.Poly, base: list, lam: Fraction) -> list[dict]:
    """Points of the class with lam fixed, where that makes the conditions and the target affine: the LP
    minimum of the target (and points along a ray when unbounded). Exact; [] when not affine."""
    fix = lambda q: P.subst(q, {"lam": P.const(lam)})
    rest = [v for v in base if v != "lam"]
    sub = [(fix(q), r) for q, r in conds]
    if any(_degree(q) > 1 for q, _ in sub) or _degree(fix(target)) > 1:
        return []
    lp = [(*_lin(q), r) for q, r in sub]
    m = exactlp.minimize_affine(lp, _lin(fix(target)), rest)
    if m["status"] == "infeasible":
        return []
    pts = [m["point"]]
    if m["status"] == "unbounded":
        pts = [{v: m["point"][v] + L * m["ray"][v] for v in rest} for L in (1, 4, 16)]
    return [{**x, "lam": lam} for x in pts]


def _monotone_claim(cfg: dict) -> str:
    return ("every 3-point conservative scheme whose flux has difference quotients in [a_lo, a_hi] x [b_lo, b_hi], "
            f"with {', '.join(cfg.get('conditions', [])) or '(no conditions)'}, is TVD")


def monotone_class(spec: dict) -> dict:
    cfg = spec.get("claims", {}).get("tvd_monotone_class")
    if cfg is None:
        return result("monotone_class", NOT_APPLICABLE, "TVD class (monotone flux)",
                      "no class claim (claims.tvd_monotone_class)")
    claim = _monotone_claim(cfg)
    try:
        conds = [parse_condition(t) for t in cfg.get("conditions", [])]
    except ValueError as ex:
        return result("monotone_class", UNKNOWN, claim, str(ex))
    if not conds:
        return result("monotone_class", UNKNOWN, claim, "no conditions: the class contains schemes that are not TVD "
                                                        "and gives no bound to decide")
    rows = products(conds)
    lp = [(c0, lin, rel) for _, p, rel in rows for c0, lin in [_lin(p)]]
    tg = [(label, p, _lin(p)) for label, p in monotone_targets()]
    names = sorted({k for _, lin, _ in lp for k in lin} | {k for *_, (_, lin) in tg for k in lin})
    certs, failed = {}, []
    for label, p, tgt in tg:
        m = exactlp.minimize_affine(lp, tgt, names)
        if m["status"] == "infeasible":
            return result("monotone_class", UNKNOWN, claim, "the conditions have no solution (even with strict "
                                                            "inequalities relaxed): the class is empty, so the claim is "
                                                            "vacuous")
        if m["status"] == "optimal" and m["value"] >= 0:
            cert = exactlp.farkas(lp, tgt, names)
            if cert is None:
                return result("monotone_class", UNKNOWN, claim, f"{label}: the LP minimum is >= 0 but no Farkas "
                                                                "certificate replayed (a bug in exactlp.py)")
            certs[label] = {"remainder": str(cert["remainder"]),
                            "multipliers": {row[0]: str(y) for row, y in zip(rows, cert["multipliers"]) if y}}
            continue
        failed.append((label, p, m))
    assumes = ["three-point conservative schemes on the periodic grid; the flux is any function F of two arguments "
               "with (F(a', b) - F(a, b))/(a' - a) in [a_lo, a_hi] and (F(a, b') - F(a, b))/(b' - b) in [b_lo, b_hi]"]
    if not failed:
        return result("monotone_class", VERIFIED, claim,
                      f"the conditions imply every hypothesis of {LEAN_MONOTONE} ({len(certs)} targets, each with a "
                      "Farkas certificate over the conditions and their pairwise products, replayed exactly): every "
                      "scheme of the class is monotone, so TVD (Harten)", {"farkas": certs}, assumes)
    tried = []
    base = sorted(set(BOUNDS) | {v for q, _ in conds for v in P.variables(q)})
    for label, p, m in failed:
        pt = m["point"]
        if m["status"] == "unbounded":
            pt = {k: pt[k] + (abs(m["point"].get(k, 0)) + 1) * m["ray"][k] for k in pt}
        pts = [{v: pt.get(v, Fraction(0)) for v in base}]
        # with lam fixed the conditions are often linear: then an exact LP point of the class
        for lam in dict.fromkeys([pts[0]["lam"], Fraction(1), Fraction(1, 2), Fraction(2), Fraction(1, 4)]):
            pts += _points_at_lam(conds, p, base, lam)
        for x in pts:
            if not all(_holds(q, r, x) for q, r in conds) or _value(p, x) >= 0:
                tried.append(f"{label}: an LP point does not meet the conditions with its true products")
                continue
            ce = monotone_counterexample(x)
            if ce is not None:
                return result("monotone_class", REFUTED, claim,
                              f"parameters in the class violate {label}, and a linear flux with those bounds raises TV "
                              f"in one step: {ce['TV(u)']} -> {ce['TV(v)']}", {"counterexample": ce, "farkas": certs},
                              assumes)
            tried.append(f"{label}: no linear flux at the points tried raised TV on the data tried")
    return result("monotone_class", UNKNOWN, claim,
                  f"not implied (no certificate from the conditions and their pairwise products): "
                  f"{', '.join(lab for lab, _, _ in failed)}; no exact counterexample found ("
                  + "; ".join(dict.fromkeys(tried)) + ")", {"farkas": certs}, assumes)


# ---------------------------------------------------------------- univariate pieces

INF = None      # an infinite end


def parse_interval(text: str) -> tuple:
    """'(a, b]' -> (a, a_closed, b, b_closed); 'inf' / '-inf' ends are open and stored as None."""
    t = text.strip()
    if len(t) < 5 or t[0] not in "([" or t[-1] not in ")]" or t.count(",") != 1:
        raise ValueError(f"{text!r}: an interval is written (a, b], [a, inf), ...")
    a, b = (s.strip() for s in t[1:-1].split(","))
    lo = INF if a in ("-inf", "-oo") else Fraction(a)
    hi = INF if b in ("inf", "+inf", "oo") else Fraction(b)
    lc, hc = t[0] == "[" and lo is not INF, t[-1] == "]" and hi is not INF
    if lo is not INF and hi is not INF and (lo > hi or (lo == hi and not (lc and hc))):
        raise ValueError(f"{text!r} is empty")
    return lo, lc, hi, hc


def intersect(I: tuple, J: tuple) -> tuple | None:
    (a, ac, b, bc), (c, cc, d, dc) = I, J
    if a is INF or (c is not INF and c > a):
        lo, lc = c, cc
    elif c is INF or a > c:
        lo, lc = a, ac
    else:
        lo, lc = a, ac and cc
    if b is INF or (d is not INF and d < b):
        hi, hc = d, dc
    elif d is INF or b < d:
        hi, hc = b, bc
    else:
        hi, hc = b, bc and dc
    if lo is not INF and hi is not INF and (lo > hi or (lo == hi and not (lc and hc))):
        return None
    return lo, lc, hi, hc


def show_interval(I: tuple) -> str:
    a, ac, b, bc = I
    return f"{'[' if ac else '('}{'-inf' if a is INF else a}, {'inf' if b is INF else b}{']' if bc else ')'}"


def _interior_point(I: tuple) -> Fraction:
    a, _, b, _ = I
    if a is INF and b is INF:
        return Fraction(0)
    if a is INF:
        return b - 1
    if b is INF:
        return a + 1
    return (a + b) / 2


def _cauchy(p: list) -> Fraction:
    p = U.trim(p)
    return 1 + max((abs(c / p[-1]) for c in p[:-1]), default=Fraction(0))


def nonneg_on(p: list, I: tuple) -> dict:
    """p >= 0 on the closure of I (ends may be infinite), exact: univariate.nonneg_on on a bounded part and
    the leading sign beyond a Cauchy root bound. {"nonneg", "certificate", "counterexample"?: {"x", "p(x)"}}."""
    p = U.trim(p)
    a, _, b, _ = I
    if not p:
        return {"nonneg": True, "certificate": {"method": "p = 0"}}
    if a is not INF and b is not INF:
        return U.nonneg_on(p, a, b)
    if a is INF and b is INF:
        left, right = nonneg_on(p, (INF, False, Fraction(0), True)), nonneg_on(p, (Fraction(0), True, INF, False))
        bad = left if not left["nonneg"] else right
        return {**bad, "certificate": {"(-inf, 0]": left["certificate"], "[0, inf)": right["certificate"]}} \
            if not bad["nonneg"] else {"nonneg": True, "certificate": {"(-inf, 0]": left["certificate"],
                                                                     "[0, inf)": right["certificate"]}}
    if a is INF:                      # (-inf, b]: q(x) = p(-x) on [-b, inf)
        q = [c * (-1) ** i for i, c in enumerate(p)]
        out = nonneg_on(q, (-b, True, INF, False))
        if "counterexample" in out:
            out["counterexample"] = {"x": -out["counterexample"]["x"], "p(x)": out["counterexample"]["p(x)"]}
        return out
    top = max(a, _cauchy(p)) + 1 if U.deg(p) > 0 else a + 1
    part = U.nonneg_on(p, a, top)
    cert = {"method": "Sturm on [a, B] with B above the Cauchy root bound, leading sign beyond", "B": top,
            "on [a, B]": part["certificate"], "leading coefficient": p[-1]}
    if not part["nonneg"]:
        return {"nonneg": False, "certificate": cert, "counterexample": part["counterexample"]}
    if U.deg(p) > 0 and p[-1] < 0:
        return {"nonneg": False, "certificate": cert, "counterexample": {"x": top, "p(x)": U.ev(p, top)}}
    return {"nonneg": True, "certificate": cert}


def _no_root(p: list, I: tuple) -> bool:
    """p has no root on the closure of I (exact: Sturm counts on the square-free part)."""
    p = U.trim(p)
    if U.deg(p) <= 0:
        return bool(p)
    a, _, b, _ = I
    B = _cauchy(p)
    lo = -B if a is INF else a
    hi = B if b is INF else b
    if lo > hi:
        return True
    if U.ev(p, lo) == 0 or U.ev(p, hi) == 0:
        return False
    if lo == hi:
        return True
    s = [Fraction(1)]
    for _, f in U.squarefree(p)[1]:
        s = U.mul(s, f)
    return U.roots_open(U.sturm_sequence(s), lo, hi) == 0


def _univariate(p: P.Poly, var: str = "r") -> list:
    out: dict = {}
    for m, c in p.items():
        if any(a != ("v", var) or k < 0 for a, k in m):
            raise ValueError(f"not a polynomial in {var}: {P.show(p)}")
        k = sum(k for _, k in m)
        out[k] = out.get(k, Fraction(0)) + c
    return U.trim([out.get(i, Fraction(0)) for i in range(max(out, default=-1) + 1)])


def parse_bound(text: str) -> tuple[list, list]:
    """'num / den' or a polynomial in r -> (num, den) as univariate coefficient lists."""
    try:
        e = parse(str(text))
        if e.kind == "div":
            num, den = _univariate(P.from_expr(e.args[0])), _univariate(P.from_expr(e.args[1]))
            if U.deg(den) == 0:
                return [c / den[0] for c in num], [Fraction(1)]
            return num, den
        return _univariate(P.from_expr(e)), [Fraction(1)]
    except ValueError:
        raise
    except Exception as ex:
        raise ValueError(f"{text!r}: {ex}") from ex


def _ev_bound(nd: tuple, x: Fraction) -> Fraction:
    return U.ev(nd[0], x) / U.ev(nd[1], x)


def _show_bound(nd: tuple) -> str:
    n, d = nd
    return U.show(n, "r") if d == [1] else f"({U.show(n, 'r')}) / ({U.show(d, 'r')})"


# ---------------------------------------------------------------- tvd_limiter_class

def limiter_targets(nu_max: Fraction) -> list[tuple[str, tuple, str, tuple]]:
    """(region label, region, side, target bound) for the hypotheses of tvd_limiter_class_meaning: on the region,
    phi >= target (side 'lo') or phi <= target (side 'hi'); targets as (num, den)."""
    one, r = [Fraction(1)], [Fraction(0), Fraction(1)]
    neg, pos = (INF, False, Fraction(0), True), (Fraction(0), False, INF, False)
    return [("r <= 0: phi(r) >= 0", neg, "lo", ([], one)), ("r <= 0: phi(r) <= 0", neg, "hi", ([], one)),
            ("r > 0: phi(r) >= 0", pos, "lo", ([], one)), ("r > 0: phi(r) <= 2", pos, "hi", ([Fraction(2)], one)),
            (f"r > 0: {nu_max} * phi(r) <= 2r", pos, "hi", ([Fraction(0), 2 / nu_max], one))] if nu_max > 0 else []


def _covered(I: tuple, pieces: list) -> Fraction | None:
    """A rational point of I that no piece covers, or None when the pieces cover I (exact sweep)."""
    a, ac, b, bc = I
    x, xc = a, ac            # the uncovered part starts at x (closed if xc)
    for _ in range(len(pieces) + 1):
        if x is not INF and b is not INF and (x > b or (x == b and not (xc and bc))):
            return None
        best = None
        for J in pieces:
            lo, lc, hi, hc = J
            starts = lo is INF or (x is not INF and (lo < x or (lo == x and (lc or not xc))))
            if not starts:
                continue
            if hi is INF:
                return None
            if x is not INF and (hi < x or (hi == x and not (hc and xc))):
                continue
            if best is None or hi > best[0] or (hi == best[0] and hc and not best[1]):
                best = (hi, hc)
        if best is None:
            if x is INF:
                return (b - 1) if b is not INF else Fraction(0)
            if xc:
                return x
            nxt = min((J[0] for J in pieces if J[0] is not INF and J[0] > x), default=None)
            end = b if b is not INF else x + 2
            end = min(end, nxt) if nxt is not None else end
            return (x + end) / 2
        x, xc = best[0], not best[1]
    return None


def _admissible(pieces: list, r: Fraction) -> tuple[Fraction | None, Fraction | None]:
    """(max lower bound, min upper bound) of phi(r) over the pieces covering r (None: no bound)."""
    lo = hi = None
    for I, b_lo, b_hi in pieces:
        if intersect(I, (r, True, r, True)) is None:
            continue
        if b_lo is not None:
            v = _ev_bound(b_lo, r)
            lo = v if lo is None else max(lo, v)
        if b_hi is not None:
            v = _ev_bound(b_hi, r)
            hi = v if hi is None else min(hi, v)
    return lo, hi


def _clip(v: Fraction, lo, hi) -> Fraction:
    if lo is not None and v < lo:
        return lo
    if hi is not None and v > hi:
        return hi
    return v


def ratio(u: list, j: int) -> Fraction:
    """r_j = (u_j - u_j-1) / (u_j+1 - u_j), 0 when u_j+1 = u_j (as in Lean)."""
    n = len(u)
    d = u[(j + 1) % n] - u[j]
    return (u[j] - u[j - 1]) / d if d else Fraction(0)


def lim_step(phi, nu: Fraction, u: list) -> list:
    """v_i = u_i - (G_i - G_i-1), G_j = nu u_j + nu(1 - nu)/2 phi(r_j) (u_j+1 - u_j), exactly."""
    n = len(u)
    G = [nu * u[j] + nu * (1 - nu) / 2 * phi(ratio(u, j)) * (u[(j + 1) % n] - u[j]) for j in range(n)]
    return [u[i] - (G[i] - G[i - 1]) for i in range(n)]


def _designs(s: Fraction) -> list[list]:
    """Increment lists with an interface whose ratio is s (a jump s then 1, or -s then -1)."""
    if s == 0:
        return [[0, 0, 0, 1, 0, 0, -1], [0, 0, 0, 1, 1, 0, -2], [0, 0, 0, -1, 0, 0, 1]]
    out = []
    for t in (1, -1):
        out += [[0, 0, s * t, t, 0, 0, 0, -(s + 1) * t], [0, 0, s * t, t, t, 0, 0, -(s + 2) * t],
                [t, t, s * t, t, 0, 0, -(s + 3) * t], [0, 0, 0, s * t, t, 0, 0, -(s + 1) * t]]
    return out


def limiter_counterexample(pieces: list, r0: Fraction, y0: Fraction, nus: list) -> dict | None:
    """Periodic data and phi values (phi(r0) = y0, elsewhere the admissible value nearest 0) whose TV rises
    after one step at some nu in `nus`, recomputed in Fractions; None if none of the designs does it."""
    lo, hi = _admissible(pieces, r0)
    if (lo is not None and y0 < lo) or (hi is not None and y0 > hi):
        return None
    for inc in _designs(r0):
        u = _increments_data([Fraction(d) for d in inc])
        table = {}
        for j in range(len(u)):
            r = ratio(u, j)
            if r not in table:
                table[r] = y0 if r == r0 else _clip(Fraction(0), *_admissible(pieces, r))
        bad = [r for r, v in table.items() for a, b in [_admissible(pieces, r)]
               if (a is not None and v < a) or (b is not None and v > b)]
        if bad:
            continue
        for nu in nus:
            v = lim_step(table.__getitem__, nu, u)
            if total_variation(v) > total_variation(u):
                return {"phi at the ratios of the data": {str(r): str(y) for r, y in table.items()},
                        "phi elsewhere": "any value meeting K (K is non-empty at every r, checked exactly)",
                        "nu": str(nu), "u": [str(x) for x in u], "v": [str(x) for x in v],
                        "TV(u)": str(total_variation(u)), "TV(v)": str(total_variation(v))}
    return None


def parse_pieces(cfg: dict) -> list:
    """K as [(interval, (num, den) lower bound or None, upper bound or None)], the r <= 0 piece included when
    stated. Raises ValueError when a piece does not parse or a denominator is not positive on its piece."""
    pieces = []
    for p in cfg.get("pieces", []):
        if set(p) - {"on", "lo", "hi"} or "on" not in p:
            raise ValueError(f"a piece is {{'on': interval, 'lo'?: bound, 'hi'?: bound}}, not {sorted(p)}")
        I = parse_interval(p["on"])
        b_lo = parse_bound(p["lo"]) if "lo" in p else None
        b_hi = parse_bound(p["hi"]) if "hi" in p else None
        for nd in (b_lo, b_hi):
            if nd is not None and (not nonneg_on(nd[1], I)["nonneg"] or not _no_root(nd[1], I)):
                raise ValueError(f"the denominator {U.show(nd[1], 'r')} is not positive on {p['on']}")
        pieces.append((I, b_lo, b_hi))
    if cfg.get("zero_for_nonpositive_r"):
        zero = ([], [Fraction(1)])
        pieces.append(((INF, False, Fraction(0), True), zero, zero))
    return pieces


def _limiter_claim(cfg: dict) -> str:
    ps = "; ".join(f"{p.get('lo', '-inf')} <= phi(r) <= {p.get('hi', 'inf')} on {p.get('on')}"
                   for p in cfg.get("pieces", []))
    z = "; phi(r) = 0 for r <= 0" if cfg.get("zero_for_nonpositive_r") else ""
    return (f"every flux-limited scheme with a limiter meeting {ps or '(no bounds)'}{z} is TVD for "
            f"0 <= nu <= {cfg.get('nu_max', '?')}")


def limiter_class(spec: dict) -> dict:
    cfg = spec.get("claims", {}).get("tvd_limiter_class")
    if cfg is None:
        return result("limiter_class", NOT_APPLICABLE, "TVD class (limiter)", "no class claim (claims.tvd_limiter_class)")
    claim = _limiter_claim(cfg)
    try:
        nu_max = Fraction(cfg["nu_max"])
        pieces = parse_pieces(cfg)
    except (KeyError, ValueError, TypeError, ZeroDivisionError) as ex:
        return result("limiter_class", UNKNOWN, claim, f"malformed class conditions: {ex}")
    if nu_max <= 0:
        return result("limiter_class", UNKNOWN, claim, "nu_max must be > 0")
    # the class is non-empty at every r: lo <= hi on every pair of overlapping pieces
    for (I, lo1, _), (J, _, hi2) in product(pieces, pieces):
        K = intersect(I, J)
        if K is None or lo1 is None or hi2 is None:
            continue
        diff = U.add(U.mul(hi2[0], lo1[1]), U.mul(lo1[0], hi2[1]), -1)
        d = nonneg_on(diff, K)
        if not d["nonneg"]:
            x = d["counterexample"]["x"]
            return result("limiter_class", UNKNOWN, claim, f"the class is empty: no phi meets K at r = {x} "
                                                           f"({_show_bound(lo1)} > {_show_bound(hi2)} there), so the "
                                                           "claim is vacuous")
    nus = sorted({nu_max * k for k in (Fraction(1), Fraction(1, 2), Fraction(1, 4), Fraction(1, 16), Fraction(1, 100))}
                 | ({Fraction(1)} if nu_max > 1 else set()), reverse=True)
    certs, failures = {}, []
    for label, region, side, tgt in limiter_targets(nu_max):
        gap = _covered(region, [I for I, *_ in pieces])
        if gap is not None:
            failures.append((label, gap, Fraction(-1) if side == "lo" else 3 + 3 / nu_max,
                             f"{label}: K does not bound phi at r = {gap}"))
            continue
        for I, b_lo, b_hi in pieces:
            J = intersect(I, region)
            if J is None:
                continue
            b = b_lo if side == "lo" else b_hi
            where = f"{label} on {show_interval(J)}"
            if b is None:
                x = _interior_point(J)
                failures.append((label, x, Fraction(-1) if side == "lo" else 3 + 3 / nu_max,
                                 f"{where}: K gives no {'lower' if side == 'lo' else 'upper'} bound"))
                continue
            # lo >= t  <=>  lo_n t_d - t_n lo_d >= 0 ;  hi <= t  <=>  t_n hi_d - hi_n t_d >= 0  (denominators > 0)
            p = U.add(U.mul(b[0], tgt[1]), U.mul(tgt[0], b[1]), -1) if side == "lo" else \
                U.add(U.mul(tgt[0], b[1]), U.mul(b[0], tgt[1]), -1)
            d = nonneg_on(p, J)
            if d["nonneg"]:
                certs[where] = {"polynomial >= 0": U.show(p, "r"), "certificate": U.jsonable(d["certificate"])}
            else:
                x = d["counterexample"]["x"]
                failures.append((label, x, _ev_bound(b, x), f"{where}: fails at r = {x} "
                                                            f"(bound {_show_bound(b)} = {_ev_bound(b, x)})"))
    assumes = ["linear advection u_t + a u_x = 0, a > 0, on the periodic grid, nu = a dt/dx; the flux-limited (Sweby) "
               "form G_j = nu u_j + nu(1 - nu)/2 phi(r_j) Delta_j, r_j = Delta_j-1 / Delta_j; phi is any function "
               "meeting the stated bounds"]
    if not failures and nu_max <= 1:
        return result("limiter_class", VERIFIED, claim,
                      f"the bounds imply every hypothesis of {LEAN_LIMITER} with nu_max = {nu_max} ({len(certs)} "
                      "piece-target pairs, each a polynomial >= 0 certified by Sturm sequences)",
                      {"sturm": certs}, assumes)
    for label, x, y, _ in failures:
        ce = limiter_counterexample(pieces, x, y, nus)
        if ce is not None:
            return result("limiter_class", REFUTED, claim,
                          f"a limiter of the class ({label} fails at r = {x}: phi(r) = {y}) and one step at nu = "
                          f"{ce['nu']} raises TV: {ce['TV(u)']} -> {ce['TV(v)']}", {"counterexample": ce}, assumes)
    if not failures:          # nu_max > 1: the theorem does not apply, and no counterexample was looked for yet
        for x in (Fraction(1), Fraction(1, 2), Fraction(2), Fraction(0)):
            lo, hi = _admissible(pieces, x)
            ce = limiter_counterexample(pieces, x, _clip(Fraction(0), lo, hi), nus)
            if ce is not None:
                return result("limiter_class", REFUTED, claim,
                              f"one step at nu = {ce['nu']} > 1 raises TV: {ce['TV(u)']} -> {ce['TV(v)']}",
                              {"counterexample": ce}, assumes)
        return result("limiter_class", UNKNOWN, claim, f"nu_max = {nu_max} > 1: the class theorem needs nu <= 1, and "
                                                       "no exact counterexample was found", {"sturm": certs}, assumes)
    return result("limiter_class", UNKNOWN, claim,
                  "K does not imply the class theorem's hypotheses (Sweby's region is sufficient, not necessary, so "
                  "this alone refutes nothing): " + "; ".join(dict.fromkeys(m for *_, m in failures))
                  + "; no exact counterexample found on the data tried", {"sturm": certs}, assumes)
