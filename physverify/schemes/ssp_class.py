"""SSP claims about a class of Runge-Kutta methods, and about the value of the SSP coefficient (exact).

Two checks, one per claim kind; neither needs a scheme, only Runge-Kutta coefficients.

`ssp_class` (claim `ssp_class_preserves`): "every explicit s-stage method in Shu-Osher form whose
coefficients satisfy the conditions K keeps every convex property forward Euler keeps, under
dt <= c * dt_FE". K is a finite list of linear (in)equalities over alpha_ik, beta_ik (1 <= i <= s,
0 <= k < i), written out or taken from named families (`FAMILIES`). Its Lean statement,
`PhysVerify.SSP.ssp_class_preserves_meaning`, is a corollary of `ssp_preserves_meaning` (written, not
yet checked by a Lean build, so the registry lists the kind as gloss only for now): it holds
for the class as soon as K implies, for every k < i <= s,

    alpha_ik >= 0,   beta_ik >= 0,   c beta_ik <= alpha_ik,   sum_k alpha_ik = 1,

and c > 0 (then alpha_ik = 0 forces beta_ik = 0, the rest of `Admissible`). Each target is a linear
inequality, so "K implies it" is decided exactly by linear programming over the rationals
(exactlp.py): VERIFIED needs a Farkas certificate for every target (multipliers y >= 0 with
target = r + sum_j y_j K_j, r >= 0, replayed as an identity). When some target is not implied,
the LP gives a method in K that violates it, and we look for a scalar counterexample:

  - a row of alpha not summing to 1: F = 0 keeps the convex set S = {1} for every step, and the
    first such stage is (row sum) != 1;
  - otherwise the method's v(c) or P(c) (ssp.py) has a negative entry: `ssp.class_witness` gives F on
    the real line with x + tF(x) >= 0 for x >= 0, t in [0, 1] (S = [0, inf), dt_FE = 1) and a negative
    stage at dt = c. We recompute the stages from the Shu-Osher arrays themselves and check both facts.

If the violating method still has v(c), P(c) >= 0 it has another Shu-Osher form with ratio c, so it is
no counterexample; then, or when K is empty, has a strict inequality we cannot meet, is nonlinear or
does not fix s, the result is UNKNOWN. Nothing here samples: every VERIFIED and REFUTED is exact.

`ssp_coefficient` (claim `ssp_coefficient`): "C(method) R value" or "C(method) R C(other)" for R in
=, <=, >=, <, >, with C the exact SSP coefficient of `ssp.coefficient` (Sturm isolation, certified at
both ends: an admissible Shu-Osher form at C, and a class witness just above it). An irrational C is
known only in a rational enclosure [lo, hi); a comparison the enclosure does not settle is UNKNOWN.
"""

from __future__ import annotations

from fractions import Fraction

from ..expr import parse
from . import checks, exactlp, poly as P, ssp, univariate as U
from .checks import NOT_APPLICABLE, REFUTED, UNKNOWN, VERIFIED, result

LEAN_CLASS = "PhysVerify.SSP.ssp_class_preserves_meaning"
RELS = ("<=", ">=", "<", ">", "=")
FAMILIES = {"alpha_nonneg": "alpha_ik >= 0", "beta_nonneg": "beta_ik >= 0", "alpha_row_sums_1": "sum_k alpha_ik = 1",
            "ratio_c": "c beta_ik <= alpha_ik", "abs_ratio_c": "c |beta_ik| <= alpha_ik"}


def names(s: int) -> list[str]:
    return [f"{a}_{i}{k}" for i in range(1, s + 1) for k in range(i) for a in ("alpha", "beta")]


def _aff(c0=Fraction(0), **lin) -> tuple:
    return (Fraction(c0), {k: Fraction(v) for k, v in lin.items() if v})


def family(name: str, s: int, c: Fraction) -> list[tuple]:
    """The conditions (const, {var: coef}, rel) of a named family, rel in >=, >, =."""
    pairs = [(i, k) for i in range(1, s + 1) for k in range(i)]
    if name == "alpha_nonneg":
        return [(*_aff(**{f"alpha_{i}{k}": 1}), ">=") for i, k in pairs]
    if name == "beta_nonneg":
        return [(*_aff(**{f"beta_{i}{k}": 1}), ">=") for i, k in pairs]
    if name == "alpha_row_sums_1":
        return [(*_aff(-1, **{f"alpha_{i}{k}": 1 for k in range(i)}), "=") for i in range(1, s + 1)]
    if name == "ratio_c":
        return [(*_aff(**{f"alpha_{i}{k}": 1, f"beta_{i}{k}": -c}), ">=") for i, k in pairs]
    if name == "abs_ratio_c":
        return [(*_aff(**{f"alpha_{i}{k}": 1, f"beta_{i}{k}": sg * c}), ">=") for i, k in pairs for sg in (-1, 1)]
    raise ValueError(f"unknown family {name!r}; known: {sorted(FAMILIES)}")


def parse_condition(text: str, allowed: set) -> tuple:
    """'lhs REL rhs' -> (const, {var: coef}, rel) with rel in >=, >, = (sides moved so that 'expr rel 0').
    Raises ValueError when it is not a linear (in)equality over the allowed variables."""
    for rel in RELS:
        if rel in text:
            lhs, rhs = text.split(rel, 1)
            if any(r in rhs for r in RELS):
                raise ValueError(f"{text!r}: one relation per condition")
            break
    else:
        raise ValueError(f"{text!r}: no relation (one of {RELS})")
    diff = P.add(P.from_expr(parse(lhs)), P.from_expr(parse(rhs)), -1)
    if rel in ("<=", "<"):
        diff = P.scale(diff, Fraction(-1))
    vs = sorted(P.variables(diff))
    if set(vs) - allowed:
        raise ValueError(f"{text!r}: variables {sorted(set(vs) - allowed)} are not coefficients alpha_ik, beta_ik "
                         "of the stated stage count")
    lin = checks._linear(diff, vs)
    if lin is None:
        raise ValueError(f"{text!r} is not linear in the coefficients")
    return lin[0], lin[1], {"<=": ">=", "<": ">"}.get(rel, rel)


def targets(s: int, c: Fraction) -> list[tuple]:
    """(label, (const, {var: coef})) for the hypotheses of ssp_preserves_meaning, each `>= 0`; the
    row sums as two inequalities, first so that a violated row sum is found before anything else."""
    out = []
    for i in range(1, s + 1):
        row = {f"alpha_{i}{k}": Fraction(1) for k in range(i)}
        out += [(f"sum_k alpha_{i}k >= 1", (Fraction(-1), row)),
                (f"sum_k alpha_{i}k <= 1", (Fraction(1), {v: -x for v, x in row.items()}))]
    for i in range(1, s + 1):
        for k in range(i):
            a, b = f"alpha_{i}{k}", f"beta_{i}{k}"
            out += [(f"{a} >= 0", _aff(**{a: 1})), (f"{b} >= 0", _aff(**{b: 1})),
                    (f"{c} * {b} <= {a}", _aff(**{a: 1, b: -c}))]
    return out


def _show(cond: tuple) -> str:
    c0, lin, rel = cond
    terms = [f"{v}*{k}" for k, v in lin.items()] + ([str(c0)] if c0 or not lin else [])
    return " + ".join(terms) + f" {rel} 0"


def _arrays(x: dict, s: int) -> tuple[list, list]:
    g = lambda a, i, k: x.get(f"{a}_{i}{k}", Fraction(0))
    return ([[g("alpha", i, k) for k in range(i)] for i in range(1, s + 1)],
            [[g("beta", i, k) for k in range(i)] for i in range(1, s + 1)])


def so_stages(alpha, beta, F, u0, dt) -> list:
    """The Shu-Osher stages u_0..u_s, straight from the arrays (no Butcher form)."""
    u = [u0]
    for ra, rb in zip(alpha, beta):
        u.append(sum((a * u[k] + dt * b * F(u[k]) for k, (a, b) in enumerate(zip(ra, rb))), Fraction(0)))
    return u


def counterexample(x: dict, s: int, c: Fraction) -> dict | None:
    """An exact scalar counterexample for the method x (a dict of coefficients), or None: a convex set S,
    F with forward Euler keeping S for steps in [0, 1], u0 in S and a stage outside S at dt = c."""
    alpha, beta = _arrays(x, s)
    for i, row in enumerate(alpha, 1):
        if sum(row) != 1:
            F = lambda v: Fraction(0)
            u = so_stages(alpha, beta, F, Fraction(1), c)
            j = next(j for j in range(1, s + 1) if u[j] != 1)
            return {"alpha": U.jsonable(alpha), "beta": U.jsonable(beta), "S": "{1} (a point; convex)",
                    "F": "F = 0 (forward Euler keeps S for every step)", "u0": "1", "dt/dt_FE": str(c),
                    "stages": [str(v) for v in u], "leaves S": f"u_{j} = {u[j]} != 1 (row {i} of alpha sums to "
                                                              f"{sum(row)})"}
    K = ssp.shu_osher_K(alpha, beta)
    v, Pm = ssp.am_at(K, c)
    if min(v) >= 0 and min(x for r in Pm for x in r) >= 0:
        return None                     # another Shu-Osher form of this method has ratio c: no counterexample
    w = ssp.class_witness(K, c)
    if w is None:
        return None
    table = {Fraction(k): Fraction(val) for k, val in w["F at the stage points"].items()}
    F = lambda y: table[y] if y in table else -y
    u0 = w["u0"]
    u = so_stages(alpha, beta, F, u0, c)
    fe_ok = u0 >= 0 and all(y < 0 or y + F(y) >= 0 for y in table)      # x + tF(x) is affine in t
    bad = [j for j in range(1, s + 1) if u[j] < 0]
    if not (fe_ok and bad):
        return None
    return {"alpha": U.jsonable(alpha), "beta": U.jsonable(beta), "S": "[0, inf)",
            "F": {**{str(k): str(val) for k, val in table.items()}, "elsewhere": "F(x) = -x"},
            "forward Euler": "x + tF(x) >= 0 for every x >= 0 and t in [0, 1] (checked at the stage points; "
                             "elsewhere it is (1 - t) x)",
            "u0": str(u0), "dt/dt_FE": str(c), "stages": [str(y) for y in u],
            "leaves S": f"u_{bad[-1]} = {u[bad[-1]]} < 0", "entry": w["entry"]}


def _claim_text(cfg: dict) -> str:
    return (f"every explicit {cfg.get('stages', '?')}-stage method in Shu-Osher form with coefficients satisfying "
            f"{', '.join(cfg.get('families', []) + cfg.get('conditions', [])) or '(no conditions)'} keeps every convex "
            f"property forward Euler keeps, for dt <= {cfg.get('c', '?')} * dt_FE")


def ssp_class(spec: dict) -> dict:
    cfg = spec.get("claims", {}).get("ssp_class")
    if cfg is None:
        return result("ssp_class", NOT_APPLICABLE, "SSP class", "no class claim (claims.ssp_class)")
    claim = _claim_text(cfg)
    s = cfg.get("stages")
    if not isinstance(s, int) or s < 1:
        return result("ssp_class", UNKNOWN, claim, "the conditions must fix the stage count (claims.ssp_class.stages, "
                                                    "an integer >= 1); a class over every s is not a finite system")
    try:
        c = Fraction(cfg["c"])
    except (KeyError, ValueError, TypeError, ZeroDivisionError):
        return result("ssp_class", UNKNOWN, claim, "claims.ssp_class.c must be a rational number")
    if c <= 0:
        return result("ssp_class", UNKNOWN, claim, "c <= 0: the class theorem gives no positive step")
    vs = names(s)
    try:
        conds = [q for f in cfg.get("families", []) for q in family(f, s, c)]
        conds += [parse_condition(t, set(vs)) for t in cfg.get("conditions", [])]
    except (ValueError, P.Undecided) as ex:
        return result("ssp_class", UNKNOWN, claim, str(ex))
    certs, failed = {}, []
    for label, tgt in targets(s, c):
        m = exactlp.minimize_affine(conds, tgt, vs)
        if m["status"] == "infeasible":
            return result("ssp_class", UNKNOWN, claim, "the conditions have no solution (even with strict inequalities "
                                                        "relaxed): the class is empty, so the claim is vacuous")
        if m["status"] == "optimal" and m["value"] >= 0:
            cert = exactlp.farkas(conds, tgt, vs)
            if cert is None:
                return result("ssp_class", UNKNOWN, claim, f"{label}: the LP minimum is >= 0 but no Farkas certificate "
                                                            "replayed (a bug in exactlp.py)")
            certs[label] = {"remainder": str(cert["remainder"]),
                            "multipliers": {_show(q): str(y) for q, y in zip(conds, cert["multipliers"]) if y}}
            continue
        failed.append((label, tgt, m))
    if not failed:
        return result("ssp_class", VERIFIED, claim,
                      f"the conditions imply every hypothesis of the class theorem for s = {s}, c = {c} "
                      f"({len(certs)} targets, each with a Farkas certificate); with c > 0, beta_ik >= 0 and "
                      f"c beta_ik <= alpha_ik force beta_ik = 0 where alpha_ik = 0 (ssp_preserves_meaning; the class "
                      f"form {LEAN_CLASS} is not yet Lean-checked)",
                      {"farkas": certs}, ["explicit Runge-Kutta methods in Shu-Osher form with s stages; "
                                          "every convex set S and F with forward Euler keeping S on [0, dt_FE]"])
    tried = []
    pool = None
    for label, tgt, m in failed:
        t0, t = tgt
        val = lambda x: t0 + sum((t.get(v, 0) * x[v] for v in vs), Fraction(0))
        pts = [m["point"]]
        if m["status"] == "unbounded":
            base, ray = m["point"], m["ray"]
            slope = sum((t.get(v, 0) * ray[v] for v in vs), Fraction(0))
            lam = max(Fraction(0), (val(base) + 1) / -slope)
            pts = [{v: base[v] + L * ray[v] for v in vs} for L in (lam, 2 * lam + 1, 4 * lam + 3)]
        # an LP vertex can be degenerate (two stages at one point, which hides a negative beta), so also
        # try convex combinations with other points of the class, close enough to keep the violation
        if pool is None:
            pool = _pool(conds, vs)
        x0 = pts[0]
        for y in pool:
            for th in (Fraction(1, 2), Fraction(1, 4), Fraction(1, 16)):
                z = {v: (1 - th) * x0[v] + th * y[v] for v in vs}
                if val(z) < 0:
                    pts.append(z)
                    break
        for x in pts:
            if not all(exactlp.holds(q, x) for q in conds):
                tried.append(f"{label}: an LP point misses a strict condition")
                continue
            ce = counterexample(x, s, c)
            if ce is not None:
                return result("ssp_class", REFUTED, claim,
                              f"a method in the class violates {label}, and one step at dt = {c} dt_FE leaves a convex "
                              f"set forward Euler keeps: {ce['leaves S']}", {"counterexample": ce},
                              ["scalar counterexample; F is a function on the real line, defined pointwise"])
            tried.append(f"{label}: no violating method tried gave a counterexample (v(c), P(c) >= 0, so another "
                         "Shu-Osher form has ratio c, or the witness needs two stages at one point)")
    return result("ssp_class", UNKNOWN, claim,
                  f"not implied: {', '.join(lab for lab, _, _ in failed)}; no exact counterexample found ("
                  + "; ".join(dict.fromkeys(tried)) + ")", {"farkas": certs})


def _pool(conds: list, vs: list) -> list[dict]:
    """Points of the (relaxed) class: LP optima of +-x_v for each coefficient, where bounded."""
    out = []
    for v in vs:
        for sg in (1, -1):
            m = exactlp.minimize_affine(conds, (Fraction(0), {v: Fraction(sg)}), vs)
            if m["status"] == "optimal" and m["point"] not in out:
                out.append(m["point"])
    return out


# ---------------------------------------------------------------- the value of C

def _enclosure(method) -> tuple[Fraction, Fraction, dict]:
    """(lo, hi, coefficient dict) with C = lo when exact (hi = lo then), else lo <= C < hi."""
    c = ssp.coefficient(method)
    if c["C"] is not None:
        return c["C"], c["C"], c
    return c["lo"], c["hi"], c


_CMP = {"=": lambda a, b: a == b, "<=": lambda a, b: a <= b, ">=": lambda a, b: a >= b,
        "<": lambda a, b: a < b, ">": lambda a, b: a > b}


def _decide(rel: str, a: tuple, b: tuple) -> bool | None:
    """The truth of x rel y for x in a, y in b, where (lo, hi) is the point lo when lo == hi, else
    [lo, hi); None when the intervals do not settle it."""
    (alo, ahi), (blo, bhi) = a, b
    if alo == ahi and blo == bhi:
        return _CMP[rel](alo, blo)
    a_pt, b_pt = alo == ahi, blo == bhi
    # x <= y surely when x's upper end is <= y's lower end (x < ahi when a is an interval)
    lt = ahi < blo or (ahi == blo and not a_pt)                       # surely x < y
    gt = alo > bhi or (alo == bhi and not b_pt)                       # surely x > y
    le, ge = lt or (ahi <= blo), gt or (alo >= bhi)
    if rel == "<":
        return True if lt else False if ge else None
    if rel == ">":
        return True if gt else False if le else None
    if rel == "<=":
        return True if le else False if gt else None
    if rel == ">=":
        return True if ge else False if lt else None
    return False if (lt or gt) else None


def ssp_coefficient(spec: dict) -> dict:
    cfg = spec.get("claims", {}).get("ssp_coefficient")
    if cfg is None:
        return result("ssp_coefficient", NOT_APPLICABLE, "SSP coefficient", "no claim (claims.ssp_coefficient)")
    rel = cfg.get("relation", "=")
    label = lambda m: m if isinstance(m, str) else "the stated method"
    rhs = label(cfg["other"]) if "other" in cfg else str(cfg.get("value"))
    claim = f"C({label(cfg.get('method'))}) {rel} {'C(' + rhs + ')' if 'other' in cfg else rhs}"
    if rel not in _CMP:
        return result("ssp_coefficient", UNKNOWN, claim, f"relation must be one of {sorted(_CMP)}")
    try:
        alo, ahi, ca = _enclosure(cfg["method"])
        if "other" in cfg:
            blo, bhi, cb = _enclosure(cfg["other"])
        else:
            blo = bhi = Fraction(cfg["value"])
            cb = None
    except (ssp.Unsupported, KeyError, ValueError, TypeError) as ex:
        return result("ssp_coefficient", UNKNOWN, claim, str(ex))
    show = lambda lo, hi: str(lo) if lo == hi else f"in [{lo}, {hi})"
    wit = {"C": show(alo, ahi), "binding entries": ca["binding"]}
    if cb is not None:
        wit["C(other)"] = show(blo, bhi)
    got = _decide(rel, (alo, ahi), (blo, bhi))
    detail = f"C = {show(alo, ahi)}" + (f", C(other) = {show(blo, bhi)}" if cb is not None else "")
    if got is None:
        return result("ssp_coefficient", UNKNOWN, claim, detail + ": the rational enclosure does not settle it", wit)
    return result("ssp_coefficient", VERIFIED if got else REFUTED, claim,
                  detail + " (exact: an admissible Shu-Osher form with ratio C, and a class witness above C)", wit,
                  ["C is the radius of absolute monotonicity of the Butcher tableau (ssp.py)"])
