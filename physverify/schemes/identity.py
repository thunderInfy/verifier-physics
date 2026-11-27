"""Stated identities: the paper's printed formula satisfies its defining identity (scalar 1D laws).

The other checks decide properties of a scheme; this one decides whether a formula a source prints
(a numerical entropy flux, a viscosity coefficient, an amplification factor) is right. The spec gives
the printed expressions in `claims.stated_identity`; the form fixes the identity they must satisfy:

  entropy_balance  the scheme's flux F(uL, uR), the entropy eta(u), the stated numerical entropy flux
                   Qh(uL, uR) (`entropy_flux`) and the stated dissipation term D(um1, u0, up1)
                   (`dissipation`, default 0: entropy conservation) satisfy, on the three-point stencil,
                       eta'(u_i) * (-(F_{i+1/2} - F_{i-1/2})) = -(Qh_{i+1/2} - Qh_{i-1/2}) + D,
                   i.e. d/dt eta(u_i) + (Qh_{i+1/2} - Qh_{i-1/2})/dx = D/dx for the semi-discrete
                   scheme du_i/dt = -(F_{i+1/2} - F_{i-1/2})/dx (D is dx times the printed right side).
  entropy_pair     q'(u) = eta'(u) f'(u) for the PDE flux f.
  viscosity_form   F(uL, uR) = (f(uL) + f(uR))/2 - Q (uR - uL)/2 for the stated Q (in uL, uR, lam;
                   `nu` stands for lam*a when f = a*u is linear).
  amplification    the stated g(z, nu) equals the von Neumann symbol sum_k c_k(nu) z^k of a linear
                   constant-coefficient update, z = e^{i theta}, compared as Laurent polynomials in z.

`let` (optional) names subexpressions, substituted in order into later lets and the stated
expressions (written in uL, uR; they are placed at each interface afterwards). `domain` (optional)
lists conditions "p > 0" or "p >= 0" on the variables; a witness must satisfy them.

The residual LHS - RHS is brought to N/Dn with N, Dn in the normal form of poly.py (division by a sum
is allowed here: N/Dn = 0 iff N = 0 where Dn != 0). VERIFIED: N normalises to 0, so the identity holds
wherever every denominator is non-zero. REFUTED: an exact rational point inside the domain, with
Dn != 0, where N/Dn != 0 (for the amplification form, a rational nu and a rational point z = ((1 - t^2)
+ 2 t i)/(1 + t^2) on the unit circle, evaluated in exact complex rationals). UNKNOWN: anything outside
the fragment (exp, log, non-integer powers, ...), or a non-zero N with no witness found. No verdict
rests on a floating-point number.
"""

from __future__ import annotations

from fractions import Fraction
from itertools import product

from ..expr import E, diff, lit, substitute, var, variables
from . import checks, linear, poly as P
from .checks import NOT_APPLICABLE, REFUTED, UNKNOWN, VERIFIED, result

FORMS = ("entropy_balance", "entropy_pair", "viscosity_form", "amplification")
VALUES = [Fraction(x) for x in (0, 1, -1, 2, "1/2", -2, "-1/2", 3)]
TS = [Fraction(x) for x in (1, "1/2", 2, "1/3", 3, -1, "-1/2", -2)]     # z = ((1 - t^2) + 2ti)/(1 + t^2)


# ---------------------------------------------------------------- rational functions over poly.py

def rational(e: E) -> tuple[P.Poly, P.Poly]:
    """(N, Dn) with e = N/Dn wherever every denominator in e is non-zero. Raises P.Undecided."""
    k, a = e.kind, e.args
    if k in ("add", "sub"):
        (n1, d1), (n2, d2) = rational(a[0]), rational(a[1])
        return P.add(P.mul(n1, d2), P.mul(n2, d1), 1 if k == "add" else -1), P.mul(d1, d2)
    if k == "neg":
        n, d = rational(a[0])
        return P.scale(n, -1), d
    if k == "mul":
        (n1, d1), (n2, d2) = rational(a[0]), rational(a[1])
        return P.mul(n1, n2), P.mul(d1, d2)
    if k == "div":
        (n1, d1), (n2, d2) = rational(a[0]), rational(a[1])
        if not n2:
            raise P.Undecided("division by an expression that normalises to 0")
        return P.mul(n1, d2), P.mul(d1, n2)
    if k == "powi":
        n, d = rational(a[0])
        return (P.power(n, e.q), P.power(d, e.q)) if e.q >= 0 else (P.power(d, -e.q), P.power(n, -e.q))
    return P.from_expr(e), P.const(1)                 # var, lit, sqrt; anything else raises Undecided


def reduced(e: E) -> tuple[P.Poly, P.Poly, bool]:
    """`rational(e)` with a denominator that is a single monomial (a constant, lam, ...) moved into N
    as negative powers, and whether e has a denominator that is not a constant."""
    n, d = rational(e)
    divides = bool(set(d) - {()})
    if len(d) == 1 and all(a[0] == "v" for m in d for a, _ in m):
        return P.mul(n, P.inverse(d)), P.const(1), divides
    return n, d, divides


# ---------------------------------------------------------------- the stated expressions

def _block(spec: dict) -> dict:
    return spec["claims"]["stated_identity"]


def _stated(spec: dict, key: str) -> E:
    """The stated expression `key`, with the spec's params and the block's lets substituted."""
    e = checks._expr(spec, _block(spec)[key])
    lets = [(name, checks._expr(spec, s)) for name, s in _block(spec).get("let", {}).items()]
    for name, d in reversed(lets):                     # a later let may use an earlier one
        e = substitute(e, {name: d})
    return e


def _at(e: E, left: str, right: str) -> E:
    return substitute(e, {"uL": var(left), "uR": var(right)})


def _sub(a: E, b: E) -> E:
    return E("sub", (a, b))


def _mul(a: E, b: E) -> E:
    return E("mul", (a, b))


def _sides(spec: dict, form: str) -> tuple[E, E, str]:
    """(LHS, RHS, the identity in words) for a real form."""
    f = checks.pde_flux(spec)
    if form == "entropy_pair":
        eta, q = _stated(spec, "eta"), _stated(spec, "q")
        return diff(q, "u"), _mul(diff(eta, "u"), diff(f, "u")), "q'(u) = eta'(u) f'(u)"
    F = checks.numerical_flux(spec)
    if F is None:
        raise P.Undecided("no numerical flux declared (scheme.numerical_flux)")
    if form == "entropy_balance":
        v = substitute(diff(_stated(spec, "eta"), "u"), {"u": var("u0")})
        Qh = _stated(spec, "entropy_flux")
        D = _stated(spec, "dissipation") if "dissipation" in _block(spec) else lit(0)
        lhs = _mul(v, E("neg", (_sub(_at(F, "u0", "up1"), _at(F, "um1", "u0")),)))
        rhs = E("add", (E("neg", (_sub(_at(Qh, "u0", "up1"), _at(Qh, "um1", "u0")),)), D))
        return lhs, rhs, ("eta'(u_i) * (-(F_{i+1/2} - F_{i-1/2})) = -(Qh_{i+1/2} - Qh_{i-1/2}) + D "
                          "(the semi-discrete entropy balance times dx)")
    Q = _stated(spec, "Q")
    if "nu" in variables(Q):
        a = P.from_expr(diff(f, "u"))
        if P.variables(a):
            raise P.Undecided("Q depends on nu = lam*a but f is not linear")
        Q = substitute(Q, {"nu": _mul(var("lam"), lit(P.evaluate(a, {})))})
    favg = E("div", (E("add", (_at_u(f, "uL"), _at_u(f, "uR"))), lit(2)))
    rhs = _sub(favg, E("div", (_mul(Q, _sub(var("uR"), var("uL"))), lit(2))))
    return F, rhs, "F(uL, uR) = (f(uL) + f(uR))/2 - Q (uR - uL)/2"


def _at_u(e: E, x: str) -> E:
    return substitute(e, {"u": var(x)})


def _domain(spec: dict) -> list[tuple[P.Poly, P.Poly, bool]]:
    """(N, Dn, strict) for each condition N/Dn > 0 (strict) or >= 0."""
    out = []
    for c in _block(spec).get("domain", []):
        op = ">=" if ">=" in c else ">"
        lhs, rhs = c.split(op)
        n, d = rational(_sub(checks._expr(spec, lhs), checks._expr(spec, rhs)))
        out.append((n, d, op == ">"))
    return out


def _inside(dom, pt) -> bool:
    for n, d, strict in dom:
        try:
            nv, dv = P.evaluate(n, pt), P.evaluate(d, pt)
        except ZeroDivisionError:
            return False
        if nv is None or not dv:
            return False
        if (nv / dv > 0) if strict else (nv / dv >= 0):
            continue
        return False
    return True


def _witness(N, Dn, dom, names):
    """An exact rational point inside the domain with Dn != 0 and N != 0, or None."""
    names = sorted(names)
    grid = (dict(zip(names, vs)) for vs in product(VALUES, repeat=len(names))) if len(names) <= 5 else iter(())
    for pt in [*grid, *checks._points(names)]:
        if not _inside(dom, pt):
            continue
        try:
            n, d = P.evaluate(N, pt), P.evaluate(Dn, pt)
        except ZeroDivisionError:                      # a monomial denominator vanishes here
            continue
        if n and d:
            return pt, n / d
    return None


# ---------------------------------------------------------------- the amplification form

def _cmul(a, b):
    return a[0] * b[0] - a[1] * b[1], a[0] * b[1] + a[1] * b[0]


def _cpow(z, k: int):
    if k < 0:
        z, k = (z[0], -z[1]), -k                       # |z| = 1, so z^-1 is the conjugate
    out = (Fraction(1), Fraction(0))
    for _ in range(k):
        out = _cmul(out, z)
    return out


def _ceval(p: P.Poly, nu: Fraction, z) -> tuple[Fraction, Fraction]:
    """p(nu, z) for p a Laurent polynomial in nu and z, z a complex rational on the unit circle."""
    re, im = Fraction(0), Fraction(0)
    for m, c in p.items():
        t = (c, Fraction(0))
        for a, k in m:
            t = _cmul(t, _cpow(z, k)) if a == ("v", "z") else (t[0] * nu ** k, t[1] * nu ** k)
        re, im = re + t[0], im + t[1]
    return re, im


def _amplification(spec: dict, claim: str) -> dict:
    got, bad = linear.coefficients(spec, "stated_identity", claim)
    if bad:
        return {**bad, "status": UNKNOWN if bad["status"] == NOT_APPLICABLE else bad["status"]}
    a, c = got
    symbol = {}
    for k, ck in c.items():
        symbol = P.add(symbol, P.mul(ck, P.power(P.var("z"), k)))
    g = P.from_expr(_stated(spec, "g"))
    if P.variables(g) - {"nu", "z"}:
        return result("stated_identity", UNKNOWN, claim, f"g uses {sorted(P.variables(g) - {'nu', 'z'})}, not only nu, z")
    r = P.add(g, symbol, -1)
    wit = {"nu": f"{a}*lam (a = {a})", "z": "e^{i theta}", "symbol sum_k c_k z^k": P.show(symbol),
           "stated g": P.show(g), "residual g - symbol": P.show(r)}
    assumptions = ["linear constant-coefficient update on a uniform grid; z^-1 = e^{-i theta}"]
    if not r:
        return result("stated_identity", VERIFIED, claim, "g - symbol normalises to 0 as a Laurent polynomial in z",
                      wit, assumptions)
    dom = _domain(spec)
    for nu in VALUES:
        if not nu or not _inside(dom, {"nu": nu}):
            continue
        for t in TS:
            z = ((1 - t * t) / (1 + t * t), 2 * t / (1 + t * t))
            v = _ceval(r, nu, z)
            if any(v):
                wit["counterexample"] = {"nu": str(nu), "z": f"({z[0]}) + ({z[1]})i", "tan(theta/2)": str(t),
                                         "g - symbol": f"({v[0]}) + ({v[1]})i"}
                return result("stated_identity", REFUTED, claim,
                              f"g - symbol = ({v[0]}) + ({v[1]})i != 0 at nu = {nu}, z = e^(i theta) with "
                              f"tan(theta/2) = {t}", wit, assumptions)
    return result("stated_identity", UNKNOWN, claim, "non-zero residual but no witness found", wit, assumptions)


# ---------------------------------------------------------------- the check

def stated_identity(spec: dict) -> dict:
    block = spec.get("claims", {}).get("stated_identity")
    if block is None:
        return result("stated_identity", NOT_APPLICABLE, "stated identity", "no claims.stated_identity block")
    form = block.get("form")
    claim = f"stated identity ({form}): LHS - RHS = 0 for all states in the stated domain"
    if form not in FORMS:
        return result("stated_identity", UNKNOWN, claim, f"unknown form {form!r}; known: {FORMS}")
    try:
        if form == "amplification":
            return _amplification(spec, claim)
        lhs, rhs, words = _sides(spec, form)
        claim = f"stated identity ({form}): {words}, for all states in the stated domain"
        N, Dn, divides = reduced(_sub(lhs, rhs))
        dom = _domain(spec)
    except P.Undecided as ex:
        return result("stated_identity", UNKNOWN, claim, str(ex))
    wit = {"residual LHS - RHS": P.show(N) + ("" if Dn == P.const(1) else f" over {P.show(Dn)}")}
    assumptions = ["every denominator of the stated expressions is non-zero"] if divides else []
    if block.get("domain"):
        assumptions.append("states in the domain " + ", ".join(block["domain"]))
    if not N:
        return result("stated_identity", VERIFIED, claim, "LHS - RHS normalises to 0", wit, assumptions)
    if "lam" in P.variables(N) | P.variables(Dn):
        dom.append((P.var("lam"), P.const(1), True))
        assumptions.append("lam = dt/dx > 0")
    hit = _witness(N, Dn, dom, P.variables(N) | P.variables(Dn))
    if hit is None:
        return result("stated_identity", UNKNOWN, claim, "non-zero residual but no witness found in the domain",
                      wit, assumptions)
    pt, val = hit
    wit["counterexample"] = {"point": checks._fmt(pt), "LHS - RHS": str(val)}
    return result("stated_identity", REFUTED, claim, f"LHS - RHS = {val} != 0 at {checks._fmt(pt)}", wit, assumptions)
