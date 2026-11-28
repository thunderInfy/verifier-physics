"""Strong-stability-preserving (SSP) Runge-Kutta methods: the class theorem as a check (exact, Fraction only).

The class theorem (`lean/PhysVerify/SSP.lean`, `ssp_preserves_meaning`, proven): write an explicit
s-stage method in Shu-Osher form, u_0 = u^n, u_i = sum_{k<i} (alpha_ik u_k + dt beta_ik F(u_k)), u_s =
u^{n+1}, with alpha, beta >= 0, each row of alpha summing to 1 and beta_ik = 0 wherever alpha_ik = 0. If
the forward-Euler step v + t F(v) stays in a convex set S for every v in S and 0 <= t <= tau, every
stage stays in S for 0 <= dt <= c tau, c = min_{beta_ik > 0} alpha_ik / beta_ik. Positivity, the global
maximum principle (a box [m, M]^N) and TVD (a sublevel set of the total variation, which is convex)
are instances, so the forward-Euler certificates of this package (`positivity`, `tvd_harten`,
`tvd_linear`, `max_principle_linear`) carry over to the Runge-Kutta step at a CFL number C times theirs.

The SSP coefficient C of a method. A method has many Shu-Osher forms; the best c over all of them is
the radius of absolute monotonicity of its Butcher tableau. With K = [[A, 0], [b^T, 0]] ((s+1) x (s+1),
strictly lower triangular for an explicit method), let

    v(r) = (I + rK)^{-1} e,     P(r) = r K (I + rK)^{-1}.

K is nilpotent, so (I + rK)^{-1} = sum_j (-rK)^j and every entry of v(r) and P(r) is a polynomial in r
with rational coefficients. We compute

    C = sup {r >= 0 : v(rho) >= 0 and P(rho) >= 0 entrywise for every rho in [0, r]}

exactly: for each entry polynomial, the first point right of 0 where it changes sign (0 if its lowest
coefficient is negative; otherwise the smallest positive root of odd multiplicity, isolated by Sturm
bisection), and C is the smallest of these. This is neither an LP nor a bisection on feasibility: it is
exact root isolation on finitely many polynomials. C is reported exactly when that root is rational
(it is found as the simplest rational in a shrinking isolating interval and checked to be a root);
otherwise as a rational enclosure [lo, hi] of width below 2^-64. Kraaijevanger (1991) shows the set
of r where v, P >= 0 is an interval, so C is his radius R(K); nothing below relies on that, because
both ends are certified directly:

  - below: at r = C (or lo), alpha = [v + P_{.0} | P_{.k}], beta = P / r is an admissible Shu-Osher form
    of the same method (checked by converting it back to K) with ratio r, so the Lean lemma applies;
  - above: at some r slightly above C (or at hi), an entry of v(r) or P(r) is negative, and an explicit
    right-hand side F on S = [0, inf) with x + tF(x) >= 0 for all x >= 0, t in [0, 1] has a stage (the
    new step, when possible) below 0 at dt = r (`class_witness`): no bound dt <= r tau holds for the
    whole class. That witness is abstract (a one-dimensional F, defined pointwise); it is evidence
    about the method, never about a particular scheme.

`ssp` (the check behind the claim `ssp_preserves`) needs the spec's update to be a forward-Euler step
of a semi-discrete scheme, u_i + lam G(u) with G independent of lam (a numerical flux free of lam),
and runs the forward-Euler certificate on [0, cfl / C]. Two more checks bear on the claim:
`ssp_linear` decides it exactly for linear constant-coefficient schemes (the Runge-Kutta step is then
the stability polynomial R(z) = sum_j gamma_j z^j of the forward-Euler operator, a linear scheme of
its own), and `ssp_violation` searches exact rational states for one Runge-Kutta step that breaks the
property, for any scheme in the exact fragment.
"""

from __future__ import annotations

from fractions import Fraction

from ..expr import E
from . import checks, poly as P, univariate as U
from .checks import NOT_APPLICABLE, REFUTED, UNKNOWN, VERIFIED, result

LEAN = "PhysVerify.SSP.ssp_preserves_meaning"
LEAN_INSTANCE = {"positivity": "PhysVerify.SSP.ssp_nonneg", "tvd": "PhysVerify.SSP.ssp_tvd",
                 "max_principle": "PhysVerify.SSP.ssp_bounds"}
PROPERTIES = ("positivity", "tvd", "max_principle")
EPS = Fraction(1, 2 ** 64)          # width of the enclosure of an irrational C

# Named methods. SSPRK(5,4) is the five-stage fourth-order method of Spiteri and Ruuth (2002) as printed,
# to 15 digits, in Shu-Osher form; the rationals here are those decimals, so the method is fourth order
# only up to the rounding (tests/test_ssp.py checks the order conditions to 1e-14) and C is that of these
# rationals. As printed, the last row of alpha sums to 1 + 1e-15; we lower its last entry by 1e-15
# (0.386708617503269 -> ...268) so that the form is consistent.
METHODS = {
    "forward_euler": {"butcher": {"A": [["0"]], "b": ["1"]}},
    "ssprk22": {"shu_osher": {"alpha": [["1"], ["1/2", "1/2"]], "beta": [["1"], ["0", "1/2"]]}},
    "ssprk33": {"shu_osher": {"alpha": [["1"], ["3/4", "1/4"], ["1/3", "0", "2/3"]],
                              "beta": [["1"], ["0", "1/4"], ["0", "0", "2/3"]]}},
    "ssprk54": {"shu_osher": {
        "alpha": [["1"],
                  ["0.444370493651235", "0.555629506348765"],
                  ["0.620101851488403", "0", "0.379898148511597"],
                  ["0.178079954393132", "0", "0", "0.821920045606868"],
                  ["0", "0", "0.517231671970585", "0.096059710526147", "0.386708617503268"]],
        "beta": [["0.391752226571890"],
                 ["0", "0.368410593050371"],
                 ["0", "0", "0.251891774271694"],
                 ["0", "0", "0", "0.544974750228521"],
                 ["0", "0", "0", "0.063692468666290", "0.226007483236906"]]}},
    "rk4": {"butcher": {"A": [["0", "0", "0", "0"], ["1/2", "0", "0", "0"], ["0", "1/2", "0", "0"],
                              ["0", "0", "1", "0"]],
                        "b": ["1/6", "1/3", "1/3", "1/6"]}},
}


class Unsupported(ValueError):
    """The method is outside what this module decides (implicit, malformed); the message says why."""


# ---------------------------------------------------------------- methods as K

def _fr(rows) -> list:
    return [[Fraction(x) for x in row] for row in rows]


def butcher_K(A, b) -> list:
    """K = [[A, 0], [b^T, 0]] for an explicit tableau (A strictly lower triangular)."""
    A, b = _fr(A), [Fraction(x) for x in b]
    s = len(b)
    if len(A) != s or any(len(row) != s for row in A):
        raise Unsupported(f"A must be {s} x {s} for {s} weights b")
    if any(A[i][j] for i in range(s) for j in range(i, s)):
        raise Unsupported("implicit tableau (A has a non-zero entry on or above the diagonal): explicit methods only")
    return [row + [Fraction(0)] for row in A] + [b + [Fraction(0)]]


def shu_osher_K(alpha, beta) -> list:
    """K of the method u_i = sum_{k<i} (alpha_ik u_k + dt beta_ik F(u_k)), i = 1..s (row i - 1 of the
    arrays has i entries). Each row of alpha must sum to 1; then u_i = u_0 + dt sum_k K_ik F(u_k) with
    K_ik = beta_ik + sum_{k<l<i} alpha_il K_lk."""
    alpha, beta = _fr(alpha), _fr(beta)
    s = len(alpha)
    if len(beta) != s or any(len(alpha[i]) != i + 1 or len(beta[i]) != i + 1 for i in range(s)):
        raise Unsupported("Shu-Osher arrays: row i (i = 1..s) must list the coefficients of u_0..u_{i-1}")
    for i, row in enumerate(alpha, 1):
        if sum(row) != 1:
            raise Unsupported(f"row {i} of alpha sums to {sum(row)}, not 1 (the form needs consistency)")
    K = [[Fraction(0)] * (s + 1) for _ in range(s + 1)]
    for i in range(1, s + 1):
        for k in range(i):
            K[i][k] = beta[i - 1][k] + sum((alpha[i - 1][l] * K[l][k] for l in range(k + 1, i)), Fraction(0))
    return K


def method_K(method) -> tuple[list, dict | None, str]:
    """(K, Shu-Osher arrays or None, a name) for a method name, {"butcher": {"A", "b"}} or
    {"shu_osher": {"alpha", "beta"}}."""
    name = method if isinstance(method, str) else "the method"
    if isinstance(method, str):
        if method not in METHODS:
            raise Unsupported(f"unknown method {method!r}; known: {sorted(METHODS)}")
        method = METHODS[method]
    if "butcher" in method:
        return butcher_K(method["butcher"]["A"], method["butcher"]["b"]), None, name
    if "shu_osher" in method:
        so = method["shu_osher"]
        return shu_osher_K(so["alpha"], so["beta"]), {"alpha": _fr(so["alpha"]), "beta": _fr(so["beta"])}, name
    raise Unsupported("a method is a name, {\"butcher\": {\"A\", \"b\"}} or {\"shu_osher\": {\"alpha\", \"beta\"}}")


def shu_osher_ratio(alpha, beta) -> dict:
    """The SSP coefficient of one Shu-Osher form, min alpha/beta over beta > 0, when the form is
    admissible for the Lean lemma (alpha, beta >= 0, beta = 0 where alpha = 0); else the reason."""
    alpha, beta = _fr(alpha), _fr(beta)
    for i, (ra, rb) in enumerate(zip(alpha, beta), 1):
        for k, (a, b) in enumerate(zip(ra, rb)):
            if a < 0 or b < 0:
                return {"admissible": False, "c": Fraction(0),
                        "reason": f"alpha_{i}{k} = {a}, beta_{i}{k} = {b}: the lemma needs alpha, beta >= 0 (a negative "
                                  "beta needs a downwind operator, which this form does not have)"}
            if a == 0 and b > 0:
                return {"admissible": True, "c": Fraction(0),
                        "reason": f"beta_{i}{k} = {b} > 0 with alpha_{i}{k} = 0: ratio 0"}
    ratios = [a / b for ra, rb in zip(alpha, beta) for a, b in zip(ra, rb) if b > 0]
    if not ratios:
        raise Unsupported("the method never evaluates F")
    return {"admissible": True, "c": min(ratios), "reason": ""}


# ---------------------------------------------------------------- v(r), P(r) as polynomial matrices

def _mm(X, Y) -> list:
    n = len(X)
    return [[sum((X[i][l] * Y[l][j] for l in range(n)), Fraction(0)) for j in range(n)] for i in range(n)]


def am_polys(K) -> tuple[list, list]:
    """(v, Pm): v[i] and Pm[i][j] as coefficient lists in r (constant first), v(r) = (I + rK)^{-1} e and
    P(r) = rK (I + rK)^{-1} = sum_{j >= 1} (-1)^(j-1) r^j K^j."""
    n = len(K)
    v = [[Fraction(1)] for _ in range(n)]
    Pm = [[[] for _ in range(n)] for _ in range(n)]
    Kj, sign = K, 1
    for j in range(1, n):
        ones = [sum(row, Fraction(0)) for row in Kj]           # K^j e
        for i in range(n):
            v[i] = U.add(v[i], [Fraction(0)] * j + [-sign * ones[i]])
            for k in range(n):
                Pm[i][k] = U.add(Pm[i][k], [Fraction(0)] * j + [sign * Kj[i][k]])
        Kj, sign = _mm(Kj, K), -sign
    return [U.trim(p) for p in v], [[U.trim(p) for p in row] for row in Pm]


def am_at(K, r: Fraction) -> tuple[list, list]:
    v, Pm = am_polys(K)
    return [U.ev(p, r) for p in v], [[U.ev(p, r) for p in row] for row in Pm]


def _entries(K) -> list:
    """(label, polynomial) for every entry that can bind: v_i and P_ik for i = 1..s, k < s."""
    v, Pm = am_polys(K)
    n = len(K)
    out = [(f"v_{i}", v[i]) for i in range(1, n)]
    out += [(f"P_{i}{k}", Pm[i][k]) for i in range(1, n) for k in range(n - 1)]
    return [(lab, p) for lab, p in out if p]


def _simplest_between(a: Fraction, b: Fraction) -> Fraction:
    """The rational with the smallest denominator in the open interval (a, b), a < b (Stern-Brocot)."""
    fl = a.numerator // a.denominator
    if Fraction(fl + 1) < b:
        return Fraction(fl + 1)
    if a == fl:                                               # a an integer: fl + 1 >= b, look in (a, b)
        return fl + 1 / _simplest_above(1 / (b - fl))
    return fl + 1 / _simplest_between(1 / (b - fl), 1 / (a - fl))


def _simplest_above(x: Fraction) -> Fraction:
    """The simplest rational strictly greater than x (x > 0): floor(x) + 1."""
    return Fraction(x.numerator // x.denominator + 1)


def first_sign_change(p: list) -> dict:
    """sup {r >= 0 : p >= 0 on [0, r]} for a non-zero p in Q[r]: {"kind": "zero"} (lowest coefficient
    negative), {"kind": "never"}, or {"kind": "root", "lo", "hi", "exact"} with the point in [lo, hi]
    (lo = hi = exact when it is a rational root), p >= 0 on [0, lo] and p(hi) < 0."""
    p = U.trim(p)
    low = next(c for c in p if c)
    if low < 0:
        return {"kind": "zero"}
    _, factors = U.squarefree(p)
    g = [Fraction(1)]
    for i, f in factors:
        if i % 2:
            g = U.mul(g, f)
    g = U.trim(g)
    if U.deg(g) <= 0:
        return {"kind": "never"}
    seq = U.sturm_sequence(g)
    bound = 1 + max(abs(c / g[-1]) for c in g[:-1])           # Cauchy: every root has |x| < bound
    if U.roots_open(seq, Fraction(0), bound) == 0:
        return {"kind": "never"}
    a, b = Fraction(0), bound          # no root of g in (0, a]; at least one in (a, b)
    step = 0
    while True:
        step += 1
        if step > U.MAX_STEPS:
            raise AssertionError("Sturm bisection did not converge")
        m = (a + b) / 2
        if U.ev(g, m) == 0 and U.roots_open(seq, a, m) == 0:
            return _exact_root(p, g, seq, m)
        if U.roots_open(seq, a, m) >= 1 or U.ev(g, m) == 0:
            b = m
        else:
            a = m
        if U.roots_open(seq, a, b) == 1:
            if step % 4 == 0:
                q = _simplest_between(a, b)
                if U.ev(g, q) == 0:
                    return _exact_root(p, g, seq, q)
            if b - a < EPS:
                break
    hi = b
    while U.ev(p, hi) >= 0:            # p(hi) = 0 only at a root of the even part; step towards the root
        hi = (a + hi) / 2
    return {"kind": "root", "lo": a, "hi": hi, "exact": None}


def _exact_root(p, g, seq, rho) -> dict:
    """rho, a rational root of g with none in (0, rho): a point just above it where p < 0."""
    d = Fraction(1, 2)
    while not (U.roots_open(seq, rho, rho + d) == 0 and U.ev(g, rho + d) != 0 and U.ev(p, rho + d) < 0):
        d /= 2
    return {"kind": "root", "lo": rho, "hi": rho + d, "exact": rho}


def coefficient(method) -> dict:
    """The SSP coefficient C of a method, exactly (or a rational enclosure), with both certificates.
    Keys: C (Fraction, or None if only enclosed), lo, hi (C in [lo, hi]), r (the certified lower bound:
    C, or a short rational just below lo), binding (the entries that fix it), certificate (an admissible
    Shu-Osher form with ratio r, when C > 0), witness (the class witness at hi, above C), form (the
    ratio of a given Shu-Osher form)."""
    K, so, name = method_K(method)
    out: dict = {"method": name, "stages": len(K) - 1}
    if so is not None:
        out["form"] = shu_osher_ratio(so["alpha"], so["beta"])
    ents = _entries(K)
    if not any(lab.startswith("P_") for lab, _ in ents):
        raise Unsupported("the method never evaluates F")
    found = [(lab, p, first_sign_change(p)) for lab, p in ents]
    zero = [(lab, p) for lab, p, f in found if f["kind"] == "zero"]
    if zero:
        lab, p = zero[0]
        r = Fraction(1, 2)
        while U.ev(p, r) >= 0:
            r /= 2
        out.update(C=Fraction(0), lo=Fraction(0), hi=Fraction(0), r=Fraction(0), binding=[lab for lab, _ in zero],
                   reason=f"{lab}(r) = {U.show(p, 'r')} has a negative lowest coefficient, so it is < 0 for every "
                          "small r > 0", witness=class_witness(K, r))
        return out
    roots = [(lab, f) for lab, p, f in found if f["kind"] == "root"]
    if not roots:
        raise Unsupported("no entry of v(r), P(r) ever changes sign: the method never evaluates F")
    lo = min(f["lo"] for _, f in roots)
    hi = min(f["hi"] for _, f in roots)
    first = [(lab, f) for lab, f in roots if f["lo"] == lo]
    exact = next((f["exact"] for _, f in first if f["exact"] is not None), None)
    C = exact if exact is not None and all(f["lo"] >= exact for _, f in roots) else None
    out.update(C=C, lo=lo, hi=hi, binding=sorted(lab for lab, f in roots if f["lo"] <= hi))
    # the certified lower bound: C itself, or the simplest rational a hair below lo (every entry is >= 0
    # on [0, lo], so on [0, r] too); r is what the verdicts use
    r = C if C is not None else _simplest_between(lo * (1 - Fraction(1, 2 ** 40)), lo)
    out["r"] = r
    out["certificate"] = shu_osher_certificate(K, r)
    out["witness"] = class_witness(K, out["hi"])
    return out


# ---------------------------------------------------------------- certificates

def shu_osher_certificate(K, r: Fraction) -> dict:
    """At r > 0 with v(r), P(r) >= 0: the Shu-Osher form alpha_i0 = v_i + P_i0, alpha_ik = P_ik (k >= 1),
    beta = P / r. Admissible with ratio >= r; converted back to K it must give the method itself."""
    if r <= 0:
        raise ValueError("a certificate needs r > 0")
    v, Pm = am_at(K, r)
    n = len(K)
    if min(v) < 0 or min(x for row in Pm for x in row) < 0:
        raise AssertionError(f"v({r}) or P({r}) has a negative entry: r is above C")
    alpha = [[v[i] + Pm[i][0]] + [Pm[i][k] for k in range(1, i)] for i in range(1, n)]
    beta = [[Pm[i][k] / r for k in range(i)] for i in range(1, n)]
    ratio = shu_osher_ratio(alpha, beta)
    assert ratio["admissible"] and ratio["c"] >= r, ratio
    assert shu_osher_K(alpha, beta) == K, "the certificate's arrays are not the method"
    return {"r": r, "alpha": alpha, "beta": beta, "ratio": ratio["c"]}


def butcher_stages(K, F, u0, dt) -> list:
    """The stages Y_0..Y_s of one step, straight from K: Y_i = u0 + dt sum_{k<i} K_ik F(Y_k)."""
    Y = []
    for i in range(len(K)):
        Y.append(u0 + dt * sum((K[i][k] * F(Y[k]) for k in range(i) if K[i][k]), Fraction(0)))
    return Y


def class_witness(K, r: Fraction) -> dict | None:
    """At r > C: a right-hand side F on the real line with x + tF(x) >= 0 for all x >= 0 and t in [0, 1]
    (tau = 1, S = [0, inf)) and u^n = u0 >= 0 for which a stage of one step with dt = r is negative.
    The stages are y = v(r) u0 + P(r) w with w_k = y_k + F(y_k), so a negative entry of v or P picks
    u0 and w >= 0; F is y_k -> w_k - y_k at the stage points (x -> -x elsewhere), checked to be a
    function, and the step is recomputed from K directly."""
    v, Pm = am_at(K, r)
    n = len(K)
    rows = sorted(range(1, n), key=lambda i: (i != n - 1, i))            # prefer the new step u^{n+1}
    for i in rows:
        cands = ([("v", None)] if v[i] < 0 else []) + [("P", k) for k in range(n - 1) if Pm[i][k] < 0]
        for kind, k in cands:
            for u0 in (Fraction(1), Fraction(2), Fraction(3)):
                for scale in (2, 3, 5, 7, 11):
                    w = [Fraction(0)] * (n - 1)
                    if kind == "P":
                        w[k] = scale * (abs(v[i]) * u0 + 1) / -Pm[i][k]
                    y = [v[j] * u0 + sum((Pm[j][l] * w[l] for l in range(n - 1)), Fraction(0)) for j in range(n)]
                    table: dict = {}
                    if any(table.setdefault(y[j], w[j]) != w[j] for j in range(n - 1)):
                        continue                                     # two stages at one point with two images
                    F = lambda x: table[x] - x if x in table else -x
                    Y = butcher_stages(K, F, u0, r)
                    if Y != y or Y[i] >= 0:
                        continue
                    # forward Euler keeps [0, inf) for t in [0, 1]: at a stage point x >= 0 the step is
                    # (1 - t) x + t w with w >= 0; elsewhere it is (1 - t) x
                    assert all(x < 0 or table[x] >= 0 for x in table)
                    out = {"dt/tau": r, "u0": u0, "F at the stage points": {str(x): str(table[x] - x) for x in table},
                           "F elsewhere": "F(x) = -x", "stages": Y, "negative stage": i,
                           "is the new step": i == n - 1, "entry": f"v_{i}" if kind == "v" else f"P_{i}{k}"}
                    if i < n - 1:
                        out.update(_push_to_new_step(K, F, u0, r, Y[i]) or {})
                    return out
    return None


def _push_to_new_step(K, F, u0, r, x_out) -> dict | None:
    """A stage x_out < 0 lies outside S, where F is unconstrained: lower F(x_out) by M until the new step
    is negative too. F stays a function, and forward-Euler admissible on [0, inf), since only its value
    at x_out changes."""
    for e in range(40):
        M = Fraction(10) ** e
        F2 = lambda x: F(x) - M if x == x_out else F(x)
        Y = butcher_stages(K, F2, u0, r)
        if Y[-1] < 0:
            return {"F at the stage points": {str(x): str(F2(x)) for x in Y[:-1]}, "stages": Y,
                    "is the new step": True, "pushed": f"F({x_out}) lowered by {M} (x = {x_out} < 0 is outside S)"}
    return None


# ---------------------------------------------------------------- the checks

def _walk(e: E):
    yield e
    for a in e.args:
        if isinstance(a, E):
            yield from _walk(a)


def forward_euler_form(spec: dict) -> str:
    """'' if the update is u_i + lam G(u) with G free of lam (a forward-Euler step of a semi-discrete
    scheme), else the reason it is not."""
    F = checks.numerical_flux(spec)
    if F is not None:
        if any(x.kind == "var" and x.name == "lam" for x in _walk(F)):
            return ("the numerical flux depends on lam = dt/dx (a Lax-Wendroff-type flux), so the update is not a "
                    "forward-Euler step u_i + lam G(u) of a semi-discrete scheme")
        return ""
    try:
        H = P.from_expr(checks.update(spec))
    except P.Undecided as ex:
        return f"the update is outside the exact fragment: {ex}"
    parts: dict = {}
    for m, c in H.items():
        k = dict(m).get(("v", "lam"), 0)
        parts[k] = P.add(parts.get(k, {}), P.scale({P._mono({x: e for x, e in m if x != ("v", "lam")}): Fraction(1)}, c))
    if set(parts) - {0, 1} or parts.get(0, {}) != P.var("u0"):
        return "the update is not u0 + lam*G(u) with G free of lam"
    return ""


def _config(spec: dict, check: str):
    """((K-info, property, cfl, claim), None) or (None, result)."""
    cfg = spec.get("claims", {}).get("ssp")
    if cfg is None:
        return None, result(check, NOT_APPLICABLE, "SSP", "no SSP claim (claims.ssp)")
    prop, cfl = cfg["property"], Fraction(cfg["cfl"])
    method = cfg["method"]
    label = method if isinstance(method, str) else "the stated method"
    claim = (f"{label}, applied to the spec's forward-Euler step, keeps {prop} for every state and every "
             f"nu = a*dt/dx in [0, {cfl}]")
    if prop not in PROPERTIES:
        return None, result(check, UNKNOWN, claim, f"property must be one of {PROPERTIES}")
    if cfl < 0:
        return None, result(check, UNKNOWN, claim, "negative CFL bound")
    try:
        K, so, _ = method_K(method)
    except Unsupported as ex:
        return None, result(check, UNKNOWN, claim, str(ex))
    return (K, method, prop, cfl, claim), None


FE_KEY = {"positivity": "positive_cfl", "tvd": "tvd_cfl", "max_principle": "tvd_cfl"}


def _fe_checks(spec: dict, prop: str, nu: Fraction) -> list[dict]:
    """The forward-Euler certificates for `prop` on [0, nu]."""
    from . import limiters, linear
    sub = {**spec, "claims": {**spec.get("claims", {}), FE_KEY[prop]: ["0", str(nu)]}}
    if prop == "positivity":
        return [checks.positivity(sub)]
    if prop == "tvd":
        return [limiters.tvd_harten(sub), linear.tvd_linear(sub)]
    return [limiters.tvd_harten(sub), linear.max_principle_linear(sub)]


_FE_MEANING = {"positivity": "non-negative data stay non-negative (S = the non-negative orthant)",
               "tvd": "TV(u^{n+1}) <= TV(u^n) (S = {TV <= TV(u^n)}, convex as TV is a seminorm)",
               "max_principle": "min_j u_j^n <= u_i^{n+1} <= max_j u_j^n (S = the box [min u^n, max u^n]^N; a local "
                                "maximum principle of forward Euler keeps that box)"}


def ssp(spec: dict) -> dict:
    """The class theorem: C exactly, then the forward-Euler certificate for the property on [0, cfl / C].
    VERIFIED when both hold; NOT_APPLICABLE when C = 0 or the update is not a forward-Euler step; UNKNOWN
    when forward Euler is not certified there (the theorem is only sufficient)."""
    got, bad = _config(spec, "ssp")
    if bad:
        return bad
    K, method, prop, cfl, claim = got
    why = forward_euler_form(spec)
    if why:
        return result("ssp", NOT_APPLICABLE, claim, why)
    try:
        c = coefficient(method)
    except Unsupported as ex:
        return result("ssp", UNKNOWN, claim, str(ex))
    wit = {"C": str(c["C"]) if c["C"] is not None else None, "C in": [str(c["lo"]), str(c["hi"])],
           "binding entries": c["binding"]}
    if "form" in c:
        wit["ratio of the stated Shu-Osher form"] = str(c["form"]["c"]) + (f" ({c['form']['reason']})"
                                                                         if c["form"]["reason"] else "")
    if c.get("witness"):
        wit["class witness above C"] = U.jsonable(c["witness"])
    if c["lo"] == 0:
        return result("ssp", NOT_APPLICABLE, claim,
                      f"C = 0 ({c['reason']}): the method is not SSP, so the class theorem gives no positive step; "
                      "the class witness is a forward-Euler-admissible right-hand side on [0, inf) with a negative "
                      "stage at that dt; it does not refute the claim for this scheme", wit)
    if cfl == 0:
        return result("ssp", VERIFIED, claim, "cfl = 0: dt = 0 and every stage is u^n", wit)
    nu_fe = cfl / c["r"]
    cert = c["certificate"]
    wit["certificate (Shu-Osher form, ratio r)"] = {"r": str(cert["r"]), "alpha": U.jsonable(cert["alpha"]),
                                                    "beta": U.jsonable(cert["beta"])}
    wit["forward-Euler range"] = ["0", str(nu_fe)]
    fe = _fe_checks(spec, prop, nu_fe)
    wit["forward Euler"] = {r["check"]: r["status"] for r in fe}
    ok = [r for r in fe if r["status"] == VERIFIED]
    cs = (f"C = {c['C']}" if c["C"] is not None
          else f"C ~ {float(c['lo']):.15g} (an exact rational enclosure of width {float(c['hi'] - c['lo']):.1e} is in "
               f"the witness), C >= {c['r']}")
    if not ok:
        return result("ssp", UNKNOWN, claim,
                      f"{cs}, but forward Euler is not certified on [0, {nu_fe}] ("
                      + "; ".join(f"{r['check']}: {r['status']}" for r in fe) + "); the class theorem is only sufficient",
                      wit)
    return result("ssp", VERIFIED, claim,
                  f"{cs}: the method has an admissible Shu-Osher form with ratio {cert['r']}, and forward Euler keeps "
                  f"{prop} on [0, {nu_fe}] ({ok[0]['check']}); so every stage, u^{{n+1}} included, does for nu <= "
                  f"{cert['r']} * {nu_fe} = {cfl} ({LEAN}, instance {LEAN_INSTANCE[prop]})", wit,
                  [f"forward Euler: {_FE_MEANING[prop]}", *ok[0]["assumptions"]])


def _laurent_mul(X: dict, Y: dict) -> dict:
    out: dict = {}
    for i, p in X.items():
        for j, q in Y.items():
            out[i + j] = U.add(out.get(i + j, []), U.mul(p, q))
    return {k: U.trim(p) for k, p in out.items() if U.trim(p)}


def stability_polynomial(K) -> list:
    """gamma_j with R(z) = sum_j gamma_j z^j: gamma_0 = 1, gamma_j = (K^j e)_s."""
    n = len(K)
    gam, Kj = [Fraction(1)], K
    for _ in range(1, n):
        gam.append(sum(Kj[n - 1], Fraction(0)))
        Kj = _mm(Kj, K)
    return U.trim(gam)


_LINEAR_EQ = ("the update is linear: u^{n+1}_i = sum_k R_k(nu) u_{i+k}^n, with R(z) the method's stability "
              "polynomial applied to the forward-Euler operator and sum_k R_k = 1; every R_k >= 0 is a convex "
              "combination of shifts, which keeps positivity, the global maximum principle and the total variation; a "
              "negative R_k(nu) breaks positivity and the maximum principle on the unit data e_k, and TVD on the box data "
              "of width w on N >= 2w periodic cells")


def _fe_linear(spec: dict):
    """(a, {offset: d_k as coefficient list}) with c_k(nu) = delta_k0 + nu d_k, or raise NotLinear / Undecided."""
    a, coeffs = checks.linear_coefficients(spec)
    off = {name: k for k, name in enumerate(checks.STENCIL5, -2)}
    D = {}
    for name, p in coeffs.items():
        cl = checks.nu_coefficients(p)
        if cl is None or len(U.trim(cl)) > 2:
            raise checks.NotLinear(f"c_{off[name]}(nu) = {P.show(p)} is not affine in nu: not a forward-Euler step")
        cl = U.trim(cl) + [Fraction(0)] * 2
        if cl[0] != (1 if name == "u0" else 0):
            raise checks.NotLinear(f"c_{off[name]}(0) = {cl[0]}: at nu = 0 the update is not the identity")
        if cl[1]:
            D[off[name]] = [Fraction(0), cl[1]]                # nu * d_k
    return a, D


def ssp_linear(spec: dict) -> dict:
    """Exact for linear constant-coefficient schemes: expand R(nu D) in the shift, decide every coefficient
    R_k(nu) >= 0 on [0, cfl] (Bernstein, else square-free + Sturm); a negative one gives exact data on
    which one Runge-Kutta step (computed stage by stage) breaks the property."""
    got, bad = _config(spec, "ssp_linear")
    if bad:
        return bad
    K, method, prop, cfl, claim = got
    if forward_euler_form(spec):
        return result("ssp_linear", NOT_APPLICABLE, claim, forward_euler_form(spec))
    try:
        a, D = _fe_linear(spec)
    except checks.NotLinear as ex:
        return result("ssp_linear", NOT_APPLICABLE, claim, f"not a linear scheme: {ex}")
    except P.Undecided as ex:
        return result("ssp_linear", UNKNOWN, claim, str(ex))
    gam = stability_polynomial(K)
    total: dict = {0: [Fraction(1)]}
    power: dict = {0: [Fraction(1)]}
    for g in gam[1:]:
        power = _laurent_mul(power, D)
        for k, p in power.items():
            total[k] = U.add(total.get(k, []), [g * x for x in p])
    R = {k: U.trim(p) for k, p in total.items() if U.trim(p)}
    wit = {"stability polynomial": U.show(gam, "z"), "R_k(nu)": {str(k): U.show(p) for k, p in sorted(R.items())}}
    for k in sorted(R):
        b = checks.bernstein(R[k] or [Fraction(0)], Fraction(0), cfl) if cfl > 0 else [U.ev(R[k], Fraction(0))]
        if min(b) >= 0:
            continue
        d = U.nonneg_on(R[k], Fraction(0), cfl)
        if d["nonneg"]:
            continue
        nu = d["counterexample"]["x"]
        return _linear_refutation(spec, K, a, R, k, nu, prop, claim, wit)
    return result("ssp_linear", VERIFIED, claim,
                  f"every R_k(nu) >= 0 on [0, {cfl}] and sum_k R_k = 1: one step is a convex combination of shifts", wit,
                  [_LINEAR_EQ])


def rk_step(spec: dict, K, u: list, lam: Fraction) -> list | None:
    """One Runge-Kutta step on a periodic grid, stage by stage, with G(v) = H(v, lam = 1) - v (the update
    is u + lam G(u)), in Fraction arithmetic; None outside the exact fragment."""
    from . import limiters
    from ..expr import intern
    H, flux = intern(checks.update(spec)), checks.numerical_flux(spec)
    flux = None if flux is None else intern(flux)

    def G(v):
        w = limiters._step(H, v, Fraction(1), flux)
        return None if w is None else [x - y for x, y in zip(w, v)]
    Y, Gs = [], []
    for i in range(len(K)):
        y = list(u)
        for k in range(i):
            if K[i][k]:
                y = [x + lam * K[i][k] * g for x, g in zip(y, Gs[k])]
        Y.append(y)
        if i < len(K) - 1:
            g = G(y)
            if g is None:
                return None
            Gs.append(g)
    return Y[-1]


def _violates(prop: str, u: list, v: list) -> str:
    from . import limiters
    if prop == "positivity" and min(u) >= 0 and min(v) < 0:
        return f"min u^{{n+1}} = {min(v)} < 0 from non-negative data"
    if prop == "max_principle" and not min(u) <= min(v) <= max(v) <= max(u):
        return f"u^{{n+1}} leaves [{min(u)}, {max(u)}]: its range is [{min(v)}, {max(v)}]"
    if prop == "tvd" and limiters.total_variation(v) > limiters.total_variation(u):
        return f"TV grows from {limiters.total_variation(u)} to {limiters.total_variation(v)}"
    return ""


def _linear_refutation(spec, K, a, R, k, nu, prop, claim, wit) -> dict:
    ks = sorted(R)
    w = ks[-1] - ks[0] + 1
    if prop == "tvd":
        n = 2 * w
        u = [Fraction(1 if 1 <= j <= w else 0) for j in range(n)]
    else:
        n = w
        u = [Fraction(0)] * n
        u[k % n] = Fraction(1)                                 # cell k feeds cell 0 through R_k
    v = rk_step(spec, K, u, nu / a)
    conv = [sum((U.ev(R[j], nu) * u[(i + j) % n] for j in R), Fraction(0)) for i in range(n)]
    if v is None or v != conv:
        return result("ssp_linear", UNKNOWN, claim, "the stage-by-stage step and R(nu D) disagree (a bug in this check)", wit)
    why = _violates(prop, u, v)
    wit.update(negative={"k": k, "nu": str(nu), "R_k(nu)": str(U.ev(R[k], nu))},
               counterexample={"periodic state u^n": [str(x) for x in u], "nu": str(nu), "lam": str(nu / a),
                               "u^{n+1}": [str(x) for x in v]})
    if not why:
        return result("ssp_linear", UNKNOWN, claim, f"R_{k}({nu}) < 0 but the data did not break {prop} (a bug)", wit)
    return result("ssp_linear", REFUTED, claim,
                  f"R_{k}(nu) = {U.ev(R[k], nu)} < 0 at nu = {nu}; on the periodic state {[str(x) for x in u]} one step "
                  f"gives {[str(x) for x in v]}: {why}", wit, [_LINEAR_EQ])


def ssp_violation(spec: dict) -> dict:
    """An exact refutation for any scheme in the fragment: a periodic rational state and a nu in (0, cfl]
    whose Runge-Kutta step (stage by stage, Fraction arithmetic) breaks the property. A failed search
    proves nothing."""
    from . import limiters
    got, bad = _config(spec, "ssp_violation")
    if bad:
        return bad
    K, method, prop, cfl, claim = got
    if forward_euler_form(spec):
        return result("ssp_violation", NOT_APPLICABLE, claim, forward_euler_form(spec))
    try:
        a = limiters._advection(spec)
        P.from_expr(checks.update(spec))
    except (checks.NonlinearFlux, P.Undecided) as ex:
        return result("ssp_violation", UNKNOWN, claim, f"{ex}: the search is parametrised by nu = a*dt/dx")
    nus = [cfl * Fraction(t, 8) for t in (8, 4, 2, 1, 6, 7, 5, 3)] + [cfl / 16, cfl / 32]
    nus = [x for x in dict.fromkeys(nus) if x / a > 0]
    tried = 0
    for data in limiters._candidates():
        u = [Fraction(x) for x in data]
        if prop == "positivity":
            u = [x - min(u) for x in u]
        for nu in nus:
            tried += 1
            v = rk_step(spec, K, u, nu / a)
            if v is None:
                continue
            why = _violates(prop, u, v)
            if why:
                wit = {"periodic state u^n": [str(x) for x in u], "nu": str(nu), "lam": str(nu / a),
                       "u^{n+1}": [str(x) for x in v]}
                return result("ssp_violation", REFUTED, claim,
                              f"one step at nu = {nu} on the periodic state {[str(x) for x in u]}: {why}", wit,
                              ["periodic grid"])
    return result("ssp_violation", UNKNOWN, claim,
                  f"no violation among {tried} (state, nu) pairs; a failed search proves nothing")
