"""Variational-integrator claims: discrete Euler–Lagrange equations, discrete Noether, order.

Trusted, judge-owned: the claim format, the variable layout, the Lean statements and the exact
order check. The untrusted planner (`tools/variational.py`) only supplies tactic text
(including the multipliers μ_k).

Claim file (`benchmark/variational/*.json`), one integrator and the claims made about it:
{
  "kind": "variational",
  "name": "...",
  "coordinates": ["x", "y"],                       # level j of coordinate x is the symbol x_j
  "symbols": {"x": {"dim": "L"}, "h": {"dim": "T"}, "m": {"dim": "M"}, ...},
  "discrete_lagrangian": "m/2*((x_1 - x_0)/h)^2*h - ...",   # L_d(q0, q1; h): levels 0, 1 only
  "lagrangian": "m/2*x_dot^2 - ...",               # continuous L(q, q_dot), for the order claim
  "domain": ["m > 0"],                             # atoms over levels 0, 1, 2, h, parameters;
                                                   # `h > 0` is always added
  "claims": [
    {"claim": "del_equations", "update": [{"lhs": "x_2", "rhs": "..."}], "expect": ..., "why": ...},
    {"claim": "discrete_momentum_conserved", "quantity": "J(x_0, x_1, ...)", "expect": ..., ...},
    {"claim": "consistent_order_p", "p": 2, "expect": ..., ...}
  ]
}

Lean layout (`PhysVerify/Discrete.lean`), the continuous layout with time levels in place of
the jet: `x_0` ↦ k, `x_1` ↦ n + k, `x_2` ↦ 2n + k, `h` and the parameters ↦ 3n, 3n+1, … in
sorted order. So `L_d` and `J` mention no level-2 variable exactly when `NoAccel n` holds.

Sign convention (derived once, used everywhere). With `L_d ≈ h·L(q, (q1 − q0)/h)`,
`D2 L_d(q0, q1) ≈ ∂L/∂q̇` at the first interval and `D1 L_d(q1, q2) ≈ h ∂L/∂q − ∂L/∂q̇` at the
second, so `DEL = D2 L_d(q0, q1) + D1 L_d(q1, q2) ≈ −h·(d/dt ∂L/∂q̇ − ∂L/∂q) = −h·EL`. The order
claim therefore tests `(1/h)·DEL + EL = O(h^p)`, with `q_j = q(t + (j − 1)h)`: the stencil is
centred on the middle level. (Centring on `q0`, `q_j = q(t + j h)`, makes every DEL look first
order, since `EL(t + h) − EL(t) = O(h)`.)
"""

from __future__ import annotations

import json
import math
import re
import time
from dataclasses import dataclass, field
from fractions import Fraction
from pathlib import Path

from . import units
from .derivation import REFUTED, UNKNOWN, VERIFIED, Result, find_witness, lean_point
from .expr import E, diff, lit, parse, simplify, substitute, to_lean, var, variables
from .theory import Malformed

KINDS = ("del_equations", "discrete_momentum_conserved", "consistent_order_p")
_ATOM = re.compile(r"^(.*?)(>|<|!=)(.*)$")
EXACT_PY = "exact (Python)"


@dataclass
class VClaim:
    kind: str
    expect: str = ""
    why: str = ""
    update: list[tuple[E, E]] = field(default_factory=list)   # del_equations: lhs = rhs
    quantity: E | None = None                                 # discrete_momentum_conserved
    p: int = 0                                                # consistent_order_p


@dataclass
class Integrator:
    name: str
    coords: list[str]
    dims: dict[str, units.Dim]          # declared symbols, levels x_j and jets x_dot, x_ddot
    declared: list[str]                 # the declared symbols (coordinates, h, parameters)
    ld: E
    lagrangian: E | None
    domain: list[tuple[str, E, E]]
    claims: list[VClaim]
    source: dict = field(default_factory=dict)

    @property
    def n(self) -> int:
        return len(self.coords)

    def level(self, q: str, j: int) -> str:
        return f"{q}_{j}"

    def params(self) -> list[str]:
        """h and the parameters, in the order of their Lean indices."""
        return sorted(set(self.declared) - set(self.coords))

    def index(self) -> dict[str, int]:
        n, idx = self.n, {}
        for k, q in enumerate(self.coords):
            for j in range(3):
                idx[self.level(q, j)] = j * n + k
        for i, s in enumerate(self.params()):
            idx[s] = 3 * n + i
        return idx

    def shift(self) -> dict[str, E]:
        """`shift n` on names: level 0 ↦ level 1, level 1 ↦ level 2."""
        return {self.level(q, j): var(self.level(q, j + 1)) for q in self.coords for j in (0, 1)}


def is_variational(spec: dict) -> bool:
    return spec.get("kind") == "variational"


def _levels(I: Integrator, js) -> set[str]:
    return {I.level(q, j) for q in I.coords for j in js}


def load_variational(spec: dict | str | Path) -> Integrator:
    if not isinstance(spec, dict):
        spec = json.loads(Path(spec).read_text())
    if not is_variational(spec):
        raise Malformed(f"claim {spec.get('name')!r}: not a variational-integrator claim")
    name = spec.get("name")
    try:
        coords = list(spec["coordinates"])
        declared = dict(spec["symbols"])
        declared.setdefault("h", {"dim": "T"})
        dims = {k: units.parse_dim(v["dim"]) for k, v in declared.items()}
        if dims["h"] != units.parse_dim("T"):
            raise Malformed("the step h must have dimension T")
        T = units.parse_dim("T")
        for q in coords:
            if q not in dims:
                raise Malformed(f"coordinate {q!r} has no dimension")
            for j in range(3):
                dims[f"{q}_{j}"] = dims[q]
            dims[f"{q}_dot"] = units.sub(dims[q], T)
            dims[f"{q}_ddot"] = units.sub(dims[q], units.smul(2, T))
        dom = []
        atoms = list(spec.get("domain", []))
        if "h>0" not in [a.replace(" ", "") for a in atoms]:
            atoms.append("h > 0")
        for a in atoms:
            m = _ATOM.match(a)
            if not m:
                raise Malformed(f"domain atom {a!r} is not `a > b`, `a < b` or `a != b`")
            dom.append((m.group(2), parse(m.group(1)), parse(m.group(3))))
        claims = []
        for c in spec["claims"]:
            kind = c["claim"]
            if kind not in KINDS:
                raise Malformed(f"unknown claim kind {kind!r} (use {KINDS})")
            vc = VClaim(kind, c.get("expect", ""), c.get("why", ""))
            if kind == "del_equations":
                vc.update = [(parse(e["lhs"]), parse(e["rhs"])) for e in c["update"]]
            elif kind == "discrete_momentum_conserved":
                vc.quantity = parse(c["quantity"])
            else:
                vc.p = int(c["p"])
            claims.append(vc)
        I = Integrator(name, coords, dims, sorted(declared), parse(spec["discrete_lagrangian"]),
                       parse(spec["lagrangian"]) if "lagrangian" in spec else None, dom, claims, spec)
    except (KeyError, ValueError) as ex:
        raise Malformed(f"claim {name!r}: {ex}") from ex
    _validate(I)
    return I


def _validate(I: Integrator) -> None:
    params = set(I.params())
    lv01, lv012 = _levels(I, (0, 1)), _levels(I, (0, 1, 2))
    jet = set(I.coords) | {f"{q}_dot" for q in I.coords}

    def only(e: E, allowed: set[str], what: str):
        bad = variables(e) - allowed
        if bad:
            raise Malformed(f"claim {I.name!r}: {what} may not mention {sorted(bad)}")

    only(I.ld, lv01 | params, "the discrete Lagrangian")
    if I.lagrangian is not None:
        only(I.lagrangian, jet | (params - {"h"}), "the continuous Lagrangian")
    for op, a, b in I.domain:
        only(a, lv012 | params, "domain atoms")
        only(b, lv012 | params, "domain atoms")
        from .derivation import _discontinuous
        bad = _discontinuous(a) or _discontinuous(b)
        if bad:
            raise Malformed(f"claim {I.name!r}: domain atoms must be continuous everywhere; found {bad}")
    for c in I.claims:
        if c.kind == "del_equations":
            if len(c.update) != I.n:
                raise Malformed(f"claim {I.name!r}: {len(c.update)} update equations for {I.n} coordinates")
            for l, r in c.update:
                only(l, lv012 | params, "the update")
                only(r, lv012 | params, "the update")
        elif c.kind == "discrete_momentum_conserved":
            only(c.quantity, lv01 | params, "the discrete momentum (levels 0, 1 only)")
        elif c.p < 1:
            raise Malformed(f"claim {I.name!r}: the order p must be at least 1")
        elif I.lagrangian is None:
            raise Malformed(f"claim {I.name!r}: an order claim needs the continuous lagrangian")


def claim_name(I: Integrator, c: VClaim) -> str:
    extra = f" {c.p}" if c.kind == "consistent_order_p" else ""
    return f"{I.name}: {c.kind}{extra}"


# ---------------------------------------------------------------- Lean statements

def lean_terms(I: Integrator) -> dict[str, str]:
    idx = I.index()
    atoms = []
    for op, a, b in I.domain:
        la, lb = f"Expr.eval env {to_lean(a, idx)}", f"Expr.eval env {to_lean(b, idx)}"
        atoms.append({">": f"{lb} < {la}", "<": f"{la} < {lb}", "!=": f"{la} ≠ {lb}"}[op])
    D = "(fun env : ℕ → ℝ => " + " ∧ ".join(atoms) + ")"
    by_index = sorted(idx, key=idx.get)
    ctx = "[" + ", ".join(units.lean_dim(I.dims[s]) for s in by_index) + "]"
    return {"n": str(I.n), "Ld": to_lean(I.ld, idx), "D": D, "ctx": ctx}


def lean_laws(I: Integrator, c: VClaim) -> str:
    idx = I.index()
    return "[" + ", ".join(f"(⟨{to_lean(l, idx)}, {to_lean(r, idx)}⟩ : Law)" for l, r in c.update) + "]"


def statement(kind: str, I: Integrator, c: VClaim) -> str:
    t = lean_terms(I)
    n, Ld, D, ctx = t["n"], t["Ld"], t["D"], t["ctx"]
    if c.kind == "del_equations":
        cs = lean_laws(I, c)
        if kind == "verified":
            return (f"(Expr.dimOf {ctx} {Ld}).isSome = true ∧ NoAccel {n} {Ld} ∧ "
                    f"DELVerified {n} {Ld} {D} {cs}")
        if kind == "refuted":
            return f"NoAccel {n} {Ld} ∧ DELRefuted {n} {Ld} {D} {cs}"
    if c.kind == "discrete_momentum_conserved":
        J = to_lean(c.quantity, I.index())
        if kind == "verified":
            return (f"(Expr.dimOf {ctx} {Ld}).isSome = true ∧ (Expr.dimOf {ctx} {J}).isSome = true ∧ "
                    f"NoAccel {n} {Ld} ∧ NoAccel {n} {J} ∧ "
                    f"∃ mus : List Expr, mus.length = {n} ∧ DMomentumVerified {n} {Ld} {D} {J} mus")
        if kind == "refuted":
            return f"NoAccel {n} {Ld} ∧ NoAccel {n} {J} ∧ DMomentumRefuted {n} {Ld} {D} {J}"
    raise KeyError((kind, c.kind))


def judge_prefix(kind: str, I: Integrator, c: VClaim, witness) -> str:
    """The conjuncts the judge proves itself; the planner proves the rest."""
    if kind != "verified":
        return ""
    if c.kind == "del_equations":
        return (f"refine ⟨by decide, by decide, ⟨{lean_point(I, witness)}, ?_⟩, ?_⟩\n"
                "· first | trivial | (simp [Expr.eval, Fn.eval] <;> norm_num)\n")
    return "refine ⟨by decide, by decide, by decide, by decide, ?_⟩\n"


MEANING = {
    ("del_equations", VERIFIED): (
        "PhysVerify.del_verified_meaning: at every step of every discrete trajectory whose "
        "triple (q_k, q_k+1, q_k+2) is in the domain, the real discrete Euler–Lagrange "
        "equations of L_d hold iff the claimed update holds; the domain is non-empty and L_d "
        "and the update take no junk values on it"),
    ("del_equations", REFUTED): (
        "PhysVerify.del_refuted_meaning: a rational triple (q0, q1, q2) in the domain at which "
        "the real discrete Euler–Lagrange equations of L_d and the claimed update disagree"),
    ("discrete_momentum_conserved", VERIFIED): (
        "PhysVerify.dmomentum_meaning: along every discrete trajectory q_0..q_N+1 whose triples "
        "are in the domain and satisfy the real discrete Euler–Lagrange equations, "
        "J(q_N, q_N+1) = J(q_0, q_1) exactly; the domain is non-empty and L_d, J and the "
        "multipliers take no junk values on it"),
    ("discrete_momentum_conserved", REFUTED): (
        "PhysVerify.dmomentum_refuted_meaning: a rational three-level discrete trajectory "
        "(q0, q1, q2) in the domain, satisfying the real discrete Euler–Lagrange equations, "
        "with ∂DEL/∂q2 invertible (q2 is the step taken from (q0, q1); its local uniqueness, "
        "the implicit function theorem, is assumed), on which J(q1, q2) ≠ J(q0, q1)"),
}
MODULE = "PhysVerify.Discrete"


# ---------------------------------------------------------------- exact order (Python)
# Laurent polynomials in h with polynomial coefficients: {monomial: Fraction}, a monomial a
# sorted tuple of (variable, exponent); only h may have a negative exponent.

class NotPolynomial(ValueError):
    pass


Poly = dict


def _pmono(m1, m2):
    d = dict(m1)
    for v, e in m2:
        d[v] = d.get(v, 0) + e
    return tuple(sorted((v, e) for v, e in d.items() if e))


def p_const(q) -> Poly:
    return {(): Fraction(q)} if q else {}


def p_var(v: str) -> Poly:
    return {((v, 1),): Fraction(1)}


def p_add(a: Poly, b: Poly, s: int = 1) -> Poly:
    out = dict(a)
    for m, c in b.items():
        out[m] = out.get(m, 0) + s * c
        if not out[m]:
            del out[m]
    return out


def p_mul(a: Poly, b: Poly) -> Poly:
    out: Poly = {}
    for m1, c1 in a.items():
        for m2, c2 in b.items():
            m = _pmono(m1, m2)
            out[m] = out.get(m, 0) + c1 * c2
            if not out[m]:
                del out[m]
    return out


def p_pow(a: Poly, k: int) -> Poly:
    out = p_const(1)
    for _ in range(k):
        out = p_mul(out, a)
    return out


def _p_inv_monomial(a: Poly) -> Poly:
    if len(a) != 1:
        raise NotPolynomial("division by a non-monomial")
    (m, c), = a.items()          # c·Π v^e: its inverse is again a (Laurent) monomial
    return {tuple((v, -e) for v, e in m): 1 / c}


def to_poly(e: E, env: dict[str, Poly]) -> Poly:
    """`e` with every variable replaced by `env[v]` (or itself), as a Laurent polynomial."""
    k, a = e.kind, e.args
    if k == "var": return env.get(e.name, p_var(e.name))
    if k == "lit": return p_const(e.q)
    if k == "neg": return p_add({}, to_poly(a[0], env), -1)
    if k in ("add", "sub"): return p_add(to_poly(a[0], env), to_poly(a[1], env), 1 if k == "add" else -1)
    if k == "mul": return p_mul(to_poly(a[0], env), to_poly(a[1], env))
    if k == "div": return p_mul(to_poly(a[0], env), _p_inv_monomial(to_poly(a[1], env)))
    if k == "powi":
        b = to_poly(a[0], env)
        return p_pow(b, e.q) if e.q >= 0 else p_pow(_p_inv_monomial(b), -e.q)
    raise NotPolynomial(f"{k} is outside the polynomial fragment of the order check")


def _hpow(m) -> int:
    return dict(m).get("h", 0)


def by_hpower(a: Poly) -> dict[int, Poly]:
    out: dict[int, Poly] = {}
    for m, c in a.items():
        out.setdefault(_hpow(m), {})[tuple(x for x in m if x[0] != "h")] = c
    return out


def p_str(a: Poly) -> str:
    if not a:
        return "0"
    terms = []
    for m, c in sorted(a.items(), key=lambda t: (-sum(e for _, e in t[0]), t[0])):
        mono = "*".join(v if e == 1 else f"{v}^{e}" for v, e in m)
        terms.append(f"({c})" + (f"*{mono}" if mono else ""))
    return " + ".join(terms)


def p_eval(a: Poly, env: dict[str, Fraction]) -> Fraction:
    return sum((c * math.prod(Fraction(env[v]) ** e for v, e in m) for m, c in a.items()), Fraction(0))


def jet_name(q: str, m: int) -> str:
    return {0: q, 1: f"{q}_dot", 2: f"{q}_ddot"}.get(m, f"{q}_d{m}")


def del_exprs(I: Integrator) -> list[E]:
    """DEL_k = D_{2,k} L_d(q0, q1) + D_{1,k} L_d(q1, q2), the Python mirror of Lean's `DEL`."""
    sh = I.shift()
    return [simplify(E("add", (diff(I.ld, I.level(q, 1)), substitute(diff(I.ld, I.level(q, 0)), sh))))
            for q in I.coords]


def el_exprs(I: Integrator) -> list[E]:
    """EL_k = d/dt ∂L/∂q̇_k − ∂L/∂q_k on the jet (q, q̇, q̈)."""
    out = []
    for q in I.coords:
        P = diff(I.lagrangian, f"{q}_dot")
        dt = lit(0)
        for r in I.coords:
            dt = E("add", (dt, E("mul", (diff(P, r), var(f"{r}_dot")))))
            dt = E("add", (dt, E("mul", (diff(P, f"{r}_dot"), var(f"{r}_ddot")))))
        out.append(simplify(E("sub", (dt, diff(I.lagrangian, q)))))
    return out


def truncation(I: Integrator, p: int) -> dict[int, list[Poly]]:
    """Coefficients of h^e, e ≤ p, of (1/h)·DEL_k + EL_k with q_j = q(t + (j − 1)h), as
    polynomials in the jet (q, q̇, q̈, q⁽³⁾, …) at t; exact (Taylor expansion, rationals)."""
    ld = to_poly(I.ld, {})
    a = max([0] + [-_hpow(m) for m in ld])           # L_d has h^-a at worst
    K = p + a + 1                                     # Taylor terms needed for exact h^≤p
    taylor = {}
    for q in I.coords:
        for j in range(3):
            s, poly = j - 1, {}
            for m in range(K + 1):
                c = Fraction(s) ** m / math.factorial(m)
                if c:
                    poly = p_add(poly, {_pmono(((jet_name(q, m), 1),), (("h", m),) if m else ()): c})
            taylor[I.level(q, j)] = poly
    inv_h = {(("h", -1),): Fraction(1)}
    out: dict[int, list[Poly]] = {}
    for k, (d, el) in enumerate(zip(del_exprs(I), el_exprs(I))):
        diffk = p_add(p_mul(inv_h, to_poly(d, taylor)), to_poly(el, {}))
        for e, coef in by_hpower(diffk).items():
            if e <= p:
                out.setdefault(e, [{} for _ in I.coords])[k] = coef
    return out


def _nonzero_point(I: Integrator, a: Poly) -> dict[str, Fraction]:
    import random
    rng = random.Random(0)
    names = sorted({v for m in a for v, _ in m})
    for t in range(200):
        env = {v: Fraction(rng.choice([-3, -2, -1, 1, 2, 3]), rng.randint(1, 3)) if t else Fraction(1)
               for v in names}
        if p_eval(a, env):
            return env
    return {}


def judge_order(I: Integrator, c: VClaim) -> Result:
    t0 = time.monotonic()
    res = Result(claim_name(I, c), UNKNOWN, "n/a")
    try:
        coeffs = truncation(I, c.p)
    except NotPolynomial as ex:
        res.detail = f"outside v1 (polynomial L_d and L only): {ex}"
        res.seconds = time.monotonic() - t0
        return res
    order = next((e for e in sorted(coeffs) if any(coeffs[e])), None)
    sign = "(1/h)·DEL + EL with q_j = q(t + (j-1)h)"
    if order == c.p:
        k = next(i for i, x in enumerate(coeffs[order]) if x)
        res.verdict = VERIFIED
        res.detail = (f"{EXACT_PY}: {sign} has vanishing coefficients below h^{c.p} and h^{c.p} "
                      f"coefficient [{I.coords[k]}] = {p_str(coeffs[order][k])}")
    elif order is not None:
        k = next(i for i, x in enumerate(coeffs[order]) if x)
        pt = _nonzero_point(I, coeffs[order][k])
        res.verdict = REFUTED
        res.detail = (f"{EXACT_PY}: the h^{order} coefficient of {sign} [{I.coords[k]}] is "
                      f"{p_str(coeffs[order][k])}, = {p_eval(coeffs[order][k], pt)} at "
                      f"{ {v: str(x) for v, x in pt.items()} }; exact order {order} < {c.p}")
    else:
        res.verdict = REFUTED
        res.detail = (f"{EXACT_PY}: every coefficient of {sign} up to h^{c.p} vanishes "
                      f"identically: the order is at least {c.p + 1}, not exactly {c.p}")
    res.seconds = time.monotonic() - t0
    return res


# ---------------------------------------------------------------- judge

def dims_ok(I: Integrator, c: VClaim) -> str:
    """Python mirror of the kernel's `dimOf` checks (L_d, J), plus [L_d] = [L]·T."""
    try:
        dl = units.dim_of(I.ld, I.dims)
        if c.kind == "discrete_momentum_conserved":
            units.dim_of(c.quantity, I.dims)
        if I.lagrangian is not None:
            want = units.add(units.dim_of(I.lagrangian, I.dims), units.parse_dim("T"))
            if dl != want:
                return f"mismatch: L_d has {units.fmt_dim(dl)}, h·L has {units.fmt_dim(want)}"
    except units.DimError as ex:
        return f"mismatch: {ex}"
    return "ok"


def judge(I: Integrator, c: VClaim, candidates: list[tuple[str, str]], check=None) -> Result:
    """Candidates are (kind, tactic) pairs from the untrusted planner; kind ∈ verified/refuted.
    The order claim is decided in exact Python and takes no candidates. Without an accepted
    certificate the verdict is UNKNOWN, never REFUTED."""
    if c.kind == "consistent_order_p":
        return judge_order(I, c)
    from . import lean_backend
    check = check or lean_backend.check
    res = Result(claim_name(I, c), UNKNOWN, dims_ok(I, c))
    t0 = time.monotonic()
    witness = find_witness(I)
    for kind, proof in candidates:
        if kind == "verified" and witness is None:   # an empty domain would make any claim VERIFIED
            res.attempts.append("verified: no witness point in the domain")
            res.detail = "no rational point found in the domain; not attempting VERIFIED"
            continue
        r = check(statement(kind, I, c), judge_prefix(kind, I, c, witness) + proof, module=MODULE)
        res.attempts.append(f"{kind}: {'ok' if r.ok else 'failed'}")
        if r.ok:
            res.verdict = VERIFIED if kind == "verified" else REFUTED
            res.detail = MEANING[(c.kind, res.verdict)] + "; axioms: " + ", ".join(sorted(r.axioms))
            break
        res.detail = " ".join(r.log.split())[:400]
    res.seconds = time.monotonic() - t0
    return res


def judge_file(I: Integrator, propose=None, batch: bool = True) -> list[Result]:
    """Judge every claim about one integrator. With `batch`, the first candidate of every Lean
    claim is checked in one `lake env lean` (`lean_backend.check_batch`); claims whose first
    candidate fails fall back to `judge` on the remaining candidates."""
    from . import lean_backend
    if propose is None:
        from .tools.variational import propose
    out: list[Result | None] = [None] * len(I.claims)
    pending, items = {}, []
    witness = find_witness(I)
    for i, c in enumerate(I.claims):
        if c.kind == "consistent_order_p":
            out[i] = judge_order(I, c)
            continue
        cands = propose(I, c)
        if not batch or not cands or (cands[0][0] == "verified" and witness is None):
            out[i] = judge(I, c, cands)
            continue
        kind, proof = cands[0]
        name = f"cert_{i}"
        items.append((name, statement(kind, I, c), judge_prefix(kind, I, c, witness) + proof))
        pending[name] = (i, kind, cands)
    if items:
        t0 = time.monotonic()
        rs = lean_backend.check_batch(items, module=MODULE)
        dt = (time.monotonic() - t0) / len(items)
        for name, (i, kind, cands) in pending.items():
            c, r = I.claims[i], rs[name]
            if r.ok:
                v = VERIFIED if kind == "verified" else REFUTED
                out[i] = Result(claim_name(I, c), v, dims_ok(I, c),
                                MEANING[(c.kind, v)] + "; axioms: " + ", ".join(sorted(r.axioms)),
                                dt, [f"{kind}: ok"])
            else:
                res = judge(I, c, cands[1:])
                res.attempts.insert(0, f"{kind}: failed")
                if res.verdict == UNKNOWN and not cands[1:]:
                    res.detail = " ".join(r.log.split())[:400]
                out[i] = res
    return out


def guarantee(c: VClaim, r: Result) -> str:
    if r.verdict == UNKNOWN:
        return "none"
    return EXACT_PY if c.kind == "consistent_order_p" else "proven (Lean)"


def main(argv=None) -> int:
    """`python -m physverify.variational benchmark/variational/`: the verdict table."""
    import sys
    paths = []
    for a in (argv if argv is not None else sys.argv[1:]) or ["benchmark/variational"]:
        p = Path(a)
        paths += sorted(p.glob("*.json")) if p.is_dir() else [p]
    rows, wrong, t0 = [], 0, time.monotonic()
    for p in paths:
        I = load_variational(p)
        for c, r in zip(I.claims, judge_file(I)):
            ok = r.verdict == c.expect
            wrong += not ok
            claim = c.kind + (f" {c.p}" if c.kind == "consistent_order_p" else "")
            rows.append((p.stem, claim, c.expect, r.verdict + ("" if ok else "  (WRONG)"),
                         guarantee(c, r)))
    print("| integrator | claim | expected | verdict | guarantee |\n|---|---|---|---|---|")
    for row in rows:
        print("| " + " | ".join(row) + " |")
    counts = {v: sum(r[3].startswith(v) for r in rows) for v in (VERIFIED, REFUTED, UNKNOWN)}
    print(f"\n{len(rows)} claims: " + ", ".join(f"{n} {v}" for v, n in counts.items())
          + f", {wrong} not as expected; {time.monotonic() - t0:.0f}s")
    return 1 if wrong else 0


if __name__ == "__main__":
    raise SystemExit(main())
