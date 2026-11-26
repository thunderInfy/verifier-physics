"""Derivation claims: "these equations of motion are the Euler–Lagrange equations of L".

Trusted, judge-owned: the claim format, the variable layout and the Lean statements. The
untrusted planner (`tools/eulerlagrange.py`) only supplies tactic text.

Claim JSON:
{
  "name": "...",
  "expect": "VERIFIED" | "REFUTED" | "UNKNOWN",      # benchmark label, ignored by the judge
  "why": "...",                                      # one line, ignored by the judge
  "coordinates": ["r", "th"],                       # q_k; velocities r_dot, accelerations r_ddot
  "symbols": {"r": {"dim": "L"}, "th": {"dim": "1"}, "m": {"dim": "M"}, ...},
  "lagrangian": "m/2*(r_dot^2 + r^2*th_dot^2) + G*M*m/r",
  "domain": ["r > 0", "m > 0"],                     # atoms `a > b`, `a < b`, `a != b`
                                                    # a, b continuous, no accelerations
  "eom": [{"lhs": "r_ddot", "rhs": "r*th_dot^2 - G*M/r^2"}, ...]   # one per coordinate
}

Lean layout (`PhysVerify/EulerLagrange.lean`), n = number of coordinates, k < n in the
order listed: `q_k` ↦ `k`, `qdot_k` ↦ `n + k`, `qddot_k` ↦ `2n + k`, other symbols ↦
`3n, 3n+1, …` in sorted order. The dimensions of `x_dot` and `x_ddot` are those of `x`
times T^-1 and T^-2.
"""

from __future__ import annotations

import json
import re
from dataclasses import dataclass, field
from fractions import Fraction
from pathlib import Path

from . import units
from .expr import E, parse, to_lean, variables
from .theory import Malformed

VERIFIED, REFUTED, UNKNOWN = "VERIFIED", "REFUTED", "UNKNOWN"
_ATOM = re.compile(r"^(.*?)(>|<|!=)(.*)$")


@dataclass
class Claim:
    name: str
    coords: list[str]
    dims: dict[str, units.Dim]
    lagrangian: E
    domain: list[tuple[str, E, E]]          # (op, a, b)
    eom: list[tuple[E, E]]                  # (lhs, rhs)
    expect: str = ""
    why: str = ""
    source: dict = field(default_factory=dict)

    @property
    def n(self) -> int:
        return len(self.coords)

    def index(self) -> dict[str, int]:
        n = self.n
        idx = {}
        for k, q in enumerate(self.coords):
            idx[q], idx[f"{q}_dot"], idx[f"{q}_ddot"] = k, n + k, 2 * n + k
        for j, s in enumerate(self.params()):
            idx[s] = 3 * n + j
        return idx

    def params(self) -> list[str]:
        return sorted(set(self.dims) - set(self.jet()))

    def jet(self) -> list[str]:
        return ([q for q in self.coords] + [f"{q}_dot" for q in self.coords]
                + [f"{q}_ddot" for q in self.coords])


def load_claim(spec: dict | str | Path) -> Claim:
    if not isinstance(spec, dict):
        spec = json.loads(Path(spec).read_text())
    try:
        coords = list(spec["coordinates"])
        dims = {k: units.parse_dim(v["dim"]) for k, v in spec["symbols"].items()}
        for q in coords:
            if q not in dims:
                raise Malformed(f"coordinate {q!r} has no dimension")
            t = units.parse_dim("T")
            dims[f"{q}_dot"] = units.sub(dims[q], t)
            dims[f"{q}_ddot"] = units.sub(dims[q], units.smul(2, t))
        dom = []
        for a in spec.get("domain", []):
            m = _ATOM.match(a)
            if not m:
                raise Malformed(f"domain atom {a!r} is not `a > b`, `a < b` or `a != b`")
            dom.append((m.group(2), parse(m.group(1)), parse(m.group(3))))
        c = Claim(spec["name"], coords, dims, parse(spec["lagrangian"]), dom,
                  [(parse(e["lhs"]), parse(e["rhs"])) for e in spec["eom"]],
                  spec.get("expect", ""), spec.get("why", ""), spec)
    except (KeyError, ValueError) as ex:
        raise Malformed(f"claim {spec.get('name')!r}: {ex}") from ex
    used = variables(c.lagrangian)
    for op, a, b in c.domain:
        used |= variables(a) | variables(b)
    for l, r in c.eom:
        used |= variables(l) | variables(r)
    if used - set(c.dims):
        raise Malformed(f"claim {c.name!r}: undeclared symbols {sorted(used - set(c.dims))}")
    accel = {f"{q}_ddot" for q in coords}
    if variables(c.lagrangian) & accel:
        raise Malformed(f"claim {c.name!r}: the Lagrangian may not depend on accelerations")
    for op, a, b in c.domain:
        # the domain may only constrain (q, qdot, parameters): `verified_meaning` needs the
        # jet of a trajectory to stay in D near t, and q'' need not be continuous
        if (variables(a) | variables(b)) & accel:
            raise Malformed(f"claim {c.name!r}: domain atoms may not mention accelerations")
        # strict inequalities of continuous expressions, so D is open
        bad = _discontinuous(a) or _discontinuous(b)
        if bad:
            raise Malformed(f"claim {c.name!r}: domain atoms must be continuous everywhere "
                            f"(polynomials, sin, cos, exp); found {bad}")
    if len(c.eom) != c.n:
        raise Malformed(f"claim {c.name!r}: {len(c.eom)} equations for {c.n} coordinates")
    return c


def _discontinuous(e: E) -> str:
    """The first node that makes `Expr.eval` discontinuous somewhere, or ''."""
    if e.kind == "div" and e.args[1].kind == "lit" and e.args[1].q != 0:
        return _discontinuous(e.args[0])                  # division by a non-zero constant
    if e.kind in ("div", "sqrt", "rpow") or (e.kind == "powi" and e.q < 0) or \
            (e.kind == "app" and e.name == "log"):
        return e.kind if e.kind != "app" else "log"
    return next((d for d in map(_discontinuous, e.args) if d), "")


# ---------------------------------------------------------------- domain witness

def _qeval(e: E, env: dict[str, Fraction]) -> Fraction | None:
    """Exact value of a domain expression (continuous nodes only), None if irrational."""
    k, a = e.kind, e.args
    if k == "var": return env[e.name]
    if k == "lit": return Fraction(e.q)
    xs = [_qeval(x, env) for x in a]
    if k == "pi" or None in xs: return None
    if k == "neg": return -xs[0]
    if k == "add": return xs[0] + xs[1]
    if k == "sub": return xs[0] - xs[1]
    if k == "mul": return xs[0] * xs[1]
    if k == "div" and xs[1] != 0: return xs[0] / xs[1]
    if k == "powi" and e.q >= 0: return xs[0] ** int(e.q)
    if k == "app" and xs[0] == 0: return {"sin": Fraction(0), "cos": Fraction(1), "exp": Fraction(1)}.get(e.name)
    return None


_WITNESS_VALUES = [Fraction(v) for v in ("1", "2", "1/2", "-1", "3", "-2", "-1/2", "1/4", "0", "5", "-3", "1/10")]


def find_witness(c: Claim, tries: int = 4000, seed: int = 0) -> dict[str, Fraction] | None:
    """A rational point of the domain, every atom checked exactly (the kernel re-checks it)."""
    import random
    rng = random.Random(seed)
    names = sorted(set(c.index()))
    for t in range(tries):
        env = {s: (Fraction(1) if t == 0 else rng.choice(_WITNESS_VALUES)) for s in names}
        ok = True
        for op, a, b in c.domain:
            x, y = _qeval(a, env), _qeval(b, env)
            if x is None or y is None or not {">": x > y, "<": x < y, "!=": x != y}[op]:
                ok = False
                break
        if ok:
            return env
    return None


def lean_point(c: Claim, env: dict[str, Fraction]) -> str:
    idx = c.index()
    items = []
    for s in sorted(idx, key=idx.get):
        q = Fraction(env.get(s, 0))
        items.append(f"({q.numerator} : ℝ)" if q.denominator == 1
                     else f"(({q.numerator} : ℝ) / {q.denominator})")
    return "(fun j : ℕ => [" + ", ".join(items) + "].getD j 0)"


def witness_proof(c: Claim, env: dict[str, Fraction]) -> str:
    """Judge-written start of every `verified` proof: the domain is not empty. The planner's
    tactic then proves the `∀ env, D env → …` part."""
    return (f"refine ⟨by decide, by decide, ⟨{lean_point(c, env)}, ?_⟩, ?_⟩\n"
            "· first | trivial | (simp [Expr.eval, Fn.eval] <;> norm_num)\n")


# ---------------------------------------------------------------- Lean statements

def lean_ctx(c: Claim) -> str:
    idx = c.index()
    by_index = sorted(idx, key=idx.get)
    return "[" + ", ".join(units.lean_dim(c.dims[s]) for s in by_index) + "]"


def lean_terms(c: Claim) -> dict[str, str]:
    idx = c.index()
    L = to_lean(c.lagrangian, idx)
    atoms = []
    for op, a, b in c.domain:
        la, lb = f"Expr.eval env {to_lean(a, idx)}", f"Expr.eval env {to_lean(b, idx)}"
        atoms.append({">": f"{lb} < {la}", "<": f"{la} < {lb}", "!=": f"{la} ≠ {lb}"}[op])
    D = "fun env : ℕ → ℝ => " + (" ∧ ".join(atoms) if atoms else "True")
    cs = "[" + ", ".join(f"(⟨{to_lean(l, idx)}, {to_lean(r, idx)}⟩ : Law)" for l, r in c.eom) + "]"
    return {"n": str(c.n), "L": L, "D": f"({D})", "cs": cs, "ctx": lean_ctx(c)}


def dims_ok(c: Claim) -> tuple[bool, str]:
    """Python mirror of the kernel's `dimsOK` (the kernel re-checks it in every certificate)."""
    try:
        units.dim_of(c.lagrangian, c.dims)
        for l, r in c.eom:
            dl, dr = units.dim_of(l, c.dims), units.dim_of(r, c.dims)
            zero = any(x.kind == "lit" and x.q == 0 for x in (l, r))  # 0 has every dimension
            if dl != dr and not zero:
                return False, f"{l!r} has {units.fmt_dim(dl)} but {r!r} has {units.fmt_dim(dr)}"
    except units.DimError as ex:
        return False, str(ex)
    return True, "ok"


def statement(kind: str, c: Claim) -> str:
    t = lean_terms(c)
    if kind == "verified":
        return (f"dimsOK {t['ctx']} {t['L']} {t['cs']} = true ∧ NoAccel {t['n']} {t['L']} ∧ "
                f"Verified {t['n']} {t['L']} {t['D']} {t['cs']}")
    if kind == "refuted":
        return f"NoAccel {t['n']} {t['L']} ∧ Refuted {t['n']} {t['L']} {t['D']} {t['cs']}"
    raise KeyError(kind)


MEANING = {
    VERIFIED: ("PhysVerify.verified_meaning: for every trajectory twice differentiable at t "
               "whose jet stays in the domain near t, the real Euler–Lagrange equations hold "
               "at t iff the claimed equations hold at t; the domain is non-empty and has no "
               "junk division/power/sqrt/log values (verified_nonempty)"),
    REFUTED: ("PhysVerify.refuted_meaning: on the quadratic trajectory through the "
              "counterexample jet, at t = 0, the real Euler–Lagrange equations and the claimed "
              "equations disagree"),
}
ASSUMPTIONS = [
    "the claim file is translated to Lean by literal serialization (physverify/expr.py to_lean)",
]


@dataclass
class Result:
    claim: str
    verdict: str
    dims: str
    detail: str = ""
    seconds: float = 0.0
    attempts: list[str] = field(default_factory=list)


def judge(c: Claim, candidates: list[tuple[str, str]], check=None) -> Result:
    """Candidates are (kind, tactic) pairs from the untrusted planner; kind ∈ verified/refuted.

    A verdict other than UNKNOWN needs the Lean kernel to accept the judge's own statement.
    A `verified` tactic proves only `∀ env, D env → …`: the judge first needs its own
    rational point of D, and proves `∃ env, D env` with it.
    """
    import time

    from . import lean_backend
    check = check or lean_backend.check
    ok, why = dims_ok(c)
    res = Result(c.name, UNKNOWN, "ok" if ok else f"mismatch: {why}")
    t0 = time.monotonic()
    witness = find_witness(c)
    for kind, proof in candidates:
        if kind == "verified":
            if witness is None:  # an empty domain would make any claim VERIFIED
                res.attempts.append("verified: no witness point in the domain")
                res.detail = "no rational point found in the domain; not attempting VERIFIED"
                continue
            proof = witness_proof(c, witness) + proof
        r = check(statement(kind, c), proof, module="PhysVerify.EulerLagrange")
        res.attempts.append(f"{kind}: {'ok' if r.ok else 'failed'}")
        if r.ok:
            res.verdict = VERIFIED if kind == "verified" else REFUTED
            res.detail = MEANING[res.verdict] + "; axioms: " + ", ".join(sorted(r.axioms))
            break
        res.detail = " ".join(r.log.split())[:400]
    res.seconds = time.monotonic() - t0
    return res
