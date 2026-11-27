"""Conserved-quantity claims: "Q is constant along every solution of the EL equations of L in D".

Trusted, judge-owned: the claim format and the Lean statements. The untrusted planner
(`tools/conserved.py`) only supplies tactic text (including the multipliers λ_k).

Claim JSON (`claims/conserved/*.json`):
{
  "kind": "conserved",
  "name": "...",
  "true": true | false | null,                      # null: ill-posed, only UNKNOWN is right
  "expect": "VERIFIED" | "REFUTED" | "UNKNOWN",      # benchmark label, ignored by the judge
  "why": "...",
  "coordinates": ["th"], "symbols": {...}, "lagrangian": "...", "domain": [...],
                                                    # as for EOM claims (derivation.py)
  "quantity": "m*l^2/2*th_dot^2 - m*g*l*cos(th)"    # Q(q, q_dot, parameters)
}

Lean statements (`PhysVerify/Conserved.lean`), same variable layout as `derivation.py`:

* verified: `(L.dimOf ctx).isSome ∧ (Q.dimOf ctx).isSome ∧ NoAccel n L ∧ NoAccel n Q ∧
  DomainForm n D as ∧ ∃ λs, λs.length = n ∧ (∀ l ∈ λs, NoAccel n l) ∧
  ConservedVerified n L D Q λs`. The multipliers are existentially quantified, so the
  statement does not depend on the planner.
* refuted: `NoAccel n L ∧ NoAccel n Q ∧ ConservedRefuted n L D Q`.
"""

from __future__ import annotations

import json
from dataclasses import dataclass
from pathlib import Path

from . import claimkinds, units
from .derivation import (REFUTED, UNKNOWN, VERIFIED, Claim, Result, find_witness, lean_terms,
                         load_claim)
from .expr import E, parse, to_lean, variables
from .theory import Malformed


@dataclass
class ConservedClaim(Claim):
    quantity: E | None = None


KIND = "conserved"                     # the claim kind of this layer (physverify/claimkinds.py)
claimkinds.require("conserved", [KIND])


def is_conserved(spec: dict) -> bool:
    return spec.get("kind") == KIND


def load_conserved(spec: dict | str | Path) -> ConservedClaim:
    if not isinstance(spec, dict):
        spec = json.loads(Path(spec).read_text())
    if not is_conserved(spec):
        raise Malformed(f"claim {spec.get('name')!r}: not a conserved-quantity claim")
    if "quantity" not in spec:
        raise Malformed(f"claim {spec.get('name')!r}: no quantity")
    # coordinates, symbols, L and D are parsed and checked exactly as for EOM claims; the
    # placeholder equations `0 = 0` only satisfy that parser and are dropped
    n = len(spec.get("coordinates", []))
    base = load_claim({**spec, "eom": [{"lhs": "0", "rhs": "0"}] * n})
    try:
        Q = parse(spec["quantity"])
    except ValueError as ex:
        raise Malformed(f"claim {base.name!r}: {ex}") from ex
    c = ConservedClaim(base.name, base.coords, base.dims, base.lagrangian, base.domain, [],
                       base.expect, base.why, spec, quantity=Q)
    if variables(Q) - set(c.dims):
        raise Malformed(f"claim {c.name!r}: undeclared symbols {sorted(variables(Q) - set(c.dims))}")
    if variables(Q) & {f"{q}_ddot" for q in c.coords}:
        raise Malformed(f"claim {c.name!r}: the quantity may not depend on accelerations")
    return c


def lean_terms_q(c: ConservedClaim) -> dict[str, str]:
    t = lean_terms(c)
    t["Q"] = to_lean(c.quantity, c.index())
    return t


def dims_ok(c: ConservedClaim) -> tuple[bool, str]:
    """Python mirror of the kernel's `dimOf` checks on L and Q (re-checked by `decide`)."""
    try:
        units.dim_of(c.lagrangian, c.dims)
        units.dim_of(c.quantity, c.dims)
    except units.DimError as ex:
        return False, str(ex)
    return True, "ok"


def statement(kind: str, c: ConservedClaim) -> str:
    t = lean_terms_q(c)
    n, L, Q, D = t["n"], t["L"], t["Q"], t["D"]
    if kind == "verified":
        return (f"(Expr.dimOf {t['ctx']} {L}).isSome = true ∧ (Expr.dimOf {t['ctx']} {Q}).isSome = true ∧ "
                f"NoAccel {n} {L} ∧ NoAccel {n} {Q} ∧ DomainForm {n} {D} {t['atoms']} ∧ "
                f"∃ lams : List Expr, lams.length = {n} ∧ (∀ l ∈ lams, NoAccel {n} l) ∧ "
                f"ConservedVerified {n} {L} {D} {Q} lams")
    if kind == "refuted":
        return f"NoAccel {n} {L} ∧ NoAccel {n} {Q} ∧ ConservedRefuted {n} {L} {D} {Q}"
    raise KeyError(kind)


# the judge proves these conjuncts itself; the planner proves the `∃ lams, …` part
PREFIX = "refine ⟨by decide, by decide, by decide, by decide, ⟨fun _ => Iff.rfl, by decide⟩, ?_⟩\n"

MEANING = {
    VERIFIED: ("PhysVerify.conserved_meaning: along every trajectory twice differentiable on an "
               "open interval, with its jet in the (open) domain and the real Euler–Lagrange "
               "equations holding there, dQ/dt = 0 and Q is constant on the interval; the domain "
               "is non-empty and L, Q and the multipliers take no junk values on it"),
    REFUTED: ("PhysVerify.conserved_refuted_meaning: at a jet in the domain where the "
              "Euler–Lagrange equations hold and the velocity Hessian of L is invertible, every "
              "trajectory through the jet has dQ/dt ≠ 0 there (assumed, not proved: that an "
              "Euler–Lagrange solution passes through the jet)"),
}


def judge(c: ConservedClaim, candidates: list[tuple[str, str]], check=None) -> Result:
    """Candidates are (kind, tactic) pairs from the untrusted planner; kind ∈ verified/refuted.
    No accepted certificate gives UNKNOWN, never REFUTED."""
    import time

    from . import lean_backend
    check = check or lean_backend.check
    ok, why = dims_ok(c)
    res = Result(c.name, UNKNOWN, "ok" if ok else f"mismatch: {why}")
    t0 = time.monotonic()
    for kind, proof in candidates:
        if kind == "verified":
            if find_witness(c) is None:
                res.attempts.append("verified: no witness point in the domain")
                res.detail = "no rational point found in the domain; not attempting VERIFIED"
                continue
            proof = PREFIX + proof
        r = check(statement(kind, c), proof, module="PhysVerify.Conserved")
        res.attempts.append(f"{kind}: {'ok' if r.ok else 'failed'}")
        if r.ok:
            res.verdict = VERIFIED if kind == "verified" else REFUTED
            res.detail = MEANING[res.verdict] + "; axioms: " + ", ".join(sorted(r.axioms))
            break
        res.detail = " ".join(r.log.split())[:400]
    res.seconds = time.monotonic() - t0
    return res
