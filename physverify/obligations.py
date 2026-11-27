"""Trusted table: obligation kind → (statement, guarantee, assumptions, conclusion theorem).

A tool names an obligation; *this* module decides exactly what must be proved and what a
successful proof means. Keep it small and boring.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction

from . import claimkinds, lean_terms as lt
from .core import OUT_OF_REGIME, PROVEN, STATISTICAL, VALIDATED
from .theory import Evidence, Theory
from .tools.binding import bind

KINDS = ("dim_mismatch", "law_vs_evidence", "orbit_excluded", "trajectory_vs_evidence")  # `_build`
claimkinds.require("theory", KINDS)


@dataclass
class Obligation:
    claim: str
    guarantee: str
    assumptions: list[str]
    evidence: list[str]
    statement: str | None = None          # Lean statement (PROVEN obligations)
    conclusion: str = ""                  # library theorem giving the physical meaning
    numeric: dict | None = None           # inputs for VALIDATED checkers
    skip: str | None = None               # e.g. OUT_OF_REGIME, with reason in `claim`


def _law(th: Theory, name: str):
    return next(l for l in th.laws if l.name == name)


def in_regime(th: Theory, bounds: dict[str, tuple[Fraction, Fraction]]) -> str | None:
    """None if the evidence box lies inside the theory's declared regime, else a reason."""
    for s, (rlo, rhi) in th.regime.items():
        if s not in bounds:
            return f"evidence does not pin down regime variable {s}"
        lo, hi = bounds[s]
        if lo < rlo or hi > rhi:
            return f"evidence {s} ∈ [{float(lo):.6g}, {float(hi):.6g}] leaves regime [{float(rlo):.6g}, {float(rhi):.6g}]"
    return None


def build(kind: str, args: dict, th: Theory, evidence: dict[str, Evidence]) -> Obligation:
    ob = _build(kind, args, th, evidence)
    stat = [evidence[e] for e in ob.evidence if e in evidence and evidence[e].statistical]
    if stat and not ob.skip:
        ev = stat[0]
        ob.guarantee = STATISTICAL
        ob.assumptions = [a for a in ob.assumptions if not a.startswith("hard bounds of")] + [
            f"{ev.id}: each reported value ± σ is a correct Gaussian marginal ({ev.source})",
            f"family {ev.family!r}: Bonferroni box value ± {float(ev.stat['z']):.4g}σ over all "
            f"K = {ev.stat['K']} measurements ⇒ all true values inside with prob ≥ 1 − α = "
            f"{float(1 - ev.stat['alpha']):.4g}"]
    return ob


def _build(kind: str, args: dict, th: Theory, evidence: dict[str, Evidence]) -> Obligation:
    if kind == "dim_mismatch":
        l = _law(th, args["law"])
        return Obligation(
            claim=f"law {l.name} ({l.lhs!r} = {l.rhs!r}) is not dimensionally homogeneous",
            guarantee=PROVEN,
            assumptions=["unit-covariance: laws of nature do not depend on the choice of units",
                         "non-degeneracy: the law holds somewhere with non-zero sides"],
            evidence=[],
            statement=f"Law.dimMismatch {lt.ctx(th)} {lt.law(l.lhs, l.rhs, th)} = true",
            conclusion="PhysVerify.Law.dimMismatch_refutes",
        )

    if kind == "law_vs_evidence":
        l, ev = _law(th, args["law"]), evidence[args["evidence"]]
        bounds = bind(th, ev)
        why = in_regime(th, bounds)
        if why:
            return Obligation(why, "", [], [ev.id], skip=OUT_OF_REGIME)
        hyps, _ = lt.bound_hyps(th, bounds)
        prem = f"{hyps} → " if hyps else ""
        return Obligation(
            claim=f"law {l.name} fails everywhere in the box of evidence {ev.id}",
            guarantee=PROVEN,
            assumptions=[f"hard bounds of {ev.id} contain the true values ({ev.source})"],
            evidence=[ev.id],
            statement=f"∀ env : ℕ → ℝ, {prem}Law.Holds {lt.law(l.lhs, l.rhs, th)} env → False",
            conclusion="(direct: the law contradicts the evidence box)",
        )

    if kind == "orbit_excluded":
        from .tools.orbit import obligation  # Lean statement for step 6
        return obligation(args, th, evidence)

    if kind == "trajectory_vs_evidence":
        from .tools.enclosure import obligation  # numeric obligation for step 5
        return obligation(args, th, evidence)

    raise KeyError(f"unknown obligation kind {kind!r}")


__all__ = ["Obligation", "build", "in_regime", "PROVEN", "STATISTICAL", "VALIDATED"]
