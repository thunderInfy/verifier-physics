"""The deterministic judge.

Rejects a theory only when a candidate's certificate re-checks against an obligation the
judge built itself, and that obligation's guarantee is allowed by policy. A failed,
timed-out or unsupported certificate is UNKNOWN — never a rejection.
"""

from __future__ import annotations

from dataclasses import dataclass, field

from . import lean_backend, obligations
from .core import (EXCLUDED, MALFORMED, NOT_REFUTED, PROVEN, REFUTED, STATISTICAL, UNKNOWN,
                   VALIDATED, Candidate, Finding)
from .theory import Evidence, Theory
from .tools import dimension


@dataclass
class Policy:
    allowed: set[str] = field(default_factory=lambda: {PROVEN, VALIDATED, STATISTICAL})


@dataclass
class Report:
    theory: str
    verdict: str
    findings: list[Finding]


def _verify(ob: obligations.Obligation, c: Candidate) -> tuple[bool, str]:
    if ob.statement is not None:
        if not isinstance(c.proof, str):
            return False, "expected Lean tactic text"
        r = lean_backend.check(ob.statement, c.proof)
        return r.ok, ("Lean kernel accepted; axioms: " + ", ".join(sorted(r.axioms))
                      if r.ok else "certificate did not check (no conclusion): " + " ".join(r.log.split())[:300])
    if ob.numeric is not None:
        from .tools.enclosure import check_certificate
        return check_certificate(ob.numeric, c.proof)
    return False, "obligation has no checker"


def judge(th: Theory, evidence: list[Evidence], candidates: list[Candidate],
          policy: Policy | None = None) -> Report:
    policy = policy or Policy()
    evs = {e.id: e for e in evidence}
    findings: list[Finding] = []
    for err in dimension.well_typed_errors(th):
        findings.append(Finding("contract", MALFORMED, err))
    for c in candidates:
        try:
            ob = obligations.build(c.kind, c.args, th, evs)
        except (KeyError, StopIteration) as ex:
            findings.append(Finding(c.tool, UNKNOWN, f"bad obligation {c.kind} {c.args}: {ex}"))
            continue
        if ob.skip:
            findings.append(Finding(c.tool, ob.skip, ob.claim, evidence=ob.evidence))
            continue
        if ob.guarantee not in policy.allowed:
            findings.append(Finding(c.tool, UNKNOWN, ob.claim, ob.guarantee, ob.assumptions,
                                    ob.evidence, "guarantee not allowed by policy"))
            continue
        ok, detail = _verify(ob, c)
        cert = {"kind": c.kind, "args": c.args, "statement": ob.statement,
                "conclusion": ob.conclusion}
        hit = EXCLUDED if ob.guarantee == STATISTICAL else REFUTED
        findings.append(Finding(c.tool, hit if ok else UNKNOWN, ob.claim, ob.guarantee,
                                ob.assumptions, ob.evidence, detail if not ok else
                                f"{detail}. {c.note}".strip(), cert))
    statuses = {f.status for f in findings}
    verdict = REFUTED if REFUTED in statuses else EXCLUDED if EXCLUDED in statuses else NOT_REFUTED
    return Report(th.name, verdict, findings)


def render(r: Report) -> str:
    lines = [f"## {r.theory}: {r.verdict}"]
    for f in r.findings:
        lines.append(f"- [{f.status}] ({f.tool}{', ' + f.guarantee if f.guarantee else ''}) {f.claim}")
        if f.status in (REFUTED, EXCLUDED):
            for a in f.assumptions:
                lines.append(f"    assumes: {a}")
            if f.certificate.get("conclusion"):
                lines.append(f"    via: {f.certificate['conclusion']}")
        if f.detail:
            lines.append("    " + f.detail.strip().splitlines()[0][:300])
    if not r.findings:
        lines.append("- no tool found a refutation")
    return "\n".join(lines)
