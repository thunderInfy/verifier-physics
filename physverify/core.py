"""Types shared by tools (untrusted proposers) and the judge (trusted decider)."""

from __future__ import annotations

from dataclasses import dataclass, field

# Guarantee labels, strongest first. Policy decides which may authorize a rejection.
PROVEN = "proven"                        # Lean kernel-checked, standard axioms only
VALIDATED = "validated-numeric"          # rigorous interval arithmetic, re-checked by the judge
STATISTICAL = "statistical"              # separate channel; never "refuted" in the strict sense
SCORE = "score-only"

# Outcomes
REFUTED = "REFUTED"                      # under the listed assumptions, with a checked certificate
EXCLUDED = "EXCLUDED"                    # statistical channel: excluded at family-wise level α
NOT_REFUTED = "NOT_REFUTED"
UNKNOWN = "UNKNOWN"                      # tool could not decide (accept)
OUT_OF_REGIME = "OUT_OF_REGIME"          # theory makes no claim about this evidence (accept)
MALFORMED = "MALFORMED"                  # input violates the contract; not a verdict on physics


@dataclass
class Candidate:
    """A proposed refutation from an untrusted tool.

    The tool only *names* an obligation (`kind` + arguments such as a law name or an evidence
    id) and supplies a proof. The judge builds the statement, the assumption list and the
    guarantee label itself (`obligations.py`), so a tool can neither weaken what is proved nor
    drop an assumption.
    """
    tool: str
    kind: str
    args: dict
    proof: object                        # Lean tactic text, or a numeric certificate
    note: str = ""                       # informational only


@dataclass
class Finding:
    tool: str
    status: str
    claim: str
    guarantee: str = ""
    assumptions: list[str] = field(default_factory=list)
    evidence: list[str] = field(default_factory=list)
    detail: str = ""
    certificate: dict = field(default_factory=dict)
