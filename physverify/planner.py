"""A simple untrusted planner: ask every registered tool for candidate refutations.

Anything smarter (an LLM choosing which tools to run, proposing proofs) plugs in here;
it cannot affect soundness because the judge re-checks every candidate.
"""

from __future__ import annotations

from .core import Candidate
from .theory import Evidence, Theory
from .tools import algebra, dimension, enclosure, orbit

REGISTRY = [dimension, algebra, orbit, enclosure]


def plan(th: Theory, evidence: list[Evidence]) -> list[Candidate]:
    out: list[Candidate] = []
    for tool in REGISTRY:
        try:
            out += tool.propose(th, evidence)
        except Exception as ex:  # a broken tool just finds nothing
            print(f"[planner] {tool.NAME} failed: {ex!r}")
    return out
