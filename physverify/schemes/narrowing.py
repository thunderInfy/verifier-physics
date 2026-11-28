"""What a narrowed reading's verdict says about the sentence it narrows (bench scoring, opt-in).

A reading may narrow a sentence to an instance: one flux, one slope, one method, a sub-range of a CFL
range. The old convention asked the reader to keep the sentence's truth value, which a blind reader
cannot do, since it does not know that value. Here the polarity comes from the sentence's quantifier
over each narrowed parameter instead, through the same relation table the checker uses
(claims.py: "checks declare their relation to a claim"):

  - universal (for every slope / flux / method, for all CFL numbers in a range, an added hypothesis
    restricting the class): the instance is NECESSARY for the sentence. Instance REFUTED -> REFUTED;
    instance VERIFIED -> NOT_REFUTED, never VERIFIED.
  - existential (stable for some / small enough CFL, there is a limiter such that ...): the instance
    is SUFFICIENT. Instance VERIFIED -> VERIFIED; instance REFUTED -> UNKNOWN.
  - mixed, or any narrowed parameter whose quantifier is not recorded and not fixed by the claim
    kind: UNKNOWN. We never guess.

A narrowed parameter is {"param": name, "quantifier": "universal" | "existential" | None}, the
quantifier being the sentence's. For the CFL number (param "cfl") a missing quantifier is read from
the claim-kind registry when the kind fixes it (`cfl_quantifier`). A reading whose verdict is about the
negated sentence passes negated=True, which swaps the quantifiers (not for all = there is a failing one).
A reading without a narrowing is returned unchanged.
"""

from __future__ import annotations

import re

from .. import claimkinds
from . import claims as C

UNIVERSAL, EXISTENTIAL = "universal", "existential"
DECIDED = (C.VERIFIED, C.REFUTED, C.REFUTED_EMPIRICALLY, C.NOT_REFUTED)
RELATION = {UNIVERSAL: C.NECESSARY, EXISTENTIAL: C.SUFFICIENT}


def cfl_quantifier(kind: str) -> str | None:
    """The kind's own quantifier over the CFL number, when its registry entry fixes it: 'there is nu0
    ...' is existential, 'for all / every nu ...' universal; otherwise None."""
    q = claimkinds.KINDS.get(kind, {}).get("quantifier", "")
    if q.startswith("there is nu0"):
        return EXISTENTIAL
    if re.search(r"\b(all|every) nu\b", q):
        return UNIVERSAL
    return None


def quantifiers(narrowed: list[dict], kinds=(), negated: bool = False) -> list[str | None]:
    out = []
    for p in narrowed:
        q = p.get("quantifier")
        if q is None and p.get("param") == "cfl":
            got = {cfl_quantifier(k) for k in kinds}
            q = got.pop() if len(got) == 1 else None
        if q is not None and negated:
            q = EXISTENTIAL if q == UNIVERSAL else UNIVERSAL
        out.append(q if q in RELATION else None)
    return out


def relation(narrowed: list[dict], kinds=(), negated: bool = False) -> str | None:
    """NECESSARY when every narrowed parameter is universal, SUFFICIENT when every one is existential,
    else None (mixed or unrecorded)."""
    qs = quantifiers(narrowed, kinds, negated)
    if not qs or None in qs or len(set(qs)) != 1:
        return None
    return RELATION[qs[0]]


def sentence_verdict(verdict: str, narrowing, narrowed: list[dict] | None, kinds=(), negated: bool = False) -> str:
    """The verdict for the sentence, from the verdict on the narrowed instance. Only a decided verdict
    moves; UNKNOWN, INCONSISTENT, SPEC_ERROR and the like pass through."""
    if not narrowing or verdict not in DECIDED:
        return verdict
    rel = relation(narrowed or [], kinds, negated)
    if rel is None:
        return C.UNKNOWN
    g = C.EXACT if verdict in (C.VERIFIED, C.REFUTED) else C.EMPIRICAL
    polarity = C._POLARITY[rel, C.outcome(verdict)]
    if polarity == "verified" and g == C.EMPIRICAL:          # as in claims.bear: an empirical pass never verifies
        polarity = "not_refuted"
    return C.label(polarity, g)


def for_reading(reading: dict, verdict: str) -> str:
    """sentence_verdict for a bench reading: its `narrowing` (text or null), its `narrowed` list (the
    narrowed parameters with the sentence's quantifier over each; absent in readings written before this
    rule, which then give UNKNOWN when narrowed), the claim kinds of its formal components and whether
    any of them is negated."""
    comps = [c for c in reading.get("formalization", []) if "claim" in c]
    return sentence_verdict(verdict, reading.get("narrowing"), reading.get("narrowed"),
                            [c["claim"] for c in comps], any(c.get("negated") for c in comps))
