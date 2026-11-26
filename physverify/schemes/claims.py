"""Trusted judge: which checks bear on which claims, and how strongly.

A check returns its own status, but a check is evidence about a claim, not the claim. Tadmor's
inequality is sufficient for "the scheme selects the entropy solution" and equivalent to "entropy
stable in Tadmor's sense"; the shock-speed study is only necessary for "conservative". The
relation lives here, in a fixed table, so no tool can report the strength of its own evidence.

The guarantee is orthogonal to the relation, and it also comes from this table: a check listed as
empirical can never produce VERIFIED or REFUTED, whatever status string it returns. An exact check
gives VERIFIED/REFUTED; an empirical one NOT_REFUTED/REFUTED_EMPIRICALLY.

Per (relation, outcome of one check):
    SUFFICIENT  pass -> verified      fail -> unknown
    NECESSARY   pass -> not refuted   fail -> refuted
    EQUIVALENT  pass -> verified      fail -> refuted
and an UNKNOWN (or NOT_APPLICABLE) outcome gives unknown. Over several checks for one claim, any
refutation refutes and any verification verifies; both at once is INCONSISTENT, which is a bug in
a checker, a spec or this table, never a physics result.
"""

from __future__ import annotations

SUFFICIENT, NECESSARY, EQUIVALENT = "SUFFICIENT", "NECESSARY", "EQUIVALENT"
EXACT, EMPIRICAL = "exact", "empirical"
VERIFIED, REFUTED, NOT_REFUTED, REFUTED_EMPIRICALLY = "VERIFIED", "REFUTED", "NOT_REFUTED", "REFUTED_EMPIRICALLY"
UNKNOWN, SUSPICIOUS, INCONSISTENT = "UNKNOWN", "SUSPICIOUS", "INCONSISTENT"
FAILURES = (REFUTED, REFUTED_EMPIRICALLY, SUSPICIOUS, INCONSISTENT)

# The strength of each check, fixed here rather than read from the check's own result.
GUARANTEE = {"consistency": EXACT, "conservation": EXACT, "positivity": EXACT, "entropy_stability": EXACT,
             "order/combined": EMPIRICAL, "order/space": EMPIRICAL, "order/time": EMPIRICAL,
             "shock_speed": EMPIRICAL, "entropy_rarefaction": EMPIRICAL}

_ORDER = ("only on the spec's smooth test problem and grids; blind to conservation (a non-conservative "
          "scheme converges at order 1 on smooth data)")
_TADMOR = ("sufficiency needs the scheme to converge, and uses that for a convex scalar flux one strictly "
           "convex entropy inequality singles out the entropy solution")

# claim -> (statement, ((check, relation, premise), ...)). The premise is what the relation rests on;
# it is carried into the verdict as an assumption.
CLAIMS = {
    "consistent": ("the numerical flux is consistent: F(u, u) = f(u)",
                   (("consistency", EQUIVALENT, ""),)),
    "conservative": ("the update is in flux form, so the total of u is conserved on periodic grids",
                     (("conservation", EQUIVALENT, ""),
                      ("shock_speed", NECESSARY, "a conservative scheme's translating shock profile moves at the "
                       "Rankine-Hugoniot speed; a non-conservative one can match it by accident on one state pair"))),
    "positive_under_cfl": ("the linear update is a non-negative combination of u_{i-1}, u_i, u_{i+1} on the "
                           "claimed CFL range", (("positivity", EQUIVALENT, ""),)),
    "entropy_stable_tadmor": ("entropy stable in Tadmor's semi-discrete sense: Q = -[v](F - F*) >= 0",
                              (("entropy_stability", EQUIVALENT, ""),)),
    "selects_entropy_solution": ("the limit of the scheme is the entropy solution, not another weak solution",
                                 (("entropy_stability", SUFFICIENT, _TADMOR),
                                  ("entropy_rarefaction", NECESSARY, "on the spec's rarefaction data only"))),
    "converges_order_p": ("converges to smooth solutions of the PDE at the order p claimed for each study",
                          tuple((f"order/{k}", NECESSARY, _ORDER) for k in ("combined", "space", "time"))),
    "correct_shock_speed": ("shocks move at the Rankine-Hugoniot speed in the limit dx -> 0",
                            (("shock_speed", NECESSARY, "on the spec's Riemann data and grids only"),)),
}

# (relation, outcome) -> polarity of the evidence for the claim
_POLARITY = {(SUFFICIENT, "pass"): "verified", (SUFFICIENT, "fail"): "unknown",
             (NECESSARY, "pass"): "not_refuted", (NECESSARY, "fail"): "refuted",
             (EQUIVALENT, "pass"): "verified", (EQUIVALENT, "fail"): "refuted"}
_LABEL = {("verified", EXACT): VERIFIED, ("verified", EMPIRICAL): NOT_REFUTED,
          ("refuted", EXACT): REFUTED, ("refuted", EMPIRICAL): REFUTED_EMPIRICALLY}


def outcome(status: str) -> str:
    """pass | fail | suspicious | unknown, from a check's status string."""
    return {"VERIFIED": "pass", "NOT_REFUTED": "pass", "REFUTED": "fail", "REFUTED_EMPIRICALLY": "fail",
            "SUSPICIOUS": "suspicious"}.get(status, "unknown")


def strength(check: str, status: str) -> str:
    """Exact only if the table says the check is exact and the check claims an exact result."""
    return EXACT if GUARANTEE.get(check) == EXACT and status in (VERIFIED, REFUTED) else EMPIRICAL


def bear(relation: str, check: str, status: str) -> tuple[str, str]:
    """(polarity, guarantee) that one check result gives the claim it bears on."""
    o = outcome(status)
    polarity = _POLARITY[relation, o] if o in ("pass", "fail") else o
    return polarity, strength(check, status)


def label(polarity: str, guarantee: str) -> str:
    return _LABEL.get((polarity, guarantee)) or {"not_refuted": NOT_REFUTED, "suspicious": SUSPICIOUS}.get(polarity, UNKNOWN)


def validate(names, table=CLAIMS) -> None:
    bad = [n for n in names if n not in table]
    if bad:
        raise ValueError(f"unknown named claims {bad}; known: {sorted(table)}")


def judge_one(name: str, results: list[dict], table=CLAIMS) -> dict:
    statement, links = table[name]
    by_check = {r["check"]: r for r in results}
    evidence = []
    for check, relation, premise in links:
        r = by_check.get(check)
        if r is None:
            continue
        polarity, g = bear(relation, check, r["status"])
        evidence.append({"check": check, "relation": relation, "status": r["status"], "polarity": polarity,
                         "guarantee": g, "gives": label(polarity, g),
                         "assumes": ([premise] if premise else []) + r.get("assumptions", [])})
    pick = lambda p: [e for e in evidence if e["polarity"] == p]
    ver, ref = pick("verified"), pick("refuted")
    if ver and ref:
        verdict, guarantee, decided = INCONSISTENT, "", ver + ref
    elif ref or ver:
        decided = ref or ver
        guarantee = EXACT if any(e["guarantee"] == EXACT for e in decided) else EMPIRICAL
        decided = [e for e in decided if e["guarantee"] == guarantee]
        verdict = label("refuted" if ref else "verified", guarantee)
    elif pick("suspicious"):
        verdict, guarantee, decided = SUSPICIOUS, EMPIRICAL, pick("suspicious")
    elif pick("not_refuted"):
        verdict, guarantee, decided = NOT_REFUTED, EMPIRICAL, pick("not_refuted")
    else:
        verdict, guarantee, decided = UNKNOWN, "", []
    assumes = list(dict.fromkeys(a for e in decided for a in e.pop("assumes")))
    for e in evidence:
        e.pop("assumes", None)
    detail = ("checker, spec or claims-table bug: " + ", ".join(f"{e['check']} gives {e['gives']}" for e in decided)
              if verdict == INCONSISTENT else "" if evidence else "no check bearing on this claim was run")
    return {"claim": name, "statement": statement, "verdict": verdict, "guarantee": guarantee,
            "decided_by": [e["check"] for e in decided], "evidence": evidence, "assumes": assumes, "detail": detail}


def judge(names, results: list[dict], table=CLAIMS) -> list[dict]:
    """One verdict per named claim the spec makes. The spec declares the claims; no check does."""
    validate(names, table)
    return [judge_one(n, results, table) for n in names]
