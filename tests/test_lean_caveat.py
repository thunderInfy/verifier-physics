"""A verdict's guarantee keeps the caveats of the checks it rests on, on the exact-Python path and
when the Lean replay upgrades it. Fast: the accepted Lean labels are written by hand, no Lean runs."""

from pathlib import Path

from physverify.schemes import checks, claims as C, lean_cert as L, load

ROOT = Path(__file__).resolve().parent.parent

SEMI = "semi-discrete inequality only, time stepping not certified"
ENTROPY_LEAN = L.LEAN + "; " + SEMI


def test_caveats_parse_the_check_labels():
    assert checks.ENTROPY_EXACT == checks.EXACT + "; " + SEMI
    assert C.caveats(checks.ENTROPY_EXACT) == [SEMI]
    assert C.caveats(ENTROPY_LEAN) == [SEMI]
    for bare in (checks.EXACT, L.LEAN, L.LEAN_CELLS, C.EXACT, ""):
        assert C.caveats(bare) == []
    assert C.caveats(L.LEAN_CELLS + "; x; y") == ["x", "y"]


def test_lean_upgrade_keeps_the_caveat():
    assert L.verdict_label([ENTROPY_LEAN]) == ENTROPY_LEAN


def test_lean_upgrade_without_caveats_is_unchanged():
    assert L.verdict_label([L.LEAN, L.LEAN]) == L.LEAN
    assert L.verdict_label([L.LEAN, L.LEAN_CELLS]) == L.LEAN_CELLS
    assert L.verdict_label([L.LEAN, checks.EXACT]) is None
    assert L.verdict_label([]) is None


def test_two_caveats_appear_once_each():
    labels = [L.LEAN_CELLS + "; first", L.LEAN + "; second; first", L.LEAN + "; second"]
    got = L.verdict_label(labels)
    assert got == L.LEAN_CELLS + "; first; second"
    assert got.count("first") == 1 and got.count("second") == 1


def _report(claim, decided_by, guarantees):
    return {"checks": [{"check": c, "guarantee": g} for c, g in guarantees.items()],
            "claims": [{"claim": claim, "guarantee": C.EXACT + "".join("; " + x for c in decided_by
                                                                       for x in C.caveats(guarantees[c])),
                        "decided_by": decided_by}]}


def test_relabel_claims_keeps_the_entropy_caveat():
    rep = _report("entropy_stable_tadmor", ["entropy_stability"], {"entropy_stability": ENTROPY_LEAN})
    L.relabel_claims(rep)
    assert rep["claims"][0]["guarantee"] == ENTROPY_LEAN


def test_relabel_claims_takes_caveats_from_required_checks():
    """Monotonicity decides the entropy claim only for a conservative, consistent scheme, so the
    verdict also carries the caveats of those two checks."""
    g = {"monotonicity": L.LEAN_CELLS, "conservation": L.LEAN + "; b", "consistency": L.LEAN + "; a; b"}
    rep = _report("selects_entropy_solution", ["monotonicity"], g)
    L.relabel_claims(rep)
    assert rep["claims"][0]["guarantee"] == L.LEAN_CELLS + "; b; a"     # sorted by check: conservation first
    g["consistency"] = checks.EXACT                                       # one check not replayed: no upgrade
    rep = _report("selects_entropy_solution", ["monotonicity"], g)
    L.relabel_claims(rep)
    assert rep["claims"][0]["guarantee"] == C.EXACT


def test_exact_python_verdict_keeps_the_caveat():
    v = C.judge_one("entropy_stable_tadmor", [{"check": "entropy_stability", "status": checks.REFUTED,
                                               "guarantee": checks.ENTROPY_EXACT}])
    assert v["verdict"] == C.REFUTED and v["guarantee"] == C.EXACT + "; " + SEMI


def test_exact_python_verdict_without_caveats_is_bare():
    v = C.judge_one("monotone_under_cfl", [{"check": "monotonicity", "status": checks.VERIFIED,
                                            "guarantee": checks.EXACT}])
    assert v["verdict"] == C.VERIFIED and v["guarantee"] == C.EXACT


def test_roe_entropy_verdicts_keep_the_caveat(checked):
    """On the shipped Roe specs every exact verdict resting on entropy_stability says semi-discrete."""
    seen = 0
    for name in ("broken-burgers-roe-no-entropy-fix", "burgers-roe-harten-fix"):
        rep = checked(load(ROOT / "schemes" / f"{name}.json"))
        for v in rep["claims"]:
            if v["guarantee"].startswith(C.EXACT) and "entropy_stability" in v["decided_by"]:
                assert v["guarantee"] == C.EXACT + "; " + SEMI, (name, v["claim"])
                seen += 1
    assert seen
