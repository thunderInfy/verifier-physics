"""A verdict's guarantee keeps the caveats of the checks it rests on, on the exact-Python path and
when the Lean replay upgrades it. Fast: the accepted Lean labels are written by hand, no Lean runs."""

from pathlib import Path

from physverify.schemes import check, checks, claims as C, lean_cert as L, load

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


def test_one_replayed_refutation_carries_the_label():
    """(a) TVD REFUTED by tv_increase (replayed) and by tvd_linear (not replayed): either refutes on its
    own, so the verdict keeps the Lean label of tv_increase (this had regressed once tvd_linear joined)."""
    rep = _report("tvd_under_cfl", ["tv_increase", "tvd_linear"], {"tv_increase": L.LEAN, "tvd_linear": checks.EXACT})
    L.relabel_claims(rep)
    assert rep["claims"][0]["guarantee"] == L.LEAN
    assert rep["claims"][0]["lean_check"] == "tv_increase"
    rep = _report("tvd_under_cfl", ["tv_increase", "tvd_linear"], {"tv_increase": checks.EXACT, "tvd_linear": checks.EXACT})
    L.relabel_claims(rep)
    assert rep["claims"][0]["guarantee"] == C.EXACT and "lean_check" not in rep["claims"][0]


def test_a_premise_not_replayed_keeps_exact_python():
    """(b) VERIFIED by a SUFFICIENT row whose own check replays but one of its required checks does not."""
    g = {"tvd_harten": L.LEAN, "conservation": L.LEAN, "consistency": L.LEAN, "flux_lipschitz": L.LEAN,
         "shock_scope_tvd": checks.EXACT}
    rep = _report("correct_shock_speed", ["tvd_harten"], g)
    L.relabel_claims(rep)
    assert rep["claims"][0]["guarantee"] == C.EXACT


def test_one_fully_replayed_sufficient_row_carries_the_label():
    """(c) VERIFIED by two SUFFICIENT rows; only one of them is Lean with all its premises. The other
    row's check is Lean too but one of its premises is not, so it cannot carry the label."""
    g = {"monotonicity": L.LEAN_CELLS, "tvd_harten": L.LEAN, "conservation": L.LEAN, "consistency": L.LEAN,
         "flux_lipschitz": L.LEAN, "shock_scope_monotone": L.LEAN, "shock_scope_tvd": checks.EXACT}
    rep = _report("correct_shock_speed", ["monotonicity", "tvd_harten"], g)
    L.relabel_claims(rep)
    assert rep["claims"][0]["guarantee"] == L.LEAN_CELLS and rep["claims"][0]["lean_check"] == "monotonicity"
    g["shock_scope_tvd"] = L.LEAN                       # now both carry one: the whole-statement label wins
    rep = _report("correct_shock_speed", ["monotonicity", "tvd_harten"], g)
    L.relabel_claims(rep)
    assert rep["claims"][0]["guarantee"] == L.LEAN and rep["claims"][0]["lean_check"] == "tvd_harten"


def test_tvd_verified_by_a_replayed_harten_row_and_an_exact_linear_row():
    rep = _report("tvd_under_cfl", ["tvd_harten", "tvd_linear"], {"tvd_harten": L.LEAN, "tvd_linear": checks.EXACT})
    L.relabel_claims(rep)
    assert rep["claims"][0]["guarantee"] == L.LEAN and rep["claims"][0]["lean_check"] == "tvd_harten"


def test_a_tvd_only_theorem_does_not_label_the_maximum_principle():
    """tvd_harten replayed through Harten's lemma states TVD H, not the convex combination the
    maximum-principle row rests on: there it counts only with its cell label, else as exact Python."""
    for cells, want in ((None, C.EXACT), (L.LEAN_CELLS, L.LEAN_CELLS)):
        rep = _report("local_max_principle_under_cfl", ["tvd_harten"], {"tvd_harten": L.LEAN})
        rep["checks"][0].update(lean_claims=L.HARTEN_FORM_CLAIMS, **({"cells_guarantee": cells} if cells else {}))
        L.relabel_claims(rep)
        assert rep["claims"][0]["guarantee"] == want
        rep = _report("tvd_under_cfl", ["tvd_harten"], {"tvd_harten": L.LEAN})
        rep["checks"][0].update(lean_claims=L.HARTEN_FORM_CLAIMS)
        L.relabel_claims(rep)
        assert rep["claims"][0]["guarantee"] == L.LEAN


def test_harten_form_rows_state_tvd_and_the_cells(monkeypatch):
    """With Lean stubbed to accept everything: minmod (both certificates) gets TVD itself for its TVD
    verdict and the cell label for its maximum principle; nothing else changes."""
    from physverify import lean_backend
    stated = []
    monkeypatch.setattr(lean_backend, "check_batch", lambda items, **kw: stated.extend(items) or {
        n: lean_backend.LeanResult(True, set(), "stub") for n, _, _ in items})
    spec = load(ROOT / "schemes/limiters/advection-minmod.json")
    rep = check(spec)
    L.certify([(spec, rep)])
    names = [n for n, _, _ in stated if "_tvd_harten" in n]
    assert "s0_tvd_harten" in names and any(n[len("s0_tvd_harten_"):].isdigit() for n in names)
    v = {x["claim"]: x for x in rep["claims"]}
    assert v["tvd_under_cfl"]["guarantee"] == L.LEAN
    assert v["local_max_principle_under_cfl"]["guarantee"] == L.LEAN_CELLS


def test_every_row_decides_alone():
    """The relabel rule relies on this: in the table each row (with its `requires`) decides a verdict on
    its own, so a verdict never needs two rows jointly. judge_one with one row's check (and its premises)
    VERIFIED or REFUTED and nothing else gives that verdict, for every row of every claim."""
    for name, (_, links) in C.CLAIMS.items():
        for check, relation, _, *requires in links:
            if C.GUARANTEE.get(check) != C.EXACT:
                continue
            premises = [{"check": c, "status": checks.VERIFIED, "guarantee": checks.EXACT} for c in (requires[0] if requires else ())]
            for status, want in ((checks.VERIFIED, C.VERIFIED), (checks.REFUTED, C.REFUTED)):
                if (relation, status) in ((C.NECESSARY, checks.VERIFIED), (C.SUFFICIENT, checks.REFUTED)):
                    continue
                v = C.judge_one(name, premises + [{"check": check, "status": status, "guarantee": checks.EXACT}])
                assert v["verdict"] == want and check in v["decided_by"], (name, check, status, v["verdict"])


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
