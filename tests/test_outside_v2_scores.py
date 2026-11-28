"""Outside benchmark v2, phase B (benchmark/outside_v2/run_v2.py): the freeze assertions, the two pins' import
isolation, the spec translation commit, the override merge, the exact errata checks, and that V2_RESULTS.md is
rendered from the verdict files. The result belongs to the NEW pin (3792caf): the freeze is asserted at the commit
that wrote the verdict files, so a later checker change on main does not break the record (the checker is not
re-run here)."""
import importlib.util
import json
from fractions import Fraction
from pathlib import Path

import pytest

D = Path(__file__).resolve().parent.parent / "benchmark" / "outside_v2"


def _load(name):
    s = importlib.util.spec_from_file_location(name, D / f"{name}.py")
    m = importlib.util.module_from_spec(s)
    s.loader.exec_module(m)
    return m


R = _load("run_v2")
EC = _load("errata_checks")


def verdicts(pin):
    return json.loads((D / f"verdicts_{pin}.json").read_text())


def verdict_commit() -> str:
    return R.git("log", "-1", "--format=%H", "HEAD", "--", "benchmark/outside_v2/verdicts_new.json").decode().strip()


# ---------------------------------------------------------------- freeze (rule 1, 3b)

def test_freeze_holds_at_the_commit_that_wrote_the_verdicts():
    """items.jsonl = its blob at 63337e1; each readings file = its readings commit, the last commit touching it;
    physverify/ and lean/ = 3792caf; lean/ unchanged d8fb00a -> 3792caf; specs/ = the translation commit."""
    assert R.frozen_errors(at=verdict_commit(), worktree=False) == []


def test_readings_and_items_on_disk_are_frozen():
    for name, commit in R.READINGS_COMMITS.items():
        assert R.git("show", f"{commit}:benchmark/outside_v2/{name}") == (D / name).read_bytes()
        assert commit[:7] in (D / "V2_PIN.md").read_text()
    assert R.git("show", f"{R.FROZEN}:benchmark/outside_v2/items.jsonl") == (D / "items.jsonl").read_bytes()


def test_specs_at_head_equal_the_translation_commit_which_precedes_the_first_run():
    tc = R.translation_commit()
    assert tc
    assert not R.git("diff", "--name-only", tc, "HEAD", "--", "benchmark/outside_v2/specs/").strip()
    first = R.git("log", "--reverse", "--format=%H", "HEAD", "--", "benchmark/outside_v2/verdicts_new.json"
                  ).decode().split()[0]
    assert R.git("merge-base", "--is-ancestor", tc, first) == b""
    assert tc != first
    assert verdicts("new")["translation_commit"] == tc


def test_freeze_check_catches_a_changed_readings_file(tmp_path, monkeypatch):
    for name in ("items.jsonl", *R.READINGS_COMMITS):
        (tmp_path / name).write_bytes((D / name).read_bytes())
    monkeypatch.setattr(R, "HERE", tmp_path)
    (tmp_path / "readings.json").write_bytes((D / "readings.json").read_bytes() + b"\n")
    errs = R.frozen_errors(at=verdict_commit())
    assert "readings.json on disk is not byte-identical to its readings commit 4c82154" in errs


# ---------------------------------------------------------------- the two pins (rule 2)

def test_each_pin_imported_its_own_checker():
    new, old = verdicts("new"), verdicts("old")
    assert (new["pin"], new["checker_commit"]) == ("NEW", R.NEW)
    assert (old["pin"], old["checker_commit"]) == ("OLD", R.OLD)
    assert new["physverify_file"] != old["physverify_file"]
    for v in (new, old):
        assert Path(v["physverify_file"]).is_relative_to(v["checker_root"])
    assert new["checker_root"] != old["checker_root"]
    assert (new["lean_store"], old["lean_store"]) == (R.STORES["NEW"], R.STORES["OLD"])


def test_pins_score_the_same_readings():
    new, old = verdicts("new"), verdicts("old")
    assert [(r["id"], r["index"]) for r in new["a1"]["readings"]] == [(r["id"], r["index"]) for r in old["a1"]["readings"]]
    assert set(new["a1"]["groups"]) == set(old["a1"]["groups"])


def test_rerun_after_the_scorer_fix_has_the_first_runs_verdicts():
    """The first run (its own commit) had a scorer bug in the NEW pin label (no Lean store attached); its Python
    verdicts and reading verdicts are those of the committed files at both pins."""
    first = R.git("log", "-1", "--format=%H", "--fixed-strings",
                  "--grep=Bench v2 B: first checker run at both pins, as run", "HEAD").decode().strip()
    assert first
    for pin in ("new", "old"):
        was = json.loads(R.git("show", f"{first}:benchmark/outside_v2/verdicts_{pin}.json"))
        now = verdicts(pin)
        strip = lambda d: {k: {n: x["verdict"] for n, x in g.items()} for k, g in d["groups"].items()}  # noqa: E731
        assert strip(was["a1"]) == strip(now["a1"])
        assert [r["verdict"] for r in was["a1"]["readings"]] == [r["verdict"] for r in now["a1"]["readings"]]
        if pin == "new":
            assert strip(was["a2"]) == strip(now["a2"])


def test_a_kind_missing_at_a_pin_is_not_statable():
    rows = R.evaluate({"items": [{"id": "x", "readings": [{"field": "both", "narrowing": "n"}], "unformalized": []}]},
                      {"readings": [{"id": "x", "index": 0, "fields": ["alone", "with_hypotheses"],
                                     "verdict": R.NOT_STATABLE}]},
                      {"x": {"source_id": "s"}}, {"x": {"alone": "TRUE", "with_hypotheses": "TRUE"}})
    assert rows[0]["score"] == {"alone": R.NOT_STATABLE, "with_hypotheses": R.NOT_STATABLE}
    assert not rows[0]["stated"]


# ---------------------------------------------------------------- overrides (rule 4)

def test_override_is_deep_merged_and_changes_the_check():
    from physverify import schemes
    from physverify.schemes import bench
    c = R.OVERRIDE_DEMO
    base = json.loads((R.ROOT / c["spec"]).read_text())
    merged = R.deep_merge(base, c["override"])
    assert merged["claims"] == {**base["claims"], "von_neumann_cfl": ["0", "2"]}   # positive_cfl kept
    run = lambda ov: schemes.check(bench._spec(R.ROOT, c["spec"], ov, [c["claim"]]))["claims"][0]["verdict"]  # noqa: E731
    assert run({"claims": merged["claims"]}) == "REFUTED"
    assert run({}) == "VERIFIED"
    demo = verdicts("new")["override_demo"]
    assert (demo["merged"], demo["base"]) == ("REFUTED", "VERIFIED")


def test_deep_merge_replaces_lists_and_recurses_dicts():
    assert R.deep_merge({"a": {"b": 1, "c": [1]}}, {"a": {"c": [2]}}) == {"a": {"b": 1, "c": [2]}}


# ---------------------------------------------------------------- errata checks (rule 6)

def test_kt06_spike_grows_to_two():
    r = EC.kt_06()
    assert r["confirmed"] and r["max_after"] == 2 and r["slopes_zero"] and r["is_upwind"]


def test_kt08_is_exactly_433_over_400_within_cfl():
    r = EC.kt_08()
    assert r["confirmed"]
    assert r["max_after_endpoint_speeds"] == Fraction(433, 400) and float(r["max_after_endpoint_speeds"]) == 1.0825
    assert r["cfl_5_3"] <= Fraction(1, 8)
    assert r["max_after_interval_speeds"] == 1


def test_kt09_table_5_1_schemes_exceed_one():
    r = EC.kt_09()
    assert r["confirmed"]
    assert all(x["above_1"] for x in r["runs"].values())
    assert r["runs"]["second order (eta_1 = 1/2), theta = 1"]["agrees_4_digits"]
    assert r["runs"]["third order (eta_1 = 3/4, eta_2 = 1/3), theta = 1"]["agrees_4_digits"]


def test_cockburn06_tv_grows_to_17_over_8():
    r = EC.cockburn_06()
    assert r["confirmed"] and r["tv_after"] == Fraction(17, 8) and r["printed_conditions_hold"]


def test_barsukow03_flux_form_is_discontinuous():
    r = EC.barsukow_03()
    assert r["confirmed"] and r["sum_kept"] and r["flux_jump_at_b_1"] != 0


def test_errata_checks_do_not_import_the_checker():
    assert "physverify" not in (D / "errata_checks.py").read_text().split('"""')[2]


# ---------------------------------------------------------------- expected rows and the rendering (rules 5, 6)

def test_expected_rows_follow_the_rulings():
    its = R.items()
    exp, _ = R.expected_rows(its, {i: True for i in ("kurganov_tadmor_2000_central:06",)})
    assert exp["E"]["kurganov_tadmor_2000_central:06"]["alone"] == "FALSE"
    assert exp["E"]["kurganov_tadmor_2000_central:08"]["alone"] == "UNSURE"      # not confirmed here
    assert exp["E"]["chen_shu_2017_esdg:05"] == exp["P"]["chen_shu_2017_esdg:05"]
    assert exp["E"]["chen_shu_2017_esdg:03"]["alone"] == "UNSURE" == exp["D"]["chen_shu_2017_esdg:03"]["alone"]
    assert exp["P"]["chen_shu_2017_esdg:03"]["alone"] == "TRUE"
    assert exp["D"]["barsukow_uzh_notes:03"]["alone"] == "TRUE"                  # derived row counted as standing
    for i in exp["P"]:
        assert exp["E"][i]["with_hypotheses"] == exp["P"][i]["with_hypotheses"]


@pytest.fixture(scope="module")
def computed():
    return R.compute()


def test_results_md_is_the_rendering_of_the_verdict_files(computed):
    assert (D / "V2_RESULTS.md").read_text() == R.render(computed)


def test_headline_numbers_come_from_the_verdict_files(computed):
    h = computed["headline"]["NEW/P"]["clean"]
    rows = computed["rows"]["NEW/P"]
    clean = [r for r in rows if r["source"] not in R.CONTAMINATED]
    assert h["items"] == len(clean) == 91
    assert h["stated"] == len({r["id"] for r in verdicts("new")["a1"]["readings"]} & {r["id"] for r in clean})
    for f in R.FIELDS:
        assert sum(sum(x["score"][f] == s for x in clean) for s in
                   ("MATCH", "WRONG", "BUG", "SPEC_ERROR", "NOT_STATABLE", "GAP", "UNSCORED")) == 91
    assert f"| NEW/P | clean | 91 | {h['stated']}/91 |" in (D / "V2_RESULTS.md").read_text()


def test_every_wrong_is_classed(computed):
    for k, rows in computed["rows"].items():
        for r in rows:
            for f in R.FIELDS:
                if r["score"][f] in ("WRONG", "BUG"):
                    assert R.WRONG_CLASS[(r["id"], f)][0] in ("checker", "reading"), (k, r["id"], f)
