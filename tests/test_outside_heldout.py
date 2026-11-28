"""The heldout half of the outside benchmark, phase B (benchmark/outside/run_heldout.py): the record of the run
at the pin (the pin commit, the verdicts file's sha256, the readings), the override merge, and that
HELDOUT_RESULTS.md is rendered from heldout_verdicts.json. The result belongs to the pin commit: once main
changes physverify/ or lean/, the checker is not re-run here."""
import copy
import importlib.util
import json
from pathlib import Path

import pytest

from physverify import reconstruction

B = Path(__file__).resolve().parent.parent / "benchmark" / "outside"
_spec = importlib.util.spec_from_file_location("run_heldout", B / "run_heldout.py")
H = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(H)


def test_heldout_record_is_intact():
    """The pin commit exists, heldout_verdicts.json names it and has the sha256 HELDOUT_PIN.md records, and
    each readings file is byte-identical to its readings commit (recorded there too)."""
    assert H.record_errors() == []
    assert H.PIN in (B / "HELDOUT_PIN.md").read_text()


def test_record_check_catches_a_changed_verdicts_file(tmp_path, monkeypatch):
    for name in ("heldout_verdicts.json", "HELDOUT_PIN.md", *H.READINGS_COMMITS):
        (tmp_path / name).write_bytes((B / name).read_bytes())
    monkeypatch.setattr(H, "HERE", tmp_path)
    monkeypatch.setattr(H, "PIN_MD", tmp_path / "HELDOUT_PIN.md")
    assert H.record_errors() == []
    (tmp_path / "heldout_verdicts.json").write_bytes((B / "heldout_verdicts.json").read_bytes() + b"\n")
    assert H.record_errors() == ["heldout_verdicts.json does not have the sha256 recorded in HELDOUT_PIN.md"]


def _checker_is_the_pins() -> bool:
    return not H.git("diff", "--name-only", H.PIN, "--", "physverify/", "lean/").strip()


def test_deep_merge_keeps_what_the_override_does_not_name():
    assert H.deep_merge({"a": {"b": 1, "c": [1]}, "d": 2}, {"a": {"c": [2], "e": 3}}) == \
        {"a": {"b": 1, "c": [2], "e": 3}, "d": 2}


def test_weno_m_override_gives_the_hand_edited_spec_and_a_different_reconstruction():
    c = H.WENO_M
    base = json.loads((H.SPECS / c["spec"]).read_text())
    hand = copy.deepcopy(base)
    hand["reconstruction"]["weights"]["kind"] = "m"
    merged = H.merged_spec(c)
    assert merged == hand and merged != base
    assert merged["reconstruction"]["weights"]["d"] == base["reconstruction"]["weights"]["d"]
    # not just the key: the checker builds a different reconstruction and decides the claim differently
    assert reconstruction.parse_reconstruction(merged["reconstruction"])["kind"] == "m"
    claim = {"claim": c["claim"], **c["params"]}
    assert reconstruction.check_claim(merged["reconstruction"], claim)["verdict"] == "VERIFIED"
    assert reconstruction.check_claim(base["reconstruction"], claim)["verdict"] == "REFUTED"
    assert H.override_demo() == {"component": c, "merged": "VERIFIED", "base": "REFUTED"}


@pytest.fixture(scope="module")
def fresh():
    return H.compute()


@pytest.fixture(scope="module")
def stored():
    return json.loads((B / "heldout_verdicts.json").read_text())


# Re-scores with the current checker and compares with the pinned verdicts, so it runs only while physverify/ and
# lean/ are the pin's; once main changes the checker it is skipped, and the record test stands for it.
@pytest.mark.skipif(not _checker_is_the_pins(), reason="physverify/ or lean/ differ from the heldout pin: the result "
                    "belongs to the pin and is checked by its sha256 (test_heldout_record_is_intact)")
def test_stored_verdicts_are_what_the_checker_gives_now(fresh):
    assert json.loads((B / "heldout_verdicts.json").read_text()) == json.loads(json.dumps(fresh, ensure_ascii=False))


def test_results_md_is_generated_from_the_verdicts_json():
    stored = json.loads((B / "heldout_verdicts.json").read_text())
    assert (B / "HELDOUT_RESULTS.md").read_text() == H.render(stored)


# this test and the next read the stored, sha256-checked verdicts (they ran on a fresh re-score while the
# checker was the pin's, which test_stored_verdicts_are_what_the_checker_gives_now equated with the stored file)
def test_every_wrong_is_classed_and_contaminated_sources_are_split_out(stored):
    for r in stored["rows"]:
        for f, c in r.get("wrong_class", {}).items():
            assert c["class"] in ("checker", "reading") and c["why"], (r["id"], f)
    t = stored["headline"]
    assert t["all"]["items"] == 77
    assert t["without both contaminated sources"]["items"] == 77 - len(stored["contaminated_items"])


def test_erratum_candidate_rests_on_an_exact_check(stored):
    e = stored["erratum_candidate"]
    assert e["as_printed"]["check_status"] == "REFUTED" and e["as_printed"]["guarantee"].startswith("exact")
    assert e["with_dv_factor"]["check_status"] == "VERIFIED"
    assert all(s["A2_score"] == "ERRATUM_CANDIDATE" for s in stored["a2_sensitivity"] if s["id"] == e["id"])
    assert "tadmor_2003_acta:17" in (B / "ERRATA_PROPOSED.md").read_text()
