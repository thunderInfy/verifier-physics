"""Tests for the paper-style claims benchmark (benchmark/scheme-claims, physverify/schemes/bench.py)."""
import json
from pathlib import Path

from physverify.schemes import bench, claims as C

B = Path(__file__).resolve().parent.parent / "benchmark" / "scheme-claims"


def test_bench_relations_and_conjunction():
    assert bench.through("necessary", C.VERIFIED) == C.NOT_REFUTED
    assert bench.through("necessary", C.REFUTED) == C.REFUTED
    assert bench.through("sufficient", C.REFUTED) == bench.through("sufficient", C.NOT_REFUTED) == C.UNKNOWN
    assert bench.through("sufficient", C.VERIFIED) == C.VERIFIED
    assert bench.through("sufficient", C.INCONSISTENT) == C.INCONSISTENT
    assert bench.conjunction([C.VERIFIED, C.REFUTED_EMPIRICALLY, C.REFUTED]) == C.REFUTED
    assert bench.conjunction([C.VERIFIED, C.VERIFIED]) == C.VERIFIED
    assert bench.conjunction([C.VERIFIED, C.NOT_REFUTED]) == C.NOT_REFUTED
    assert bench.conjunction([C.VERIFIED, bench.UNFORMALIZED]) == C.UNKNOWN
    assert bench.conjunction([bench.UNFORMALIZED]) == bench.UNFORMALIZED
    assert [bench.score(True, v) for v in (C.VERIFIED, C.REFUTED_EMPIRICALLY, C.NOT_REFUTED, C.INCONSISTENT)] == \
        ["match", "WRONG", "gap", "BUG"]
    assert [bench.score(False, v) for v in (C.REFUTED, C.VERIFIED, C.UNKNOWN)] == ["match", "WRONG", "gap"]


def test_bench_has_no_wrong_verdict_and_matches_what_is_recorded():
    """The benchmark's soundness bar: no decisive verdict against the expected truth, for readings
    and for components; every gap is explained; claims.json records what the verifier gives now."""
    data = json.loads((B / "claims.json").read_text())
    assert not bench.validate(data, B)
    rows = bench.evaluate(data, bench.run(data, B))
    assert 15 <= len(data["claims"]) <= 20
    assert not [r["id"] for r in rows if r["score"] in ("WRONG", "BUG")]
    assert not [(r["id"], c) for r in rows for c in r["components"] if c["score"] in ("WRONG", "BUG")]
    assert not [r["id"] for r in rows if (r["score"] == "gap") != bool(r["gap"])]
    assert [(r["verdict"], r["score"]) for r in rows] == \
        [(r["_r"]["actual"]["verdict"], r["_r"]["actual"]["result"]) for r in rows]
