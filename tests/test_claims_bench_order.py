"""The claims-benchmark readings decided by the exact order and von Neumann checks for linear schemes."""
import json
from pathlib import Path

from physverify.schemes import bench, claims as C

B = Path(__file__).resolve().parent.parent / "benchmark" / "scheme-claims"


def test_order_and_von_neumann_readings_are_decided_exactly():
    data = json.loads((B / "claims.json").read_text())
    data["claims"] = [c for c in data["claims"] if c["id"] in ("C01", "C04", "C19")]
    verdicts = bench.run(data, B)
    got = {(r["id"], r["reading"][:30]): (r["verdict"], r["score"]) for r in bench.evaluate(data, verdicts)}
    want = {("C01", "local truncation error O(dx^2)"): (C.VERIFIED, "match"),
            ("C04", "von Neumann (L2) stable for ev"): (C.REFUTED, "match"),
            ("C19", "converges at order 1 to smooth"): (C.VERIFIED, "match"),
            ("C19", "local truncation error O(dx)"): (C.VERIFIED, "match"),
            ("C19", "converges at order 1 in dx at "): (C.NOT_REFUTED, "gap")}
    assert {k: got[k] for k in want} == want

    upwind = lambda override: verdicts["../../schemes/advection-upwind.json", json.dumps(override, sort_keys=True)]
    assert upwind({"claims": {"von_neumann_cfl": ["0", "2"]}})["von_neumann_stable_under_cfl"]["decided_by"] == \
        ["von_neumann"]
    assert upwind({})["consistent_order_p"]["decided_by"] == ["truncation_order"]
    # combined order only: the Lax-Richtmyer row decides; separate space/time orders are outside its scope
    assert upwind({"claims": {"order": {"combined": 1}}})["converges_order_p"]["decided_by"] == ["truncation_order"]
    assert upwind({"claims": {"order": {"space": 1, "time": 1}}})["converges_order_p"]["decided_by"] == \
        ["order/space", "order/time"]
