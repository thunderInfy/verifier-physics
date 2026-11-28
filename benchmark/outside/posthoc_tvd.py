"""POST-HOC readings with the TVD class kinds (tvd_monotone_class, tvd_limiter_class), not a result.

Usage: uv run python benchmark/outside/posthoc_tvd.py   (prints the table as JSON)

Written after the dev items of bench v1 (benchmark/outside, the dev half) and the items of bench v2
(benchmark/outside_v2) and their expected values were seen. It reads nothing frozen for writing: each item's
sentence and expected values come from items.jsonl, the readings below are ours, their specs are new files in
posthoc_tvd/ of each benchmark, and the score is run_dev.score on each field, with and without the narrowing
rule (physverify/schemes/narrowing.py). No item of either benchmark states a limiter class (Sweby's region),
so only tvd_monotone_class appears.
"""

from __future__ import annotations

import importlib.util
import json
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent
U = "universal"
# (bench, item id, spec, narrowing, narrowed): every reading takes the class of three-point conservative schemes
# whose flux has bounded difference quotients (a_lo >= 0 >= b_hi, lam (a_hi - b_lo) <= 1)
READINGS = [
    ("v1", "mfa_oslo_notes:14", "outside/posthoc_tvd/monotone-flux-class.json",
     "(4.45) read with sup-bounds: a constant L1 >= dF/da and L2 >= -dF/db everywhere, lam (L1 + L2) <= 1 (the "
     "sentence's pointwise |F_a(v,w)| + |F_b(u,v)| <= dx/dt with a shared v is a little weaker)",
     [{"param": "CFL condition (4.45) as uniform bounds on the flux's difference quotients", "quantifier": U}]),
    ("v1", "harten_1982_highres:02", "outside/posthoc_tvd/monotone-flux-class.json",
     "a monotone (2k+1)-point scheme narrowed to k = 1, monotone through flux bounds and a CFL relation",
     [{"param": "stencil width (k = 1 taken)", "quantifier": U},
      {"param": "monotonicity as flux bounds and lam (L1 + L2) <= 1", "quantifier": U}]),
    ("v2", "barsukow_uzh_notes:09", "outside_v2/posthoc_tvd/monotone-flux-class.json",
     "a monotone method narrowed to three points, monotone through flux bounds and a CFL relation",
     [{"param": "stencil width (three points taken)", "quantifier": U},
      {"param": "monotonicity as flux bounds and lam (L1 + L2) <= 1", "quantifier": U}]),
]


def _run_dev():
    s = importlib.util.spec_from_file_location("posthoc_tvd_run_dev", HERE / "run_dev.py")
    m = importlib.util.module_from_spec(s)
    s.loader.exec_module(m)
    return m


def _items(bench: str) -> dict:
    path = ROOT / "benchmark" / ("outside" if bench == "v1" else "outside_v2") / "items.jsonl"
    return {json.loads(x)["id"]: json.loads(x) for x in path.read_text().splitlines() if x.strip()}


def table() -> list[dict]:
    from physverify import schemes
    from physverify.schemes import narrowing
    rd = _run_dev()
    dev = {e["id"]: e for e in rd.load()["items"]}
    out = []
    for bench, iid, spec, narrow, narrowed in READINGS:
        item = _items(bench)[iid]
        if bench == "v1":
            assert iid in dev and not dev[iid]["readings"], iid          # a dev item the frozen readings left GAP
        rep = schemes.check(schemes.load(ROOT / "benchmark" / spec))
        (v,) = [c["verdict"] for c in rep["claims"]]
        reading = {"narrowing": narrow, "narrowed": narrowed,
                   "formalization": [{"claim": "tvd_monotone_class", "negated": False}]}
        sentence = narrowing.for_reading(reading, v)
        out.append({"bench": bench, "id": iid, "spec": spec, "instance verdict": v, "sentence verdict (rule)": sentence,
                    "score": {f: rd.score(item[f"expected_{f}"], v) for f in rd.FIELDS},
                    "score under the narrowing rule": {f: rd.score(item[f"expected_{f}"], sentence) for f in rd.FIELDS},
                    "expected": {f: item[f"expected_{f}"] for f in rd.FIELDS}})
    return out


def main() -> int:
    print(json.dumps(table(), indent=1))
    return 0


if __name__ == "__main__":
    sys.exit(main())
