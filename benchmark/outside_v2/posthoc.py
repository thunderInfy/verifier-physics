"""POST-HOC re-scores on bench v2 (POSTHOC_SSP.md, POSTHOC_NARROWING.md). Written after the items, their expected
values and the frozen verdicts were seen: dev evidence for the new SSP kinds and the narrowing rule, not a result.

Usage: uv run python benchmark/outside_v2/posthoc.py   (prints the numbers both notes quote, as JSON)

Nothing frozen is read for writing: the verdict files, readings and items are loaded as they are, and the
narrowing rule is applied in memory through run_v2.evaluate(narrowing_rule=True). The SSP specs are new files in
posthoc_specs/, run with the current checker.
"""

from __future__ import annotations

import importlib.util
import json
import sys
from collections import Counter
from pathlib import Path

HERE = Path(__file__).resolve().parent


def _load(name: str):
    s = importlib.util.spec_from_file_location(f"posthoc_{name}", HERE / f"{name}.py")
    m = importlib.util.module_from_spec(s)
    s.loader.exec_module(m)
    return m


R = _load("run_v2")

U, E = "universal", "existential"
# POST-HOC annotation (ours, after seeing the items): the sentence's quantifier over each parameter A1 narrowed.
# A1's readings carry no `narrowed` field; without this table the rule gives UNKNOWN for every narrowed reading.
NARROWED = {
    ("borges_costa_don_2006_wenoz:04", 0): [{"param": "critical point order n_cp = 1", "quantifier": None},
                                           {"param": "eps = 0", "quantifier": U}],
    ("kurganov_tadmor_2000_central:07", 0): [{"param": "slope (every one meeting (4.6); theta = 1, 2 taken)",
                                             "quantifier": U},
                                            {"param": "scalar flux f (f = u taken)", "quantifier": U}],
    ("guermond_popov_2016_invariant_domains:01", 0): [{"param": "hyperbolic system (scalar f = u taken)",
                                                      "quantifier": U},
                                                     {"param": "dimension, mesh (1D uniform P1 taken)", "quantifier": U}],
    ("guermond_popov_2016_invariant_domains:02", 0): [{"param": "hyperbolic system ('any', scalar f = u taken)",
                                                      "quantifier": U},
                                                     {"param": "dimension, mesh (1D uniform P1 taken)", "quantifier": U}],
    ("guermond_popov_2016_invariant_domains:04", 0): [{"param": "hyperbolic system (scalar f = u taken)",
                                                      "quantifier": U},
                                                     {"param": "dimension, mesh (1D uniform P1 taken)", "quantifier": U}],
    ("guermond_popov_2016_invariant_domains:05", 0): [{"param": "convex invariant set A and system (scalar, "
                                                      "intervals taken)", "quantifier": U},
                                                     {"param": "dimension, mesh (1D uniform P1 taken)", "quantifier": U}],
    ("chen_shu_2017_esdg:08", 0): [{"param": "system and convex entropy (Burgers, u^2/2 taken)", "quantifier": U}],
    ("chen_shu_2017_esdg:09", 0): [{"param": "admissible lambda_L, lambda_R (Rusanov taken)", "quantifier": U},
                                   {"param": "system and convex entropy (Burgers, u^2/2 taken)", "quantifier": U}],
    ("barsukow_uzh_notes:01", 0): [{"param": "advection speed c (c = 1 taken)", "quantifier": U}],
    ("barsukow_uzh_notes:06", 0): [{"param": "scalar flux f (Burgers taken)", "quantifier": U}],
    ("barsukow_uzh_notes:12", 0): [{"param": "advection speed c (c = 1 taken)", "quantifier": U}],
    ("barsukow_uzh_notes:13", 0): [{"param": "advection speed c (c = 1 taken)", "quantifier": U},
                                   {"param": "slope s_i = (d_x q)(x_i) + O(dx) (central taken)", "quantifier": U}],
}


def _rows(rule: bool, annotate: bool, pin: str = "NEW", row: str = "P") -> list[dict]:
    its = R.items()
    a1 = R.load("readings.json")
    V = json.loads((HERE / f"verdicts_{pin.lower()}.json").read_text())
    checks = R.errata_confirmed()
    exp, _ = R.expected_rows(its, {r["id"]: r["confirmed"] for r in checks.values()})
    return R.evaluate(a1, V["a1"], its, exp[row], narrowing_rule=rule, narrowed=NARROWED if annotate else None)


def narrowing() -> dict:
    out = {}
    for row in ("P", "E"):
        base = _rows(False, False, row=row)
        strict = _rows(True, False, row=row)
        ann = _rows(True, True, row=row)
        moved = []
        for b, s, a in zip(base, strict, ann):
            for f in R.FIELDS:
                if b["score"][f] != a["score"][f] or b["score"][f] != s["score"][f]:
                    inst = [x["instance_verdict"] for x in a["readings"] if f in x["fields"]]
                    sent = [x["verdict"] for x in a["readings"] if f in x["fields"]]
                    moved.append({"id": b["id"], "field": f, "expected": b["expected"][f], "before": b["score"][f],
                                  "unrecorded": s["score"][f], "annotated": a["score"][f],
                                  "instance_verdict": inst, "sentence_verdict": sent})
        tal = lambda rows: {k: v for k, v in R.tally(rows, row).items()
                            if k in ("match", "match_narrowed", "wrong", "gap", "unscored", "decided_fields")}
        out[row] = {"before": tal(base), "unrecorded": tal(strict), "annotated": tal(ann), "moved": moved,
                    "moves": dict(Counter(f"{m['before']} -> {m['annotated']}" for m in moved))}
    return out


def ssp() -> list[dict]:
    from physverify import schemes
    out = []
    for p in sorted((HERE / "posthoc_specs").glob("*.json")):
        d = json.loads(p.read_text())
        for sp in d.get("specs", [d]):
            rep = schemes.check(sp)
            out.append({"file": p.name, "name": sp["name"], "verdicts": {v["claim"]: v["verdict"] for v in rep["claims"]},
                        "details": {c["check"]: c["detail"] for c in rep["checks"] if c["check"].startswith("ssp")}})
    return out


def ssprk33_third_order() -> bool:
    """SSPRK(3,3) meets the four order conditions up to order 3 (its Butcher tableau, exactly)."""
    from fractions import Fraction as Fr
    A = [[Fr(0)] * 3, [Fr(1), Fr(0), Fr(0)], [Fr(1, 4), Fr(1, 4), Fr(0)]]
    b = [Fr(1, 6), Fr(1, 6), Fr(2, 3)]
    c = [sum(r) for r in A]
    Ac = [sum(A[i][j] * c[j] for j in range(3)) for i in range(3)]
    dot = lambda x, y: sum(p * q for p, q in zip(x, y))                # noqa: E731
    return (dot(b, [1] * 3) == 1 and dot(b, c) == Fr(1, 2) and dot(b, [x * x for x in c]) == Fr(1, 3)
            and dot(b, Ac) == Fr(1, 6))


def main() -> int:
    print(json.dumps({"narrowing": narrowing(), "ssp": ssp(), "ssprk33_third_order": ssprk33_third_order()}, indent=1, default=str))
    return 0


if __name__ == "__main__":
    sys.exit(main())
