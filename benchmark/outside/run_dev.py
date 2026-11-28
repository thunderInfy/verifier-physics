"""Usage: uv run python benchmark/outside/run_dev.py [--write]

Runs the formal readings of the outside benchmark's dev items (dev_readings.json) and scores them
against the frozen expected values in items.jsonl. Heldout items are never read beyond their id and
source. With --write the verdicts and scores are stored in dev_readings.json.

This file is formalization, not trusted code. Each reading is a conjunction of components, a named
claim of physverify/schemes/claims.py on a spec in specs/ (or `reconstruction_order_p` of
physverify/reconstruction.py on a reconstruction spec, with the claim's parameters in `params`), with the relations of
physverify/schemes/bench.py (`same`, `necessary`, `sufficient`). A component may also be
`negated`: the reading asserts that the claim it bears on fails. Negation is applied after the
relation: a decisive verdict flips (VERIFIED <-> REFUTED), an empirical refutation of the claim
gives only NOT_REFUTED for its negation, and NOT_REFUTED gives UNKNOWN.

A reading with `tuned_on` uses a claim kind that was chosen by its coverage of the dev items themselves
(reconstruction v3); the summary counts those readings and the matches resting only on them.

Scores per item and expected field (TRUE / FALSE / UNSURE):
    MATCH     VERIFIED on TRUE, REFUTED or REFUTED_EMPIRICALLY on FALSE
    WRONG     a decisive verdict against a TRUE/FALSE expectation
    GAP       expectation TRUE/FALSE, but no decisive verdict (or no reading)
    UNSCORED  expectation UNSURE
    BUG       INCONSISTENT verdict
A field with several readings scores WRONG if any reading is WRONG, else MATCH if any is."""

from __future__ import annotations

import hashlib
import json
import sys
from collections import Counter
from pathlib import Path

from physverify import reconstruction
from physverify.schemes import bench, check, claims as C, narrowing

HERE = Path(__file__).resolve().parent
SPECS = HERE / "specs"
FIELDS = ("alone", "with_hypotheses")
EXPECTED = {"TRUE": True, "FALSE": False, "UNSURE": None}
# the gap taxonomy of README.md, in the order that picks the primary reason; `family_unspecified` is a gap in
# the source (a parameter fixed numerically, its asymptotic scaling left open), the others are the checker's
REASONS = ("family_unspecified", "not-checkable", "illegible", "scheme-class", "multi-d", "system", "reconstruction", "time-stepping",
           "variable-coefficients", "not-expressible", "claim-kind-missing")
NEGATE = {C.VERIFIED: C.REFUTED, C.REFUTED: C.VERIFIED, C.REFUTED_EMPIRICALLY: C.NOT_REFUTED,
          C.NOT_REFUTED: C.UNKNOWN}
DECIDED = (C.VERIFIED, C.REFUTED, C.REFUTED_EMPIRICALLY)


def half(source_id: str) -> str:
    return "dev" if int(hashlib.sha256(source_id.encode()).hexdigest(), 16) % 2 == 0 else "heldout"


def dev_items() -> dict:
    """id -> item for the dev half only, in file order."""
    out = {}
    for line in (HERE / "items.jsonl").read_text().splitlines():
        item = json.loads(line)
        if half(item["source_id"]) == "dev":
            out[item["id"]] = item
    return out


def load() -> dict:
    return json.loads((HERE / "dev_readings.json").read_text())


def fields_of(x) -> list[str]:
    f = x["fields"] if "fields" in x else x["field"]
    return list(FIELDS) if f == "both" else [f] if isinstance(f, str) else list(f)


def validate(data: dict, items: dict) -> list[str]:
    errs = []
    ids = [e["id"] for e in data["items"]]
    if ids != list(items):
        errs.append("dev_readings.json must list every dev item once, in items.jsonl order")
    for e in data["items"]:
        stated, unformalized = set(), Counter()
        for r in e["readings"]:
            stated.update(fields_of(r))
            for c in r["formalization"]:
                if "unformalized" in c:
                    continue
                if c.get("claim") not in C.CLAIMS and c.get("claim") not in reconstruction.CLAIMS:
                    errs.append(f"{e['id']}: unknown named claim {c.get('claim')!r}")
                if (c.get("claim") in reconstruction.CLAIMS) != ("params" in c):
                    errs.append(f"{e['id']}: `params` goes with a reconstruction claim, and only there")
                if c.get("relation", "same") not in bench.RELATIONS:
                    errs.append(f"{e['id']}: bad relation {c.get('relation')!r}")
                if not (SPECS / c["spec"]).is_file():
                    errs.append(f"{e['id']}: no spec {c['spec']}")
            if "narrowing" not in r:
                errs.append(f"{e['id']}: reading without a `narrowing` field (null if none)")
        for u in e["unformalized"]:
            unformalized.update(fields_of(u))
            if not u["reasons"] or any(x not in REASONS for x in u["reasons"]):
                errs.append(f"{e['id']}: reasons must come from {REASONS}")
        if stated & set(unformalized) or stated | set(unformalized) != set(FIELDS) or max(
                unformalized.values(), default=1) > 1:
            errs.append(f"{e['id']}: each field needs readings or one unformalized entry, not both")
    return errs


def _key(c: dict) -> tuple[str, str]:
    return c["spec"], json.dumps(c.get("override", c.get("params", {})), sort_keys=True)


def components(data: dict):
    for e in data["items"]:
        for r in e["readings"]:
            yield from (c for c in r["formalization"] if "unformalized" not in c)


def run(data: dict, checker=check) -> dict:
    """{(spec, override): {named claim: verdict}}, one check per spec and override."""
    groups: dict = {}
    for c in components(data):
        groups.setdefault(_key(c), (c, []))[1].append(c["claim"])
    out = {}
    for key, (c, names) in groups.items():
        if c["claim"] in reconstruction.CLAIMS:
            spec = json.loads((SPECS / c["spec"]).read_text())
            out[key] = {n: reconstruction.check_claim(spec["reconstruction"], {"claim": n, **c["params"]})["verdict"]
                        for n in dict.fromkeys(names)}
            continue
        names = list(dict.fromkeys(names))
        report = checker(bench._spec(SPECS, c["spec"], c.get("override", {}), names))
        out[key] = {v["claim"]: v["verdict"] for v in report["claims"]}
    return out


def score(expected: str, verdict: str) -> str:
    if verdict == C.INCONSISTENT:
        return "BUG"
    e = EXPECTED[expected]
    if e is None:
        return "UNSCORED"
    if verdict not in DECIDED:
        return "GAP"
    return "MATCH" if (verdict == C.VERIFIED) == e else "WRONG"


def reading_verdict(r: dict, verdicts: dict) -> dict:
    comps = []
    for c in r["formalization"]:
        if "unformalized" in c:
            comps.append({"named": bench.UNFORMALIZED, "reading": bench.UNFORMALIZED})
            continue
        v = verdicts[_key(c)][c["claim"]]
        t = bench.through(c.get("relation", "same"), v)
        comps.append({"named": v, "reading": NEGATE.get(t, t) if c.get("negated") else t})
    return {"verdict": bench.conjunction([x["reading"] for x in comps]), "components": comps}


def field_score(scores: list[str]) -> str:
    for s in ("BUG", "WRONG", "MATCH"):
        if s in scores:
            return s
    return scores[0]


def evaluate(data: dict, items: dict, verdicts: dict, narrowing_rule: bool = False) -> list[dict]:
    """One row per dev item: the verdict of each reading and the score of each field. With
    narrowing_rule (off for the frozen results), a narrowed reading's verdict is first mapped to the
    sentence's by its quantifier (physverify/schemes/narrowing.py)."""
    rows = []
    for e in data["items"]:
        item = items[e["id"]]
        actual = [reading_verdict(r, verdicts) for r in e["readings"]]
        if narrowing_rule:
            actual = [{**a, "instance_verdict": a["verdict"], "verdict": narrowing.for_reading(r, a["verdict"])}
                      for r, a in zip(e["readings"], actual)]
        scores = {}
        for f in FIELDS:
            mine = [score(item[f"expected_{f}"], a["verdict"])
                    for r, a in zip(e["readings"], actual) if f in fields_of(r)]
            scores[f] = field_score(mine) if mine else ("UNSCORED" if item[f"expected_{f}"] == "UNSURE" else "GAP")
        rows.append({"id": e["id"], "property": item["property"], "actual": actual, "score": scores,
                     "stated": bool(e["readings"]), "_e": e, "_item": item})
    return rows


def primary(reasons: list[str]) -> str:
    return min(reasons, key=REASONS.index)


def summary(rows: list[dict]) -> dict:
    n = len(rows)
    by_prop = Counter(r["property"] for r in rows)
    stated_prop = Counter(r["property"] for r in rows if r["stated"])
    readings = [(r, rd, a) for r in rows for rd, a in zip(r["_e"]["readings"], r["actual"])]
    field_stated = {f: sum(any(f in fields_of(rd) for rd in r["_e"]["readings"]) for r in rows) for f in FIELDS}
    gaps_primary, gaps_any, gaps_primary_field = Counter(), Counter(), Counter()
    for r in rows:
        for u in r["_e"]["unformalized"]:
            gaps_primary[primary(u["reasons"])] += 1
            gaps_any.update(set(u["reasons"]))
            for f in fields_of(u):
                gaps_primary_field[primary(u["reasons"]), f] += 1
    differ = [r for r in rows if r["_item"]["expected_alone"] != r["_item"]["expected_with_hypotheses"]]
    return {
        "items": n,
        "stated": sum(r["stated"] for r in rows),
        "stated_by_field": field_stated,
        "stated_by_property": {p: (stated_prop[p], by_prop[p]) for p in sorted(by_prop, key=lambda p: -by_prop[p])},
        "readings": len(readings),
        "decided": sum(a["verdict"] in DECIDED for _, _, a in readings),
        "verdicts": dict(Counter(a["verdict"] for _, _, a in readings)),
        "scores": {f: dict(Counter(r["score"][f] for r in rows)) for f in FIELDS},
        "wrong": [(r["id"], f) for r in rows for f in FIELDS if r["score"][f] in ("WRONG", "BUG")],
        "tuned_readings": sum(1 for _, rd, _ in readings if rd.get("tuned_on")),
        "tuned_matches": sum(1 for r in rows for f in FIELDS if r["score"][f] == "MATCH" and all(
            rd.get("tuned_on") for rd in r["_e"]["readings"] if f in fields_of(rd))),
        "narrowed_matches": sum(1 for r in rows for f in FIELDS if r["score"][f] == "MATCH" and all(
            rd["narrowing"] for rd in r["_e"]["readings"] if f in fields_of(rd))),
        "gaps_primary": dict(gaps_primary.most_common()),
        "gaps_any": dict(gaps_any.most_common()),
        "gaps_primary_by_field": {f"{k} ({f})": v for (k, f), v in sorted(gaps_primary_field.items())},
        "fields_differ": len(differ),
        "fields_differ_pairs": {f"{a} alone, {h} with hypotheses": k for (a, h), k in Counter(
            (r["_item"]["expected_alone"], r["_item"]["expected_with_hypotheses"]) for r in differ).most_common()},
        "fields_differ_stated": [(r["id"], r["_item"]["expected_alone"], r["score"]["alone"],
                                  r["_item"]["expected_with_hypotheses"], r["score"]["with_hypotheses"])
                                 for r in differ if r["stated"]],
    }


def write(data: dict, rows: list[dict]) -> None:
    for e, row in zip(data["items"], rows):
        for rd, a in zip(e["readings"], row["actual"]):
            rd["actual"] = a
        e["score"] = row["score"]
    (HERE / "dev_readings.json").write_text(json.dumps(data, indent=1, ensure_ascii=False) + "\n")


def main(argv: list[str]) -> int:
    data, items = load(), dev_items()
    errs = validate(data, items)
    if errs:
        print("\n".join(errs))
        return 2
    rows = evaluate(data, items, run(data))
    for r in rows:
        if r["stated"]:
            for rd, a in zip(r["_e"]["readings"], r["actual"]):
                print(f"{r['id']} [{rd['field']}] {a['verdict']}: {rd['reading'][:90]}")
    print(json.dumps(summary(rows), indent=1))
    if "--write" in argv:
        write(data, rows)
    return 1 if summary(rows)["wrong"] else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
