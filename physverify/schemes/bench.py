"""Usage: python -m physverify.schemes.bench DIR [--write]

Benchmark of claims as papers write them. DIR/claims.json holds sentences; each sentence has one
or more readings, and each reading is formalized as a conjunction of components. A component is
a named claim (from the trusted table in claims.py) on a spec file, or an `unformalized` note
saying why no named claim expresses it. Spec paths are relative to DIR.

This file is formalization, not trusted code. A component's `relation` says how the named claim
bears on the reading, in the vocabulary of claims.py:
    same        the named claim is the reading's conjunct (possibly through a stated `bridge` lemma)
    necessary   the conjunct implies the named claim: only a refutation transfers
    sufficient  the named claim implies the conjunct: only a verification transfers

Per reading: expected true matches VERIFIED, expected false matches REFUTED or
REFUTED_EMPIRICALLY. A decisive verdict against the expectation is WRONG. Anything else
(NOT_REFUTED, UNKNOWN, UNFORMALIZED, SUSPICIOUS) is a gap, which the reading should explain in
its `gap` field. Components may also carry `expected`, the truth of the named claim on that
spec, and a decisive component verdict against it is WRONG as well.

Exit code 1 on any WRONG verdict, 3 on any INCONSISTENT one; gaps never fail. With --write the
verdicts are stored in each reading's `actual` field."""

from __future__ import annotations

import json
import sys
from pathlib import Path

from . import check, claims as C, load

UNFORMALIZED = "UNFORMALIZED"
DECIDES = {C.VERIFIED: True, C.REFUTED: False, C.REFUTED_EMPIRICALLY: False}
RELATIONS = ("same", "necessary", "sufficient")


def through(relation: str, verdict: str) -> str:
    """What a named claim's verdict says about the reading's conjunct."""
    if verdict == C.INCONSISTENT or relation == "same":
        return verdict
    if relation == "necessary":
        return C.NOT_REFUTED if verdict == C.VERIFIED else verdict
    return verdict if verdict == C.VERIFIED else C.UNKNOWN


def conjunction(verdicts: list[str]) -> str:
    for v in (C.INCONSISTENT, C.REFUTED, C.REFUTED_EMPIRICALLY):
        if v in verdicts:
            return v
    if all(v == C.VERIFIED for v in verdicts):
        return C.VERIFIED
    if all(v == UNFORMALIZED for v in verdicts):
        return UNFORMALIZED
    if C.SUSPICIOUS in verdicts:
        return C.SUSPICIOUS
    if any(v in (C.UNKNOWN, UNFORMALIZED) for v in verdicts):
        return C.UNKNOWN
    return C.NOT_REFUTED


def score(expected, verdict: str) -> str:
    """match | WRONG | gap | BUG (INCONSISTENT) | unscored (expected is not true/false)."""
    if verdict == C.INCONSISTENT:
        return "BUG"
    if expected not in (True, False):
        return "unscored"
    if verdict not in DECIDES:
        return "gap"
    return "match" if DECIDES[verdict] == expected else "WRONG"


def _key(c: dict) -> tuple[str, str]:
    return c["spec"], json.dumps(c.get("override", {}), sort_keys=True)


def _spec(base: Path, path: str, override: dict, names: list[str]) -> dict:
    spec = load(base / path)
    for k, v in override.items():
        spec[k] = {**spec[k], **v} if isinstance(v, dict) and isinstance(spec.get(k), dict) else v
    spec["named_claims"] = names
    # skip the studies no requested claim looks at; every check that bears on one still runs
    wanted = {row[0] for n in names for row in C.CLAIMS[n][1]}
    for key in ("shock_speed", "entropy_rarefaction"):
        if key not in wanted:
            spec.get("claims", {}).pop(key, None)
    if not wanted & {"order/combined", "order/space", "order/time", "order_l1/combined", "order_linf/combined"}:
        spec.pop("test", None)
    return spec


def components(bench: dict):
    for item in bench["claims"]:
        for r in item["readings"]:
            yield from r["formalization"]


def validate(bench: dict, base: Path) -> list[str]:
    """Structural problems in the benchmark file (no checks are run)."""
    errs = []
    for item in bench["claims"]:
        for r in item["readings"]:
            where = f"{item['id']}: {r['reading'][:40]!r}"
            if r.get("expected") not in (True, False, "unsettled"):
                errs.append(f"{where}: expected must be true, false or \"unsettled\"")
            if not r["formalization"]:
                errs.append(f"{where}: empty formalization (use an `unformalized` component)")
            for c in r["formalization"]:
                if "unformalized" in c:
                    continue
                if c.get("claim") not in C.CLAIMS:
                    errs.append(f"{where}: unknown named claim {c.get('claim')!r}")
                if c.get("relation", "same") not in RELATIONS:
                    errs.append(f"{where}: relation must be one of {RELATIONS}")
                if not (base / c["spec"]).is_file():
                    errs.append(f"{where}: no spec file {c['spec']}")
    return errs


def run(bench: dict, base: Path) -> dict:
    """{(spec, override): {named claim: verdict dict}}, one check() per spec and override."""
    groups: dict = {}
    for c in components(bench):
        if "unformalized" not in c:
            groups.setdefault(_key(c), (c, []))[1].append(c["claim"])
    out = {}
    for key, (c, names) in groups.items():
        names = list(dict.fromkeys(names))
        report = check(_spec(base, c["spec"], c.get("override", {}), names))
        out[key] = {v["claim"]: v for v in report["claims"]}
    return out


def evaluate(bench: dict, verdicts: dict) -> list[dict]:
    rows = []
    for item in bench["claims"]:
        for r in item["readings"]:
            comps = []
            for c in r["formalization"]:
                if "unformalized" in c:
                    comps.append({"named": UNFORMALIZED, "reading": UNFORMALIZED, "score": "gap"})
                    continue
                v = verdicts[_key(c)][c["claim"]]["verdict"]
                comps.append({"named": v, "reading": through(c.get("relation", "same"), v),
                              "score": score(c["expected"], v) if "expected" in c else "unscored"})
            verdict = conjunction([x["reading"] for x in comps])
            rows.append({"id": item["id"], "sentence": item["sentence"], "reading": r["reading"],
                         "expected": r["expected"], "verdict": verdict, "score": score(r["expected"], verdict),
                         "components": comps, "gap": r.get("gap"), "_r": r})
    return rows


def _cell(s: str, n: int) -> str:
    s = s if len(s) <= n else s[:n - 1] + "…"
    return s.replace("|", "\\|")


def render(rows: list[dict]) -> str:
    exp = {True: "true", False: "false"}
    lines = ["| # | claim | reading | expected | actual | result |", "|---|---|---|---|---|---|"]
    last = None
    for r in rows:
        head = r["id"] != last
        last = r["id"]
        lines.append(f"| {r['id'] if head else ''} | {_cell(r['sentence'], 70) if head else ''} | "
                     f"{_cell(r['reading'], 60)} | {exp.get(r['expected'], r['expected'])} | {r['verdict']} | "
                     f"{r['score']} |")
    gaps = [r for r in rows if r["score"] == "gap"]
    count = lambda s: sum(r["score"] == s for r in rows)
    lines += ["", f"readings: {len(rows)}; match {count('match')}, gap {len(gaps)}, WRONG {count('WRONG')}, "
              f"BUG {count('BUG')}, unscored {count('unscored')}"]
    if gaps:
        lines += ["", "gaps (a decisive verdict was expected, none was given):"]
        for r in gaps:
            g = r["gap"] or {"kind": "UNEXPLAINED", "note": "no gap note in claims.json"}
            lines.append(f"- {r['id']} [{r['verdict']}] {g['kind']}: {_cell(r['reading'], 80)}")
    stale = [r for r in rows if r["score"] != "gap" and r["gap"]]
    for r in stale:
        lines.append(f"warning: {r['id']} has a gap note but scored {r['score']}: {_cell(r['reading'], 60)}")
    bad = [(r, c) for r in rows for c in r["components"] if c["score"] in ("WRONG", "BUG")]
    for r, c in bad:
        lines.append(f"!!! {r['id']}: a component's named-claim verdict {c['named']} contradicts its expected truth")
    return "\n".join(lines)


def main(argv: list[str]) -> int:
    dirs = [a for a in argv if not a.startswith("--")]
    if len(dirs) != 1:
        print(__doc__)
        return 2
    base = Path(dirs[0])
    path = base / "claims.json"
    bench = json.loads(path.read_text())
    errs = validate(bench, base)
    if errs:
        print("\n".join(errs))
        return 2
    rows = evaluate(bench, run(bench, base))
    print(render(rows))
    if "--write" in argv:
        for r in rows:
            r["_r"]["actual"] = {"verdict": r["verdict"], "result": r["score"],
                                 "components": [c["named"] for c in r["components"]]}
        path.write_text(json.dumps(bench, indent=1, ensure_ascii=False) + "\n")
    scores = [r["score"] for r in rows] + [c["score"] for r in rows for c in r["components"]]
    return 3 if "BUG" in scores else 1 if "WRONG" in scores else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
