"""Checks for discrete schemes: a numerical scheme is a theory of a discrete universe.

`check(spec)` runs the exact structural checks (`checks.py`) and the empirical convergence
studies (`convergence.py`) that the spec claims, and returns a list of plain result dicts.
"""

from __future__ import annotations

import json
from pathlib import Path

from . import checks, convergence


def load(path) -> dict:
    return json.loads(Path(path).read_text())


def check(spec: dict) -> list[dict]:
    out = [checks.consistency(spec), checks.conservation(spec), checks.positivity(spec)]
    if "test" in spec:
        out += convergence.studies(spec)
    return out


FAILURES = (checks.REFUTED, convergence.REFUTED_EMPIRICALLY, convergence.SUSPICIOUS)


def render(spec: dict, results: list[dict]) -> str:
    bad = [r["check"] for r in results if r["status"] in FAILURES]
    lines = [f"## {spec['name']}: " + (f"FAILS {', '.join(bad)}" if bad else "no claim refuted")]
    for r in results:
        g = f", {r['guarantee']}" if r["guarantee"] else ""
        lines.append(f"- [{r['status']}] ({r['check']}{g}) {r['claim']}")
        if r["detail"]:
            lines.append(f"    {r['detail']}")
        for a in r["assumptions"]:
            lines.append(f"    assumes: {a}")
        w = r["witness"]
        if "table" in w:
            lines.append(f"    study: {w['study']}")
            lines += [f"      {row}" for row in w["table"]]
        elif w:
            for k, v in w.items():
                lines.append(f"    {k}: {v}")
    return "\n".join(lines)
