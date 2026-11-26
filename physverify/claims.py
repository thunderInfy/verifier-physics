"""Usage: python -m physverify.claims DIR_OR_FILES... [--json]

Checks derivation claims (see `physverify/derivation.py`), prints a verdict table and
exits 1 if any verdict is wrong: VERIFIED for a claim labelled false, REFUTED for a
claim labelled true, or anything but UNKNOWN for a claim labelled ill-posed (`"true": null`,
e.g. an empty domain or one where a sqrt argument is negative). A verdict that differs from `expect` but is still sound (for example
UNKNOWN where VERIFIED was hoped for) is flagged but is not a failure.
"""

from __future__ import annotations

import json
import sys
from dataclasses import asdict
from pathlib import Path

from .derivation import REFUTED, UNKNOWN, VERIFIED, judge, load_claim
from .theory import Malformed
from .tools import eulerlagrange


def wrong(verdict: str, true: bool | None) -> bool:
    """`true` is None for an ill-posed claim (empty domain, junk values): only UNKNOWN is right."""
    if true is None:
        return verdict != UNKNOWN
    return (verdict == VERIFIED and not true) or (verdict == REFUTED and true)


def main(argv: list[str]) -> int:
    as_json = "--json" in argv
    args = [a for a in argv if not a.startswith("--")]
    if not args:
        print(__doc__)
        return 2
    paths: list[Path] = []
    for a in args:
        p = Path(a)
        paths += sorted(p.glob("*.json")) if p.is_dir() else [p]
    rows, bad = [], 0
    for p in paths:
        try:
            c = load_claim(p)
        except Malformed as ex:
            print(f"MALFORMED {p}: {ex}")
            bad += 1
            continue
        true = c.source.get("true", c.expect == VERIFIED)
        res = judge(c, eulerlagrange.propose(c))
        w = wrong(res.verdict, true)
        bad += w
        rows.append((p.stem, c.expect, res, true, w))
    if as_json:
        print(json.dumps([{**asdict(r), "file": f, "expect": e, "true": t, "wrong": w}
                          for f, e, r, t, w in rows], indent=2))
    else:
        print(f"| {'claim':38s} | {'truth':5s} | {'expect':8s} | {'verdict':8s} | {'dims':8s} | {'time':>6s} | note")
        print(f"|{'-' * 40}|{'-' * 7}|{'-' * 10}|{'-' * 10}|{'-' * 10}|{'-' * 8}|------")
        for f, e, r, t, w in rows:
            note = "WRONG" if w else ("" if r.verdict == e else "differs from expected (sound)")
            dims = "ok" if r.dims == "ok" else "mismatch"
            print(f"| {f:38s} | {'ill' if t is None else str(t).lower():5s} | {e:8s} | {r.verdict:8s} | {dims:8s} | "
                  f"{r.seconds:5.0f}s | {note}")
        n = len(rows)
        counts = {v: sum(r.verdict == v for _, _, r, _, _ in rows) for v in (VERIFIED, REFUTED, UNKNOWN)}
        print(f"\n{n} claims: {counts[VERIFIED]} VERIFIED, {counts[REFUTED]} REFUTED, "
              f"{counts[UNKNOWN]} UNKNOWN, {bad} wrong")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
