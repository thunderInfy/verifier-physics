"""Usage: python -m physverify THEORY.json [EVIDENCE.json ...] [--json] [--alpha=0.01]

--alpha is the family-wise error budget of the statistical channel (default 0.01)."""

import json
import sys
from dataclasses import asdict

from fractions import Fraction

from . import registry
from .judge import judge, render
from .planner import plan
from .theory import Malformed, load_theory


def main(argv: list[str]) -> int:
    as_json = "--json" in argv
    alpha = next((Fraction(a.split("=", 1)[1]) for a in argv if a.startswith("--alpha=")),
                 registry.DEFAULT_ALPHA)
    args = [a for a in argv if not a.startswith("--")]
    if not args:
        print(__doc__)
        return 2
    try:
        th = load_theory(args[0])
    except Malformed as ex:
        print(f"MALFORMED: {ex}")
        return 3
    evidence = registry.load(args[1:], alpha)
    report = judge(th, evidence, plan(th, evidence))
    print(json.dumps(asdict(report), indent=2, default=str) if as_json else render(report))
    return {"REFUTED": 1, "EXCLUDED": 4}.get(report.verdict, 0)


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
