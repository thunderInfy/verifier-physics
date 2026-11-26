"""Usage: python -m physverify.schemes SPEC.json [SPEC.json ...] [--json]

Exit code 1 if any claim is refuted (exactly or empirically) or flagged suspicious."""

import json
import sys

from . import FAILURES, check, load, render


def main(argv: list[str]) -> int:
    paths = [a for a in argv if not a.startswith("--")]
    if not paths:
        print(__doc__)
        return 2
    failed = False
    for p in paths:
        spec = load(p)
        results = check(spec)
        failed |= any(r["status"] in FAILURES for r in results)
        print(json.dumps({"scheme": spec["name"], "results": results}, indent=1)
              if "--json" in argv else render(spec, results))
    return 1 if failed else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
