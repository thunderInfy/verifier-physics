"""Usage: python -m physverify.schemes SPEC.json [SPEC.json ...] [--json] [--lean]

--lean kernel-checks the exact verdicts in scope (lean_cert.py) in one Lean run for all specs and
upgrades their guarantee to "proven (Lean)"; without Lean, or if a proof fails, they keep the
exact-Python label. Lean never changes a verdict.

Exit code 1 if any named claim is refuted (exactly or empirically), suspicious or INCONSISTENT
(for a spec with no named claims: if any raw check is). Exit code 3 if any claim is INCONSISTENT,
which is a checker, spec or claims-table bug, not a physics result."""

import json
import sys

from . import check, claims, failed, load, render


def main(argv: list[str]) -> int:
    paths = [a for a in argv if not a.startswith("--")]
    if not paths:
        print(__doc__)
        return 2
    bad = inconsistent = False
    runs = [(spec, check(spec)) for spec in map(load, paths)]
    if "--lean" in argv:
        from .lean_cert import certify
        certify(runs)
    for spec, report in runs:
        bad |= bool(failed(report))
        inconsistent |= any(v["verdict"] == claims.INCONSISTENT for v in report["claims"])
        print(json.dumps({"scheme": spec["name"], **report}, indent=1)
              if "--json" in argv else render(spec, report))
    return 3 if inconsistent else 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
