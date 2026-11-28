"""Usage: uv run python benchmark/outside_v2/validate_specs.py

Parse-only validation of the translated specs (rule 3b of phase B): each spec under specs/ is loaded as JSON, every
expression in it goes through the expression parser (physverify.expr.parse), its variables are checked against the
stencil names the scheme layer reads, and every named claim must exist. A reconstruction spec goes through
reconstruction.parse_reconstruction, and the params of each reading that names it through parse_claim. No check,
judge or scorer runs here."""

from __future__ import annotations

import json
import sys
from pathlib import Path

from physverify import expr, reconstruction
from physverify.schemes import claims as C

HERE = Path(__file__).resolve().parent
SPECS = HERE / "specs"
FLUX_VARS = {"uLL", "uL", "uR", "uRR", "lam"}
UPDATE_VARS = {"um2", "um1", "u0", "up1", "up2", "lam"}


def spec_files() -> list[Path]:
    return sorted(SPECS.rglob("*.json"))


def errors(path: Path, recon_params: list[dict]) -> list[str]:
    s = json.loads(path.read_text())
    where = str(path.relative_to(HERE))
    errs = []
    if s.get("kind") == "reconstruction":
        try:
            reconstruction.parse_reconstruction(s["reconstruction"])
            for p in recon_params:
                reconstruction.parse_claim({"claim": "reconstruction_order_p", **p})
        except Exception as e:  # noqa: BLE001
            errs.append(f"{where}: {type(e).__name__}: {e}")
        return errs
    params = set(s.get("params", {}))
    exprs = [("pde.flux", s["pde"]["flux"], {"u"} | params)]
    for k, allowed in (("numerical_flux", FLUX_VARS), ("update", UPDATE_VARS)):
        if k in s["scheme"]:
            exprs.append((f"scheme.{k}", s["scheme"][k], allowed | params))
    for v in s.get("params", {}).values():
        exprs.append(("params", v, set()))
    for name, text, allowed in exprs:
        try:
            extra = expr.variables(expr.parse(text)) - allowed
        except Exception as e:  # noqa: BLE001
            errs.append(f"{where}: {name}: {type(e).__name__}: {e}")
            continue
        if extra:
            errs.append(f"{where}: {name} uses {sorted(extra)}")
    errs += [f"{where}: unknown named claim {n}" for n in s.get("named_claims", []) if n not in C.CLAIMS]
    return errs


def main() -> int:
    readings = json.loads((HERE / "readings.json").read_text())
    recon = [c["params"] for e in readings["items"] for r in e["readings"] for c in r["formalization"]
             if c.get("claim") in reconstruction.CLAIMS]
    errs = [x for p in spec_files() for x in errors(p, recon if p.name == "borges-wenoz-fd.json" else [])]
    for p in spec_files():
        print(p.relative_to(HERE), "ERROR" if any(str(p.relative_to(HERE)) in x for x in errs) else "parses")
    print("\n".join(errs) or "all specs parse")
    return 1 if errs else 0


if __name__ == "__main__":
    sys.exit(main())
