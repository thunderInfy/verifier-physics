"""Usage: uv run python papers/scheme-claims/paper_numbers.py [NAME ...]

Every number in main.tex that is not asserted by a test comes from one function here. A
\\repro{paper_numbers.py::NAME} marker in the paper names the function; with no arguments the script runs
them all and prints `NAME.key: value` lines. Nothing here is trusted code: it calls the checker and
prints what the checker returns, and the paper copies the output.
"""
from __future__ import annotations

import json
import subprocess
import sys
from fractions import Fraction
from pathlib import Path

from physverify.schemes import bench, check, checks, fixedjump, limiters, linear, load
from physverify.schemes import poly as P

ROOT = Path(__file__).resolve().parents[2]
S = ROOT / "schemes"
B = ROOT / "benchmark" / "scheme-claims"


def _with(name: str, **claims) -> dict:
    spec = load(S / f"{name}.json")
    spec["claims"] = {**spec.get("claims", {}), **claims}
    return spec


def _counterexample(r: dict) -> dict:
    w = r["witness"]["counterexample"]
    return {"lam": w["lam"], "state": ", ".join(w["state (um1, u0, up1)"]), "raised": w["increased"],
            "by": w["by"], "H before": w["H before"], "H after": w["H after"]}


def rusanov_hand_pair() -> dict:
    """The pair we found by hand: lam = 9/10, raise u0 from 1 to 101/100 (the spec's own normal form)."""
    H = P.from_expr(checks.update(load(S / "burgers-rusanov.json")))
    at = lambda *s: P.evaluate(H, dict(zip(("um1", "u0", "up1", "lam"), map(Fraction, s))))
    a, b = at(1, 1, "-9/10", "9/10"), at(1, "101/100", "-9/10", "9/10")
    return {"H(1, 1, -9/10)": str(a), "H(1, 101/100, -9/10)": str(b), "decreases": str(b < a),
            "lam*max|u|": str(Fraction(9, 10) * Fraction(101, 100))}


def rusanov_bounds() -> dict:
    """The monotonicity check on Rusanov's update at the claimed bounds 1, 1/2, 334/1000 and 1/3."""
    out = {}
    for c in ("1", "1/2", "334/1000", "1/3"):
        r = checks.monotonicity(_with("burgers-rusanov", monotone_cfl=c))
        out[f"c={c} status"] = r["status"]
        if r["status"] == checks.REFUTED:
            out.update({f"c={c} {k}": v for k, v in _counterexample(r).items()})
        else:
            cells = r["witness"]["cells"]
            certs = [p["certificate"] for cell in cells for p in cell["partials"].values()]
            out[f"c={c} cells"] = str(len(cells))
            out[f"c={c} partials certified"] = str(len(certs))
            out[f"c={c} Farkas identities"] = str(sum(isinstance(x, dict) and "farkas" in x for x in certs))
    return out


def rusanov_cell_example() -> dict:
    """One of the 32 certified cells at c = 1/3: the first whose u0-partial is not affine-trivial."""
    r = checks.monotonicity(_with("burgers-rusanov", monotone_cfl="1/3"))
    cell = r["witness"]["cells"][1]
    out = {"cell": " and ".join(cell["cell"]), "H": cell["H"], "region": ", ".join(r["witness"]["region"])}
    for k, p in cell["partials"].items():
        out[f"dH/d{k}"] = p[f"dH/d{k}"]
        out[f"{k} identity"] = p["certificate"]["farkas"]
    return out


def rusanov_claims() -> dict:
    """Claim verdicts on the two Rusanov specs (monotone_under_cfl, plus the entropy claim via Crandall-Majda)."""
    out = {}
    for name, names in (("broken-burgers-rusanov-wide-cfl", ["consistent", "conservative", "monotone_under_cfl"]),
                        ("burgers-rusanov", ["consistent", "conservative", "monotone_under_cfl"])):
        spec = load(S / f"{name}.json")
        spec["named_claims"] = names
        spec.pop("test", None)
        for v in check(spec)["claims"]:
            out[f"{name} {v['claim']}"] = f"{v['verdict']} ({v['guarantee']}; decided by {', '.join(v['decided_by'])})"
    return out


def table_size() -> dict:
    """The trusted relation table: named claims and rows (claims.py)."""
    from physverify.schemes import claims as C
    return {"named claims": str(len(C.CLAIMS)), "rows": str(sum(len(links) for _, links in C.CLAIMS.values()))}


def bench_counts() -> dict:
    """The benchmark: readings, scores, and the breakdowns in GAPS.md (about 40 s)."""
    data = json.loads((B / "claims.json").read_text())
    rows = bench.evaluate(data, bench.run(data, B))
    n = lambda f: str(sum(1 for r in rows if f(r)))
    out = {"sentences": str(len(data["claims"])), "readings": str(len(rows))}
    for s in ("match", "gap", "WRONG", "BUG", "unscored"):
        out[s] = n(lambda r, s=s: r["score"] == s)
    for e in (True, False):
        out[f"match expected {e}"] = n(lambda r, e=e: r["score"] == "match" and r["expected"] is e)
        out[f"gap expected {e}"] = n(lambda r, e=e: r["score"] == "gap" and r["expected"] is e)
    for v in ("VERIFIED", "REFUTED", "REFUTED_EMPIRICALLY"):
        out[f"match {v}"] = n(lambda r, v=v: r["score"] == "match" and r["verdict"] == v)
    for v in ("UNFORMALIZED", "UNKNOWN", "NOT_REFUTED"):
        out[f"gap {v}"] = n(lambda r, v=v: r["score"] == "gap" and r["verdict"] == v)
    out["readings per sentence"] = ", ".join(f"{i['id']}:{len(i['readings'])}" for i in data["claims"])
    return out


def certificate_examples() -> dict:
    """The witnesses quoted in the certificates section, as the checks return them."""
    out = {}
    r = checks.conservation(load(S / "advection-lax-wendroff.json"))
    out["LW conservation"] = r["status"]
    out["LW recovered flux"] = r["witness"]["recovered_flux"]
    r = checks.positivity(load(S / "broken-advection-lax-friedrichs-wide-cfl.json"))
    out["LxF wide positivity"] = f"{r['status']}: {r['detail']}"
    r = checks.positivity(load(S / "advection-lax-friedrichs.json"))
    out["LxF positivity"] = r["status"]
    out["LxF Bernstein coefficients"] = json.dumps(r["witness"]["bernstein"])
    r = limiters.tv_increase(load(S / "limiters" / "broken-advection-lw-flux-form-tvd.json"))
    w = r["witness"]
    out["LW TV increase"] = (f"{r['status']}: u = ({', '.join(w['periodic state u^n'])}) at nu = {w['nu']}, "
                             f"TV {w['TV(u^n)']} -> {w['TV(u^{n+1})']}")
    r = fixedjump.stationary_shock_rh_violation(load(S / "broken-burgers-nonconservative.json"))
    w = r["witness"]
    out["frozen jump"] = (f"{r['status']}: {w['uL']} | {w['uR']}, f(uL) = {w['f(uL)']}, f(uR) = {w['f(uR)']}, "
                          f"RH speed {w['Rankine-Hugoniot speed']}; identities {sorted(w['identities'].items())}")
    r = limiters.monotonicity_wide(load(S / "limiters" / "broken-advection-minmod-monotone.json"))
    out["minmod monotone"] = f"{r['status']}: {r['detail']}"
    r = checks.entropy_stability(load(S / "broken-burgers-roe-no-entropy-fix.json"))
    out["Roe Tadmor"] = f"{r['status']}: {r['detail']}"
    r = linear.von_neumann(load(S / "broken-advection-ftcs.json"))
    out["FTCS von Neumann"] = f"{r['status']}: 1 - |g|^2 = {r['witness']['1 - |g|^2']}; {r['detail']}"
    r = linear.von_neumann(load(S / "broken-advection-fake-second-order.json"))
    out["halved LW von Neumann"] = f"{r['status']}: {r['detail']}"
    for name in ("advection-minmod", "advection-superbee"):
        r = limiters.tvd_harten(load(S / "limiters" / f"{name}.json"))
        out[f"{name} TVD"] = f"{r['status']}: {r['detail']}"
    return out


def product_rule() -> dict:
    """The telescoping trap in its scalar form: centred quasi-linear Burgers, u_i - (lam/2) u_i (u_{i+1} - u_{i-1})."""
    spec = {"name": "centred quasi-linear Burgers", "pde": {"flux": "u^2/2"},
            "scheme": {"update": "u0 - lam/2*u0*(up1 - um1)"}}
    r = checks.conservation(spec)
    return {"status": r["status"], "recovered flux": r["witness"].get("recovered_flux", ""),
            "consistency": checks.consistency(spec)["status"]}


def gate() -> dict:
    """The merge gate's test count (runs the suite, a few minutes)."""
    p = subprocess.run([sys.executable, "-m", "pytest", "-q", "tests/", "--ignore=tests/test_lean.py"],
                       cwd=ROOT, capture_output=True, text=True)
    return {"summary": p.stdout.strip().splitlines()[-1]}


ALL = {k: f for k, f in list(globals().items())
       if callable(f) and not k.startswith("_") and getattr(f, "__module__", "") == __name__}

if __name__ == "__main__":
    for name in sys.argv[1:] or ALL:
        for k, v in ALL[name]().items():
            print(f"{name}.{k}: {v}")
