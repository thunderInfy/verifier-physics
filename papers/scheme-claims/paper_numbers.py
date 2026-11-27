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


PAIR_334 = ("-834499/2500000", "834833/2500000", "-834499/2500000")   # the checker's pair at c = 334/1000


def _rusanov_du0(um1, u0, up1, lam="1") -> Fraction:
    """dH/du_i of the spec's own update at a state where raising u_i keeps the sign cell (u_i >= 0,
    u_{i+-1} <= 0, |u_{i+-1}| <= u_i). There H is quadratic in u_i, so the one-sided three-point
    difference is the exact derivative; the third difference is checked to be zero."""
    H = P.from_expr(checks.update(load(S / "burgers-rusanov.json")))
    h = Fraction(1, 1000)
    f = [P.evaluate(H, {"um1": Fraction(um1), "u0": Fraction(u0) + k * h, "up1": Fraction(up1), "lam": Fraction(lam)})
         for k in range(4)]
    assert f[3] - 3 * f[2] + 3 * f[1] - f[0] == 0, "H is not quadratic in u_i here"
    return (-3 * f[0] + 4 * f[1] - f[2]) / (2 * h)


def rusanov_sharp_family() -> dict:
    """The sharp monotone bound 1/3. On the cell u_i >= 0, u_{i+-1} <= 0, |u_{i+-1}| <= u_i both alphas
    equal u_i, so dH/du_i = 1 - 2 w_i + (w_{i-1} + w_{i+1})/2 (w = lam u); at w_i = c, w_{i+-1} = -c this
    is 1 - 3c. Evaluated exactly from the spec's update at lam = 1."""
    out = {}
    for c in ("1/3", "334/1000", "1/2", "1"):
        x = Fraction(c)
        out[f"dH/du_i at c={c}"] = str(_rusanov_du0(-x, x, -x))
        out[f"1 - 3c at c={c}"] = str(1 - 3 * x)
    um1, u0, up1 = map(Fraction, PAIR_334)
    out["checker pair at 334/1000 in the cell"] = str(u0 >= 0 >= um1 and -um1 <= u0 and up1 == um1)
    out["dH/du_i at the checker pair"] = str(_rusanov_du0(um1, u0, up1))
    out["closed form at the checker pair"] = str(1 - 2 * u0 + (um1 + up1) / 2)
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


def lean_replay() -> dict:
    """The theorems the full `--lean` pass states (README, "Lean certificates for the exact scheme
    checks"), written without running Lean: the specs in the README's order (schemes/*.json, then
    schemes/*/*.json), so theorem s<i>_... belongs to the i-th spec. About a minute."""
    from physverify import lean_backend
    from physverify.schemes import lean_cert
    paths = sorted(S.glob("*.json")) + sorted(S.glob("*/*.json"))
    pairs = [(spec, check(spec)) for spec in map(load, paths)]
    stated, real = [], lean_backend.check_batch
    lean_backend.check_batch = lambda items, **kw: stated.extend(items) or {
        n: lean_backend.LeanResult(False, set(), "not run") for n, _, _ in items}
    try:
        lean_cert.certify(pairs)
    finally:
        lean_backend.check_batch = real
    names = [n for n, _, _ in stated]
    i = paths.index(S / "broken-burgers-rusanov-wide-cfl.json")
    rus = [n for n in names if n.startswith(f"s{i}_monotonicity")]
    # the stated_identity rows (schemes/identity/) came after the last full Lean run, which covered the others
    ident = {f"s{j}_" for j, p in enumerate(paths) if p.parent.name == "identity"}
    new = [n for n in names if any(n.startswith(s) for s in ident)]
    out = {"specs": str(len(paths)), "theorems stated": str(len(names)),
           "specs in schemes/identity": str(len(ident)),
           "theorems stated for schemes/identity": str(len(new)),
           "specs outside schemes/identity": str(len(paths) - len(ident)),
           "theorems stated outside schemes/identity": str(len(names) - len(new)),
           "sqrt side theorems": str(sum(n.endswith("_sqrt") for n in names)),
           "Rusanov refutation theorems": ", ".join(rus),
           "Rusanov refutation statement": next(s for n, s, _ in stated if n == rus[0])}
    not_stated = sorted({(s["name"], r["check"], r["lean"]) for s, rep in pairs for r in rep["checks"]
                         if r.get("lean", "").startswith("not stated")})
    out["not stated"] = "; ".join(f"{a} {b}: {c}" for a, b, c in not_stated) or "none"
    return out


def _stating_lean(pairs: list) -> list:
    """Run lean_cert.certify on (spec, report) pairs without Lean: every theorem the judge states is
    taken as accepted, which is what the full --lean pass on the example specs gives (532 of 532).
    Returns the stated (name, statement, proof) items; the reports' labels are upgraded in place."""
    from physverify import lean_backend
    from physverify.schemes import lean_cert
    stated, real = [], lean_backend.check_batch
    lean_backend.check_batch = lambda items, **kw: stated.extend(items) or {
        n: lean_backend.LeanResult(True, set(), "assumed accepted, not run") for n, _, _ in items}
    try:
        lean_cert.certify(pairs)
    finally:
        lean_backend.check_batch = real
    return stated


def bench_lean_labels() -> dict:
    """How many of the benchmark's verdicts would carry a Lean label after the replay, if Lean accepts
    every theorem the judge states for them (Lean is not run here). A named-claim verdict carries one by
    the rule of `lean_cert.lean_carrier` (one deciding check with its required checks). A VERIFIED reading carries one if
    every component's named-claim verdict does; a REFUTED reading if one of its refuting components does.
    Also: the readings whose decisive named claims all have a meaning theorem in physverify/claimkinds.py."""
    from physverify.claimkinds import KINDS
    data = json.loads((B / "claims.json").read_text())
    groups: dict = {}
    for c in bench.components(data):
        if "unformalized" not in c:
            groups.setdefault(bench._key(c), (c, []))[1].append(c["claim"])
    pairs, keys = [], []
    for key, (c, names) in groups.items():
        spec = bench._spec(B, c["spec"], c.get("override", {}), list(dict.fromkeys(names)))
        pairs.append((spec, check(spec)))
        keys.append(key)
    stated = _stating_lean(pairs)
    verdicts = {k: {v["claim"]: v for v in rep["claims"]} for k, (_, rep) in zip(keys, pairs)}
    rows = bench.evaluate(data, verdicts)
    decisive = [r for r in rows if r["score"] == "match"]

    def comps(r):
        return [(c, verdicts[bench._key(c)][c["claim"]]) for c in r["_r"]["formalization"] if "unformalized" not in c]

    def deciding(r):
        cs = comps(r)
        return cs if r["verdict"] == "VERIFIED" else [(c, v) for c, v in cs if v["verdict"] == r["verdict"]]

    lean = lambda v: v["guarantee"].startswith("proven (Lean")
    label = [r for r in decisive if (all if r["verdict"] == "VERIFIED" else any)(lean(v) for _, v in deciding(r))]
    whole = [r for r in label if (all if r["verdict"] == "VERIFIED" else any)(
        lean(v) and not v["guarantee"].startswith("proven (Lean, per cell") for _, v in deciding(r))]
    meaning = [r for r in decisive if all(KINDS[c["claim"]]["meaning"] for c, _ in deciding(r))]
    return {"readings": str(len(rows)), "decisive verdicts": str(len(decisive)),
            "theorems stated": str(len(stated)),
            "decisive with a Lean label": str(len(label)),
            "of which proven (Lean), not per cell": str(len(whole)),
            "of which per cell": str(len(label) - len(whole)),
            "decisive VERIFIED with a Lean label": str(sum(r["verdict"] == "VERIFIED" for r in label)),
            "decisive REFUTED with a Lean label": str(sum(r["verdict"] == "REFUTED" for r in label)),
            "without a Lean label": "; ".join(f"{r['id']} {r['reading'][:40]}" for r in decisive if r not in label),
            "decisive whose claims all have a meaning theorem": str(len(meaning))}


def claim_kinds() -> dict:
    """The claim-kind registry (physverify/claimkinds.py): kinds, and those with a Lean meaning theorem."""
    from physverify.claimkinds import KINDS
    with_meaning = [n for n, k in KINDS.items() if k["meaning"]]
    schemes = [n for n, k in KINDS.items() if "schemes" in k["layers"]]
    return {"kinds": str(len(KINDS)), "with a meaning theorem": str(len(with_meaning)),
            "scheme kinds": str(len(schemes)),
            "scheme kinds with a meaning theorem": str(sum(n in with_meaning for n in schemes)),
            "names with a meaning theorem": ", ".join(with_meaning)}


_TEX = {"\\": "\\textbackslash{}", "_": "\\_", "^": "\\^{}", "&": "\\&", "%": "\\%", "#": "\\#", "$": "\\$",
        "{": "\\{", "}": "\\}", "~": "\\~{}", "<=": "$\\le$", ">=": "$\\ge$", "->": "$\\to$", "·": "$\\cdot$",
        "–": "--", "<": "$<$", ">": "$>$", "|": "$|$"}


def _tex(s: str) -> str:
    """Plain text from claimkinds.py as LaTeX text, in one pass so nothing is escaped twice."""
    import re
    return re.sub("|".join(map(re.escape, sorted(_TEX, key=len, reverse=True))), lambda m: _TEX[m.group()], s)


CLAIM_KINDS_TEX = Path(__file__).resolve().parent / "claim_kinds_table.tex"


def _claim_kinds_tex() -> str:
    """The rows of the glossary's claim-kind table, generated from physverify/claimkinds.py. main.tex
    inputs claim_kinds_table.tex (written by `paper_numbers.py --write-table`); tests/test_paper_numbers.py
    fails if that file drifts from this function."""
    from physverify.claimkinds import KINDS
    code = lambda s: "\\code{" + _tex(s).replace("\\_", "\\_\\allowbreak{}").replace(".", ".\\allowbreak{}") + "}"
    out = ["% generated from physverify/claimkinds.py by `paper_numbers.py --write-table`; do not edit"]
    for name, k in KINDS.items():
        params = f" ({', '.join(k['params'])})" if k["params"] else ""
        meaning = code(k["meaning"]) if k["meaning"] else "gloss only"
        out.append(f"{code(name)}{_tex(params)} & {_tex(k['gloss'])} & {_tex(k['quantifier'])} & {meaning} \\\\")
    # the closing rule is part of the file: after \input, \bottomrule would be a misplaced \noalign
    return "\n".join(out + ["\\bottomrule"]) + "\n"


def _run_dev():
    import importlib.util
    spec = importlib.util.spec_from_file_location("run_dev", ROOT / "benchmark" / "outside" / "run_dev.py")
    rd = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(rd)
    return rd


def outside_dev() -> dict:
    """The dev half of the outside benchmark (benchmark/outside/run_dev.py summary; about 5 s). The heldout
    half is never run here."""
    rd = _run_dev()
    data, items = rd.load(), rd.dev_items()
    rows = rd.evaluate(data, items, rd.run(data))
    s = rd.summary(rows)
    all_items = [json.loads(x) for x in (ROOT / "benchmark" / "outside" / "items.jsonl").read_text().splitlines()]
    out = {"items, all": str(len(all_items)), "sources, all": str(len({i["source_id"] for i in all_items})),
           "items, dev": str(s["items"]), "sources, dev": str(len({i["source_id"] for i in items.values()})),
           "items, heldout": str(sum(rd.half(i["source_id"]) == "heldout" for i in all_items)),
           "stated": str(s["stated"]), "stated alone": str(s["stated_by_field"]["alone"]),
           "stated with hypotheses": str(s["stated_by_field"]["with_hypotheses"]),
           "readings": str(s["readings"]), "decided": str(s["decided"]), "wrong": str(len(s["wrong"])),
           "fields differ": str(s["fields_differ"]), "fields differ, stated": str(len(s["fields_differ_stated"])),
           "narrowed matches": str(s["narrowed_matches"]),
           "tuned readings": str(s["tuned_readings"]), "tuned matches": str(s["tuned_matches"]),
           "instance from justification": ", ".join(
               e["id"] for e in data["items"] for r in e["readings"] if r.get("instance_from_justification"))}
    for k, v in s["verdicts"].items():
        out[f"verdict {k}"] = str(v)
    for p, (a, b) in s["stated_by_property"].items():
        out[f"property {p}"] = f"{a}/{b}"
    for f in rd.FIELDS:
        out[f"TRUE/FALSE fields {f}"] = str(sum(i[f"expected_{f}"] != "UNSURE" for i in items.values()))
        for k, v in s["scores"][f].items():
            out[f"score {f} {k}"] = str(v)
    for k, v in s["gaps_any"].items():
        out[f"gap any {k}"] = str(v)
    for k, v in s["gaps_primary"].items():
        out[f"gap primary entries {k}"] = str(v)
    for k, v in s["gaps_primary_by_field"].items():
        out[f"gap primary {k}"] = str(v)
    for k, v in s["fields_differ_pairs"].items():
        out[f"differ {k}"] = str(v)
    out["differ, stated"] = "; ".join(f"{i}: {a} {sa}, {h} {sh}" for i, a, sa, h, sh in s["fields_differ_stated"])
    return out


# the gap reasons of benchmark/outside/run_dev.py (REASONS), as the paper's gap table names and explains them
GAP_REASONS = {
    "scheme-class": ("class of schemes", "theorems about every scheme with a property (monotone implies TVD, "
                     "the Lax--Wendroff theorem); a spec is one scheme"),
    "reconstruction": ("reconstruction", "discontinuous data, ENO of higher order, DG and finite-volume schemes "
                       "with time stepping"),
    "multi-d": ("multi-D", "2D rectangles and triangles"),
    "system": ("system", "Euler, general systems with entropy variables"),
    "claim-kind-missing": ("claim kind missing", "semi-discrete order, order away from extrema, energy identities "
                           "summed over the grid, E-fluxes"),
    "not-checkable": ("not checkable", "numerical observations, comparisons, existential wording, a clause whose "
                      "reading is a judgment call"),
    "family_unspecified": ("$\\varepsilon$ family unspecified", "a gap in the source: $\\varepsilon = 10^{-6}$ is "
                           "fixed but its scaling with $\\Delta x$ is left open, and the truth depends on it"),
    "illegible": ("illegible", "the formula is illegible in the scan"),
    "variable-coefficients": ("variable coefficients", "a velocity that varies in space"),
    "not-expressible": ("not expressible", "a formula that divides by a state difference"),
    "time-stepping": ("time stepping", "Runge--Kutta or multistep methods beyond a five-point update"),
}
OUTSIDE_GAPS_TEX = Path(__file__).resolve().parent / "outside_gaps_table.tex"


def _outside_gaps_tex(numbers: dict | None = None) -> str:
    """The rows of the outside benchmark's gap table (primary entries, entries listing the reason at all), from
    the runner's counts, most primary first. main.tex inputs outside_gaps_table.tex (written by
    `paper_numbers.py --write-table`); tests/test_paper_numbers.py fails if that file drifts from this function."""
    n = numbers or outside_dev()
    count = lambda kind, r: int(n.get(f"gap {kind} {r}", "0"))
    rows = sorted(_run_dev().REASONS, key=lambda r: (-count("primary entries", r), -count("any", r), r))
    out = ["% generated from benchmark/outside/run_dev.py by `paper_numbers.py --write-table`; do not edit"]
    for r in rows:
        label, what = GAP_REASONS[r]
        out.append(f"{label} & {count('primary entries', r)} & {count('any', r)} & {what} \\\\")
    return "\n".join(out + ["\\bottomrule"]) + "\n"


def outside_naive_readings() -> dict:
    """The two naive readings of DEV_RESULTS.md that we rejected because they would have been WRONG. Neither
    is in dev_readings.json; this runs them, plus the exact arithmetic behind tecno:04's printed identity."""
    out = {}
    # fjordholm_mishra_tadmor_2012_tecno:04, read as "the scheme with flux (3.2) is entropy stable" on Burgers:
    # entropy conservative flux (uL^2 + uL uR + uR^2)/6 for eta = u^2/2 (v = u), D = 1
    spec = {"name": "tecno:04 naive", "pde": {"flux": "u^2/2"},
            "scheme": {"numerical_flux": "(uL^2 + uL*uR + uR^2)/6 - (uR - uL)/2"},
            "named_claims": ["consistent", "entropy_stable_tadmor"], "claims": {"entropy_stability": {}}}
    for v in check(spec)["claims"]:
        out[f"tecno:04 {v['claim']}"] = f"{v['verdict']} ({v['guarantee']})"
    # the printed identity (3.3) at f = 0 (so ~F = ~Q = 0), E = u^2/2, D = 1, dx = 1, (u_{i-1}, u_i, u_{i+1}) = (0, 0, 1)
    u = [Fraction(0), Fraction(0), Fraction(1)]
    flux = lambda a, b: -(b - a) / 2                                # F = ~F - D [v] / 2 with ~F = 0
    dE = u[1] * -(flux(u[1], u[2]) - flux(u[0], u[1]))              # dE(u_i)/dt = v_i du_i/dt
    jump = lambda a, b: b - a
    Q = lambda a, b, s: s * (a + b) / 2 * jump(a, b) / 2            # ^Q = ~Q + s (1/2) vbar D [v]
    rhs = -(jump(u[1], u[2]) ** 2 + jump(u[0], u[1]) ** 2) / 4
    for s, name in ((1, "printed (+)"), (-1, "corrected (-)")):
        out[f"tecno:04 dE/dt the identity requires, {name}"] = str(rhs - (Q(u[1], u[2], s) - Q(u[0], u[1], s)))
    out["tecno:04 dE/dt of the scheme"] = str(dE)
    # mfa_oslo_notes:02, read as "the central scheme is not von Neumann stable": FTCS on linear advection
    spec = load(S / "broken-advection-ftcs.json")
    spec["named_claims"] = ["von_neumann_stable_under_cfl", "stable_for_small_cfl"]
    spec.pop("test", None)
    for v in check(spec)["claims"]:
        out[f"mfa:02 {v['claim']} on [{', '.join(spec['claims']['von_neumann_cfl'])}]"] = \
            f"{v['verdict']} ({v['guarantee']}), so the negated reading is {'VERIFIED' if v['verdict'] == 'REFUTED' else '?'}"
    # the literal sentence fails: U_j = (-1)^j on an even periodic grid is a fixed point of FTCS
    U = [(-1) ** j for j in range(8)]
    nxt = [U[j] - Fraction(1, 2) * (U[(j + 1) % 8] - U[j - 1]) for j in range(8)]
    out["mfa:02 energy before, after one step of (-1)^j at nu = 1"] = f"{sum(x * x for x in U)}, {sum(x * x for x in nxt)}"
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
    if sys.argv[1:] == ["--write-table"]:
        CLAIM_KINDS_TEX.write_text(_claim_kinds_tex())
        OUTSIDE_GAPS_TEX.write_text(_outside_gaps_tex())
        sys.exit(0)
    for name in sys.argv[1:] or ALL:
        for k, v in ALL[name]().items():
            print(f"{name}.{k}: {v}")
