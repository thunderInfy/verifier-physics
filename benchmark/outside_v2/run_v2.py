"""Usage:
    uv run python benchmark/outside_v2/run_v2.py --all            # freeze check, both pins, render
    uv run python benchmark/outside_v2/run_v2.py --checker-root R --out FILE [--a2]   # one pin (subprocess)
    uv run python benchmark/outside_v2/run_v2.py --render         # V2_RESULTS.md from the verdict files

Phase B of the v2 outside benchmark: scores reader A1's blind readings (readings.json) of the 95 held-out items with
the checker at two pins, NEW (3792caf, this tree) and OLD (b2cafbe, a throwaway `git worktree` outside the repo),
against three rows of expected values (P frozen, E errata, D printed+derived), measures A1/A2 agreement on the
22-item subset and runs A2's readings at NEW as a reading-sensitivity number.

Each pin runs in its own subprocess (`--checker-root`): `python -S` (no site processing, so the venv's editable
`.pth` for this tree is never read) with PYTHONPATH = <checker root>:<venv site-packages> and nothing else from the
environment. The subprocess asserts that `physverify.__file__` lies under the checker root and records it in its
verdict file. The parent (orchestration, scoring, rendering) never imports physverify.

Verdict files hold what the checker said at a pin: one entry per (spec, override, params) group, its Python verdicts
and guarantees, and the pin's measured Lean status of each verdict (Lean is not run: the pin's
`measure_lean.Replay` answers the checker's Lean calls from that pin's measured store, and a theorem whose text is
not in the store is `not measured`). Scores are computed from the verdict files at render time; V2_RESULTS.md is
the rendering (a test checks it). Scorer code, not trusted code; physverify/, lean/, readings and specs are never
edited here."""

from __future__ import annotations

import copy
import hashlib
import importlib.util
import json
import os
import re
import subprocess
import sys
import sysconfig
from collections import Counter
from pathlib import Path

HERE = Path(__file__).resolve().parent
BENCH = HERE.parent
ROOT = BENCH.parent
SPECS = HERE / "specs"

OLD = "b2cafbebed25a0aab659616eaafcd8db90c49426"
NEW = "3792caf54dbc66099d9855ec2d3d38b8d4242088"
LEAN_D8 = "d8fb00a4249bd708c10657aefcd9e3c8ac34dece"
FROZEN = "63337e1"
READINGS_COMMITS = {"readings.json": "4c82154397c6c8f2ce1176870b7f283c5b2cc124",
                    "readings_a2.json": "c6f480d74631f2c4de9cba57fcdd9fdabbdd84a9"}
TRANSLATION_SUBJECT = "Bench v2 B: spec translation"
STORES = {"OLD": "papers/scheme-claims/lean_measured_b2cafbe.json",
          "NEW": "papers/scheme-claims/lean_measured_d8fb00a.json"}
SCRATCH = Path("/tmp/w0084-old-pin")
FIELDS = ("alone", "with_hypotheses")
REASONS = ("family_unspecified", "not-checkable", "illegible", "scheme-class", "multi-d", "system", "reconstruction",
           "time-stepping", "variable-coefficients", "not-expressible", "claim-kind-missing")
VERIFIED, REFUTED, REFUTED_EMPIRICALLY, INCONSISTENT = "VERIFIED", "REFUTED", "REFUTED_EMPIRICALLY", "INCONSISTENT"
DECIDED = (VERIFIED, REFUTED, REFUTED_EMPIRICALLY)
SPEC_ERROR, NOT_STATABLE, UNFORMALIZED = "SPEC_ERROR", "NOT_STATABLE", "UNFORMALIZED"
CONTAMINATED = {"borges_costa_don_2006_wenoz": "the repo's benchmark/reconstruction/weno5-z-fd.json and "
                "weno5-z2-fd.json were built from this report (V2_PIN.md)"}

# A2 may not add specs: its null specs map to the files the scorer wrote word for word from spec_needed (TRANSLATION.md)
A2_SPECS = {"barsukow_uzh_notes:06": "benchmark/outside_v2/specs/a2/barsukow-modified-lf-burgers-update.json",
            "barsukow_uzh_notes:07": "benchmark/outside_v2/specs/a2/barsukow-modified-lf-burgers-flux.json"}

# every WRONG of the first run, classed by hand after it: (id, field) -> (class, one-line justification); the
# expected value of these fields is the same in rows P, E and D, and the verdict the same at both pins
_W13 = ("reading", "A1 narrowed 'for every slope with s_i = (d_x q)(x_i) + O(dx)' to the central (Fromm) slope, an "
        "instance on which the statement holds; the convention (benchmark/outside/README.md, narrowing) lets a FALSE "
        "sentence be narrowed only to an instance where it fails, and a statement over a class of slopes is "
        "scheme-class, not narrowed. The checker's VERIFIED (stable for small CFL, order 2) is right for that instance")
WRONG_CLASS: dict = {("barsukow_uzh_notes:13", "alone"): _W13, ("barsukow_uzh_notes:13", "with_hypotheses"): _W13}
# syntax-only repairs of a SPEC_ERROR spec (a key-name typo): (spec, diff)
SYNTAX_FIXES: list = []
# checker bugs found while scoring; each would get a labelled re-score section, the headline stays the first run
CHECKER_BUGS: list = []


def git(*args: str, cwd: Path = ROOT) -> bytes:
    return subprocess.run(["git", *args], cwd=cwd, check=True, capture_output=True).stdout


def rel(p: Path) -> str:
    return str(p.relative_to(ROOT))


# ---------------------------------------------------------------- freeze

def translation_commit() -> str:
    return git("log", "-1", "--format=%H", "--fixed-strings", f"--grep={TRANSLATION_SUBJECT}", "HEAD").decode().strip()


def frozen_errors(at: str = "HEAD", worktree: bool = True) -> list[str]:
    """Rule 1 and 3b: items.jsonl is its blob at the freeze; each readings file is byte-identical to its readings
    commit (the last commit touching it); physverify/ and lean/ are as at NEW (at `at`, and in the working tree);
    lean/ is unchanged from d8fb00a (whose measured run NEW uses) to NEW; the specs equal the translation commit."""
    errs = []
    v2 = "benchmark/outside_v2"
    if git("show", f"{FROZEN}:{v2}/items.jsonl") != git("show", f"{at}:{v2}/items.jsonl"):
        errs.append(f"items.jsonl at {at} differs from its blob at {FROZEN}")
    if worktree and git("show", f"{FROZEN}:{v2}/items.jsonl") != (HERE / "items.jsonl").read_bytes():
        errs.append(f"items.jsonl on disk differs from its blob at {FROZEN}")
    for name, commit in READINGS_COMMITS.items():
        path = f"{v2}/{name}"
        if git("show", f"{commit}:{path}") != git("show", f"{at}:{path}"):
            errs.append(f"{name} at {at} is not byte-identical to its readings commit {commit[:7]}")
        if worktree and git("show", f"{commit}:{path}") != (HERE / name).read_bytes():
            errs.append(f"{name} on disk is not byte-identical to its readings commit {commit[:7]}")
        if git("log", "-1", "--format=%H", at, "--", path).decode().strip() != commit:
            errs.append(f"{name}: the last commit touching it is not {commit[:7]}")
    for rev in ([at], []) if worktree else ([at],):
        if git("diff", "--name-only", NEW, *rev, "--", "physverify/", "lean/").strip():
            errs.append(f"physverify/ or lean/ differ between {NEW[:7]} and {rev[0] if rev else 'the working tree'}")
    if git("diff", "--name-only", LEAN_D8, NEW, "--", "lean/").strip():
        errs.append(f"lean/ differs between {LEAN_D8[:7]} and {NEW[:7]}")
    tc = translation_commit()
    if not tc:
        errs.append("no spec translation commit")
    elif git("diff", "--name-only", tc, at, "--", f"{v2}/specs/").strip() or (
            worktree and git("diff", "--name-only", tc, "--", f"{v2}/specs/").strip()):
        errs.append(f"specs/ differ from the translation commit {tc[:7]}")
    return errs


# ---------------------------------------------------------------- readings (no physverify)

def fields_of(x) -> list[str]:
    f = x["fields"] if "fields" in x else x["field"]
    return list(FIELDS) if f == "both" else [f] if isinstance(f, str) else list(f)


def formal(r: dict) -> list[dict]:
    return [c for c in r["formalization"] if "unformalized" not in c]


def load(name: str) -> dict:
    return json.loads((HERE / name).read_text())


def items() -> dict:
    return {json.loads(l)["id"]: json.loads(l) for l in (HERE / "items.jsonl").read_text().splitlines()}


def spec_path(c: dict, item_id: str) -> str:
    """The spec of a component, relative to the repository root: A1 writes paths relative to benchmark/, A2
    relative to the root or null (then the scorer's mapping A2_SPECS)."""
    if c.get("spec") is None:
        return A2_SPECS[item_id]
    return c["spec"] if c["spec"].startswith("benchmark/") else f"benchmark/{c['spec']}"


def key(c: dict, item_id: str) -> str:
    return json.dumps([spec_path(c, item_id), c.get("override", {}), c.get("params", {})], sort_keys=True)


def validate(data: dict, its: dict, subset: list[str] | None = None) -> list[str]:
    errs = []
    ids = [e["id"] for e in data["items"]]
    if ids != (subset if subset is not None else list(its)):
        errs.append("readings must list every item once, in order")
    for e in data["items"]:
        stated, unf = set(), Counter()
        for r in e["readings"]:
            stated.update(fields_of(r))
            for c in formal(r):
                if not (ROOT / spec_path(c, e["id"])).is_file():
                    errs.append(f"{e['id']}: no spec {spec_path(c, e['id'])}")
        for u in e["unformalized"]:
            unf.update(fields_of(u))
            if not u["reasons"] or any(x not in REASONS for x in u["reasons"]):
                errs.append(f"{e['id']}: reasons must come from the taxonomy")
        if stated & set(unf) or stated | set(unf) != set(FIELDS) or max(unf.values(), default=1) > 1:
            errs.append(f"{e['id']}: each field needs readings or one unformalized entry, not both")
    return errs


def deep_merge(base, override):
    """override into base, recursively for dicts; any other value (lists included) replaces."""
    if isinstance(base, dict) and isinstance(override, dict):
        out = copy.deepcopy(base)
        for k, v in override.items():
            out[k] = deep_merge(base[k], v) if k in base else copy.deepcopy(v)
        return out
    return copy.deepcopy(override)


# ---------------------------------------------------------------- one pin (the subprocess)

def pin_run(checker_root: Path, out: Path, with_a2: bool) -> dict:
    """Runs inside the isolated subprocess: imports the pin's physverify, checks where it came from, runs every
    group of A1 (and A2) and writes the verdict file."""
    import physverify
    mod = Path(physverify.__file__).resolve()
    root = checker_root.resolve()
    assert root in mod.parents, f"physverify imported from {mod}, not under --checker-root {root}"
    from physverify import reconstruction, schemes
    from physverify.schemes import bench, claims as C, lean_cert
    head = git("rev-parse", "HEAD", cwd=root).decode().strip()
    # NEW is this tree: its HEAD is the branch, whose physverify/ and lean/ equal NEW's (frozen_errors, run first)
    if root == ROOT.resolve() and not git("diff", "--name-only", NEW, "--", "physverify/", "lean/", cwd=root).strip():
        label, commit = "NEW", NEW
    else:
        label, commit = ("OLD" if head == OLD else head[:7]), head
    ms = importlib.util.spec_from_file_location("measure_lean_pin", root / "papers/scheme-claims/measure_lean.py")
    ML = importlib.util.module_from_spec(ms)
    ms.loader.exec_module(ML)
    store_file = STORES.get(label)
    store = json.loads((ROOT / store_file).read_text()) if store_file else {"theorems": {}}
    negate = {C.VERIFIED: C.REFUTED, C.REFUTED: C.VERIFIED, C.REFUTED_EMPIRICALLY: C.NOT_REFUTED,
              C.NOT_REFUTED: C.UNKNOWN}

    def lean_status(v: dict, checks: dict, used: list) -> tuple[str, str]:
        """The pin's measured status of a verdict: kernel-checked if the replayed run gives it a Lean label;
        otherwise from the theorems of its deciding checks (named s0_<check>_<k> by lean_cert), matched by the
        sha of their text against the pin's store."""
        if v["guarantee"].startswith("proven (Lean"):
            return "kernel-checked", v["guarantee"]
        msgs, shas = [], []
        for d in v.get("decided_by", []):
            m = checks.get(d, {}).get("lean")
            if m:
                msgs.append(f"{d}: {m}")
            shas += [h for n, h in used if n.startswith(f"s0_{d}_")]
        det = "; ".join(msgs) or "no Lean statement for the deciding checks"
        if not shas:
            return "Python-only", det
        if any(h not in store["theorems"] for h in shas):
            return "not measured", det
        if all(store["theorems"][h]["status"] == "accepted" for h in shas):
            return "Python-only (its checks' theorems accepted, the verdict's label needs more)", det
        return "measured, not accepted", det

    def run_group(c: dict, item_id: str, names: list[str]) -> dict:
        path = spec_path(c, item_id)
        unknown = [n for n in names if n not in C.CLAIMS and n not in reconstruction.CLAIMS]
        res = {n: {"verdict": NOT_STATABLE, "guarantee": "", "detail": f"claim kind {n} does not exist at this pin",
                   "lean": "n/a", "lean_detail": ""} for n in unknown}
        names = [n for n in names if n not in unknown]
        if not names:
            return res
        try:
            merged = deep_merge(json.loads((ROOT / path).read_text()), c.get("override", {}))
            if names[0] in reconstruction.CLAIMS:
                for n in names:
                    v = reconstruction.check_claim(merged["reconstruction"], {"claim": n, **c["params"]})
                    res[n] = {"verdict": v["verdict"], "guarantee": "exact (reconstruction_order_p)",
                              "detail": v.get("detail", ""), "lean": "Python-only",
                              "lean_detail": "reconstruction claims have no Lean statement"}
                return res
            # bench._spec merges one level deep; handing it the deep-merged top-level values gives the merged spec
            spec = bench._spec(ROOT, path, {t: merged[t] for t in c.get("override", {})}, names)
            report = schemes.check(copy.deepcopy(spec))
            py = copy.deepcopy(report)
            with ML.Replay(store) as rp:
                lean_cert.certify([(spec, report)])
            used = list(rp.used)
            checks = {r["check"]: r for r in report["checks"]}
            for v, vl in zip(py["claims"], report["claims"]):
                st, det = lean_status(vl, checks, used)
                res[v["claim"]] = {"verdict": v["verdict"], "guarantee": v.get("guarantee", ""),
                                   "detail": v.get("detail", ""), "lean": st, "lean_detail": det,
                                   "lean_guarantee": vl.get("guarantee", "")}
        except Exception as ex:  # noqa: BLE001: the spec, not the scorer, is at fault; recorded, not repaired
            for n in names:
                res[n] = {"verdict": SPEC_ERROR, "guarantee": "", "detail": f"{type(ex).__name__}: {ex}",
                          "lean": "n/a", "lean_detail": ""}
        return res

    def run_readings(data: dict) -> dict:
        groups: dict = {}
        for e in data["items"]:
            for r in e["readings"]:
                for c in formal(r):
                    groups.setdefault(key(c, e["id"]), (c, e["id"], []))[2].append(c["claim"])
        V = {k: run_group(c, i, list(dict.fromkeys(ns))) for k, (c, i, ns) in groups.items()}
        rows = []
        for e in data["items"]:
            for idx, r in enumerate(e["readings"]):
                comps = []
                for c in r["formalization"]:
                    if "unformalized" in c:
                        comps.append({"named": UNFORMALIZED, "reading": UNFORMALIZED})
                        continue
                    v = V[key(c, e["id"])][c["claim"]]["verdict"]
                    if v in (SPEC_ERROR, NOT_STATABLE):
                        comps.append({"key": key(c, e["id"]), "claim": c["claim"], "named": v, "reading": v})
                        continue
                    t = bench.through(c.get("relation", "same"), v)
                    comps.append({"key": key(c, e["id"]), "claim": c["claim"], "named": v,
                                  "reading": negate.get(t, t) if c.get("negated") else t})
                reads = [x["reading"] for x in comps]
                verdict = (SPEC_ERROR if SPEC_ERROR in reads else NOT_STATABLE if NOT_STATABLE in reads
                           else bench.conjunction(reads))
                rows.append({"id": e["id"], "index": idx, "fields": fields_of(r), "verdict": verdict,
                             "components": comps})
        return {"groups": V, "readings": rows}

    out_d = {"about": "Checker output for the v2 readings at one pin (run_v2.py --checker-root); scores are computed "
                      "from this file by run_v2.py --render.",
             "pin": label, "checker_commit": commit, "checker_root_head": head, "checker_root": str(root),
             "physverify_file": str(mod),
             "lean_store": store_file, "readings_commits": READINGS_COMMITS, "translation_commit": translation_commit(),
             "a1": run_readings(load("readings.json"))}
    if with_a2:
        out_d["a2"] = run_readings(load("readings_a2.json"))
        out_d["override_demo"] = override_demo(run_group)
    out.write_text(json.dumps(out_d, indent=1, ensure_ascii=False) + "\n")
    return out_d


# A2's barsukow_uzh_notes:01 override, which bench._spec's one-level merge would apply by replacing the whole
# `claims` block (dropping positive_cfl); the scorer deep-merges it
OVERRIDE_DEMO = {"spec": "benchmark/outside/specs/upwind-advection.json",
                 "override": {"claims": {"von_neumann_cfl": ["0", "2"]}}, "claim": "von_neumann_stable_under_cfl"}


def override_demo(run_group) -> dict:
    base = {k: v for k, v in OVERRIDE_DEMO.items() if k != "override"}
    b = json.loads((ROOT / OVERRIDE_DEMO["spec"]).read_text())
    return {"component": OVERRIDE_DEMO,
            "merged_claims": deep_merge(b, OVERRIDE_DEMO["override"])["claims"], "base_claims": b["claims"],
            "merged": run_group(OVERRIDE_DEMO, "", [OVERRIDE_DEMO["claim"]])[OVERRIDE_DEMO["claim"]]["verdict"],
            "base": run_group(base, "", [base["claim"]])[base["claim"]]["verdict"]}


# ---------------------------------------------------------------- orchestration (parent; no physverify import)

def clean_env(checker_root: Path) -> dict:
    site = sysconfig.get_paths()["purelib"]
    return {"PATH": os.environ.get("PATH", "/usr/bin:/bin"), "HOME": os.environ.get("HOME", "/tmp"),
            "PYTHONPATH": f"{checker_root}{os.pathsep}{site}", "PYTHONNOUSERSITE": "1", "LC_ALL": "C.UTF-8"}


def run_pin(checker_root: Path, out: Path, with_a2: bool) -> dict:
    cmd = [sys.executable, "-S", str(Path(__file__).resolve()), "--checker-root", str(checker_root), "--out", str(out)]
    subprocess.run(cmd + (["--a2"] if with_a2 else []), env=clean_env(checker_root), cwd="/tmp", check=True)
    v = json.loads(out.read_text())
    assert Path(checker_root).resolve() in Path(v["physverify_file"]).parents, v["physverify_file"]
    return v


def run_all() -> None:
    errs = frozen_errors()
    if errs:
        raise SystemExit("freeze broken:\n" + "\n".join(errs))
    its = items()
    errs = validate(load("readings.json"), its) + validate(load("readings_a2.json"), its, subset())
    if errs:
        raise SystemExit("\n".join(errs))
    run_pin(ROOT, HERE / "verdicts_new.json", True)
    if SCRATCH.exists():
        raise SystemExit(f"{SCRATCH} exists; remove it first")
    git("worktree", "add", "--detach", str(SCRATCH), OLD)
    try:
        run_pin(SCRATCH, HERE / "verdicts_old.json", False)
    finally:
        git("worktree", "remove", "--force", str(SCRATCH))
    (HERE / "V2_RESULTS.md").write_text(render())


def subset() -> list[str]:
    return (HERE / "subset_a2.txt").read_text().split()


PROBE = ("import json, sys, physverify; from physverify.schemes import claims as C; "
         "print(json.dumps({'file': physverify.__file__, 'ssp_preserves': 'ssp_preserves' in C.CLAIMS, "
         "'sys_path': sys.path[:3]}))")


def probe() -> list[dict]:
    """Import-only check of the isolation (no checker run): each pin's subprocess, and for contrast a plain venv
    interpreter with the OLD tree appended to sys.path, which the editable install would shadow."""
    out = []
    git("worktree", "add", "--detach", str(SCRATCH), OLD)
    try:
        for r in (ROOT, SCRATCH):
            p = subprocess.run([sys.executable, "-S", "-c", PROBE], env=clean_env(r), cwd="/tmp", check=True,
                               capture_output=True, text=True)
            out.append({"root": str(r), **json.loads(p.stdout)})
        p = subprocess.run([sys.executable, "-c", f"import sys; sys.path.append({str(SCRATCH)!r}); " + PROBE],
                           cwd="/tmp", check=True, capture_output=True, text=True)
        out.append({"root": f"{SCRATCH} appended to sys.path, venv site processing on (the trap)", **json.loads(p.stdout)})
    finally:
        git("worktree", "remove", "--force", str(SCRATCH))
    return out


def main(argv: list[str]) -> int:
    if "--probe" in argv:
        print(json.dumps(probe(), indent=1))
        return 0
    if "--checker-root" in argv:
        pin_run(Path(argv[argv.index("--checker-root") + 1]), Path(argv[argv.index("--out") + 1]), "--a2" in argv)
        return 0
    if "--all" in argv:
        run_all()
    elif "--render" in argv:
        (HERE / "V2_RESULTS.md").write_text(render())
    else:
        print(__doc__)
    return 0


# ---------------------------------------------------------------- expected values (rule 6)

def errata_table() -> dict:
    """id -> (before, after) of ERRATA.md's post-freeze expected_alone rows."""
    out = {}
    for line in (HERE / "ERRATA.md").read_text().splitlines():
        m = re.match(r"\| `([^`]+)` \| expected_alone \| (\w+) \| (\w+) \|", line)
        if m:
            out[m[1]] = (m[2], m[3])
    return out


def standing() -> list[dict]:
    return [json.loads(l) for l in (HERE / "standing_conditions.jsonl").read_text().splitlines()]


def errata_confirmed() -> dict:
    s = importlib.util.spec_from_file_location("errata_checks", HERE / "errata_checks.py")
    m = importlib.util.module_from_spec(s)
    s.loader.exec_module(m)
    return m.results()


STRICT = "chen_shu_2017_esdg:03"       # ruled strict by the team (2026-11-28): (E) and (D) only, flagged


def expected_rows(its: dict, confirmed: dict) -> tuple[dict, list[dict]]:
    """{P, E, D: {id: {field: TRUE|FALSE|UNSURE}}} and the log of every change from P."""
    P = {i: {f: it[f"expected_{f}"] for f in FIELDS} for i, it in its.items()}
    E, D, log = copy.deepcopy(P), copy.deepcopy(P), []
    null_rows: dict = {}
    for r in standing():
        if r["location"] is None:
            null_rows.setdefault(r["id"], []).append(r)
    for i, (before, after) in errata_table().items():
        assert P[i]["alone"] == before, i
        e = after
        why = "ERRATA.md re-derivation"
        if after == "FALSE" and not confirmed.get(i, False):
            e, why = "UNSURE", "re-derived FALSE, not confirmed by errata_checks.py"
        elif after == "FALSE":
            why = "re-derived FALSE, confirmed exactly by errata_checks.py"
        E[i]["alone"] = e
        d_only = all(r["derived"] for r in null_rows.get(i, [])) and null_rows.get(i)
        D[i]["alone"] = before if d_only else e
        log.append({"id": i, "P": before, "E": e, "D": D[i]["alone"], "why": why,
                    "D_why": "every null-location row is derived:true, counted as standing in (D)" if d_only else ""})
    E[STRICT]["alone"] = D[STRICT]["alone"] = "UNSURE"
    log.append({"id": STRICT, "P": P[STRICT]["alone"], "E": "UNSURE", "D": "UNSURE",
                "why": "ruled strict by the team: its semi-discrete condition is not counted as printed; ERRATA.md has "
                       "no re-derived value for it, so it is UNSURE (a doubt)", "D_why": ""})
    return {"P": P, "E": E, "D": D}, log


# ---------------------------------------------------------------- scoring (from the verdict files)

def score(expected: str, verdict: str) -> str:
    if verdict == INCONSISTENT:
        return "BUG"
    if verdict in (SPEC_ERROR, NOT_STATABLE):
        return verdict
    if expected == "UNSURE":
        return "UNSCORED"
    if verdict not in DECIDED:
        return "GAP"
    return "MATCH" if (verdict == VERIFIED) == (expected == "TRUE") else "WRONG"


ORDER = ("BUG", "WRONG", "MATCH", SPEC_ERROR, NOT_STATABLE)


def field_score(scores: list[str]) -> str:
    for s in ORDER:
        if s in scores:
            return s
    return scores[0]


def evaluate(data: dict, run: dict, its: dict, exp: dict) -> list[dict]:
    by = {}
    for r in run["readings"]:
        by.setdefault(r["id"], []).append(r)
    rows = []
    for e in data["items"]:
        reads = by.get(e["id"], [])
        sc = {}
        for f in FIELDS:
            mine = [score(exp[e["id"]][f], r["verdict"]) for r in reads if f in r["fields"]]
            sc[f] = field_score(mine) if mine else ("UNSCORED" if exp[e["id"]][f] == "UNSURE" else "GAP")
        rows.append({"id": e["id"], "source": its[e["id"]]["source_id"], "expected": exp[e["id"]], "score": sc,
                     "stated": any(r["verdict"] != NOT_STATABLE for r in reads),
                     "stated_fields": {f: any(f in r["fields"] and r["verdict"] != NOT_STATABLE for r in reads)
                                       for f in FIELDS},
                     "narrowed": all(x.get("narrowing") for x in e["readings"]) if e["readings"] else False,
                     "readings": reads})
    return rows


def tally(rows: list[dict], row: str = "P") -> dict:
    reads = [a for r in rows for a in r["readings"]]
    sc = {f: Counter(r["score"][f] for r in rows) for f in FIELDS}
    wrong = [(r["id"], f) for r in rows for f in FIELDS if r["score"][f] in ("WRONG", "BUG")]
    cls = Counter(WRONG_CLASS.get((i, f), ("unclassed",))[0] for i, f in wrong)
    return {
        "items": len(rows),
        "stated": sum(r["stated"] for r in rows),
        "stated_by_field": {f: sum(r["stated_fields"][f] for r in rows) for f in FIELDS},
        "readings": len(reads),
        "decided_readings": sum(a["verdict"] in DECIDED for a in reads),
        "decided_fields": sum(sc[f]["MATCH"] + sc[f]["WRONG"] for f in FIELDS),
        "match": sum(sc[f]["MATCH"] for f in FIELDS),
        "match_narrowed": sum(1 for r in rows for f in FIELDS if r["score"][f] == "MATCH" and r["narrowed"]),
        "wrong": len(wrong),
        "wrong_checker": cls["checker"],
        "wrong_reading": cls["reading"],
        "spec_error": sum(sc[f][SPEC_ERROR] for f in FIELDS),
        "not_statable": sum(sc[f][NOT_STATABLE] for f in FIELDS),
        "gap": sum(sc[f]["GAP"] for f in FIELDS),
        "unscored": sum(sc[f]["UNSCORED"] for f in FIELDS),
    }


def compute() -> dict:
    its = items()
    a1, a2 = load("readings.json"), load("readings_a2.json")
    V = {"NEW": json.loads((HERE / "verdicts_new.json").read_text()),
         "OLD": json.loads((HERE / "verdicts_old.json").read_text())}
    checks = errata_confirmed()
    exp, exp_log = expected_rows(its, {r["id"]: r["confirmed"] for r in checks.values()})
    out = {"pins": {p: {k: v[k] for k in ("pin", "checker_commit", "checker_root", "physverify_file", "lean_store",
                                          "translation_commit")} for p, v in V.items()},
           "expected_log": exp_log, "errata_checks": checks, "rows": {}, "headline": {}}
    for p, v in V.items():
        for rw in ("P", "E", "D"):
            rows = evaluate(a1, v["a1"], its, exp[rw])
            out["rows"][f"{p}/{rw}"] = rows
            clean = [r for r in rows if r["source"] not in CONTAMINATED]
            cont = [r for r in rows if r["source"] in CONTAMINATED]
            out["headline"][f"{p}/{rw}"] = {"clean": tally(clean, rw), "contaminated": tally(cont, rw),
                                            "all": tally(rows, rw)}
    topics = source_topics()
    rows = out["rows"]["NEW/P"]
    out["by_topic"] = [{"source": s, "topic": topics[s], **tally([r for r in rows if r["source"] == s])}
                       for s in dict.fromkeys(r["source"] for r in rows)]
    out["pin_diff"] = pin_diff(V["OLD"]["a1"], V["NEW"]["a1"])
    out["lean"] = lean_table(V)
    out["agreement"] = agreement(a1, a2)
    a2rows = [r for r in evaluate(a2, V["NEW"]["a2"], its, exp["P"]) if r["readings"]]
    by1 = {r["id"]: r for r in rows}
    out["a2_sensitivity"] = [{"id": r["id"], "field": f, "A2_verdict": [a["verdict"] for a in r["readings"]
                                                                        if f in a["fields"]][0],
                              "A2_score": r["score"][f], "A1_score": by1[r["id"]]["score"][f]}
                             for r in a2rows for f in FIELDS if any(f in a["fields"] for a in r["readings"])]
    out["override_demo"] = V["NEW"]["override_demo"]
    out["ssp"] = ssp_table(a1, a2, its)
    per = Counter(it["source_id"] for it in its.values())
    drafts = a1.get("specs", {})
    files = sorted(SPECS.rglob("*.json"))
    out["stats"] = {"capped": sum(k == 15 for k in per.values()),
                    "capped_ids": ", ".join(f"`{s}`" for s, k in per.items() if k == 15),
                    "nspecs": len(files),
                    "verbatim": sum(p.name in drafts and json.loads(p.read_text()) == drafts[p.name]
                                    for p in files if p.parent == SPECS)}
    return out


TEXTBOOK = [
    "upwind, Lax-Wendroff, Beam-Warming and the Fromm slope method for linear advection: von Neumann stability on a "
    "CFL range and consistency order 1 or 2 (barsukow_uzh_notes:01, :12, :13); the checker's linear checks and the "
    "repo's test schemes were built on the same textbook results",
    "the modified Lax-Friedrichs method is conservative and monotone under a CFL bound (barsukow_uzh_notes:06, :07)",
    "the Godunov and local Lax-Friedrichs (Rusanov) fluxes are entropy stable in Tadmor's sense (chen_shu_2017_esdg:08, "
    ":09); the checker's entropy check and the scheme-claims benchmark rest on the same framework",
    "the upwind (first-order monotone) scheme keeps every interval containing the data, a non-negative combination "
    "(guermond_popov_2016_invariant_domains:01, :02, :05 on the reduction A1 chose)",
    "minmod-limited second-order fluxes are TVD under a CFL bound, through Harten's lemma "
    "(kurganov_tadmor_2000_central:07); the checker's tvd_harten check is that lemma",
    "SSP Runge-Kutta methods as convex combinations of forward-Euler steps (cockburn_shu_2001_rkdg_review:01, A2's "
    "reading); the class theorem behind ssp_preserves",
    "WENO weights and the order loss at critical points (borges_costa_don_2006_wenoz, contaminated in any case)",
]
CONFOUNDS = [
    "v2's topic list was chosen by the team after it saw the v1 gaps (time stepping first), so it is not "
    "independent of the checker's development. Coverage per topic is in the table above.",
    "The SSP class theorem and the ssp_preserves kind were built after v1's gaps were seen, before v2 was opened; "
    "v2 was frozen (63337e1) before both (82218f5, 5b1b8f4).",
    "The readers reused specs written with access to the checker: A2 used the dev spec "
    "benchmark/outside/specs/upwind-advection.json; A1 wrote new drafts, but opened 3 v1 dev spec files for "
    "syntax and listed their names in outside_v2/ (blindness slip).",
    "A2 ran `git log -3` after writing its readings and saw an aggregate tally of the post-freeze re-derivations "
    "(no ids) (blindness slip).",
    "The scorer translated A1's drafts and A2's spec_needed into specs (TRANSLATION.md). It was blind to verdicts "
    "at the time, but not a blind reader, and it had read ERRATA.md before translating; {verbatim} of the {nspecs} specs "
    "are verbatim copies of A1's drafts.",
    "The collector's 15-item cap truncated some sources ({capped} sources have exactly 15 items: {capped_ids}).",
    "The standing-condition rule, and the (E) and (D) rows built on it, were written after the freeze.",
    "Narrowed readings: every one of A1's readings narrows its sentence to an instance (linear advection, Burgers, "
    "one slope, one CFL range). A VERIFIED on an instance verifies the instance, not the general sentence; by the "
    "dev convention it scores MATCH, and those matches are counted separately (column 'MATCH narrowed').",
]


def _table(head: list[str], rows: list[list]) -> list[str]:
    return ["| " + " | ".join(head) + " |", "|" + "---|" * len(head)] + \
           ["| " + " | ".join(str(x) for x in r) + " |" for r in rows]


def render(v: dict | None = None) -> str:
    """V2_RESULTS.md from verdicts_new.json and verdicts_old.json (through compute()): every number below is read
    from them, from items.jsonl and ERRATA.md, or from errata_checks.py."""
    v = v or compute()
    H = v["headline"]
    n = H["NEW/P"]
    c, t = n["clean"], n["contaminated"]
    L = ["# Outside benchmark v2: results (phase B)", "",
         "Generated by `run_v2.py --all` (or `--render`) from `verdicts_new.json` and `verdicts_old.json`; do not edit "
         "by hand (`tests/test_outside_v2_scores.py` checks that this file is their rendering). Only reader A1's "
         "readings count for the headline. Scores per item and expected field: MATCH is VERIFIED on TRUE or REFUTED "
         "on FALSE, WRONG a decided verdict against TRUE/FALSE, GAP no decided verdict (or no reading) on TRUE/FALSE, "
         "UNSCORED an UNSURE expectation, SPEC_ERROR a spec the checker could not run, NOT_STATABLE a claim kind that "
         "does not exist at the pin.", "",
         "## Headline", "",
         f"At NEW (`3792caf`), with the frozen expected values (row P), A1 stated {c['stated']} of the {c['items']} "
         f"clean items and {t['stated']} of the {t['items']} contaminated WENO-Z items "
         f"({n['all']['stated']}/{n['all']['items']} in all). The checker decided {c['decided_fields']} clean fields: "
         f"{c['match']} MATCH, {c['wrong']} WRONG ({c['wrong_checker']} checker, {c['wrong_reading']} reading). "
         f"{c['spec_error']} fields are SPEC_ERROR.", "",
         "Coverage (stated/N) does not depend on the expected values; they only move MATCH, WRONG, GAP and UNSCORED.",
         "Fields count twice per item (alone, with hypotheses), so MATCH + WRONG + SPEC_ERROR + NOT_STATABLE + GAP + "
         "UNSCORED = 2 x items.", ""]
    head = ["pin / row", "set", "items", "stated", "alone", "with hyp.", "decided fields", "MATCH", "MATCH narrowed",
            "WRONG", "WRONG checker", "WRONG reading", "SPEC_ERROR", "NOT_STATABLE", "GAP", "UNSCORED"]
    rows = []
    for k, h in H.items():
        for s in ("clean", "contaminated", "all"):
            x = h[s]
            rows.append([k, s, x["items"], f"{x['stated']}/{x['items']}", x["stated_by_field"]["alone"],
                         x["stated_by_field"]["with_hypotheses"], x["decided_fields"], x["match"], x["match_narrowed"],
                         x["wrong"], x["wrong_checker"], x["wrong_reading"], x["spec_error"], x["not_statable"],
                         x["gap"], x["unscored"]])
    L += _table(head, rows)
    L += ["", "Rows: (P) the frozen expected values of items.jsonl, the preregistered score; (E) expected_alone "
          "replaced by ERRATA.md's post-freeze re-derivations with the team's rulings; (D) as (E), with the "
          "standing-condition rows marked derived:true counted as standing. 'clean' is the 91 items outside the "
          "contaminated source, 'contaminated' its 4 items, 'all' the 95.", "",
          "### WRONG, each classed", ""]
    wr = [(r["id"], f) for r in v["rows"]["NEW/P"] for f in FIELDS if r["score"][f] in ("WRONG", "BUG")]
    for i, f in wr:
        cl = WRONG_CLASS.get((i, f), ("unclassed", ""))
        L.append(f"- `{i}` {f}: **{cl[0]}**. {cl[1]}.")
    if not wr:
        L.append("None.")
    same = all({(r["id"], f) for r in v["rows"][k] for f in FIELDS if r["score"][f] in ("WRONG", "BUG")} == set(wr)
               for k in v["rows"])
    L += ["", f"The same fields are WRONG in every pin and row: {'yes' if same else 'no'}. The item's expected value "
          "is FALSE in P, E and D. Under our reading the statement as printed fails stability for some admissible "
          "slopes (the frozen justification's slope with K = 1 at nu = 1/2), and it holds for the central slope A1 "
          "chose.", "",
          "### Stated items (NEW, row P)", ""]
    L += _table(["id", "expected (alone / hyp.)", "fields", "components (named verdicts)", "reading verdict",
                 "score (alone / hyp.)"],
                [[f"`{r['id']}`", f"{r['expected']['alone']} / {r['expected']['with_hypotheses']}",
                  ", ".join(a["fields"]), ", ".join(x["named"] for x in a["components"]), a["verdict"],
                  f"{r['score']['alone']} / {r['score']['with_hypotheses']}"]
                 for r in v["rows"]["NEW/P"] for a in r["readings"]])
    L += ["", "A component the reader left unformalized is UNFORMALIZED, and a conjunction with one is at best UNKNOWN. "
          "That is why `guermond_popov_2016_invariant_domains:04` (the SSP clause) is a GAP although its formal part "
          "is VERIFIED. For `borges_costa_don_2006_wenoz:04` the named claim (order 5 at a first-order critical "
          "point, eps = 0, flux difference) is REFUTED and A1 negated it, so that component reads VERIFIED; the "
          "item's expected values are UNSURE, so it is unscored.", "",
          "### Coverage per topic (NEW, row P)", ""]
    L += _table(["source", "topic", "items", "stated", "decided fields", "MATCH", "WRONG", "SPEC_ERROR", "GAP", "UNSCORED"],
                [[f"`{x['source']}`" + (" (contaminated)" if x["source"] in CONTAMINATED else ""), x["topic"],
                  x["items"], x["stated"], x["decided_fields"], x["match"], x["wrong"], x["spec_error"], x["gap"],
                  x["unscored"]] for x in v["by_topic"]])
    # expected rows
    L += ["", "## Expected values: rows P, E, D", "",
          "The team's rulings (2026-11-28): `chen_shu_2017_esdg:05` counts as printed; `chen_shu_2017_esdg:03` is ruled "
          "strict, so it changes in (E) and (D) only and is flagged as a doubt; smoothness counts as part of 'order of "
          "accuracy', so those items stay TRUE. Exact-check rule: a re-derivation to FALSE counts as FALSE only if "
          "errata_checks.py confirms its counterexample exactly; otherwise it is UNSURE.", ""]
    L += _table(["id", "P", "E", "D", "why (E)", "why (D)"],
                [[f"`{x['id']}`", x["P"], x["E"], x["D"], x["why"], x["D_why"] or "as (E)"] for x in v["expected_log"]])
    L += ["", "Doubt: `chen_shu_2017_esdg:03`. ERRATA.md has no re-derived value for it (STANDING.md counts its condition "
          "as printed), so under the strict ruling we have no value and record UNSURE. A1 left it unformalized "
          "(scheme-class), so the doubt moves one field from GAP to UNSCORED and changes no MATCH or WRONG.", "",
          "### errata_checks.py (exact, Fraction arithmetic)", ""]
    ec = v["errata_checks"]
    L += _table(["case", "item", "confirmed", "what was evaluated", "numbers"],
                [[k, f"`{x['id']}`", "yes" if x["confirmed"] else "NO", x["evaluated"],
                  "; ".join(f"{a} = {b}" for a, b in x.items() if a not in ("id", "confirmed", "evaluated", "runs"))]
                 for k, x in ec.items()])
    k9 = ec["kt_09"]["runs"]
    L += ["", "KT:09, one step of each Table 5.1 scheme (exact maximum, its decimal, and ERRATA's quoted decimal):", ""]
    L += _table(["run", "max u^{n+1}", "decimal", "ERRATA quotes", "agrees to 4 digits", "> 1"],
                [[k, f"`{x['max_after']}`", x["decimal"], x["quoted"], x["agrees_4_digits"], x["above_1"]]
                 for k, x in k9.items()])
    L += ["", f"KT:08's 1.0825 is exactly {ec['kt_08']['max_after_endpoint_speeds']} = 1 + 2 lambda at lambda = "
          f"{ec['kt_08']['lambda']}, which satisfies (5.3) (lambda max|f'| = {ec['kt_08']['cfl_5_3']} <= 1/8). With "
          f"the interval speeds (4.10) the maximum stays {ec['kt_08']['max_after_interval_speeds']}. So the statement as "
          "printed, under our reading (the speeds of (4.17)-(4.19)), fails, and (4.10) is what changes the outcome. "
          "KT:09's quoted decimals match theta = 1 (ERRATA.md does not state theta); at theta = 2 the maximum also "
          "exceeds 1. For `barsukow_uzh_notes:03` the evaluation covers the map, its sum and the forced flux; the "
          "step 'every flux form differs from this one by a constant' is a two-line algebraic argument, stated in "
          "errata_checks.py, which we counted as part of the exact check.", ""]
    # pins
    pd, pins = v["pin_diff"], v["pins"]
    L += ["## Two pins", ""]
    L += _table(["pin", "checker commit", "checker root", "physverify imported from", "Lean store"],
                [[p, f"`{x['checker_commit'][:7]}`", f"`{x['checker_root']}`", f"`{x['physverify_file']}`",
                  f"`{x['lean_store']}`"] for p, x in pins.items()])
    L += ["", "Each pin ran in its own subprocess: `python -S` (so the venv's editable `.pth` for this tree is not read) "
          "with PYTHONPATH = <checker root>:<venv site-packages> and a clean environment. Each subprocess asserted "
          "that `physverify.__file__` lies under its root, and the test asserts that the two paths differ. An "
          "import-only probe before the first run (`run_v2.py --probe`) showed the trap: a plain venv interpreter "
          "with the OLD tree appended to sys.path imports NEW's physverify. OLD ran from a throwaway "
          "`git worktree add --detach /tmp/w0084-old-pin b2cafbe`, removed afterwards.", "",
          f"Per-verdict differences between OLD and NEW, over {pd['verdicts']} named verdicts in {pd['groups']} groups "
          f"of A1's readings: {len(pd['components'])} component differences and {len(pd['readings'])} reading "
          "differences.", ""]
    if pd["components"] or pd["readings"]:
        L += _table(["group", "claim", "what", "OLD", "NEW", "cause"],
                    [[f"`{x['group']}`", x["claim"], x["what"], x["OLD"], x["NEW"], x["cause"]] for x in pd["components"]])
    L += ["The checker changes in b2cafbe..3792caf (`git log -- physverify/ lean/`), and what each could move:", ""]
    L += [f"- `{cm}`: {what}; claim kinds affected: {', '.join(sorted(k)) or 'none (no checker code)'}"
          for cm, what, k in RANGE]
    L += ["", "No A1 reading names `ssp_preserves`, the only claim kind the range adds or changes, so no verdict can "
          "move. A reading that needs it is NOT_STATABLE at OLD; A2's `cockburn_shu_2001_rkdg_review:01` is the only "
          "such reading, and A2 is scored at NEW only. So the zero delta is expected. The isolation check above is "
          "what shows it is not an import artefact.", "",
          "### Lean status (Lean not run)", "",
          "For each of A1's verdicts, the pin's measured status where the theorem text the checker writes matches "
          "one in that pin's store (`lean_measured_b2cafbe.json` for OLD, `lean_measured_d8fb00a.json` for NEW; "
          "lean/ is unchanged from d8fb00a to 3792caf, which the freeze check asserts). The checker's Lean calls were "
          "answered from the store by the pin's own `measure_lean.Replay`, and no Lean process ran. 'not measured' "
          "means the checker states a theorem but no measured run has its text (the v2 specs are new). "
          "'Python-only' means the deciding checks state no Lean theorem. Every verdict scored here is the Python "
          "checker's.", ""]
    L += _table(["spec", "claim", "verdict", "Lean at NEW", "Lean at OLD", "detail (NEW)"],
                [[f"`{x['spec']}`", x["claim"], x["verdict"], x["NEW"], x["OLD"], x["detail"][:160]] for x in v["lean"]])
    kc = sum(x["NEW"] == "kernel-checked" for x in v["lean"])
    L += ["", f"Kernel-checked verdicts at NEW: {kc} of {len(v['lean'])}. Every decided verdict in this run rests on "
          "the Python checker (exact Fraction arithmetic) alone.", ""]
    # agreement
    a = v["agreement"]
    L += ["## Reader agreement (A1 vs A2, the 22-item subset)", "",
          f"- (i) same statable / not decision: {a['same_statable_items']}/{a['items']} items, "
          f"{a['same_statable_fields']}/{a['fields']} fields.",
          f"- (ii) fields both left unformalized: {a['both_unformalized_fields']}; same primary reason code: "
          f"{a['same_primary_reason']}/{a['both_unformalized_fields']}.",
          f"- (iii) fields both formalized: {a['both_formalized_fields']}; same claim kinds and quantifiers (claim, "
          f"relation, negation, form, regime, n_cp): {a['same_kinds_quantifiers']}/{a['both_formalized_fields']}; then "
          f"same verdict-relevant parameters (spec, override, p, eps): {a['same_parameters']}/{a['both_formalized_fields']}; "
          f"same spec content after overrides (pde, params, scheme, claims): {a['same_spec_content']}/"
          f"{a['both_formalized_fields']}; same number of unformalized parts: {a['same_unformalized_parts']}/"
          f"{a['both_formalized_fields']}.", "",
          "The fields both formalized are `barsukow_uzh_notes:01` and `:06`. A2 chose relation `necessary` where A1 "
          "chose `same` (consistency of :01, conservativity of :06), and A2 added a negated instability component to "
          ":01 ('conditionally'). So no field agrees on kinds and quantifiers.", "",
          "Disagreements (primary reason, or `formalized`):", ""]
    L += _table(["id", "field", "A1", "A2"], [[f"`{d['id']}`", d["field"], d["A1"], d["A2"]] for d in a["disagreements"]])
    L += ["", "### Reading sensitivity (NEW checker on A2's readings, row P; not part of the headline)", ""]
    L += _table(["id", "field", "A2 verdict", "A2 score", "A1 score"],
                [[f"`{s['id']}`", s["field"], s["A2_verdict"], s["A2_score"], s["A1_score"]] for s in v["a2_sensitivity"]])
    s2 = v["a2_sensitivity"]
    L += ["", f"A2's readings score as A1's on {sum(s['A2_score'] == s['A1_score'] for s in s2)}/{len(s2)} of the fields "
          f"A2 stated. A2 MATCH: {sum(s['A2_score'] == 'MATCH' for s in s2)}; A1 MATCH on the same fields: "
          f"{sum(s['A1_score'] == 'MATCH' for s in s2)}.", "",
          "A2's null specs map to `specs/a2/` (TRANSLATION.md, choices A1-A3).", ""]
    # ssp
    sp = v["ssp"]
    L += ["## SSP analysis (diagnostic; scorer judgments made after scoring, never used to re-score)", "",
          f"`ssp_preserves` was used in {sp['A1_components']} components by A1 ({sp['A1_items']} items) and in "
          f"{sp['A2_components']} components by A2 ({sp['A2_items']} item). We judged {sp['relevant']} items SSP-relevant "
          f"((a): {sp['relevant_yes']} yes, {sp['relevant_partly']} partly), i.e. about a time-stepping method keeping a "
          "convex property that forward Euler keeps. Columns (a) and (c) are our judgments; (b) is what each reader "
          "picked. (c) uses the kind as it is at 3792caf: one scalar 1D spec, one named or tabulated explicit "
          "Runge-Kutta method, property positivity, tvd or max_principle, a CFL bound.", "",
          "Answer to (c) among the SSP-relevant items: " +
          ", ".join(f"{k}: {n}" for k, n in sorted(sp["by_category"].items())) +
          " ('instance': statable as an instance; 'too narrow': the kind cannot say it, e.g. a class statement over "
          "methods or a quantity it does not state; 'other': multi-d or a system, outside the scheme layer).", "",
          "So the gap is mostly the kind, not the readers' vocabulary. Most SSP-relevant sentences are class "
          "statements about methods or SSP coefficients, or are 2D or systems. Where the kind fits as an instance "
          "(`cockburn_shu_2001_rkdg_review:01`), A1 chose not-checkable and A2 used the kind, which is a reader "
          "difference. For `guermond_popov_2016_invariant_domains:04`, A1 left the SSP clause unformalized as "
          "existential.", ""]
    L += _table(["id", "(a) SSP-relevant", "(b) A1 picked", "(b) A2 picked", "(c) statable", "(c) why"],
                [[f"`{r['id']}`", r["relevant"], r["A1"], r["A2"], r["statable"], r["why"]] for r in sp["rows"]])
    # contamination, confounds
    L += ["", "## Contamination", "",
          "- `borges_costa_don_2006_wenoz` (4 items, reported apart above): " + CONTAMINATED["borges_costa_don_2006_wenoz"] + ".",
          "- The other 8 source ids and their authors' names were searched for in the commit messages up to 3792caf, "
          "in `git grep` of the tree outside benchmark/outside_v2/ (DEV_RESULTS.md included) and in "
          "benchmark/outside/. They appear only in v2's own collection commits, and once in v1's dropped-source list "
          "(a different Cockburn-Shu paper, not opened: 404). None was read while building the checker.", "",
          "Limitation, not excludable: textbook results the v2 sources restate, which the checker or its tests rest on:", ""]
    L += [f"- {x}" for x in TEXTBOOK]
    L += ["", "## Confounds and limitations", ""]
    L += [f"{i}. {x.format(**v['stats'])}" for i, x in enumerate(CONFOUNDS, 1)]
    # spec log, overrides, spec errors, bugs
    od = v["override_demo"]
    L += ["", "## Spec-choice log", "",
          "Verdict-relevant parameters inherited from a reused dev spec rather than fixed by the reading:", "",
          f"- A1: none of its specs reuses a dev spec. Its {v['stats']['verbatim']} scheme drafts are its own and "
          "are copied verbatim. The "
          "WENO-Z spec takes the candidate coefficients c_kj and the pairing of ideal weights with stencils from "
          "the dev spec `jiang-shu-weno5-js-fd.json`, as A1's draft directs (TRANSLATION.md, W1 and W3).",
          "- A2: `benchmark/outside/specs/upwind-advection.json` (dev) for `barsukow_uzh_notes:01` and "
          "`cockburn_shu_2001_rkdg_review:01`: a = 1, flux a*uL, von_neumann_cfl [0, 1] (A2 overrides it to [0, 2] in "
          "one component) and positive_cfl [0, 1] (not used by A2's claims).", "",
          "## Overrides", "",
          "Overrides are deep-merged into the base spec (scorer code). A2's override "
          "`{\"claims\": {\"von_neumann_cfl\": [\"0\", \"2\"]}}` on the dev upwind spec keeps the other claims "
          f"(merged claims: `{json.dumps(od['merged_claims'])}`, base: `{json.dumps(od['base_claims'])}`) and gives "
          f"a different check: von_neumann_stable_under_cfl is {od['merged']} merged and {od['base']} on the base spec "
          "(a test asserts both).", "",
          "## SPEC_ERROR and syntax fixes", "",
          f"SPEC_ERROR fields (NEW, P, all): {n['all']['spec_error']}. Both chen-shu specs "
          "(`chen-shu-godunov-burgers.json`, `chen-shu-hll-rusanov-burgers.json`, items `chen_shu_2017_esdg:08` "
          "and `:09`) fail with `KeyError: 'q'`. A1's drafts declare `claims.entropy_stability.eta` without the "
          "entropy flux `q`, and the checker reads both once `eta` is given. That is a missing key, not a key-name "
          "typo, so it is not repaired, and the readings stay SPEC_ERROR. Syntax-only fixes: "
          + ("none." if not SYNTAX_FIXES else ""), ""]
    for s, diff in SYNTAX_FIXES:
        L += [f"- `{s}`:", "```diff", diff, "```"]
    L += ["## Checker bugs and re-score", ""]
    if not CHECKER_BUGS:
        L += ["No checker bug was found while scoring, so there is no re-score section, and the headline is the first "
              "run. The bare `KeyError: 'q'` above is a poor error message, not a wrong verdict (a missing input is "
              "refused). A message naming the missing key would be a usability fix and changes no score.", "",
              "A scorer bug (not a checker bug), fixed and recorded: in the first run (commit with subject 'Bench v2 B: "
              "first checker run at both pins, as run'), the NEW subprocess took its pin label from the branch HEAD, "
              "so it attached no Lean store and named the branch commit. The fix labels this tree NEW when its "
              "physverify/ and lean/ equal 3792caf. The re-run's Python verdicts and reading verdicts are identical to "
              "the first run's at both pins (checked against that commit); only NEW's Lean status column and its "
              "pin fields changed."]
    L += ["", "## Freeze", "",
          "Asserted by `frozen_errors()` before anything runs, and checked on the record by "
          "`tests/test_outside_v2_scores.py`: items.jsonl equals its blob at 63337e1; readings.json and "
          "readings_a2.json equal their readings commits (`4c82154`, `c6f480d`, each the last commit touching its "
          "file) byte for byte; `git diff 3792caf -- physverify/ lean/` is empty at HEAD and in the working tree; "
          "lean/ is unchanged from d8fb00a to 3792caf; specs/ equals the translation commit "
          f"(`{pins['NEW']['translation_commit'][:7]}`, before the first checker run)."]
    return "\n".join(L) + "\n"


def source_topics() -> dict:
    out = {}
    for line in (HERE / "SOURCES.md").read_text().splitlines():
        m = re.match(r"\| `([a-z0-9_]+)` \| \w+ \| ([^|]+) \|", line)
        if m:
            out[m[1]] = m[2].strip()
    return out


# what changed in the checker between the pins (git log b2cafbe..3792caf -- physverify/ lean/), and what each
# change can move: a verdict difference between the pins is attributed to the entry whose claim kinds it touches
RANGE = [("5b1b8f4", "SSP time stepping: ssp.py, claim kind ssp_preserves (claims.py, claimkinds.py, schemes/__init__.py)",
          {"ssp_preserves"}),
         ("82218f5, 98430c6", "Lean: the SSP class theorem (lean/PhysVerify/SSP.lean, SSPAxioms.lean)", {"ssp_preserves"}),
         ("3792caf", "Lean re-measured at the SSP code (lean_measured_d8fb00a.json; no checker code)", set())]


def pin_diff(old: dict, new: dict) -> dict:
    diffs = []
    for k in sorted(set(old["groups"]) | set(new["groups"])):
        for n in sorted(set(old["groups"].get(k, {})) | set(new["groups"].get(k, {}))):
            o, w = old["groups"].get(k, {}).get(n, {}), new["groups"].get(k, {}).get(n, {})
            for what in ("verdict", "lean"):
                if o.get(what) != w.get(what):
                    cause = [c for c, _, kinds in RANGE if n in kinds] or (
                        ["3792caf (the measured store)"] if what == "lean" else ["unattributed"])
                    diffs.append({"group": json.loads(k)[0], "claim": n, "what": what, "OLD": o.get(what),
                                  "NEW": w.get(what), "cause": ", ".join(cause)})
    rd = [{"id": a["id"], "OLD": a["verdict"], "NEW": b["verdict"]} for a, b in zip(old["readings"], new["readings"])
          if a["verdict"] != b["verdict"]]
    return {"components": diffs, "readings": rd,
            "groups": len(new["groups"]), "verdicts": sum(len(g) for g in new["groups"].values())}


def lean_table(V: dict) -> list[dict]:
    out = []
    for k, g in V["NEW"]["a1"]["groups"].items():
        for n, x in g.items():
            o = V["OLD"]["a1"]["groups"].get(k, {}).get(n, {})
            out.append({"spec": Path(json.loads(k)[0]).name, "claim": n, "verdict": x["verdict"],
                        "NEW": x["lean"], "OLD": o.get("lean"), "detail": x["lean_detail"]})
    return out


# ---------------------------------------------------------------- agreement (rule 7), as run_heldout.py measures it

def primary(reasons: list[str]) -> str:
    return min(reasons, key=REASONS.index)


def unformalized_primary(e: dict) -> dict:
    return {f: primary(u["reasons"]) for u in e["unformalized"] for f in fields_of(u)}


def kinds(r: dict) -> list:
    return sorted([c["claim"], c.get("relation", "same"), bool(c.get("negated")),
                   (c.get("params") or {}).get("form"), (c.get("params") or {}).get("regime"),
                   (c.get("params") or {}).get("n_cp")] for c in formal(r))


def params_of(r: dict, item_id: str) -> list:
    return sorted([c["claim"], spec_path(c, item_id), json.dumps(c.get("override", {}), sort_keys=True),
                   (c.get("params") or {}).get("p"), (c.get("params") or {}).get("eps"), bool(c.get("negated"))]
                  for c in formal(r))


def scheme_of(r: dict, item_id: str) -> list:
    """The verdict-relevant content of each component's spec after its override: pde, params, scheme and the
    claims block (a reading-level comparison that does not depend on which file holds the spec)."""
    out = []
    for c in formal(r):
        s = deep_merge(json.loads((ROOT / spec_path(c, item_id)).read_text()), c.get("override", {}))
        out.append(json.dumps([c["claim"], {k: s.get(k) for k in ("pde", "params", "scheme", "claims", "reconstruction")},
                               c.get("params"), bool(c.get("negated"))], sort_keys=True))
    return sorted(out)


def agreement(a1: dict, a2: dict) -> dict:
    by1 = {e["id"]: e for e in a1["items"]}
    sub = subset()
    assert [e["id"] for e in a2["items"]] == sub
    rows, same_items, same_fields, both_unf, same_reason, both_form = [], 0, 0, 0, 0, []
    for e2 in a2["items"]:
        e1 = by1[e2["id"]]
        same_items += bool(e1["readings"]) == bool(e2["readings"])
        p1, p2 = unformalized_primary(e1), unformalized_primary(e2)
        for f in FIELDS:
            same_fields += (f in p1) == (f in p2)
            if f in p1 and f in p2:
                both_unf += 1
                same_reason += p1[f] == p2[f]
                if p1[f] != p2[f]:
                    rows.append({"id": e2["id"], "field": f, "A1": p1[f], "A2": p2[f]})
            if f not in p1 and f not in p2:
                r1 = [r for r in e1["readings"] if f in fields_of(r)]
                r2 = [r for r in e2["readings"] if f in fields_of(r)]
                k_same = [kinds(r) for r in r1] == [kinds(r) for r in r2]
                n_unf = ([len(r["formalization"]) - len(formal(r)) for r in r1] ==
                         [len(r["formalization"]) - len(formal(r)) for r in r2])
                p_same = [params_of(r, e2["id"]) for r in r1] == [params_of(r, e2["id"]) for r in r2]
                s_same = [scheme_of(r, e2["id"]) for r in r1] == [scheme_of(r, e2["id"]) for r in r2]
                both_form.append({"id": e2["id"], "field": f, "same_kinds_quantifiers": k_same,
                                  "same_unformalized_parts": n_unf, "same_parameters": k_same and p_same,
                                  "same_spec_content": k_same and s_same,
                                  "A1": [kinds(r) for r in r1], "A2": [kinds(r) for r in r2]})
            if (f in p1) != (f in p2):
                rows.append({"id": e2["id"], "field": f, "A1": p1.get(f, "formalized"), "A2": p2.get(f, "formalized")})
    return {"items": len(sub), "same_statable_items": same_items, "fields": 2 * len(sub),
            "same_statable_fields": same_fields, "both_unformalized_fields": both_unf,
            "same_primary_reason": same_reason, "both_formalized_fields": len(both_form),
            "same_kinds_quantifiers": sum(x["same_kinds_quantifiers"] for x in both_form),
            "same_parameters": sum(x["same_parameters"] for x in both_form),
            "same_spec_content": sum(x["same_spec_content"] for x in both_form),
            "same_unformalized_parts": sum(x["same_unformalized_parts"] for x in both_form),
            "both_formalized": both_form, "disagreements": rows}


# ---------------------------------------------------------------- SSP diagnostic (the team's amendment)

# Scorer judgments made AFTER scoring, diagnostics only; nothing is re-scored with them. (a) is the item about a
# time-stepping method preserving a convex property that holds under forward Euler; (c) could ssp_preserves, as it
# is at 3792caf (one scalar 1D spec, one named or tabulated explicit RK method, property positivity, tvd or
# max_principle, a CFL bound), have stated it, and if not, why. Items not listed: (a) no, (c) not applicable.
SSP_JUDGED = {
    "cockburn_shu_2001_rkdg_review:01": ("yes", "instance", "yes, as an instance: k = 0 DG is the upwind scheme, "
                                         "with named methods (ssprk22, ssprk33) and property tvd, as A2 wrote it. "
                                         "'Regardless of its accuracy' over the whole class is a class statement"),
    "cockburn_shu_2001_rkdg_review:06": ("yes", "too narrow", "only partly: one method (as Shu-Osher arrays) on a "
                                         "k = 0 upwind instance fits, but the theorem is over every method meeting "
                                         "the printed alpha/beta conditions, and its TVBM bound (+ C M Q, the TVB "
                                         "limiter for k >= 1) is not one of the kind's properties"),
    "guermond_popov_2016_invariant_domains:04": ("yes", "instance", "the clause 'can be made high-order in time by "
                                                 "SSP algorithms' is existential; an instance (one named SSP method on "
                                                 "the P1 upwind reduction, property max_principle) is statable, the "
                                                 "existential is not"),
    "kurganov_tadmor_2000_central:09": ("yes", "other", "not as printed: the scheme is two-dimensional, and the kind "
                                        "takes a 1D scalar forward-Euler step. A 1D narrowing (data constant in y, "
                                        "Table 5.1's methods as Shu-Osher arrays, property max_principle) could be "
                                        "written; we did not try it"),
    "kurganov_tadmor_2000_central:10": ("yes", "too narrow", "no: the multi-level methods (5.8) are not one-step "
                                        "Runge-Kutta methods in Shu-Osher form, and the scheme is 2D"),
    "kurganov_tadmor_2000_central:06": ("partly", "other", "no: the maximum-principle part is 2D, and the TVD part is "
                                        "semi-discrete (no time stepper)"),
    "ketcheson_2019_relaxation_rk:10": ("yes", "too narrow", "no: a class statement over every method absolutely "
                                        "monotonic at -r (an iff on R_gamma(-r)); the kind takes one method"),
    "ketcheson_2019_relaxation_rk:11": ("yes", "too narrow", "no: it compares SSP coefficients C(A, gamma b) and "
                                        "C(A, b) over all methods; the kind reports preservation at a CFL bound, not "
                                        "the value of C as a claim"),
    "ketcheson_2019_relaxation_rk:14": ("yes", "too narrow", "no: it states that relaxation methods keep the SSP "
                                        "coefficient; their weights gamma_n b depend on the solution, and the kind "
                                        "takes a fixed method and does not state C as a claim"),
    "hu_adams_shu_2013_pp_flux_limiter:01": ("partly", "other", "no: the limiter is for the Euler system (the kind is "
                                             "scalar), and the sentence covers every high-order base scheme; SSP "
                                             "enters only by applying the limiter at each stage"),
    "hu_adams_shu_2013_pp_flux_limiter:05": ("partly", "other", "as item 01"),
}


def ssp_table(a1: dict, a2: dict, its: dict) -> dict:
    by2 = {e["id"]: e for e in a2["items"]}

    def picked(e: dict | None) -> str:
        if e is None:
            return "not read"
        ks = list(dict.fromkeys(c["claim"] for r in e["readings"] for c in formal(r)))
        rs = list(dict.fromkeys(primary(u["reasons"]) for u in e["unformalized"]))
        return ", ".join(ks + rs)

    rows = []
    for e in a1["items"]:
        a, cat, why = SSP_JUDGED.get(e["id"], ("no", "n/a", ""))
        rows.append({"id": e["id"], "relevant": a, "A1": picked(e), "A2": picked(by2.get(e["id"])),
                     "statable": cat, "why": why})
    rel = [r for r in rows if r["relevant"] != "no"]
    uses = lambda d: sum(c["claim"] == "ssp_preserves" for e in d["items"] for r in e["readings"]  # noqa: E731
                         for c in formal(r))
    used_items = lambda d: sum(any(c["claim"] == "ssp_preserves" for r in e["readings"] for c in formal(r))  # noqa: E731
                               for e in d["items"])
    return {"rows": rows, "relevant": len(rel), "relevant_yes": sum(r["relevant"] == "yes" for r in rows),
            "relevant_partly": sum(r["relevant"] == "partly" for r in rows),
            "by_category": dict(Counter(r["statable"] for r in rel)),
            "A1_components": uses(a1), "A1_items": used_items(a1), "A2_components": uses(a2), "A2_items": used_items(a2)}


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
