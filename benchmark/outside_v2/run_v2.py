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

# every WRONG of the first run, classed by hand after it: (id, field, row) -> (class, one-line justification)
WRONG_CLASS: dict = {}
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
    commit = git("rev-parse", "HEAD", cwd=root).decode().strip()
    label = "NEW" if commit == NEW else "OLD" if commit == OLD else commit[:7]
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
             "pin": label, "checker_commit": commit, "checker_root": str(root), "physverify_file": str(mod),
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


def render() -> str:
    raise NotImplementedError


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
