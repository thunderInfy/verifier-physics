"""Usage: uv run python papers/scheme-claims/measure_lean.py collect | ingest RESULTS | registry |
       ingest-registry RESULTS | summary   [--store FILE]

A measured Lean run, stored in lean_measured_<commit>.json, one file per measured commit (the commit in
the name and the store's `commit` field; FILE defaults to the one for HEAD). The paper's Lean-label numbers
come from lean_measured_b2cafbe.json (PAPER_STORE), the run at the heldout pin; collected at 1d73a80, whose
Lean key is the same.

Every spec the paper's numbers draw on is run through the checker's own Lean path: `lean_cert.certify`
for the scheme specs (schemes/, our claims benchmark, the dev readings of the outside benchmark) and
`variational.judge_file` for the update-map, variational and kernel files. Nothing here states a theorem
or decides a label: inside `Replay`, `lean_backend.check_batch` is split into one file per theorem
(the real `check_batch` on a one-item list, so each theorem is attributed exactly as in a batch), and
`lean_backend._run`, the one place Lean is called, answers from the store. A theorem not in the store
is written to lean/build_certs/measure/jobs/<sha>.lean, the exact file the checker would compile.

    collect   run every spec; write the theorems not measured yet as jobs, and record the specs whose
              theorems are all measured (with their claims' labels). A spec already recorded with the
              same Lean key is skipped, so a crash only costs a restart.
    ingest    read a results directory of lean_run_jobs.sh (run on the Lean machine) into the store; the
              host is read from RESULTS/host.json (written on the Lean machine) when it is there
    registry  write lean/build_certs/measure/registry.lean: `#print axioms` of the Lean meaning theorem
              of every claim kind that has one (physverify/claimkinds.py)
    ingest-registry  read RESULTS/registry.{log,exit,time} of that file into the store
    summary   print the counts

Loop collect -> run the jobs on the Lean machine -> ingest until collect reports no pending theorem.
The status of a theorem: accepted (no error in it, `#print axioms` within propext, Classical.choice,
Quot.sound), rejected (an error inside the declaration, or any other axiom, e.g. sorryAx or
Lean.ofReduceBool), error (Lean failed outside the declaration: import, crash, out of memory) or
timeout (the per-theorem wall-clock limit; host-dependent).
"""
from __future__ import annotations

import datetime
import hashlib
import json
import re
import subprocess
import sys
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
PAPER_STORE = HERE / "lean_measured_b2cafbe.json"
WORK = ROOT / "lean" / "build_certs" / "measure"
# what a theorem's text and its fate depend on: the Lean project (toolchain and Mathlib rev included), the
# judges and planners that write the statements and proofs, and the checks whose witnesses the planners use
KEY_PATHS = ("lean", "physverify/lean_backend.py", "physverify/schemes", "physverify/tools", "physverify/variational.py",
             "physverify/kernel.py", "physverify/expr.py", "physverify/derivation.py")
HOST = {"name": "lean-build", "machine": "GCP e2-standard-8", "cpus": 8, "ram_gb": 32}   # unless host.json says
LIMIT_S = 1200          # per theorem; the README's warm full pass is about 1 s per theorem
RETRY_S = 3600          # one retry, for the superbee TVD theorem only
STATUSES = ("accepted", "rejected", "error", "timeout")


def _git(*args: str) -> str:
    return subprocess.run(["git", *args], cwd=ROOT, capture_output=True, text=True, check=True).stdout.strip()


def lean_key(rev: str = "HEAD") -> dict:
    """Git object ids of KEY_PATHS at `rev`, with the Lean toolchain and the Mathlib rev spelled out."""
    manifest = json.loads(_git("show", f"{rev}:lean/lake-manifest.json"))
    mathlib = next(p["rev"] for p in manifest["packages"] if p["name"] == "mathlib")
    return {"lean_toolchain": _git("show", f"{rev}:lean/lean-toolchain"), "mathlib_rev": mathlib,
            "trees": {p: _git("rev-parse", f"{rev}:{p}") for p in KEY_PATHS}}


def store_path(rev: str = "HEAD") -> Path:
    return HERE / f"lean_measured_{_git('rev-parse', '--short=7', rev)}.json"


def store_paths() -> list[Path]:
    return sorted(HERE.glob("lean_measured_*.json"))


def load_store(path: Path = PAPER_STORE) -> dict:
    return json.loads(path.read_text()) if path.is_file() else {"theorems": {}, "specs": {}}


def sha(src: str) -> str:
    return hashlib.sha256(src.encode()).hexdigest()[:20]


# ---------------------------------------------------------------- answering Lean from the store

class Replay:
    """`with Replay(store) as rp:` the checker's Lean calls are answered from store["theorems"]: one file
    per theorem, keyed by the sha of its text. rp.pending collects the files not measured yet (answered as
    failed, so nothing is upgraded on them); rp.used lists (theorem name, sha) in call order."""

    def __init__(self, store: dict):
        self.theorems, self.pending, self.used, self.call = store["theorems"], {}, [], None

    def __enter__(self):
        from physverify import lean_backend as lb
        self.lb, self.saved = lb, (lb.check_batch, lb.check, lb._run)
        batch, check = lb.check_batch, lb.check

        def split(items, **kw):
            out = {}
            for it in items:
                self.call = {"via": "check_batch", "item": list(it), "kw": {k: v for k, v in kw.items() if k != "timeout"}}
                out.update(batch([it], **kw))
            return out

        def single(statement, proof, **kw):
            self.call = {"via": "check", "item": [statement, proof], "kw": {k: v for k, v in kw.items() if k != "timeout"}}
            return check(statement, proof, **kw)

        def run(src, timeout):
            h = sha(src)
            self.used.append((re.search(r"^theorem (\w+) :", src, re.M)[1], h))
            t = self.theorems.get(h)
            if t is None:
                self.pending[h] = (src, self.call)
                return False, "not measured"
            return (False, "timeout") if t["status"] == "timeout" else (t["exit"] == 0, t["log"])

        lb.check_batch, lb.check, lb._run = split, single, run
        return self

    def __exit__(self, *exc):
        self.lb.check_batch, self.lb.check, self.lb._run = self.saved


# ---------------------------------------------------------------- the specs the paper counts

def _scheme_claims(pairs) -> list:
    return [{"claim": v["claim"], "verdict": v["verdict"], "guarantee": v["guarantee"],
             **({"lean_check": v["lean_check"]} if "lean_check" in v else {})} for _, rep in pairs for v in rep["claims"]]


def _scheme_checks(pairs) -> list:
    return [{"check": r["check"], "status": r["status"], "guarantee": r.get("guarantee", ""),
             **({"lean": r["lean"]} if "lean" in r else {})} for _, rep in pairs for r in rep["checks"] if "lean" in r]


def scheme_paths() -> list[Path]:
    S = ROOT / "schemes"
    return sorted(S.glob("*.json")) + sorted(S.glob("*/*.json"))


def _groups(data: dict, components) -> dict:
    groups: dict = {}
    for c in components(data):
        if "unformalized" not in c:
            groups.setdefault(json.dumps([c["spec"], c.get("override", {})], sort_keys=True), (c, []))[1].append(c["claim"])
    return groups


def bench_specs(base: Path, data: dict, components) -> list[tuple[str, dict]]:
    """(id, spec) per (spec, override) group of a benchmark's readings, as bench.run checks them."""
    from physverify import reconstruction
    from physverify.schemes import bench
    out = []
    for key, (c, names) in _groups(data, components).items():
        if c["claim"] in reconstruction.CLAIMS:
            continue                       # checked in Python only: no Lean statement
        out.append((key, bench._spec(base, c["spec"], c.get("override", {}), list(dict.fromkeys(names)))))
    return out


def run_dev():
    import importlib.util
    spec = importlib.util.spec_from_file_location("run_dev", ROOT / "benchmark" / "outside" / "run_dev.py")
    rd = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(rd)
    return rd


def units() -> list[tuple[str, str, object]]:
    """(id, kind, thunk) for every spec the paper counts; thunk() runs the checker's Lean path and returns
    what it decided (claims with their guarantees)."""
    from physverify import schemes
    from physverify.schemes import bench, lean_cert
    out = []

    def scheme(spec):
        def go():
            pairs = [(spec, schemes.check(spec))]
            lean_cert.certify(pairs)
            return {"claims": _scheme_claims(pairs), "checks": _scheme_checks(pairs)}
        return go

    for p in scheme_paths():
        out.append((str(p.relative_to(ROOT)), "schemes", scheme(schemes.load(p))))
    B = ROOT / "benchmark" / "scheme-claims"
    for key, spec in bench_specs(B, json.loads((B / "claims.json").read_text()), bench.components):
        out.append((f"benchmark/scheme-claims {key}", "bench", scheme(spec)))
    rd = run_dev()
    for key, spec in bench_specs(rd.SPECS, rd.load(), rd.components):
        out.append((f"benchmark/outside {key}", "outside", scheme(spec)))

    def judged(path):
        def go():
            from physverify.variational import guarantee, judge_file, load
            I = load(path)
            return {"claims": [{"claim": r.claim, "kind": c.kind, "verdict": r.verdict, "guarantee": guarantee(c, r),
                                "attempts": r.attempts} for c, r in zip(I.claims, judge_file(I))]}
        return go

    for d in ("variational", "kernels"):
        for p in sorted((ROOT / "benchmark" / d).glob("*.json")):
            out.append((str(p.relative_to(ROOT)), d, judged(p)))
    return out


# ---------------------------------------------------------------- collect / ingest

def collect(path: Path, only: str | None = None) -> int:
    store, key, commit = load_store(path), lean_key(), _git("rev-parse", "HEAD")
    jobs = WORK / "jobs"
    jobs.mkdir(parents=True, exist_ok=True)
    pending, done, skipped = {}, 0, 0
    for uid, kind, go in units():
        if only and only not in uid:
            continue
        rec = store["specs"].get(uid)
        if rec and rec["key"] == key and all(h in store["theorems"] for _, h in rec["theorems"]):
            skipped += 1
            continue
        t = time.time()
        with Replay(store) as rp:
            decided = go()
        print(f"{uid}: {len(rp.used)} theorems, {len(rp.pending)} pending ({time.time() - t:.0f} s)", flush=True)
        if rp.pending:
            pending.update(rp.pending)
            continue
        th = [store["theorems"][h] for _, h in rp.used]
        store["specs"][uid] = {"kind": kind, "commit": commit, "key": key, "theorems": rp.used,
                               "lean_wall_s": round(sum(x["seconds"] for x in th), 1),
                               "statuses": {s: sum(x["status"] == s for x in th) for s in STATUSES if any(x["status"] == s for x in th)},
                               **decided}
        done += 1
    for h, (src, call) in pending.items():
        (jobs / f"{h}.lean").write_text(src)
        (jobs / f"{h}.json").write_text(json.dumps(call, ensure_ascii=False))
    _write(store, path, collected=True)
    print(f"recorded {done}, skipped {skipped} (already recorded with this key); {len(pending)} theorems pending "
          f"in {jobs}" if pending else f"recorded {done}, skipped {skipped}; nothing pending")
    return len(pending)


def classify(src: str, call: dict, exit_code: int, log: str) -> dict:
    """Status of one theorem file from Lean's exit code and output. Acceptance is decided by the checker's
    own function (`check_batch` or `check`, whichever wrote the file), fed this output; the rest only
    tells a rejection (an error inside the declaration, or an axiom beyond the standard three) from an
    error outside it."""
    from physverify import lean_backend as lb
    if exit_code in (124, 137):
        return {"status": "timeout", "axioms": []}
    seen, saved = [], lb._run
    lb._run = lambda s, t: seen.append(s) or (exit_code == 0, log)
    try:
        if call["via"] == "check_batch":
            r = lb.check_batch([tuple(call["item"])], **call["kw"])[call["item"][0]]
        else:
            r = lb.check(*call["item"], **call["kw"])
    finally:
        lb._run = saved
    if seen != [src]:
        raise ValueError("the checker would not write this file from the recorded call")
    name = re.search(r"^theorem (\w+) :", src, re.M)[1]
    start = src[:src.index(f"theorem {name} :")].count("\n") + 1
    errors = [int(x[1]) for x in re.finditer(r":(\d+):\d+: error", log)]
    axioms = lb._axioms(name, log)
    if r.ok:
        status = "accepted"
    elif any(x >= start for x in errors) or (not errors and axioms is not None and not axioms <= lb.STD_AXIOMS):
        status = "rejected"
    else:
        status = "error"
    return {"status": status, "axioms": sorted(axioms or [])}


def _kept(log: str) -> str:
    """The lines of Lean's output that decide a theorem's fate (error positions and the axiom report)."""
    return "\n".join(x for x in log.splitlines() if re.search(r":\d+:\d+: error|depends on axioms|does not depend on any axioms", x))


def _host(results: Path, store: dict) -> dict:
    """The Lean machine as RESULTS/host.json records it (written there by the run), else the store's or HOST."""
    f = results / "host.json"
    return json.loads(f.read_text()) if f.is_file() else store.get("host", HOST)


def ingest(results: Path, path: Path, retry: bool = False, parallel: int = 6) -> None:
    store = load_store(path)
    host = store["host"] = _host(results, store)
    jobs, n = WORK / "jobs", 0
    for ex in sorted(results.glob("*.exit")):
        h = ex.stem
        old = store["theorems"].get(h)
        if old and not retry:
            continue
        src = (jobs / f"{h}.lean").read_text()
        call = json.loads((jobs / f"{h}.json").read_text())
        code = int(ex.read_text().strip())
        log = (results / f"{h}.log").read_text(errors="replace")
        wall, rss = (results / f"{h}.time").read_text().split()[-2:]
        limit = int((results / "limit").read_text()) if (results / "limit").is_file() else LIMIT_S
        c = classify(src, call, code, log)
        att = {"status": c["status"], "seconds": float(wall), "limit_s": limit}
        rec = {"name": re.search(r"^theorem (\w+) :", src, re.M)[1], **c, "exit": code, "seconds": float(wall),
               "peak_rss_mb": round(int(rss) / 1024), "limit_s": limit, "host": host["name"], "log": _kept(log),
               "attempts": (old or {}).get("attempts", []) + [att]}
        if c["status"] != "accepted":
            first = re.search(r"^.*:\d+:\d+: error.*$", log, re.M)
            rec["message"] = (log[first.start():] if first else log)[:6000]
        store["theorems"][h] = rec
        n += 1
    # the wall-clock of the run (several starts if it was resumed), as lean_run_jobs.sh stamps it
    stamps = lambda kind: sorted(int(p.read_text()) for p in results.glob(f"run.{kind}.*"))
    store.setdefault("runs", {})[results.name] = {
        "host": host["name"], "parallel": parallel, "starts": stamps("start"), "ends": stamps("end"),
        "theorems": len(list(results.glob("*.exit")))}
    _write(store, path)
    print(f"ingested {n} theorems from {results}")


# ---------------------------------------------------------------- the registry's meaning theorems

def _full_names(text: str) -> dict[str, str]:
    """name as written after `theorem` -> its full name, from the file's namespace/section/end nesting."""
    frames, out = [], {}
    for line in text.splitlines():
        if m := re.match(r"(?:noncomputable )?(namespace|section)\b ?(\S*)", line):
            frames.append((m[1], m[2]))
        elif m := re.match(r"end\b ?(\S*)", line):
            if frames and frames[-1][1] == m[1]:
                frames.pop()
        elif m := re.match(r"theorem (\S+)\s", line):
            out[m[1]] = ".".join([n for k, n in frames if k == "namespace"] + [m[1]])
    return out


def meaning_theorems() -> dict[str, str]:
    """Claim kind -> the full Lean name of its meaning theorem (physverify/claimkinds.py, `meaning`)."""
    from physverify.claimkinds import KINDS
    names: dict = {}
    for p in sorted((ROOT / "lean" / "PhysVerify").rglob("*.lean")):
        for short, full in _full_names(p.read_text()).items():
            names.setdefault(short, []).append(full)
    out = {}
    for kind, k in KINDS.items():
        if k["meaning"]:
            (full,) = names[k["meaning"]]     # one theorem by that name, as test_claimkinds asserts it exists
            out[kind] = full
    return out


def registry_source() -> str:
    return "import PhysVerify\n" + "".join(f"#print axioms {n}\n" for n in meaning_theorems().values())


def ingest_registry(results: Path, path: Path) -> None:
    """The axioms of each meaning theorem, from Lean's output on registry.lean: accepted if only the
    standard three, rejected if any other (sorryAx included), error if Lean printed nothing for it."""
    from physverify import lean_backend as lb
    store, log = load_store(path), (results / "registry.log").read_text(errors="replace")
    if (results / "registry.lean").read_text() != registry_source():
        raise ValueError("registry.lean on the Lean machine is not what `registry` writes now")
    reg = {}
    for kind, name in meaning_theorems().items():
        ax = lb._axioms(name, log)
        reg[kind] = {"theorem": name, "axioms": sorted(ax or []),
                     "status": "error" if ax is None else "accepted" if ax <= lb.STD_AXIOMS else "rejected"}
    wall, rss = (results / "registry.time").read_text().split()[-2:]
    store["registry"] = {"exit": int((results / "registry.exit").read_text().strip()), "seconds": float(wall),
                         "peak_rss_mb": round(int(rss) / 1024), "host": _host(results, store)["name"],
                         "theorems": reg}
    _write(store, path)
    print(json.dumps({k: v["status"] for k, v in reg.items()}, indent=1))


def summary(store: dict) -> dict:
    used = {h for s in store["specs"].values() for _, h in s["theorems"]}
    th = {h: store["theorems"][h] for h in used}
    out = {"specs": len(store["specs"]), "theorems": len(th),
           **{s: sum(t["status"] == s for t in th.values()) for s in STATUSES},
           "lean seconds (sum over theorems)": round(sum(t["seconds"] for t in th.values())),
           "by kind": {k: sum(s["kind"] == k for s in store["specs"].values())
                       for k in dict.fromkeys(s["kind"] for s in store["specs"].values())}}
    out["not accepted"] = {t["name"]: t["status"] for t in th.values() if t["status"] != "accepted"}
    return out


def _write(store: dict, path: Path, collected: bool = False) -> None:
    """Save the store; `collected`: the commit and Lean key are those of this collect run. `file_commit` is
    the commit the file is named after: `commit` unless set by hand (b2cafbe, see file_commit_note there)."""
    if collected or "commit" not in store:
        store["commit"], store["key"] = _git("rev-parse", "HEAD"), lean_key()
    store.setdefault("file_commit", store["commit"])
    store.setdefault("host", HOST)
    store["measured"] = datetime.date.today().isoformat()
    store["limits"] = {"per_theorem_s": LIMIT_S, "retry_s": RETRY_S}
    store["summary"] = summary(store)
    store.setdefault("runs", {})
    order = ["commit", "file_commit", "file_commit_note", "measured", "key", "host", "limits", "summary", "runs",
             "registry", "specs", "theorems"]
    path.write_text(json.dumps({k: store[k] for k in order}, indent=1, ensure_ascii=False) + "\n")


if __name__ == "__main__":
    args = sys.argv[1:]
    path = store_path()
    if "--store" in args:
        i = args.index("--store")
        path, args = Path(args[i + 1]), args[:i] + args[i + 2:]
    cmd = args[0] if args else "summary"
    if cmd == "collect":
        collect(path, args[1] if len(args) > 1 else None)
    elif cmd == "ingest":
        par = args[args.index("--parallel") + 1] if "--parallel" in args else 6
        ingest(Path(args[1]), path, retry="--retry" in args, parallel=int(par))
    elif cmd == "registry":
        WORK.mkdir(parents=True, exist_ok=True)
        (WORK / "registry.lean").write_text(registry_source())
        print(f"wrote {WORK / 'registry.lean'}: {len(meaning_theorems())} theorems")
    elif cmd == "ingest-registry":
        ingest_registry(Path(args[1]), path)
    else:
        print(json.dumps(summary(load_store(path)), indent=1))
