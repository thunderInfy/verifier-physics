"""Usage: uv run python papers/scheme-claims/measure_lean.py collect | ingest RESULTS [--host H] | summary

The measured Lean run behind the paper's Lean-label numbers, stored in lean_measured.json.

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
    ingest    read a results directory of lean_run_jobs.sh (run on the Lean machine) into the store
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
STORE = HERE / "lean_measured.json"
WORK = ROOT / "lean" / "build_certs" / "measure"
# what a theorem's text and its fate depend on: the Lean project (toolchain and Mathlib rev included), the
# judges and planners that write the statements and proofs, and the checks whose witnesses the planners use
KEY_PATHS = ("lean", "physverify/lean_backend.py", "physverify/schemes", "physverify/tools", "physverify/variational.py",
             "physverify/kernel.py", "physverify/expr.py", "physverify/derivation.py")
HOST = {"name": "lean-build", "machine": "GCP e2-standard-8", "cpus": 8, "ram_gb": 32}
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


def load_store() -> dict:
    return json.loads(STORE.read_text()) if STORE.is_file() else {"theorems": {}, "specs": {}}


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

def collect(only: str | None = None) -> int:
    store, key, commit = load_store(), lean_key(), _git("rev-parse", "HEAD")
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
    _write(store, collected=True)
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


def ingest(results: Path, host: dict = HOST, retry: bool = False, parallel: int = 6) -> None:
    store = load_store()
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
    _write(store)
    print(f"ingested {n} theorems from {results}")


def summary(store: dict | None = None) -> dict:
    store = store or load_store()
    used = {h for s in store["specs"].values() for _, h in s["theorems"]}
    th = {h: store["theorems"][h] for h in used}
    out = {"specs": len(store["specs"]), "theorems": len(th),
           **{s: sum(t["status"] == s for t in th.values()) for s in STATUSES},
           "lean seconds (sum over theorems)": round(sum(t["seconds"] for t in th.values())),
           "by kind": {k: sum(s["kind"] == k for s in store["specs"].values())
                       for k in dict.fromkeys(s["kind"] for s in store["specs"].values())}}
    out["not accepted"] = {t["name"]: t["status"] for t in th.values() if t["status"] != "accepted"}
    return out


def _write(store: dict, collected: bool = False) -> None:
    """Save the store; `collected`: the commit and Lean key are those of this collect run."""
    if collected or "commit" not in store:
        store["commit"], store["key"] = _git("rev-parse", "HEAD"), lean_key()
    store["host"] = HOST
    store["measured"] = datetime.date.today().isoformat()
    store["limits"] = {"per_theorem_s": LIMIT_S, "retry_s": RETRY_S}
    store["summary"] = summary(store)
    store.setdefault("runs", {})
    order = ["commit", "measured", "key", "host", "limits", "summary", "runs", "specs", "theorems"]
    STORE.write_text(json.dumps({k: store[k] for k in order}, indent=1, ensure_ascii=False) + "\n")


if __name__ == "__main__":
    cmd = sys.argv[1] if len(sys.argv) > 1 else "summary"
    if cmd == "collect":
        collect(sys.argv[2] if len(sys.argv) > 2 else None)
    elif cmd == "ingest":
        par = sys.argv[sys.argv.index("--parallel") + 1] if "--parallel" in sys.argv else 6
        ingest(Path(sys.argv[2]), retry="--retry" in sys.argv, parallel=int(par))
    else:
        print(json.dumps(summary(), indent=1))
