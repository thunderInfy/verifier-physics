"""Usage: uv run python benchmark/outside/run_heldout.py [--write]

Phase B of the heldout run: scores reader A1's blind readings of the 77 heldout items
(heldout_readings.json) against the frozen expected values in items.jsonl, the way run_dev.py scores dev,
measures agreement with reader A2 (heldout_readings_a2.json, 24 items) and runs A2's readings as a
reading-sensitivity check. With --write it stores heldout_verdicts.json and renders HELDOUT_RESULTS.md
from it (every number in the .md comes from the .json).

Nothing runs unless the pin holds: physverify/ and lean/ unchanged since the A0 commit, and both readings
files byte-identical to their readings commits (frozen_errors). The checker is never changed here.

Scorer code, not trusted code. It differs from run_dev.py in two places, both outside physverify/:
- overrides are deep-merged into the base spec (deep_merge). run_dev.py applies none to reconstruction
  claims, and bench._spec merges one level deep, which would replace the whole `weights` block of a spec by
  {"kind": "m"} and drop d, beta and q;
- a component's key includes its params as well as its override (run_dev._key keeps only the override when
  both are present, so two reconstruction components with one override would share the first one's params;
  no dev reading has both, so dev is unaffected).
A component whose spec (base + override) makes the checker raise is SPEC_ERROR; it is not repaired."""

from __future__ import annotations

import copy
import importlib.util
import json
import subprocess
import sys
from collections import Counter
from pathlib import Path

from physverify import reconstruction
from physverify.schemes import bench, check, claims as C

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent
SPECS = HERE / "specs"
_s = importlib.util.spec_from_file_location("run_dev", HERE / "run_dev.py")
D = importlib.util.module_from_spec(_s)
_s.loader.exec_module(D)
FIELDS, DECIDED = D.FIELDS, D.DECIDED

PIN = "b2cafbebed25a0aab659616eaafcd8db90c49426"
READINGS_COMMITS = {"heldout_readings.json": "2774e571164a245189a89a1fe7584340ddc3aac7",
                    "heldout_readings_a2.json": "0d16ffeda6c295d35c21f03c905998fd3086cd58"}
SPEC_ERROR = "SPEC_ERROR"

# sources the team read while building the checker; their items are reported apart, every headline with and
# without them
CONTAMINATED = {
    "henrick_aslam_powers_2005_mapped": "read directly while building reconstruction_order_p: the v1 reconstruction "
    "brief cited it for the critical-point expectations, WENO-M was built from its eq. (43), p. 557 and Table 10 "
    "(benchmark/reconstruction/weno5-m-fd.json, weno5-js-fd.json, weno3-js-fd.json; README.md, the WENO-M table)",
    "tadmor_2003_acta": "cited as a source of the semi-discrete entropy-stability check in the scheme-claims "
    "benchmark the checker was built against (benchmark/scheme-claims/claims.json, C03 and the E-scheme items; "
    "GAPS.md references), written 2026-11-26, before the outside benchmark existed. We cannot show which pages "
    "were read, so we treat it as read",
}
NOT_FOUND = ("shu1997_icase_notes", "gottlieb_shu_1998_tvdrk", "gottlieb_shu_tadmor_2001_ssp",
             "zhang_shu_2010_euler_positivity")
# results the heldout sources state that the checker's design or the dev specs also rest on, from textbooks and
# other papers; they cannot be excluded
TEXTBOOK = [
    "two-stage SSP (TVD) Runge-Kutta as a convex combination of forward Euler steps: dev spec "
    "ssp-rk2-upwind-advection.json (dev zhang_shu_2010_maxprinciple, mfa_oslo_notes:20), which three of the heldout "
    "readings reuse; the heldout gottlieb_shu_1998_tvdrk and gottlieb_shu_tadmor_2001_ssp state it",
    "Tadmor's semi-discrete entropy framework (entropy variables, F* = [psi]/[v], Q = -[v](F - F*) >= 0): the "
    "entropy_stability check and dev specs from fjordholm_mishra_tadmor_2012_tecno and tadmor_1987_viscosity; "
    "tadmor_2003_acta is a survey of the same framework",
    "WENO5 of Jiang and Shu (candidates, ideal weights, indicators): dev jiang_shu_1995_weno, dev spec "
    "jiang-shu-weno5-js-fd.json, which every heldout WENO reading reuses",
    "positivity-preserving limiters and Gauss-Lobatto decompositions: dev zhang_shu_2010_maxprinciple and "
    "zhang_shu_2011_survey, the same authors' framework as the heldout zhang_shu_2010_euler_positivity",
]

# A2 may not add specs: each formal component names the spec it needs in `spec_needed`. The scorer maps it to
# the spec (and override) that writes it; the tadmor:17 spec is new, written word for word from spec_needed
A2_SPECS = {
    "tadmor_2003_acta:12": {"spec": "tecno-entropy-conservative-burgers.json"},
    "tadmor_2003_acta:17": {"spec": "a2/tadmor-6-14-burgers-as-printed.json"},
    "henrick_aslam_powers_2005_mapped:05": {"spec": "jiang-shu-weno5-js-fd.json",
                                            "override": {"reconstruction": {"weights": {"kind": "m"}}}},
    "henrick_aslam_powers_2005_mapped:10": {"spec": "jiang-shu-weno5-js-fd.json",
                                            "override": {"reconstruction": {"weights": {"kind": "m"}}}},
}
A2_MAPPING_NOTES = [
    "tadmor_2003_acta:12: A2's first component carries params {\"form\": \"entropy_balance\"} on stated_identity, a "
    "scheme claim (params go with reconstruction claims only); the mapped spec's stated_identity has form "
    "entropy_balance already, so the params are dropped",
    "tadmor_2003_acta:12: A2's consistent component runs on the same spec, with `consistent` added to its named "
    "claims (as A1's override does)",
    "tadmor_2003_acta:17: the spec is specs/a2/tadmor-6-14-burgers-as-printed.json, written by the scorer from A2's "
    "spec_needed; [x]^+ = max(x, 0) is written (x + sqrt(x^2))/2. Erratum candidate only, never scored",
]
ERRATUM_ITEM = "tadmor_2003_acta:17"
ERRATUM_VARIANT = "a2/tadmor-6-14-burgers-with-dv-factor.json"

# every WRONG of the first run, classed by hand after it: (id, field) -> (class, one-line justification)
WRONG_CLASS: dict = {}
# syntax-only repairs of a SPEC_ERROR spec (a typo in a key name): (id, diff); none were needed
SYNTAX_FIXES: list = []
CHECKER_BUGS: list = []


def git(*args: str) -> bytes:
    return subprocess.run(["git", *args], cwd=ROOT, check=True, capture_output=True).stdout


def frozen_errors() -> list[str]:
    """The pin: physverify/ and lean/ as at PIN (in HEAD and in the working tree), and each readings file
    byte-identical at HEAD, on disk and at its readings commit, which is the last commit touching it."""
    errs = []
    for rev in (["HEAD"], []):
        if git("diff", "--name-only", PIN, *rev, "--", "physverify/", "lean/").strip():
            errs.append(f"physverify/ or lean/ differ between {PIN[:7]} and {rev[0] if rev else 'the working tree'}")
    for name, commit in READINGS_COMMITS.items():
        path = f"benchmark/outside/{name}"
        if not (git("show", f"{commit}:{path}") == git("show", f"HEAD:{path}") == (ROOT / path).read_bytes()):
            errs.append(f"{name} is not byte-identical to its readings commit {commit[:7]}")
        if git("log", "-1", "--format=%H", "HEAD", "--", path).decode().strip() != commit:
            errs.append(f"{name}: the last commit touching it is not {commit[:7]}")
    return errs


def heldout_items() -> dict:
    out = {}
    for line in (HERE / "items.jsonl").read_text().splitlines():
        item = json.loads(line)
        if D.half(item["source_id"]) == "heldout":
            out[item["id"]] = item
    return out


def stripped() -> dict:
    return {json.loads(l)["item_id"]: json.loads(l) for l in (HERE / "heldout_stripped.jsonl").read_text().splitlines()}


def load(name: str = "heldout_readings.json") -> dict:
    return json.loads((HERE / name).read_text())


def deep_merge(base, override):
    """override into base, recursively for dicts; any other value (lists included) replaces."""
    if isinstance(base, dict) and isinstance(override, dict):
        out = copy.deepcopy(base)
        for k, v in override.items():
            out[k] = deep_merge(base[k], v) if k in base else copy.deepcopy(v)
        return out
    return copy.deepcopy(override)


def merged_spec(c: dict) -> dict:
    return deep_merge(bench.load(SPECS / c["spec"]), c.get("override", {}))


def key(c: dict) -> tuple:
    return c["spec"], json.dumps(c.get("override", {}), sort_keys=True), json.dumps(c.get("params", {}), sort_keys=True)


def formal(r: dict) -> list[dict]:
    return [c for c in r["formalization"] if "unformalized" not in c]


def run(readings: list[dict], checker=check) -> dict:
    """key -> {named claim: {"verdict", "guarantee", "detail"}}, one checker call per spec, override and params."""
    groups: dict = {}
    for r in readings:
        for c in formal(r):
            groups.setdefault(key(c), (c, []))[1].append(c["claim"])
    out = {}
    for k, (c, names) in groups.items():
        names = list(dict.fromkeys(names))
        try:
            spec = merged_spec(c)
            if c["claim"] in reconstruction.CLAIMS:
                out[k] = {}
                for n in names:
                    v = reconstruction.check_claim(spec["reconstruction"], {"claim": n, **c["params"]})
                    out[k][n] = {"verdict": v["verdict"], "guarantee": "exact (reconstruction_order_p)",
                                 "detail": v.get("detail", "")}
                continue
            # bench._spec merges one level deep; handing it the deep-merged top-level values gives the merged spec
            report = checker(bench._spec(SPECS, c["spec"], {t: spec[t] for t in c.get("override", {})}, names))
            out[k] = {v["claim"]: {"verdict": v["verdict"], "guarantee": v.get("guarantee", ""),
                                   "detail": v.get("detail", "")} for v in report["claims"]}
        except Exception as e:  # noqa: BLE001: the spec, not the scorer, is at fault; recorded, not repaired
            out[k] = {n: {"verdict": SPEC_ERROR, "guarantee": "", "detail": f"{type(e).__name__}: {e}"} for n in names}
    return out


def reading_verdict(r: dict, V: dict) -> dict:
    comps = []
    for c in r["formalization"]:
        if "unformalized" in c:
            comps.append({"named": bench.UNFORMALIZED, "reading": bench.UNFORMALIZED})
            continue
        v = V[key(c)][c["claim"]]["verdict"]
        if v == SPEC_ERROR:
            comps.append({"named": v, "reading": v})
            continue
        t = bench.through(c.get("relation", "same"), v)
        comps.append({"named": v, "reading": D.NEGATE.get(t, t) if c.get("negated") else t})
    reads = [x["reading"] for x in comps]
    return {"verdict": SPEC_ERROR if SPEC_ERROR in reads else bench.conjunction(reads), "components": comps}


def score(expected: str, verdict: str) -> str:
    return SPEC_ERROR if verdict == SPEC_ERROR else D.score(expected, verdict)


def field_score(scores: list[str]) -> str:
    for s in ("BUG", "WRONG", "MATCH", SPEC_ERROR):
        if s in scores:
            return s
    return scores[0]


def evaluate(data: dict, items: dict, V: dict) -> list[dict]:
    rows = []
    for e in data["items"]:
        item = items[e["id"]]
        actual = [reading_verdict(r, V) for r in e["readings"]]
        scores = {}
        for f in FIELDS:
            mine = [score(item[f"expected_{f}"], a["verdict"]) for r, a in zip(e["readings"], actual)
                    if f in D.fields_of(r)]
            scores[f] = field_score(mine) if mine else ("UNSCORED" if item[f"expected_{f}"] == "UNSURE" else "GAP")
        rows.append({"id": e["id"], "source": item["source_id"], "expected": {f: item[f"expected_{f}"] for f in FIELDS},
                     "stated": bool(e["readings"]), "score": scores,
                     "readings": [{"fields": D.fields_of(r), "reading": r["reading"], **a}
                                  for r, a in zip(e["readings"], actual)]})
    return rows


def inherited(r: dict, view: dict) -> list[str]:
    """Verdict-relevant parameters of the reused dev spec that neither the reading nor the reader view fixes."""
    text = view["scheme"]["definition"]
    out = []
    for c in formal(r):
        if c["spec"] == "jiang-shu-weno5-js-fd.json":
            if "p = 2" not in text and "q = 2" not in text:
                out.append("q = 2, the power in alpha_k = d_k/(eps + beta_k)^q (the view prints the power as p, "
                           "without a value)")
            if "β_0 =" not in text:
                out.append("the smoothness indicators beta_k (the view cites (37) without printing them)")
    return list(dict.fromkeys(out))


def tally(rows: list[dict]) -> dict:
    reads = [a for r in rows for a in r["readings"]]
    sc = {f: Counter(r["score"][f] for r in rows) for f in FIELDS}
    wrong = [(r["id"], f) for r in rows for f in FIELDS if r["score"][f] in ("WRONG", "BUG")]
    cls = Counter(WRONG_CLASS.get(w, ("unclassed",))[0] for w in wrong)
    return {
        "items": len(rows),
        "stated": sum(r["stated"] for r in rows),
        "stated_by_field": {f: sum(any(f in a["fields"] for a in r["readings"]) for r in rows) for f in FIELDS},
        "readings": len(reads),
        "decided_readings": sum(a["verdict"] in DECIDED for a in reads),
        "verdicts": dict(sorted(Counter(a["verdict"] for a in reads).items())),
        "scores": {f: dict(sorted(sc[f].items())) for f in FIELDS},
        "decided_fields": sum(sc[f]["MATCH"] + sc[f]["WRONG"] for f in FIELDS),
        "match": sum(sc[f]["MATCH"] for f in FIELDS),
        "wrong": len(wrong),
        "wrong_checker": cls["checker"],
        "wrong_reading": cls["reading"],
        "spec_error": sum(sc[f][SPEC_ERROR] for f in FIELDS),
        "gap": sum(sc[f]["GAP"] for f in FIELDS),
        "unscored": sum(sc[f]["UNSCORED"] for f in FIELDS),
    }


def unformalized_primary(e: dict) -> dict:
    return {f: D.primary(u["reasons"]) for u in e["unformalized"] for f in D.fields_of(u)}


def kinds(r: dict) -> list:
    return sorted([c["claim"], c.get("relation", "same"), bool(c.get("negated")),
                   (c.get("params") or {}).get("form"), (c.get("params") or {}).get("regime"),
                   (c.get("params") or {}).get("n_cp")] for c in formal(r))


def a2_formal(e: dict) -> dict:
    """A2's readings with each null spec replaced by the scorer's mapping (A2_SPECS)."""
    m = A2_SPECS.get(e["id"])
    out = copy.deepcopy(e)
    for r in out["readings"]:
        for c in formal(r):
            c["spec"] = m["spec"]
            if "override" in m:
                c["override"] = m["override"]
            if c["claim"] not in reconstruction.CLAIMS:
                c.pop("params", None)
            if c["claim"] == "consistent":
                c["override"] = {"named_claims": ["stated_identity", "consistent"]}
    return out


def params_of(r: dict) -> list:
    return sorted([c["claim"], c["spec"], json.dumps(c.get("override", {}), sort_keys=True),
                   (c.get("params") or {}).get("p"), (c.get("params") or {}).get("eps"), bool(c.get("negated"))]
                  for c in formal(r))


def agreement(a1: dict, a2: dict) -> dict:
    by1 = {e["id"]: e for e in a1["items"]}
    subset = (HERE / "heldout_subset_a2.txt").read_text().split()
    assert [e["id"] for e in a2["items"]] == subset
    rows, same_stat_items, same_stat_fields, both_unf, same_reason, both_form = [], 0, 0, 0, 0, []
    for e2 in a2["items"]:
        e1 = by1[e2["id"]]
        same_stat_items += bool(e1["readings"]) == bool(e2["readings"])
        p1, p2 = unformalized_primary(e1), unformalized_primary(e2)
        for f in FIELDS:
            same_stat_fields += (f in p1) == (f in p2)
            if f in p1 and f in p2:
                both_unf += 1
                same_reason += p1[f] == p2[f]
                if p1[f] != p2[f]:
                    rows.append({"id": e2["id"], "field": f, "A1": p1[f], "A2": p2[f]})
            if f not in p1 and f not in p2:
                r1 = [r for r in e1["readings"] if f in D.fields_of(r)]
                r2 = [r for r in a2_formal(e2)["readings"] if f in D.fields_of(r)]
                k_same = [kinds(r) for r in r1] == [kinds(r) for r in r2]
                n_unf = [len(r["formalization"]) - len(formal(r)) for r in r1] == \
                        [len(r["formalization"]) - len(formal(r)) for r in r2]
                p_same = [params_of(r) for r in r1] == [params_of(r) for r in r2]
                both_form.append({"id": e2["id"], "field": f, "same_kinds_quantifiers": k_same,
                                  "same_unformalized_parts": n_unf, "same_parameters": k_same and p_same})
            if (f in p1) != (f in p2):
                rows.append({"id": e2["id"], "field": f, "A1": p1.get(f, "formalized"), "A2": p2.get(f, "formalized")})
    return {
        "items": len(subset),
        "same_statable_items": same_stat_items,
        "fields": 2 * len(subset),
        "same_statable_fields": same_stat_fields,
        "both_unformalized_fields": both_unf,
        "same_primary_reason": same_reason,
        "both_formalized_fields": len(both_form),
        "same_kinds_quantifiers": sum(x["same_kinds_quantifiers"] for x in both_form),
        "same_parameters": sum(x["same_parameters"] for x in both_form),
        "same_unformalized_parts": sum(x["same_unformalized_parts"] for x in both_form),
        "both_formalized": both_form,
        "disagreements": rows,
    }


WENO_M = {"spec": "jiang-shu-weno5-js-fd.json", "override": {"reconstruction": {"weights": {"kind": "m"}}},
          "claim": "reconstruction_order_p",
          "params": {"p": 5, "form": "flux_difference", "regime": "critical", "eps": "0", "n_cp": 1}}


def override_demo() -> dict:
    """The WENO-M override changes the verdict: the merged spec is not scored with the base (Jiang-Shu) weights."""
    base = {k: x for k, x in WENO_M.items() if k != "override"}
    return {"component": WENO_M, "merged": run([{"formalization": [WENO_M]}])[key(WENO_M)][WENO_M["claim"]]["verdict"],
            "base": run([{"formalization": [base]}])[key(base)][base["claim"]]["verdict"]}


def entropy_check(spec: str, checker=check) -> dict:
    report = checker(bench._spec(SPECS, spec, {}, ["entropy_stable_tadmor"]))
    c = [x for x in report["checks"] if x["check"] == "entropy_stability"][0]
    return {"spec": spec, "claim_verdict": report["claims"][0]["verdict"], "check_status": c["status"],
            "guarantee": c["guarantee"], "detail": c["detail"]}


def compute(checker=check) -> dict:
    errs = frozen_errors()
    if errs:
        raise SystemExit("pin broken:\n" + "\n".join(errs))
    items, view = heldout_items(), stripped()
    a1, a2 = load(), load("heldout_readings_a2.json")
    errs = [x.replace("dev_readings.json", "heldout_readings.json").replace("dev item", "heldout item")
            for x in D.validate(a1, items)]
    if errs:
        raise SystemExit("\n".join(errs))
    a1_readings = [r for e in a1["items"] for r in e["readings"]]
    V = run(a1_readings, checker)
    rows = evaluate(a1, items, V)
    for e, row in zip(a1["items"], rows):
        for r, out in zip(e["readings"], row["readings"]):
            out["inherited"] = inherited(r, view[e["id"]])
    for row in rows:
        for f in FIELDS:
            if row["score"][f] in ("WRONG", "BUG"):
                c = WRONG_CLASS.get((row["id"], f), ("unclassed", ""))
                row.setdefault("wrong_class", {})[f] = {"class": c[0], "why": c[1]}
    clean = [r for r in rows if r["source"] not in CONTAMINATED]
    no_h = [r for r in rows if r["source"] != "henrick_aslam_powers_2005_mapped"]
    # A2: the mapped readings, run on the same checker; tadmor:17 is the erratum candidate, never scored
    a2m = {"about": a2["about"], "items": [a2_formal(e) for e in a2["items"]]}
    sub_items = {e["id"]: items[e["id"]] for e in a2m["items"]}
    VA2 = run([r for e in a2m["items"] for r in e["readings"]], checker)
    a2rows = [x for x in evaluate(a2m, sub_items, VA2) if x["stated"]]
    by_id = {r["id"]: r for r in rows}
    sens = []
    for x in a2rows:
        for f in FIELDS:
            if any(f in a["fields"] for a in x["readings"]):
                sens.append({"id": x["id"], "field": f, "A2_verdict": [a["verdict"] for a in x["readings"]
                                                                        if f in a["fields"]][0],
                             "A2_score": "ERRATUM_CANDIDATE" if x["id"] == ERRATUM_ITEM else x["score"][f],
                             "A1_score": by_id[x["id"]]["score"][f]})
    er = [x for x in a2rows if x["id"] == ERRATUM_ITEM][0]
    erratum = {"id": ERRATUM_ITEM, "expected": er["expected"], "A2_reading": er["readings"][0]["reading"],
               "A2_reading_verdict": er["readings"][0]["verdict"],
               "as_printed": entropy_check(A2_SPECS[ERRATUM_ITEM]["spec"], checker),
               "with_dv_factor": entropy_check(ERRATUM_VARIANT, checker)}
    dev = json.loads((HERE / "dev_readings.json").read_text())["items"]
    dev_sc = Counter(e["score"][f] for e in dev for f in FIELDS)
    spec_log = [{"id": r["id"], "fields": a["fields"], "inherited": a["inherited"]} for r in rows for a in r["readings"]]
    return {
        "about": "Phase B scores of the heldout half (generated by run_heldout.py; HELDOUT_RESULTS.md is rendered "
                 "from this file). Only reader A1's readings count for the headline.",
        "pin": {"checker": PIN, "readings_commits": READINGS_COMMITS},
        "contaminated": CONTAMINATED,
        "contaminated_items": [r["id"] for r in rows if r["source"] in CONTAMINATED],
        "headline": {"all": tally(rows), "without henrick_aslam_powers_2005_mapped": tally(no_h),
                     "without both contaminated sources": tally(clean)},
        "by_source": {s: tally([r for r in rows if r["source"] == s]) for s in dict.fromkeys(r["source"] for r in rows)},
        "dev_for_context": {"items": len(dev), "stated": sum(bool(e["readings"]) for e in dev),
                            "match": dev_sc["MATCH"], "wrong": dev_sc["WRONG"] + dev_sc["BUG"]},
        "rows": rows,
        "spec_choice_log": spec_log,
        "spec_choice_readings_with_inherited": sum(bool(x["inherited"]) for x in spec_log),
        "agreement": agreement(a1, a2),
        "a2_sensitivity": sens,
        "a2_mapping_notes": A2_MAPPING_NOTES,
        "erratum_candidate": erratum,
        "override_demo": override_demo(),
        "syntax_fixes": SYNTAX_FIXES,
        "checker_bugs": CHECKER_BUGS,
    }


def main(argv: list[str]) -> int:
    out = compute()
    if "--write" in argv:
        (HERE / "heldout_verdicts.json").write_text(json.dumps(out, indent=1, ensure_ascii=False) + "\n")
        (HERE / "HELDOUT_RESULTS.md").write_text(render(out))
    print(json.dumps(out["headline"], indent=1))
    return 0


def _table(head: list[str], rows: list[list]) -> list[str]:
    return ["| " + " | ".join(head) + " |", "|" + "---|" * len(head)] + \
           ["| " + " | ".join(str(x) for x in r) + " |" for r in rows]


def render(v: dict) -> str:
    """HELDOUT_RESULTS.md from heldout_verdicts.json: every number below is read from v."""
    h, a, e = v["headline"], v["agreement"], v["erratum_candidate"]
    al = h["all"]
    L = ["# Heldout results (phase B)", "",
         "Generated by `run_heldout.py --write` from `heldout_verdicts.json`; do not edit by hand (a test checks that",
         "this file is the rendering of that one). Scored the way `run_dev.py` scores dev: per item and expected field,",
         "MATCH is VERIFIED on TRUE or REFUTED on FALSE, WRONG a decisive verdict against TRUE/FALSE, GAP no decisive",
         "verdict (or no reading) on TRUE/FALSE, UNSCORED an UNSURE expectation. Only reader A1's readings count.", "",
         "## Pin", "",
         f"- Checker: `{v['pin']['checker']}`; `git diff` of `physverify/` and `lean/` against it is empty at HEAD and in",
         "  the working tree (asserted by `frozen_errors()` before anything runs, and by `tests/test_outside_heldout.py`).",
         ]
    for name, c in v["pin"]["readings_commits"].items():
        L.append(f"- `{name}`: byte-identical at HEAD, on disk and at its readings commit `{c}`, the last commit touching it.")
    L += ["- Lean was not run: every verdict is the Python checker's (exact verdicts are Fraction arithmetic, their",
          "  Lean certificates pending, as the checker reports).", "",
          "## Headline", "",
          f"A1 gave a formal reading for {al['stated']} of the {al['items']} heldout items ({al['readings']} readings). "
          f"Coverage by field: alone {al['stated_by_field']['alone']}/{al['items']}, with hypotheses "
          f"{al['stated_by_field']['with_hypotheses']}/{al['items']}.", ""]
    head = ["", "items", "stated", "readings", "decided readings", "decided fields", "MATCH", "WRONG",
            "WRONG checker", "WRONG reading", "SPEC_ERROR", "GAP", "UNSCORED"]
    L += _table(head, [[k, t["items"], f"{t['stated']}/{t['items']}", t["readings"], t["decided_readings"],
                        t["decided_fields"], t["match"], t["wrong"], t["wrong_checker"], t["wrong_reading"],
                        t["spec_error"], t["gap"], t["unscored"]] for k, t in h.items()])
    clean = h["without both contaminated sources"]
    L += ["", "Fields are counted twice per item (alone, with hypotheses), so MATCH + WRONG + SPEC_ERROR + GAP + UNSCORED "
          f"= 2 x items. Verdicts of A1's readings: {', '.join(f'{k} {n}' for k, n in al['verdicts'].items())}.", "",
          f"**Every decided field ({al['decided_fields']}) is on a contaminated source.** Without them A1 stated "
          f"{clean['stated']} of {clean['items']} items and the checker decided {clean['decided_fields']} fields: on "
          "uncontaminated heldout sources this run measures nothing about verdict accuracy, only coverage.", "",
          "WRONG: none" if not al["wrong"] else "WRONG, each classed:", ""]
    for r in v["rows"]:
        for f, c in r.get("wrong_class", {}).items():
            L.append(f"- `{r['id']}` {f}: {c['class']}: {c['why']}")
    L += ["", "By source:", ""]
    L += _table(["source", "items", "stated", "decided fields", "MATCH", "WRONG", "GAP", "UNSCORED"],
                [[f"`{s}`" + (" (contaminated)" if s in v["contaminated"] else ""), t["items"], t["stated"],
                  t["decided_fields"], t["match"], t["wrong"], t["gap"], t["unscored"]] for s, t in v["by_source"].items()])
    L += ["", "## Stated items", ""]
    L += _table(["id", "expected (alone / hyp.)", "reading fields", "components (named verdicts)", "verdict",
                 "score (alone / hyp.)"],
                [[f"`{r['id']}`", f"{r['expected']['alone']} / {r['expected']['with_hypotheses']}", ", ".join(rd["fields"]),
                  ", ".join(c["named"] for c in rd["components"]), rd["verdict"],
                  f"{r['score']['alone']} / {r['score']['with_hypotheses']}"]
                 for r in v["rows"] for rd in r["readings"]])
    L += ["", "A component the reader left unformalized is UNFORMALIZED; a conjunction with one is at best UNKNOWN (a",
          "reading is decided VERIFIED only if every part is). The three SSP readings and henrick:10 are GAPs for this",
          "reason alone: their formal part is VERIFIED.", "",
          "## Contamination", "",
          "Sources the team read while building the checker; their items are reported apart above (rows without them).", ""]
    for s, why in v["contaminated"].items():
        L.append(f"- `{s}`: {why}.")
    L += ["", f"Contaminated items ({len(v['contaminated_items'])}): " +
          ", ".join(f"`{i}`" for i in v["contaminated_items"]) + ".", "",
          "Searched (commit messages, `git grep` of the pinned tree outside the collection files items.jsonl, FROZEN.md, "
          "SOURCES.md, SAMPLING.md, COVERAGE.md, skipped.jsonl, and DEV_RESULTS.md) and not found as read while building: "
          + ", ".join(f"`{s}`" for s in NOT_FOUND) + ".", "",
          "Limitation, not excludable: textbook results the heldout sources also state, which the checker or the dev "
          "specs rest on:", ""]
    L += [f"- {t}" for t in TEXTBOOK]
    dv = v["dev_for_context"]
    L += ["", "## Confounds", "",
          f"For context, dev: {dv['stated']}/{dv['items']} items stated, {dv['match']} MATCH, {dv['wrong']} WRONG "
          f"(stored scores in dev_readings.json). Heldout: {al['stated']}/{al['items']} stated, {al['match']} MATCH, "
          f"{al['wrong']} WRONG. The gap between them is not a generalisation measurement alone:", "",
          "1. Dev readers saw the expected values and the collector's `property` tag (a coarse claim-kind hint); the",
          "   heldout readers saw neither (`heldout_stripped.jsonl`: sentence, scheme, hypotheses, location).",
          "2. Both heldout readers opened FROZEN.md, which holds the aggregate heldout expected-value tallies and",
          "   property-tag counts (not per item).",
          "3. The dev specs were written with checker access, and A1's heldout readings reuse them with overrides, so the",
          "   heldout formalisations inherit checker-informed choices (see the spec-choice log).",
          "4. The sources are new. A dev -> heldout gap mixes new sources, blind readers, a less informative view and",
          "   checker-informed specs; and here the decided heldout fields all lie on contaminated sources.", "",
          "## Overrides", "",
          "`run_dev.py` does not apply A1's overrides as written: its reconstruction path reads the base spec and ignores",
          "`override`, and `bench._spec` merges one level deep, so `{\"reconstruction\": {\"weights\": {\"kind\": \"m\"}}}`",
          "would replace the whole weights block (dropping d, beta, q). `run_heldout.py` deep-merges each override into",
          "its base spec (scorer code; physverify unchanged). The test shows the merged WENO-M spec equals the hand-edited",
          "one and decides differently from the base spec (flux difference, n_cp = 1, eps = 0, p = 5: "
          f"{v['override_demo']['merged']} merged, {v['override_demo']['base']} base).",
          "The tadmor:12 override (`named_claims` with `consistent`) is honoured: the scorer asks the checker for the",
          "named claim of each component.", "",
          "## SPEC_ERROR and syntax fixes", "",
          f"SPEC_ERROR fields: {al['spec_error']}. Syntax-only fixes: "
          + ("none." if not v["syntax_fixes"] else ""), ""]
    for i, diff in v["syntax_fixes"]:
        L += [f"- `{i}`:", "```diff", diff, "```"]
    n_inh = v["spec_choice_readings_with_inherited"]
    L += ["## Spec-choice log", "",
          "Verdict-relevant parameters of the reused dev spec that neither the reading nor the reader view determines.",
          f"Readings with at least one: {n_inh} of {len(v['spec_choice_log'])}.", ""]
    L += _table(["id", "fields", "inherited from the dev spec"],
                [[f"`{x['id']}`", ", ".join(x["fields"]), "; ".join(x["inherited"]) or "none"] for x in v["spec_choice_log"]])
    L += ["", "The SSP and entropy-conservative readings name their operator, flux and entropy pair in the narrowing,",
          "so nothing is listed for them; that the narrowing picks the instance a dev spec already writes is confound 3.", "",
          "## Reader agreement (A1 vs A2, the 24-item subset)", "",
          f"- (i) same statable/not decision: {a['same_statable_items']}/{a['items']} items, "
          f"{a['same_statable_fields']}/{a['fields']} fields.",
          f"- (ii) fields both left unformalized: {a['both_unformalized_fields']}; same primary reason code: "
          f"{a['same_primary_reason']}/{a['both_unformalized_fields']}.",
          f"- (iii) fields both formalized: {a['both_formalized_fields']}; same claim kinds and quantifiers (claim, "
          f"relation, negation, form, regime, n_cp): {a['same_kinds_quantifiers']}/{a['both_formalized_fields']}; "
          f"then same verdict-relevant parameters (spec after mapping, override, p, eps): "
          f"{a['same_parameters']}/{a['both_formalized_fields']}; same number of unformalized parts: "
          f"{a['same_unformalized_parts']}/{a['both_formalized_fields']}.", "",
          "A2 names the spec it needs in words (`spec_needed`); for (iii) and for the sensitivity run the scorer maps it",
          "to a spec of specs/, so agreement on the spec itself is partly the scorer's doing; p, eps, n_cp, regime and",
          "negation are A2's own:", ""]
    L += [f"- {n}" for n in v["a2_mapping_notes"]]
    L += ["", "Disagreements (primary reason, or `formalized`):", ""]
    L += _table(["id", "field", "A1", "A2"], [[f"`{d['id']}`", d["field"], d["A1"], d["A2"]] for d in a["disagreements"]])
    L += ["", "## Reading sensitivity (checker on A2's readings; not part of the headline)", ""]
    L += _table(["id", "field", "A2 verdict", "A2 score", "A1 score"],
                [[f"`{s['id']}`", s["field"], s["A2_verdict"], s["A2_score"], s["A1_score"]] for s in v["a2_sensitivity"]])
    scored = [s for s in v["a2_sensitivity"] if s["A2_score"] != "ERRATUM_CANDIDATE"]
    L += ["", f"On the fields both readers stated, A2's readings score as A1's on "
          f"{sum(s['A2_score'] == s['A1_score'] for s in scored)}/{len(scored)}.", "",
          f"## Erratum candidate: `{e['id']}` (never scored)", "",
          f"Expected values: {e['expected']['alone']} / {e['expected']['with_hypotheses']}. A1 left the item "
          "unformalized; A2 read it as: " + e["A2_reading"] + ".", "",
          "A2 noted, from a hand calculation (not a checker run; reported with its pass, not recorded in",
          "heldout_readings_a2.json), that the scheme (6.14) as printed may not be",
          "entropy stable once |uR - uL| > 1.5. The checker, on A2's reading (N = 1, Burgers, U = u^2/2, the viscosity",
          "term (1/8)[a(uR) - a(uL)]^+ without the <l, Dv> factor that (6.13) carries):", "",
          f"- as printed (`specs/{e['as_printed']['spec']}`): `entropy_stable_tadmor` {e['as_printed']['claim_verdict']}, "
          f"guarantee {e['as_printed']['guarantee']}. {e['as_printed']['detail']}.",
          f"- with the <l, Dv> = uR - uL factor of (6.13) (`specs/{e['with_dv_factor']['spec']}`, a scorer variant, "
          f"not a reading): {e['with_dv_factor']['claim_verdict']}, guarantee {e['with_dv_factor']['guarantee']}. "
          f"{e['with_dv_factor']['detail']}.", "",
          "By hand, for D = uR - uL: F - F* = D^2/12 - [D]^+/8, so Q = -D (F - F*) = D^2 (1/8 - D/12) for D > 0 and",
          "-D^3/12 for D < 0: Q < 0 exactly when D > 3/2, A2's threshold. With the factor, Q = D^3/24 for D > 0.",
          "The statement as printed, under our reading, fails semi-discrete entropy stability (an exact check);",
          "with the <l, Dv> factor of (6.13) on the viscosity term it holds. The second-order part is not checked.",
          "Credit for the hand calculation: reader A2. Proposed in ERRATA_PROPOSED.md (heldout section).", "",
          "## Checker bugs and re-score", ""]
    if not v["checker_bugs"]:
        L += ["No checker bug was found while scoring, so there is no re-score section: the headline is the first run.",
              "The two scorer-side issues (overrides not deep-merged, run_dev's component key dropping params when an",
              "override is present) are in scorer code, were handled before the first run, and change no dev score."]
    return "\n".join(L) + "\n"


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
