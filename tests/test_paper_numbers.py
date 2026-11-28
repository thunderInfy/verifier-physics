"""Every reproducibility marker in the paper (papers/scheme-claims/main.tex) names a target that exists:
a pytest test `tests/X.py::name` or a function `paper_numbers.py::name` of papers/scheme-claims/paper_numbers.py
(static: the files are parsed). No number is typed into the text's \\rn markers: each takes its value by key
from numbers.tex, which paper_numbers.py generates. The other tests check the generated files against their
sources, each measured Lean run (lean_measured_<commit>.json) against the commit it names and one of them
against HEAD, and a few numbers the text derives by hand."""
import ast
import functools
import json
import re
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
PAPER = ROOT / "papers" / "scheme-claims"
TARGET = re.compile(r"\{((?:tests/[\w/]+\.py|paper_numbers\.py)::\w+)\}")
RN_KEY = re.compile(r"\\rn\{([A-Za-z][\w.\-]*)\}(?!\{)")      # \rn{KEY}, one argument, KEY not a number
HINT = "run: uv run python papers/scheme-claims/paper_numbers.py --write-table"


def _functions(path: Path) -> set[str]:
    return {n.name for n in ast.parse(path.read_text()).body if isinstance(n, ast.FunctionDef)}


def _tex_sources() -> dict[str, str]:
    """main.tex and every .tex file it inputs (recursively), with comments dropped."""
    out, todo = {}, ["main.tex"]
    while todo:
        name = todo.pop()
        out[name] = re.sub(r"(?<!\\)%.*", "", (PAPER / name).read_text())
        todo += [n for n in re.findall(r"\\input\{([^}]+\.tex)\}", out[name]) if n not in out and n not in todo]
    return out


def _rn_keys() -> list[str]:
    return [k for text in _tex_sources().values() for k in RN_KEY.findall(text)]


@functools.cache
def _paper_numbers():
    import importlib.util
    spec = importlib.util.spec_from_file_location("paper_numbers", PAPER / "paper_numbers.py")
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


@functools.cache
def _out(name: str) -> dict:
    """paper_numbers.py's function `name`, run once per test session (several take minutes)."""
    return _paper_numbers().ALL[name]()


def test_every_repro_target_resolves():
    """Every \\repro marker in the text and every target numbers.tex gives an \\rn names a test or function
    that exists."""
    tex = "".join(t for name, t in _tex_sources().items() if name != "numbers.tex")
    markers = len(re.findall(r"\\repro\{", tex))
    targets = TARGET.findall(tex)
    assert markers > 0 and len(targets) == markers, "a marker has a target that is not FILE::FUNCTION"
    targets += [f"paper_numbers.py::{fn}" for fn, *_ in _paper_numbers().NUMBERS.values()]
    missing = []
    for t in sorted(set(targets)):
        file, name = t.split("::")
        path = PAPER / file if file == "paper_numbers.py" else ROOT / file
        if not path.is_file() or name not in _functions(path):
            missing.append(t)
    assert not missing, missing


def test_no_number_is_typed_into_an_rn():
    """Every \\rn in main.tex and the files it inputs is \\rn{KEY}: one argument, a key, never a literal value
    (and no second argument, as the old \\rn{value}{target} had). numbers.tex is input once, before any \\rn."""
    sources = _tex_sources()
    for name, text in sources.items():
        uses = re.findall(r"\\rn\{", text)
        bad = [text[m.start():m.start() + 60] for m in re.finditer(r"\\rn\{", text) if not RN_KEY.match(text, m.start())]
        assert not bad, (name, bad)
        assert len(RN_KEY.findall(text)) == len(uses)
    assert "numbers.tex" in sources and sources["main.tex"].count("\\input{numbers.tex}") == 1
    assert sources["main.tex"].index("\\input{numbers.tex}") < sources["main.tex"].index("\\begin{document}")
    assert len(_rn_keys()) > 100


def test_every_rn_key_is_one_paper_numbers_defines():
    """Every key an \\rn uses is an entry of paper_numbers.NUMBERS (and numbers.tex defines it); every entry is
    used, so the table holds nothing the paper does not print."""
    pn = _paper_numbers()
    used = set(_rn_keys())
    assert not used - set(pn.NUMBERS), sorted(used - set(pn.NUMBERS))
    assert not set(pn.NUMBERS) - used, sorted(set(pn.NUMBERS) - used)
    defined = re.findall(r"^\\pnset\{([^}]+)\}", (PAPER / "numbers.tex").read_text(), re.M)
    assert defined == list(pn.NUMBERS), "numbers.tex is not NUMBERS: " + HINT


def test_numbers_tex_is_what_paper_numbers_gives_now():
    """numbers.tex is what paper_numbers.py generates now from the data files and the checker."""
    pn = _paper_numbers()
    outputs = {fn: _out(fn) for fn in dict.fromkeys(fn for fn, *_ in pn.NUMBERS.values())}
    assert (PAPER / "numbers.tex").read_text() == pn._numbers_tex(outputs), HINT


def test_lean_stores_are_named_explicitly():
    """The paper's Lean numbers read two named stores, never "the latest": the pin (b2cafbe) and the
    re-measurement on main (f09a5cb). A newer lean_measured_*.json next to them does not move the paper."""
    pn = _paper_numbers()
    assert pn.PAPER_STORE.name == "lean_measured_b2cafbe.json" and pn.MAIN_STORE.name == "lean_measured_f09a5cb.json"
    assert _measure_lean().PAPER_STORE == pn.PAPER_STORE
    src = (PAPER / "paper_numbers.py").read_text()
    assert "load_store()" not in src and "store_paths" not in src


def test_pin_store_was_collected_on_the_pins_verifier_code():
    """lean_measured_b2cafbe.json was collected at 1d73a80 (`commit`) and carries b2cafbe's Lean key
    (`file_commit`). The abstract says the verifier code (physverify/, lean/, the specs) of the two commits is
    identical, not the trees: between them only papers/, README.md, benchmark/outside/DEV_RESULTS.md and
    tests/test_paper_numbers.py change."""
    store = json.loads(_paper_numbers().PAPER_STORE.read_text())
    a, b = store["commit"], store["file_commit"]
    assert (a[:7], b[:7]) == ("1d73a80", "b2cafbe")
    git = lambda *args: subprocess.run(["git", *args], cwd=ROOT, capture_output=True, text=True, check=True).stdout
    changed = git("diff", "--name-only", a, b).split()
    allowed = {"README.md", "benchmark/outside/DEV_RESULTS.md", "tests/test_paper_numbers.py"}
    assert changed and all(f.startswith("papers/") or f in allowed for f in changed), changed
    assert git("diff", "--name-only", a, b, "--", "physverify", "lean", "schemes", "benchmark") == \
        "benchmark/outside/DEV_RESULTS.md\n"


def test_claim_kind_table_matches_the_registry():
    """The glossary's claim-kind table (claim_kinds_table.tex, input by main.tex) is what paper_numbers.py
    generates from physverify/claimkinds.py now: one row per kind, in registry order."""
    from physverify.claimkinds import KINDS
    pn = _paper_numbers()
    text = (PAPER / "claim_kinds_table.tex").read_text()
    assert text == pn._claim_kinds_tex(), "run: uv run python papers/scheme-claims/paper_numbers.py --write-table"
    assert "\\input{claim_kinds_table.tex}" in (PAPER / "main.tex").read_text()
    rows = [line for line in text.splitlines() if line.endswith("\\\\")]
    assert len(rows) == len(KINDS)
    assert sum(not r.endswith("gloss only \\\\") for r in rows) == sum(bool(k["meaning"]) for k in KINDS.values())


def test_outside_gap_table_matches_the_runner():
    """The outside benchmark's gap table (outside_gaps_table.tex, input by main.tex) is what paper_numbers.py
    generates from run_dev.py's counts now: one row per reason in run_dev.REASONS, and the primary entries add
    up to the entries the runner lists."""
    pn = _paper_numbers()
    numbers = _out("outside_dev")
    text = (PAPER / "outside_gaps_table.tex").read_text()
    assert text == pn._outside_gaps_tex(numbers), "run: uv run python papers/scheme-claims/paper_numbers.py --write-table"
    assert "\\input{outside_gaps_table.tex}" in (PAPER / "main.tex").read_text()
    reasons = pn._run_dev().REASONS
    assert set(pn.GAP_REASONS) == set(reasons)
    rows = [line for line in text.splitlines() if line.endswith("\\\\")]
    assert len(rows) == len(reasons)
    primary = sum(int(v) for k, v in numbers.items() if k.startswith("gap primary entries "))
    assert sum(int(r.split(" & ")[1]) for r in rows) == primary


def test_outside_naive_readings_would_be_wrong():
    """The two rejected readings of the outside benchmark's dev half: each gives a decisive verdict against
    a FALSE expected value (tecno:04 VERIFIED on the scheme; mfa:02's negated stability claim VERIFIED)."""
    out = _out("outside_naive_readings")
    assert out["tecno:04 entropy_stable_tadmor"].startswith("VERIFIED")
    assert out["tecno:04 dE/dt of the scheme"] == "0"
    assert out["tecno:04 dE/dt the identity requires, printed (+)"] == "-1/2"
    assert out["tecno:04 dE/dt the identity requires, corrected (-)"] == "0"
    assert all(v.startswith("REFUTED") for k, v in out.items() if k.startswith("mfa:02") and "stable" in k)
    assert out["mfa:02 energy before, after one step of (-1)^j at nu = 1"] == "8, 8"
    items = {json.loads(x)["id"]: json.loads(x) for x in (ROOT / "benchmark/outside/items.jsonl").read_text().splitlines()}
    for i in ("fjordholm_mishra_tadmor_2012_tecno:04", "mfa_oslo_notes:02"):
        assert items[i]["expected_alone"] == items[i]["expected_with_hypotheses"] == "FALSE"


def test_rusanov_sharp_bound_is_exactly_one_third():
    """Along w_i = c, w_{i+-1} = -c the spec's own dH/du_i is 1 - 3c (exact Fractions): zero at c = 1/3,
    negative at c = 334/1000. The checker's refuting pair at 334/1000 lies in the same sign cell, where
    the closed form 1 - 2w_i + (w_{i-1} + w_{i+1})/2 is H's partial."""
    from fractions import Fraction
    from physverify.schemes import checks
    pn = _paper_numbers()
    for c in map(Fraction, ("1/3", "334/1000", "1/2", "1", "1/10")):
        assert pn._rusanov_du0(-c, c, -c) == 1 - 3 * c
    assert pn._rusanov_du0(Fraction(-1, 3), Fraction(1, 3), Fraction(-1, 3)) == 0
    assert pn._rusanov_du0(Fraction(-334, 1000), Fraction(334, 1000), Fraction(-334, 1000)) < 0
    r = checks.monotonicity(pn._with("burgers-rusanov", monotone_cfl="334/1000"))
    w = r["witness"]["counterexample"]
    assert r["status"] == checks.REFUTED and w["lam"] == "1" and w["increased"] == "u0"
    assert tuple(w["state (um1, u0, up1)"]) == pn.PAIR_334
    um1, u0, up1 = map(Fraction, pn.PAIR_334)
    assert u0 >= 0 >= max(um1, up1) and max(-um1, -up1) <= u0
    assert pn._rusanov_du0(um1, u0, up1) == 1 - 2 * u0 + (um1 + up1) / 2 < 0


def _measure_lean():
    import importlib.util
    spec = importlib.util.spec_from_file_location("measure_lean", PAPER / "measure_lean.py")
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def test_lean_measurements_match_their_commits():
    """Every measured run, lean_measured_<commit>.json, is named after a commit it records (`file_commit`;
    `commit` is where it was collected), each commit it names is in the repository and has the Lean key the
    run was measured with (git object ids of measure_lean.KEY_PATHS, the toolchain and the Mathlib rev), and
    it names its host; every theorem it uses has a measured status on that host, and an accepted one only
    the standard axioms. The paper's numbers come from one of them, measure_lean.PAPER_STORE."""
    from physverify.lean_backend import STD_AXIOMS
    ml = _measure_lean()
    paths = ml.store_paths()
    assert ml.PAPER_STORE in paths
    for p in paths:
        store = json.loads(p.read_text())
        assert p.name == f"lean_measured_{store['file_commit'][:7]}.json", p.name
        for c in {store["commit"], store["file_commit"]}:
            assert subprocess.run(["git", "cat-file", "-e", f"{c}^{{commit}}"], cwd=ROOT).returncode == 0, (p.name, c)
            assert ml.lean_key(c) == store["key"], f"{p.name}: the code at {c[:7]} is not the code it measured"
        assert all(s["key"] == store["key"] for s in store["specs"].values()), p.name
        assert {"name", "machine", "cpus", "ram_gb"} <= set(store["host"]), p.name
        used = {h for s in store["specs"].values() for _, h in s["theorems"]}
        assert used <= set(store["theorems"]), p.name
        for h in used:
            t = store["theorems"][h]
            assert t["status"] in ml.STATUSES and t["host"] == store["host"]["name"], (p.name, h, t["name"])
            if t["status"] == "accepted":
                assert t["exit"] == 0 and set(t["axioms"]) <= STD_AXIOMS, (p.name, h, t["name"])


def _current_store() -> dict:
    ml = _measure_lean()
    key = ml.lean_key()
    current = [json.loads(p.read_text()) for p in ml.store_paths() if json.loads(p.read_text())["key"] == key]
    assert current, ("no lean_measured_<commit>.json was measured with the Lean project, judges, planners and checks "
                     "of HEAD: rerun papers/scheme-claims/measure_lean.py (see its docstring)")
    return current[0]


def test_lean_measurement_is_current_and_complete():
    """A measured run has the Lean key of HEAD, covers every spec the paper counts now (the example specs,
    schemes/ssp/ included) and names the machine it ran on: CPUs, RAM, and the Lean and Mathlib versions."""
    ml = _measure_lean()
    store = _current_store()
    assert store["key"]["lean_toolchain"] == (ROOT / "lean/lean-toolchain").read_text().strip()
    assert set(store["specs"]) == {uid for uid, _, _ in ml.units()}, "a spec is not measured (or no longer counted)"
    assert any(uid.startswith("schemes/ssp/") for uid in store["specs"])
    h = store["host"]
    assert h["cpus"] > 0 and h["ram_gb"] > 0 and h["machine"]
    assert store["key"]["lean_toolchain"].split(":v")[-1] in h["lean_version"]
    assert store["key"]["mathlib_rev"] == h["mathlib_rev"]


def test_lean_measurement_covers_every_meaning_theorem_of_the_registry():
    """The current run also ran `#print axioms` on the Lean meaning theorem of every claim kind that has one
    (physverify/claimkinds.py; ssp_preserves's PhysVerify.SSP.ssp_preserves_meaning among them), on the same
    machine: each depends on the standard axioms only."""
    from physverify.claimkinds import KINDS
    from physverify.lean_backend import STD_AXIOMS
    ml = _measure_lean()
    store = _current_store()
    reg = store["registry"]
    assert reg["exit"] == 0 and reg["host"] == store["host"]["name"]
    assert set(reg["theorems"]) == {k for k, v in KINDS.items() if v["meaning"]}
    assert reg["theorems"]["ssp_preserves"]["theorem"] == "PhysVerify.SSP.ssp_preserves_meaning"
    for kind, t in reg["theorems"].items():
        assert t["theorem"] == ml.meaning_theorems()[kind]
        assert t["status"] == "accepted" and set(t["axioms"]) <= STD_AXIOMS, (kind, t)


def test_generated_tables_match_their_sources():
    """The tables main.tex inputs are what paper_numbers.py generates now (the benchmark's from a run of the
    checker, the Lean run's from lean_measured.json)."""
    pn = _paper_numbers()
    rows = pn._bench_rows()
    hint = "run: uv run python papers/scheme-claims/paper_numbers.py --write-table"
    assert (PAPER / "bench_table.tex").read_text() == pn._bench_tex(rows), hint
    assert (PAPER / "bench_counts_table.tex").read_text() == pn._bench_counts_tex(rows), hint
    assert (PAPER / "lean_measured_table.tex").read_text() == pn._lean_measured_tex(), hint
    assert (PAPER / "outside_property_table.tex").read_text() == pn._outside_property_tex(_out("outside_dev")), hint
    assert (PAPER / "v2_topic_table.tex").read_text() == pn._v2_topic_tex(), hint
    tex = (PAPER / "main.tex").read_text()
    for name in ("bench_table", "bench_counts_table", "lean_measured_table", "outside_property_table",
                 "v2_topic_table"):
        assert "\\input{" + name + ".tex}" in tex


def test_out_of_sample_headline():
    """The headline of the abstract and the introduction: out of sample, at sentence level, nothing is decided
    and nothing is certified wrong. v1 held-out (frozen at b2cafbe): on the 42 clean items 3 stated, 0 decided,
    and every decided field of the 77 lies on a contaminated source. v2 (frozen first score): 11 of 91 clean
    stated, 0 checker WRONG; every MATCH is on a narrowed reading, and under the narrowing polarity rule
    (post-hoc) nothing is decided. OLD -> NEW changes no verdict."""
    h = _out("outside_heldout")
    clean = "without both contaminated sources"
    assert (h[f"{clean}: items"], h[f"{clean}: stated"], h[f"{clean}: decided_fields"]) == ("42", "3", "0")
    assert h["all: decided_fields"] == h["all: match"] == "8" and h["all: wrong"] == "0"
    assert (h["all: items"], h["all: stated"]) == ("77", "11")
    v = _out("outside_v2")
    assert (v["clean: items"], v["clean: stated"], v["clean: wrong_checker"]) == ("91", "11", "0")
    assert v["clean: match"] == v["clean: match_narrowed"] == "14" and v["clean: wrong_reading"] == "2"
    assert v["OLD -> NEW verdicts changed"] == "0" and v["errata confirmed exactly"] == "5"
    p = _out("outside_v2_posthoc")
    assert p["annotated: decided_fields"] == p["unrecorded: decided_fields"] == "0"
    assert p["moved MATCH -> GAP"] == "14" and p["moved WRONG -> GAP"] == "2"


def test_lean_status_vocabulary():
    """The paper's Lean vocabulary (accepted / tactic failure / heartbeat cap / found false) covers every theorem
    of the pinned run (b2cafbe) and of the current one (f09a5cb), and Lean found no statement false."""
    out = _out("lean_current")
    for name in ("b2cafbe", "f09a5cb"):
        n = [int(out[f"{name}: {k}"]) for k in ("accepted", "tactic failure", "heartbeat cap", "found false")]
        assert sum(n) == int(out[f"{name}: theorems"]) and n[1:] == [1, 1, 0], (name, n)
        assert out[f"{name}: timeout status"] == "0"
    assert (out["b2cafbe: theorems"], out["f09a5cb: theorems"]) == ("598", "600")
    assert out["f09a5cb: registry meanings accepted"] == "12/12"
    assert out["f09a5cb: commit"] == "f09a5cb" and out["f09a5cb: machine"] == out["b2cafbe: machine"]
    assert out["b2cafbe: not accepted"] == out["f09a5cb: not accepted"]


def test_lean_labels_come_from_the_measured_run():
    """The benchmark's Lean labels are lean_cert's rule applied to the measured statuses: no theorem the
    judge states now is missing from lean_measured.json (that raises), and the measured share is at most
    the projected one (every stated theorem taken as accepted)."""
    out = _out("bench_lean_labels")
    assert int(out["decisive with a Lean label"]) <= int(out["projected (every stated theorem accepted): decisive with a Lean label"])
    assert out["theorems stated"] == out["projected: theorems stated"]
