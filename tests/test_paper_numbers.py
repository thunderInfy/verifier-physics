"""Every reproducibility marker in the paper (papers/scheme-claims/main.tex) names a target that exists:
a pytest test `tests/X.py::name` or a function `paper_numbers.py::name` of papers/scheme-claims/paper_numbers.py.
Static only (the files are parsed, nothing is run), so it is fast."""
import ast
import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
PAPER = ROOT / "papers" / "scheme-claims"
TARGET = re.compile(r"\{((?:tests/[\w/]+\.py|paper_numbers\.py)::\w+)\}")


def _functions(path: Path) -> set[str]:
    return {n.name for n in ast.parse(path.read_text()).body if isinstance(n, ast.FunctionDef)}


def test_every_repro_target_resolves():
    tex = re.sub(r"(?<!\\)%.*", "", (PAPER / "main.tex").read_text())       # drop comments
    markers = len(re.findall(r"\\rn\{", tex)) + len(re.findall(r"\\repro\{", tex))
    targets = TARGET.findall(tex)
    assert markers > 0 and len(targets) == markers, "a marker has a target that is not FILE::FUNCTION"
    missing = []
    for t in sorted(set(targets)):
        file, name = t.split("::")
        path = PAPER / file if file == "paper_numbers.py" else ROOT / file
        if not path.is_file() or name not in _functions(path):
            missing.append(t)
    assert not missing, missing


def _paper_numbers():
    import importlib.util
    spec = importlib.util.spec_from_file_location("paper_numbers", PAPER / "paper_numbers.py")
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


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
    numbers = pn.outside_dev()
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
    pn = _paper_numbers()
    out = pn.outside_naive_readings()
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
