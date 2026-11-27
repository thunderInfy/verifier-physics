"""Scheme certificates without Lean: statement generation, batch attribution and the fallback rules.
(The kernel checks themselves are in tests/test_scheme_lean.py.)"""
import copy
import glob
from pathlib import Path

import pytest

from physverify import lean_backend, schemes
from physverify.expr import parse
from physverify.schemes import checks, lean_cert, systems

ROOT = Path(__file__).resolve().parent.parent
SPECS = sorted(glob.glob(str(ROOT / "schemes/**/*.json"), recursive=True))


def _exact(spec):
    out = (systems.check_all(spec) if systems.is_system(spec)
           else [checks.consistency(spec), checks.conservation(spec), checks.positivity(spec)])
    return [r for r in out if r["check"] in lean_cert.SCOPE and r["status"] in (checks.VERIFIED, checks.REFUTED)]


@pytest.mark.parametrize("path", SPECS, ids=[Path(p).stem for p in SPECS])
def test_every_in_scope_verdict_is_stated(path):
    spec = schemes.load(path)
    for r in _exact(spec):
        obs = lean_cert.obligations(spec, r, "t")
        assert obs and all(n.startswith("t_") for n, _, _ in obs)
        assert all("sorry" not in p for _, _, p in obs)


def test_statement_does_not_depend_on_the_witness():
    """The judge writes statements from the spec; scrambling the witness changes proofs only."""
    spec = schemes.load(ROOT / "schemes/broken-advection-downwind.json")
    for r in _exact(spec):
        bad = copy.deepcopy(r)
        for k in bad["witness"]:
            bad["witness"][k] = "junk" if isinstance(bad["witness"][k], str) else bad["witness"][k]
        try:
            junk = [s for _, s, _ in lean_cert.obligations(spec, bad, "t")]
        except Exception:      # the planner may choke on junk; the statement is what we compare
            junk = None
        good = [s for _, s, _ in lean_cert.obligations(spec, r, "t")]
        assert junk is None or junk == good


def test_statements_have_no_junk_division_or_sqrt():
    """A denominator must be a monomial in variables the statement assumes > 0; every sqrt gets a
    separate `_sqrt` theorem that its argument is >= 0."""
    with pytest.raises(lean_cert.Unsupported):
        lean_cert.real(parse("1/(uR - uL)"), {"uL": "a", "uR": "b"}, {"lam"}, [])
    with pytest.raises(lean_cert.Unsupported):
        lean_cert.real(parse("1/u"), {"u": "a"}, {"lam"}, [])
    roots = []
    assert "/" in lean_cert.real(parse("u/(2*lam)"), {"u": "a", "lam": "lam"}, {"lam"}, roots) and not roots
    spec = schemes.load(ROOT / "schemes/burgers-rusanov.json")
    names = [n for r in _exact(spec) for n, _, _ in lean_cert.obligations(spec, r, "t")]
    assert any(n.endswith("_sqrt") for n in names)
    stmt = next(s for r in _exact(spec) for n, s, _ in lean_cert.obligations(spec, r, "t") if n.endswith("_sqrt"))
    assert stmt.count("0 ≤") >= 1 and "Real.sqrt" not in stmt.split("→")[-1].split("0 ≤", 1)[0]


def _fake_run(log, ok=False):
    return lambda src, timeout: (ok, log(src) if callable(log) else log)


def test_check_batch_attributes_errors_per_theorem(monkeypatch):
    items = [(f"t{i}", "True", "trivial") for i in range(3)]

    def log(src):
        lines = src.splitlines()
        bad = next(i for i, l in enumerate(lines, 1) if l.startswith("theorem t1 "))
        return (f"f.lean:{bad + 1}:2: error: unsolved goals\n"
                + "".join(f"'t{i}' depends on axioms: [propext]\n" for i in range(3)))
    monkeypatch.setattr(lean_backend, "_run", _fake_run(log))
    res = lean_backend.check_batch(items)
    assert [res[f"t{i}"].ok for i in range(3)] == [True, False, True]
    # an error outside every theorem (the import, say) rejects all of them
    monkeypatch.setattr(lean_backend, "_run", _fake_run("f.lean:1:0: error: unknown module\n"
                                                        + "".join(f"'t{i}' depends on axioms: []\n" for i in range(3))))
    assert not any(r.ok for r in lean_backend.check_batch(items).values())
    # sorryAx, a missing axiom report, or the sanitizer: rejected
    monkeypatch.setattr(lean_backend, "_run", _fake_run("'t0' depends on axioms: [sorryAx]\n't1' does not depend on any axioms\n", True))
    res = lean_backend.check_batch(items[:2] + [("t2", "True", "sorry")])
    assert [res[f"t{i}"].ok for i in range(3)] == [False, True, False]


def _report(path):
    spec = schemes.load(ROOT / path)
    return spec, schemes.check(spec)


def test_guarantee_upgrades_only_when_every_theorem_is_accepted(monkeypatch):
    spec, rep = _report("schemes/advection-upwind.json")
    before = [(r["check"], r["status"], r["guarantee"]) for r in rep["checks"]]
    verdicts = [(v["claim"], v["verdict"]) for v in rep["claims"]]
    # Lean missing: nothing changes
    monkeypatch.setattr(lean_backend, "_run", lambda src, t: (False, "Lean not available"))
    lean_cert.certify([(spec, rep)])
    assert [(r["check"], r["status"], r["guarantee"]) for r in rep["checks"]] == before
    # one consistency theorem fails, the rest pass: only consistency keeps the exact-Python label
    spec, rep = _report("schemes/advection-upwind.json")

    def log(src):
        names = [l.split()[1] for l in src.splitlines() if l.startswith("theorem ")]
        bad = next(i for i, l in enumerate(src.splitlines(), 1) if "_consistency_" in l and l.startswith("theorem"))
        return f"f.lean:{bad}:0: error: boom\n" + "".join(f"'{n}' depends on axioms: [propext]\n" for n in names)
    monkeypatch.setattr(lean_backend, "_run", _fake_run(log))
    lean_cert.certify([(spec, rep)])
    g = {r["check"]: r["guarantee"] for r in rep["checks"]}
    assert g["consistency"] == checks.EXACT
    assert g["conservation"] == g["positivity"] == lean_cert.LEAN
    assert g["monotonicity"] == lean_cert.LEAN_CELLS
    claims = {v["claim"]: v["guarantee"] for v in rep["claims"]}
    assert claims["conservative"] == lean_cert.LEAN and claims["consistent"] == "exact"
    assert [(v["claim"], v["verdict"]) for v in rep["claims"]] == verdicts        # verdicts never change
