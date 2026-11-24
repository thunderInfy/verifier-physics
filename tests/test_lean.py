"""End-to-end tests through the Lean kernel (slow: ~10 s per certificate)."""
from pathlib import Path

import pytest

from physverify import registry
from physverify.core import EXCLUDED, NOT_REFUTED, REFUTED, Candidate
from physverify.judge import judge
from physverify.planner import plan
from physverify.theory import load_theory

ROOT = Path(__file__).resolve().parent.parent
EVIDENCE = registry.load(sorted((ROOT / "data").glob("**/*.json")))
pytestmark = pytest.mark.lean


def run(name, candidates=None):
    th = load_theory(ROOT / "theories" / f"{name}.json")
    return judge(th, EVIDENCE, plan(th, EVIDENCE) if candidates is None else candidates)


# Completeness regression: true theories must never be refuted.
@pytest.mark.parametrize("name", ["newton-gravity", "pendulum-nonlinear", "pendulum-small-angle",
                                  "inverse-cube-force", "gr-ppn", "brans-dicke-omega-ge-40000",
                                  "photon-lorentz-invariant"])
def test_true_theories_not_refuted(name):
    assert run(name).verdict == NOT_REFUTED


@pytest.mark.parametrize("name,tool", [
    ("kepler-wrong-dimension", "dimension"),
    ("kepler-wrong-factor", "algebra"),
    ("inverse-fourth-force", "orbit"),
    ("pendulum-linear", "enclosure"),
    ("power-law-2.1", "enclosure"),
])
def test_false_theories_refuted(name, tool):
    r = run(name)
    assert r.verdict == REFUTED
    assert any(f.status == REFUTED and f.tool == tool for f in r.findings)


@pytest.mark.parametrize("name", ["brans-dicke-omega-le-1000", "nordstrom-scalar",
                                  "photon-anisotropic-1e-16"])
def test_statistically_excluded(name):
    r = run(name)
    assert r.verdict == EXCLUDED
    assert not any(f.status == REFUTED for f in r.findings)   # never promoted to the strict channel


def test_adversarial_planner_cannot_refute_newton():
    """A lying planner: bogus proofs, sorry, and obligations for laws that hold."""
    bogus = [
        Candidate("evil", "dim_mismatch", {"law": "kepler3"}, "decide"),
        Candidate("evil", "law_vs_evidence", {"law": "kepler3", "evidence": "kepler-earth"}, "sorry"),
        Candidate("evil", "law_vs_evidence", {"law": "kepler3", "evidence": "kepler-earth"},
                  "intro env h_GM h_T h_a hlaw\nexact absurd hlaw (by simp)"),
        Candidate("evil", "orbit_excluded", {"evidence": "orbit-halley"}, "intro env; simp_all"),
        Candidate("evil", "trajectory_vs_evidence", {"evidence": "trajectory-mercury-10d"},
                  {"h": "864000", "boxes": [{v: ["-1e99", "1e99"] for v in
                                             ["x", "y", "z", "vx", "vy", "vz"]}]}),
    ]
    r = run("newton-gravity", bogus)
    assert r.verdict == NOT_REFUTED
