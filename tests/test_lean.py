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


DERIV_FACTS = [
    # symbolic derivatives evaluate to the textbook ones
    ("∀ env : ℕ → ℝ, (Expr.deriv 0 (.powi (.var 0) 3)).eval env = 3 * env 0 ^ 2",
     "intro env; simp [Expr.deriv, Expr.dir, Expr.basis, Expr.eval]; ring"),
    ("(Expr.deriv 0 (.app .sin (.var 0))).eval (fun _ => 0) = 1",
     "simp [Expr.deriv, Expr.dir, Expr.basis, Expr.eval, Fn.eval]"),
    # the correctness theorem, with its side condition discharged from the hypothesis
    ("∀ env : ℕ → ℝ, 0 < env 0 → HasDerivAt (fun x => (Expr.app .log (.var 0)).eval "
     "(Function.update env 0 x)) ((Expr.deriv 0 (.app .log (.var 0))).eval env) (env 0)",
     "intro env h; exact Expr.hasDerivAt_deriv 0 _ env ⟨trivial, h.ne'⟩"),
    # EL of a free particle L = m/2 · qdot² is m · qddot (n = 1: q = 0, qdot = 1, qddot = 2, m = 3)
    ("∀ env : ℕ → ℝ, (EL 1 0 (.mul (.div (.var 3) (.lit 2)) (.powi (.var 1) 2))).eval env = "
     "env 3 * env 2",
     "intro env; simp [EL, dt, timeDir, Expr.deriv, Expr.dir, Expr.basis, Expr.eval]; ring"),
]


@pytest.mark.parametrize("statement,proof", DERIV_FACTS)
def test_deriv_facts(statement, proof):
    from physverify.lean_backend import check
    r = check(statement, proof, module="PhysVerify.EulerLagrange")
    assert r.ok, r.log[-2000:]


def test_deriv_wrong_derivative_rejected():
    from physverify.lean_backend import check
    r = check("(Expr.deriv 0 (.app .sin (.var 0))).eval (fun _ => 0) = -1",
              "simp [Expr.deriv, Expr.dir, Expr.basis, Expr.eval, Fn.eval]",
              module="PhysVerify.EulerLagrange")
    assert not r.ok


CLAIMS = sorted((ROOT / "claims").glob("*.json"))


@pytest.mark.parametrize("path", CLAIMS, ids=[p.stem for p in CLAIMS])
def test_derivation_claims(path):
    """True claims are never REFUTED, false ones never VERIFIED; and we hit the expected verdict."""
    from physverify.derivation import load_claim
    from physverify.derivation import judge as judge_claim
    from physverify.tools import eulerlagrange
    c = load_claim(path)
    r = judge_claim(c, eulerlagrange.propose(c))
    assert r.verdict != ("REFUTED" if c.source["true"] else "VERIFIED")
    assert r.verdict == c.expect, r.detail


def test_derivation_judge_rejects_planner_tricks():
    """A lying planner gets UNKNOWN: wrong-direction certificates, sorry, trivial tactics."""
    from physverify.derivation import UNKNOWN, load_claim
    from physverify.derivation import judge as judge_claim
    from physverify.tools import eulerlagrange
    true_c = load_claim(ROOT / "claims/pendulum.json")
    false_c = load_claim(ROOT / "claims/pendulum-sin-vs-cos.json")
    # the true claim's certificate cannot verify the false claim, and vice versa
    (v,) = eulerlagrange.propose(true_c)
    r_false = eulerlagrange.propose(false_c)
    assert judge_claim(false_c, [v]).verdict == UNKNOWN
    assert judge_claim(true_c, [r_false[0], ("verified", "sorry"),
                                ("refuted", "simp_all"), ("verified", "decide")]).verdict == UNKNOWN


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
