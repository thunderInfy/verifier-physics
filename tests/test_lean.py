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
     "intro env; simp [Expr.deriv, Expr.dir, Expr.basis, Expr.eval, zpow_two]; ring"),
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
    if c.source["true"] is None:      # ill-posed: neither verdict is right
        assert r.verdict == "UNKNOWN", r.detail
    assert r.verdict != ("REFUTED" if c.source["true"] else "VERIFIED")
    assert r.verdict == c.expect, r.detail


# The statements as they were before the empty-domain and junk-value fixes: used only to show
# that the new benchmark claims did get through them.
OLD_DEFS = """
def OldVerified (n : ℕ) (L : Expr) (D : (ℕ → ℝ) → Prop) (cs : List Law) : Prop :=
  ∀ env, D env → DomainOK n L env ∧ (ELSystem n L env ↔ Claims cs env)
def OldRefuted (n : ℕ) (L : Expr) (D : (ℕ → ℝ) → Prop) (cs : List Law) : Prop :=
  ∃ env, D env ∧ DomainOK n L env ∧ ¬(ELSystem n L env ↔ Claims cs env)
"""


def _old_tactic(tactic: str) -> str:
    """The planner's `verified` tactic without its PhysOK step."""
    from physverify.tools.eulerlagrange import PHYS
    lines = [l for l in tactic.splitlines() if not l.lstrip("· ").startswith(PHYS[:-1])]
    return "\n".join(lines).replace("refine ⟨⟨?_, ?_⟩, ?_, ?_⟩", "refine ⟨⟨?_, ?_⟩, ?_⟩")


def test_empty_domain_never_verified():
    """`th > 1/2, th < -1/2`: the old statement held vacuously; the new one is false in Lean,
    so no tactic can give VERIFIED, and the judge does not even try."""
    from physverify.derivation import UNKNOWN, lean_terms, load_claim, statement
    from physverify.derivation import judge as judge_claim
    from physverify.lean_backend import check
    c = load_claim(ROOT / "claims/pendulum-empty-domain.json")
    t = lean_terms(c)
    vacuous = "intro env h\nobtain ⟨-, -, -, h1, h2⟩ := h\nnorm_num [Expr.eval] at h1 h2\nlinarith"
    old = check(f"OldVerified {t['n']} {t['L']} {t['D']} {t['cs']}", vacuous, preamble=OLD_DEFS,
                module="PhysVerify.EulerLagrange")
    assert old.ok, old.log[-2000:]
    neg = check(f"¬ ({statement('verified', c)})",
                "rintro ⟨-, -, ⟨env, h⟩, -⟩\n" + vacuous.split("\n", 1)[1],
                module="PhysVerify.EulerLagrange")
    assert neg.ok, neg.log[-2000:]
    # a planner proposing the vacuous proof, with or without the judge's prefix, gets UNKNOWN
    r = judge_claim(c, [("verified", vacuous), ("verified", "refine ⟨by decide, by decide, ?_⟩\n" + vacuous)])
    assert r.verdict == UNKNOWN


def test_junk_sqrt_claim_no_longer_verifies():
    """x^(1/2) on the domain x != 0: Lean's x^(1/2) = 0 for x < 0 let the planner's own
    certificate prove the old statement; the new one requires 0 < x on D and is false."""
    from physverify.derivation import UNKNOWN, lean_terms, load_claim, statement
    from physverify.derivation import judge as judge_claim
    from physverify.lean_backend import check
    from physverify.tools import eulerlagrange
    c = load_claim(ROOT / "claims/root-potential-negative-x.json")
    t = lean_terms(c)
    ((kind, tactic),) = eulerlagrange.propose(c)
    assert kind == "verified"
    old = check(f"OldVerified {t['n']} {t['L']} {t['D']} {t['cs']}", _old_tactic(tactic),
                preamble=OLD_DEFS, module="PhysVerify.EulerLagrange")
    assert old.ok, old.log[-2000:]
    r = judge_claim(c, [(kind, tactic)])
    assert r.verdict == UNKNOWN, r.detail
    # the new statement is false: at x = -1 (in D) the real power x^(1/2) is junk
    # layout: x = 0, x_dot = 1, x_ddot = 2, k = 3, m = 4
    point = "(fun j : ℕ => [(-1 : ℝ), 0, 0, 1, 1].getD j 0)"
    neg = check(f"¬ ({statement('verified', c)})",
                f"rintro ⟨-, -, -, h⟩\nhave := (h {point} (by norm_num [Expr.eval])).2.1.1\n"
                "norm_num [Expr.physOK, Expr.eval] at this",
                module="PhysVerify.EulerLagrange")
    assert neg.ok, neg.log[-2000:]
    # with the domain the author meant, x > 0, the same claim is VERIFIED
    good = load_claim(ROOT / "claims/root-potential.json")
    assert judge_claim(good, eulerlagrange.propose(good)).verdict == "VERIFIED"


def test_junk_sqrt_counterexample_rejected():
    """x'' = -sqrt(k/m)^2 x with the sign of k left open: at k < 0 Lean's sqrt(k/m) = 0 gave a
    counterexample to a claim that is right wherever sqrt(k/m) is real. Now UNKNOWN."""
    from physverify.derivation import UNKNOWN, lean_terms, load_claim
    from physverify.derivation import judge as judge_claim
    from physverify.lean_backend import check
    from physverify.tools import eulerlagrange
    c = load_claim(ROOT / "claims/oscillator-sqrt-frequency.json")
    t = lean_terms(c)
    # layout: x = 0, x_dot = 1, x_ddot = 2, k = 3, m = 4; the jet x = 1, x'' = 0 at k = -1, m = 1
    point = "(fun j : ℕ => [(1 : ℝ), 0, 0, -1, 1].getD j 0)"
    old = check(f"OldRefuted {t['n']} {t['L']} {t['D']} {t['cs']}",
                f"refine ⟨{point}, by norm_num [Expr.eval], ?_, ?_⟩\n"
                "· refine ⟨?_, ?_⟩\n"
                "  · simp [Expr.diffOK, Expr.eval]\n"
                "  · intro k hk; interval_cases k; norm_num [Expr.diffOK, Expr.deriv, Expr.dir, Expr.basis, Expr.eval]\n"
                "· intro h\n"
                "  have := h.2 (by norm_num [Claims, Law.Holds, Expr.eval, "
                "Real.sqrt_eq_zero_of_nonpos (by norm_num : (-1 : ℝ) ≤ 0)]) 0 (by norm_num)\n"
                "  norm_num [EL, dt, timeDir, Expr.deriv, Expr.dir, Expr.basis, Expr.eval] at this",
                preamble=OLD_DEFS, module="PhysVerify.EulerLagrange")
    assert old.ok, old.log[-2000:]
    r = judge_claim(c, eulerlagrange.propose(c))
    assert r.verdict == UNKNOWN, r.detail


def test_junk_division_counterexample_rejected():
    """The pendulum with l > 0 left out of the domain: at l = 0 the EL equation is 0 = 0, and
    Lean's g/0 = 0 makes the claim th'' = 0, so th'' = 1 was a counterexample to the old
    `Refuted`. PhysOK now needs l != 0 for g/l, and both new statements are provably false."""
    from physverify.derivation import UNKNOWN, lean_terms, load_claim, statement
    from physverify.derivation import judge as judge_claim
    from physverify.lean_backend import check
    from physverify.tools import eulerlagrange
    c = load_claim(ROOT / "claims/pendulum-length-unconstrained.json")
    t = lean_terms(c)
    # layout: th = 0, th_dot = 1, th_ddot = 2, g = 3, l = 4, m = 5; the jet th'' = 1 at l = 0
    point = "(fun j : ℕ => [(0 : ℝ), 0, 1, 1, 0, 1].getD j 0)"
    unfold = "EL, dt, timeDir, Expr.deriv, Expr.dir, Expr.basis, Expr.eval, Fn.eval"
    old = check(f"OldRefuted {t['n']} {t['L']} {t['D']} {t['cs']}",
                f"refine ⟨{point}, by norm_num [Expr.eval], ?_, ?_⟩\n"
                "· refine ⟨?_, ?_⟩\n"
                "  · simp [Expr.diffOK, Expr.eval]\n"
                "  · intro k hk; interval_cases k; norm_num [Expr.diffOK, Expr.deriv, Expr.dir, Expr.basis, Expr.eval]\n"
                "· intro h\n"
                f"  have := h.1 (by intro k hk; interval_cases k; norm_num [{unfold}])\n"
                "  norm_num [Claims, Law.Holds, Expr.eval, Fn.eval] at this",
                preamble=OLD_DEFS, module="PhysVerify.EulerLagrange")
    assert old.ok, old.log[-2000:]
    # new Verified is false: the same point is in D, and g/l is junk there
    neg_v = check(f"¬ ({statement('verified', c)})",
                  f"rintro ⟨-, -, -, h⟩\n"
                  f"have := ((h {point} (by norm_num [Expr.eval])).2.1.2 _ (List.mem_singleton_self _)).2\n"
                  "norm_num [Expr.physOK, Expr.eval] at this",
                  module="PhysVerify.EulerLagrange")
    assert neg_v.ok, neg_v.log[-2000:]
    # new Refuted is false: wherever PhysOK holds, l != 0 and the claim is the EL equation
    neg_r = check(f"¬ ({statement('refuted', c)})",
                  "rintro ⟨-, env, hD, -, hP, hne⟩\n"
                  "have hl : env 4 ≠ 0 := by\n"
                  "  simpa [Expr.physOK, Expr.eval, Fn.eval] using (hP.2 _ (List.mem_singleton_self _)).2\n"
                  "simp only [Expr.eval, Rat.cast_zero] at hD\n"
                  "obtain ⟨hm, -⟩ := hD\n"
                  "apply hne\n"
                  "refine ELSystem_iff_of_cert rfl !![Expr.eval env (.var 5) * Expr.eval env (.var 4) ^ 2] "
                  "(by simp [Matrix.det_unique, Expr.eval, hl, hm.ne']) ?_\n"
                  "intro k\n"
                  "fin_cases k\n"
                  f"simp [{unfold}, Matrix.of_apply]\n"
                  "field_simp",
                  module="PhysVerify.EulerLagrange")
    assert neg_r.ok, neg_r.log[-2000:]
    r = judge_claim(c, eulerlagrange.propose(c))
    assert r.verdict == UNKNOWN, r.detail


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
