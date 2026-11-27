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
                "rintro ⟨-, -, -, ⟨env, h⟩, -⟩\n" + vacuous.split("\n", 1)[1],
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
                f"rintro ⟨-, -, -, -, h⟩\nhave := (h {point} (by norm_num [Expr.eval])).2.1.1\n"
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


def test_verified_statement_gives_meaning_at_t():
    """Every VERIFIED statement contains `DomainForm`, so `verified_meaning_at` applies: the
    jet need only be in D at t. Atoms outside the continuous fragment fail `Atom.ok`."""
    from physverify.derivation import lean_terms, load_claim, statement
    from physverify.lean_backend import check
    c = load_claim(ROOT / "claims/kepler-polar.json")
    t = lean_terms(c)
    r = check(f"({statement('verified', c)}) → ∀ (q : ℕ → ℝ → ℝ) (p : ℕ → ℝ) (t : ℝ), "
              "(∀ j < 2, DifferentiableAt ℝ (q j) t) → "
              "(∀ j < 2, DifferentiableAt ℝ (_root_.deriv (q j)) t) → "
              f"{t['D']} (trajEnv 2 q p t) → "
              f"((∀ k < 2, realEL 2 k {t['L']} q p t = 0) ↔ Claims {t['cs']} (trajEnv 2 q p t))",
              "rintro ⟨-, hacc, hform, hcert⟩ q p t h1 h2 hD\n"
              "exact verified_meaning_at hcert hacc hform q p t h1 h2 hD",
              module="PhysVerify.EulerLagrange")
    assert r.ok, r.log[-2000:]
    bad = check("(Atom.lt (.div (.lit 1) (.var 0)) (.lit 1)).ok 1 = false ∧ "
                "(Atom.ne (.var 2) (.lit 0)).ok 1 = false ∧ (Atom.lt (.powi (.var 0) (-1)) (.lit 1)).ok 1 = false ∧ "
                "(Atom.lt (.div (.var 0) (.lit 2)) (.app .cos (.var 1))).ok 1 = true",
                "decide", module="PhysVerify.EulerLagrange")
    assert bad.ok, bad.log[-2000:]


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
                  f"rintro ⟨-, -, -, -, h⟩\n"
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


# ---------------------------------------------------------------- conserved quantities
# Claims in claims/conserved/ (physverify/conserved.py), certificates in PhysVerify.Conserved.

CONS_CLAIMS = sorted((ROOT / "claims/conserved").glob("*.json"))
CONS_MOD = "PhysVerify.Conserved"


def _load_cons(stem):
    from physverify.conserved import load_conserved
    return load_conserved(ROOT / f"claims/conserved/{stem}.json")


@pytest.mark.parametrize("path", CONS_CLAIMS, ids=[p.stem for p in CONS_CLAIMS])
def test_conserved_claims(path):
    """True claims are never REFUTED, false ones never VERIFIED, ill-posed ones UNKNOWN; and we
    hit the expected verdict."""
    from physverify.conserved import judge, load_conserved
    from physverify.tools import conserved as P
    c = load_conserved(path)
    r = judge(c, P.propose(c))
    if c.source["true"] is None:
        assert r.verdict == "UNKNOWN", r.detail
    assert r.verdict != ("REFUTED" if c.source["true"] else "VERIFIED")
    assert r.verdict == c.expect, r.detail


def test_verified_statement_gives_conserved_meaning():
    """Every VERIFIED statement has what `conserved_meaning` needs: Q is constant on every
    interval on which a solution's jet stays in D."""
    from physverify.conserved import lean_terms_q, statement
    from physverify.lean_backend import check
    c = _load_cons("kepler-angular-momentum")
    t = lean_terms_q(c)
    r = check(f"({statement('verified', c)}) → ∀ (q : ℕ → ℝ → ℝ) (p : ℕ → ℝ) (a b : ℝ), "
              "(∀ t ∈ Set.Ioo a b, ∀ j < 2, DifferentiableAt ℝ (q j) t) → "
              "(∀ t ∈ Set.Ioo a b, ∀ j < 2, DifferentiableAt ℝ (_root_.deriv (q j)) t) → "
              f"(∀ t ∈ Set.Ioo a b, {t['D']} (trajEnv 2 q p t)) → "
              f"(∀ t ∈ Set.Ioo a b, ∀ k < 2, realEL 2 k {t['L']} q p t = 0) → "
              f"∀ s ∈ Set.Ioo a b, ∀ t ∈ Set.Ioo a b, "
              f"Expr.eval (trajEnv 2 q p s) {t['Q']} = Expr.eval (trajEnv 2 q p t) {t['Q']}",
              "rintro ⟨-, -, hacc, hQ, hform, lams, hlen, -, hcert⟩ q p a b h1 h2 hD hEL\n"
              "exact (conserved_meaning hcert hlen hacc hQ hform q p a b h1 h2 hD hEL).2",
              module=CONS_MOD)
    assert r.ok, r.log[-2000:]


OLD_CONS_DEFS = """
def OldConservedVerified (n : ℕ) (L : Expr) (D : (ℕ → ℝ) → Prop) (Q : Expr) (lams : List Expr) : Prop :=
  (∃ env, D env) ∧ ∀ env, D env → DomainOK n L env ∧ L.physOK env ∧ Q.diffOK env ∧ Q.physOK env ∧
    (dt n Q).eval env = lamSum n L env 0 lams
def OldConservedRefuted (n : ℕ) (L : Expr) (D : (ℕ → ℝ) → Prop) (Q : Expr) : Prop :=
  ∃ env, D env ∧ DomainOK n L env ∧ L.physOK env ∧ Q.diffOK env ∧ Q.physOK env ∧
    ELSystem n L env ∧ (dt n Q).eval env ≠ 0
"""


def test_junk_multiplier_rejected():
    """λ = th_dot + 0/(m - m) is junk everywhere (Lean's x/0 = 0). Noether's identity still
    holds in Lean, and so does the statement without conditions on λ; the judge's statement
    requires physOK of λ on D, so this certificate gives UNKNOWN. (A junk λ cannot make a
    false claim pass: on a solution Σ λ_k · 0 = 0 whatever the λ_k are.)"""
    from physverify.conserved import UNKNOWN, judge, lean_terms_q
    from physverify.expr import parse
    from physverify.lean_backend import check
    from physverify.tools import conserved as P
    c = _load_cons("pendulum-energy")
    junk = parse("th_dot + 0/(m - m)")
    tac = P.verified_tactic(c, [junk])
    assert judge(c, [("verified", tac)]).verdict == UNKNOWN
    # the same proof, minus the λ bullet, proves the statement without conditions on λ
    t = lean_terms_q(c)
    head, rest = tac.split("\n", 1)
    lam, witness = head.split("refine ⟨", 1)[1].split(", rfl, by decide, ", 1)
    lines = rest.splitlines()
    i = next(k for k, l in enumerate(lines) if l.startswith("· simp only [List.mem_cons"))
    body = "\n".join(lines[:i] + lines[i + 2:]).replace(
        "refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩", "refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_, ?_⟩")
    r = check(f"OldConservedVerified {t['n']} {t['L']} {t['D']} {t['Q']} {lam}",
              f"refine ⟨{witness}\n{body}", preamble=OLD_CONS_DEFS, module=CONS_MOD)
    assert r.ok, r.log[-2000:]


def test_degenerate_lagrangian_cannot_be_refuted():
    """L = m x_dot^2/2 + lam (x - a): the jet x = a = 1, x_dot = 1 satisfies the EL system and
    has dx/dt = 1, though x = a on every solution. The statement without `Regular` is provable
    there; the judge's statement is false (the Hessian is singular at every jet)."""
    from physverify.conserved import UNKNOWN, judge, lean_terms_q, statement
    from physverify.lean_backend import check
    from physverify.tools import conserved as P
    c = _load_cons("constraint-multiplier-position")
    t = lean_terms_q(c)
    # layout: x = 0, lam = 1, x_dot = 2, lam_dot = 3, x_ddot = 4, lam_ddot = 5, a = 6, m = 7
    pt = "(fun j : ℕ => [(1 : ℝ), 0, 1, 0, 0, 0, 1, 1].getD j 0)"
    unf = "EL, dt, timeDir, Expr.deriv, Expr.dir, Expr.basis, Expr.eval, Fn.eval, Expr.diffOK"
    old = check(f"OldConservedRefuted {t['n']} {t['L']} {t['D']} {t['Q']}",
                f"refine ⟨{pt}, by norm_num [Expr.eval], ⟨?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩\n"
                f"· simp [{unf}] <;> norm_num\n"
                f"· intro k hk; interval_cases k <;> simp [{unf}] <;> norm_num\n"
                "· simp [Expr.physOK, Expr.eval] <;> norm_num\n· simp [Expr.diffOK]\n"
                "· simp [Expr.physOK]\n"
                f"· intro k hk; interval_cases k <;> simp [{unf}] <;> norm_num\n"
                f"· simp [{unf}]",
                preamble=OLD_CONS_DEFS, module=CONS_MOD)
    assert old.ok, old.log[-2000:]
    neg = check(f"¬ ({statement('refuted', c)})",
                "rintro ⟨-, -, env, -, -, -, -, -, -, hreg, -⟩\n"
                "apply hreg\n"
                "simp [Regular, Matrix.det_fin_two, Matrix.of_apply, Expr.deriv, Expr.dir, "
                "Expr.basis, Expr.eval]",
                module=CONS_MOD)
    assert neg.ok, neg.log[-2000:]
    assert judge(c, P.propose(c)).verdict == UNKNOWN


def test_conserved_judge_rejects_planner_tricks():
    from physverify.conserved import UNKNOWN, judge
    from physverify.tools import conserved as P
    good, bad = _load_cons("pendulum-energy"), _load_cons("pendulum-energy-wrong-sign")
    # the true claim's certificate does not verify the false one, and vice versa
    (v,) = P.propose(good)
    assert judge(bad, [v]).verdict == UNKNOWN
    assert judge(good, [P.propose(bad)[0], ("verified", "sorry"), ("refuted", "simp_all"),
                        ("verified", "decide")]).verdict == UNKNOWN


# ---------------------------------------------------------------- scheme certificates (lean_cert.py)
# Every exact verdict in scope must come back "proven (Lean)" (or the per-cell label), with the same
# status as without Lean; a wrong multiplier, flux potential or counterexample must fall back.

import glob  # noqa: E402
import time  # noqa: E402
import types  # noqa: E402

from physverify import schemes  # noqa: E402
from physverify.schemes import checks, lean_cert, lean_planner  # noqa: E402

SPECS = sorted(glob.glob(str(ROOT / "schemes/**/*.json"), recursive=True))
LABELS = (lean_cert.LEAN, lean_cert.LEAN_CELLS)


def _in_scope(r):
    return ((r["check"] in lean_cert.SCOPE and r["status"] in (checks.VERIFIED, checks.REFUTED))
            or (r["check"] in lean_cert.CELL_SCOPE and r["status"] == checks.VERIFIED)
            or (r["check"] in lean_cert.REF_SCOPE and r["status"] == checks.REFUTED))


@pytest.fixture(scope="module")
def certified():
    pairs = [(schemes.load(p), None) for p in SPECS]
    pairs = [(s, schemes.check(s)) for s, _ in pairs]
    before = [[(r["check"], r["status"]) for r in rep["checks"]] for _, rep in pairs]
    t = time.time()
    results = lean_cert.certify(pairs)
    print(f"\nscheme certificates: {len(results)} theorems, one Lean run, {time.time() - t:.0f}s")
    return pairs, before, results


def test_every_exact_verdict_in_scope_is_proven(certified):
    pairs, _, results = certified
    # a check's own caveat may follow the label (the entropy check's "semi-discrete inequality only")
    missing = [(s["name"], r["check"], r.get("lean")) for s, rep in pairs for r in rep["checks"]
               if _in_scope(r) and not r["guarantee"].startswith(LABELS)]
    assert not missing, missing
    assert all(v.ok for v in results.values())


def test_verdicts_unchanged_and_claims_carry_the_label(certified):
    pairs, before, _ = certified
    assert [[(r["check"], r["status"]) for r in rep["checks"]] for _, rep in pairs] == before
    lean_claims = [v for _, rep in pairs for v in rep["claims"] if v["guarantee"] in LABELS]
    assert {v["verdict"] for v in lean_claims} == {"VERIFIED", "REFUTED"}
    assert any(v["claim"] == "monotone_under_cfl" and v["guarantee"] == lean_cert.LEAN_CELLS for v in lean_claims)


def test_wrong_certificates_fall_back_to_exact_python():
    """A corrupted multiplier, flux potential or counterexample is rejected by Lean; the verdict keeps
    its status and its exact-Python guarantee."""
    def corrupt(fn, old, new):
        def g(*a):
            return fn(*a).replace(old, new, 1)
        return g
    planner = types.SimpleNamespace(**{k: getattr(lean_planner, k) for k in dir(lean_planner) if not k.startswith("__")})
    planner.cell_proof = corrupt(lean_planner.cell_proof, "![(1 : ℝ)]", "![(2 : ℝ)]")        # a Farkas multiplier
    planner.proof = corrupt(lean_planner.proof, "(-lam * ", "(-2 * lam * ")                     # the flux potential
    spec = schemes.load(ROOT / "schemes/advection-upwind.json")
    rep = schemes.check(spec)
    lean_cert.certify([(spec, rep)], planner=planner)
    g = {r["check"]: (r["status"], r["guarantee"]) for r in rep["checks"]}
    assert g["monotonicity"] == (checks.VERIFIED, checks.EXACT)
    assert g["conservation"] == (checks.VERIFIED, checks.EXACT)
    # a counterexample nu at which the offending coefficient is not negative
    planner = types.SimpleNamespace(**vars(planner))
    planner.proof = lean_planner.proof
    down = schemes.load(ROOT / "schemes/broken-advection-downwind.json")
    rep = schemes.check(down)
    pos = next(r for r in rep["checks"] if r["check"] == "positivity")
    pos["witness"]["violating_nu"] = "0"     # c_{i+1}(0) = 0, so this is no counterexample
    lean_cert.certify([(down, rep)], planner=planner)
    assert (pos["status"], pos["guarantee"]) == (checks.REFUTED, checks.EXACT)


# ---------------------------------------------------------------- variational integrators
# Claim files in benchmark/variational/ (physverify/variational.py), certificates in
# PhysVerify.Discrete. Skipped cleanly where there is no Lean toolchain or no Mathlib build.

import shutil  # noqa: E402

from physverify import lean_backend  # noqa: E402

VAR_BENCH = sorted((ROOT / "benchmark/variational").glob("*.json"))
VAR_MOD = "PhysVerify.Discrete"
needs_lean = pytest.mark.skipif(
    shutil.which("lake") is None and not (Path.home() / ".elan/bin/lake").exists()
    or (lean_backend.MODE == "local" and not (lean_backend.LEAN_DIR / ".lake/packages/mathlib").is_dir()),
    reason="no Lean toolchain / Mathlib build")


def _load_var(stem):
    from physverify.variational import load_variational
    return load_variational(ROOT / f"benchmark/variational/{stem}.json")


@pytest.fixture(scope="module")
def var_results():
    from physverify.variational import judge_file, load_variational
    t = time.time()
    out = {p.stem: judge_file(load_variational(p)) for p in VAR_BENCH}
    print(f"\nvariational bench: {sum(map(len, out.values()))} claims, {time.time() - t:.0f}s")
    return out


@needs_lean
@pytest.mark.parametrize("path", VAR_BENCH, ids=[p.stem for p in VAR_BENCH])
def test_variational_bench(var_results, path):
    """True claims are never REFUTED, false ones never VERIFIED, and every claim gets its label."""
    from physverify.variational import load_variational
    I = load_variational(path)
    for raw, c, r in zip(I.source["claims"], I.claims, var_results[path.stem]):
        assert r.verdict != ("REFUTED" if raw["true"] else "VERIFIED"), (r.claim, r.detail)
        assert r.verdict == c.expect, (r.claim, r.detail)
        if c.kind != "consistent_order_p" and r.verdict != "UNKNOWN":
            assert "; axioms: " in r.detail and "sorryAx" not in r.detail


@needs_lean
def test_dmomentum_statement_gives_exact_conservation():
    """Every VERIFIED discrete-momentum statement gives what `dmomentum_meaning` needs: J is
    constant along every discrete trajectory whose triples stay in D."""
    from physverify.expr import to_lean
    from physverify.variational import lean_terms, statement
    I = _load_var("central-quartic-trapezoid")
    c = I.claims[0]
    t, J = lean_terms(I), to_lean(c.quantity, I.index())
    r = lean_backend.check(
        f"({statement('verified', I, c)}) → ∀ (q : ℕ → ℕ → ℝ) (p : ℕ → ℝ) (N : ℕ), "
        f"(∀ k < N, {t['D']} (stepEnv 2 q p k)) → "
        f"(∀ k < N, ∀ i < 2, realDEL 2 i {t['Ld']} q p k = 0) → "
        f"Expr.eval (stepEnv 2 q p N) {J} = Expr.eval (stepEnv 2 q p 0) {J}",
        "rintro ⟨-, -, hacc, hJ, mus, hlen, hcert⟩ q p N hD hDEL\n"
        "exact dmomentum_meaning hcert hlen hacc hJ q p N hD hDEL",
        module=VAR_MOD)
    assert r.ok, r.log[-2000:]


@needs_lean
def test_corrupted_multiplier_rejected():
    """A wrong μ (the planner's μ_0 plus 1) breaks the identity: Lean rejects, UNKNOWN."""
    from physverify.expr import E, lit
    from physverify.tools import variational as P
    from physverify.variational import UNKNOWN, VERIFIED, del_exprs, judge
    I = _load_var("free-particle-2d")
    c = I.claims[0]
    mus = P.multipliers(I, c, del_exprs(I))
    assert judge(I, c, [("verified", P.mom_verified_tactic(I, mus))]).verdict == VERIFIED
    bad = [E("add", (mus[0], lit(1))), mus[1]]
    assert judge(I, c, [("verified", P.mom_verified_tactic(I, bad))]).verdict == UNKNOWN


@needs_lean
def test_junk_multiplier_rejected():
    """μ_0 + 1/(m - m) is junk everywhere (Lean's x/0 = 0): the identity still holds in Lean,
    but the statement requires physOK of every μ on D, so the certificate gives UNKNOWN."""
    from physverify.expr import E, parse, to_lean
    from physverify.tools import variational as P
    from physverify.variational import UNKNOWN, del_exprs, judge, lean_terms
    I = _load_var("free-particle-2d")
    c = I.claims[0]
    mus = P.multipliers(I, c, del_exprs(I))
    junk = [E("add", (mus[0], parse("1/(m - m)"))), mus[1]]
    assert judge(I, c, [("verified", P.mom_verified_tactic(I, junk))]).verdict == UNKNOWN
    t, idx = lean_terms(I), I.index()
    J, ms = to_lean(c.quantity, idx), "[" + ", ".join(to_lean(m, idx) for m in junk) + "]"
    intro, facts, _ = P._intro(I)
    r = lean_backend.check(
        f"∀ env, {t['D']} env → (Expr.ren (shift 2) {J}).eval env - Expr.eval env {J} = "
        f"delSum 2 {t['Ld']} env 0 {ms}",
        f"{intro}\nsimp [delSum, {P.UNF}{facts}] <;> {P.IDENT}", module=VAR_MOD)
    assert r.ok, r.log[-2000:]


@needs_lean
def test_variational_judge_rejects_planner_tricks():
    from physverify.tools import variational as P
    from physverify.variational import UNKNOWN, judge
    I = _load_var("central-quartic-trapezoid")
    good, wrong = I.claims[0], I.claims[1]
    (v,) = P.propose(I, good)
    assert judge(I, wrong, [v]).verdict == UNKNOWN          # the true claim's certificate
    assert judge(I, good, [P.propose(I, wrong)[0], ("verified", "sorry"), ("refuted", "simp_all"),
                           ("verified", "decide")]).verdict == UNKNOWN
