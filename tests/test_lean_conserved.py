"""Conserved-quantity claims through the Lean kernel (slow: ~10-30 s per certificate)."""
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parent.parent
CLAIMS = sorted((ROOT / "claims/conserved").glob("*.json"))
pytestmark = pytest.mark.lean
MOD = "PhysVerify.Conserved"


def _load(stem):
    from physverify.conserved import load_conserved
    return load_conserved(ROOT / f"claims/conserved/{stem}.json")


@pytest.mark.parametrize("path", CLAIMS, ids=[p.stem for p in CLAIMS])
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
    c = _load("kepler-angular-momentum")
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
              module=MOD)
    assert r.ok, r.log[-2000:]


OLD_DEFS = """
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
    c = _load("pendulum-energy")
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
              f"refine ⟨{witness}\n{body}", preamble=OLD_DEFS, module=MOD)
    assert r.ok, r.log[-2000:]


def test_degenerate_lagrangian_cannot_be_refuted():
    """L = m x_dot^2/2 + lam (x - a): the jet x = a = 1, x_dot = 1 satisfies the EL system and
    has dx/dt = 1, though x = a on every solution. The statement without `Regular` is provable
    there; the judge's statement is false (the Hessian is singular at every jet)."""
    from physverify.conserved import UNKNOWN, judge, lean_terms_q, statement
    from physverify.lean_backend import check
    from physverify.tools import conserved as P
    c = _load("constraint-multiplier-position")
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
                preamble=OLD_DEFS, module=MOD)
    assert old.ok, old.log[-2000:]
    neg = check(f"¬ ({statement('refuted', c)})",
                "rintro ⟨-, -, env, -, -, -, -, -, -, hreg, -⟩\n"
                "apply hreg\n"
                "simp [Regular, Matrix.det_fin_two, Matrix.of_apply, Expr.deriv, Expr.dir, "
                "Expr.basis, Expr.eval]",
                module=MOD)
    assert neg.ok, neg.log[-2000:]
    assert judge(c, P.propose(c)).verdict == UNKNOWN


def test_judge_rejects_planner_tricks():
    from physverify.conserved import UNKNOWN, judge
    from physverify.tools import conserved as P
    good, bad = _load("pendulum-energy"), _load("pendulum-energy-wrong-sign")
    # the true claim's certificate does not verify the false one, and vice versa
    (v,) = P.propose(good)
    assert judge(bad, [v]).verdict == UNKNOWN
    assert judge(good, [P.propose(bad)[0], ("verified", "sorry"), ("refuted", "simp_all"),
                        ("verified", "decide")]).verdict == UNKNOWN
