"""Planner side of the scheme certificates (untrusted): tactic text for the statements that
`lean_cert.py` writes. It may use anything, the check's witness included; a wrong proof only makes
Lean reject the theorem, and the verdict then keeps its exact-Python guarantee.
"""

from __future__ import annotations

from fractions import Fraction

from ..expr import E, lit, parse, substitute, var, variables
from . import checks, poly as P
from .lean_cert import poly_lean, rat, real

# `ring` falls back to `ring_nf` without failing, so the alternatives use `ring1` or end in `done`
RING = ("first | ring1 | (field_simp; ring1) | (ring_nf; done) | (ring_nf; simp; done) | (simp; ring_nf; done) "
        "| (ring_nf; simp only [Real.sq_sqrt, sq_nonneg, Real.sqrt_zero]; ring1) "
        "| (field_simp; ring_nf; simp only [Real.sq_sqrt, sq_nonneg, Real.sqrt_zero]; ring1)")


def _r(e, names, L):
    return real(e, names, L["positive"], [])


def _intro_binders(L: dict) -> str:
    return "intro " + " ".join(L["binders"] + [f"h_{b}" for b in L["binders"]])


def _vec(vals) -> str:
    return "![" + ", ".join(rat(v) for v in vals) + "]"


def _args(L: dict, env: dict) -> str:
    """Binder values from an exact point (lam and the parameters), then their positivity proofs."""
    return " ".join(rat(env.get(b, 1)) for b in L["binders"]) + " (by norm_num)" * len(L["binders"])


def sqrt_proof(L: dict, n: int) -> str:
    split = "" if n == 1 else "refine ⟨" + ", ".join(["?_"] * n) + "⟩ <;> "
    return f"intros\n{split}positivity"


def _phi(spec: dict, L: dict) -> list[str]:
    """Phi(qm1, q0, qp1, qp2) for the interface i + 1/2: -lam*F for a declared flux, else the
    telescoping candidate D(base, q0, qp1) + D(base, base, q0) of `checks.telescoping`."""
    names = {b: b for b in L["binders"]}
    if L["nf"] is not None:
        win = {"LL": "qm1", "L": "q0", "R": "qp1", "RR": "qp2"}
        for j, c in enumerate(L["state"]):
            names.update({f"{c}{s}": f"({q} {j})" for s, q in win.items()})
        return [f"(-lam * {_r(F, names, L)})" for F in L["nf"]]
    base = {c: lit(1 if c in L["dom"] else 0) for c in L["state"]}
    for j, c in enumerate(L["state"]):
        names.update({f"_b{c}": f"(q0 {j})", f"_c{c}": f"(qp1 {j})"})
    out = []
    for k, H in enumerate(L["update"]):
        D = E("sub", (H, var(f"{L['state'][k]}0")))
        at = lambda a, b, c: substitute(D, {f"{x}{s}": v[x] for x in L["state"] for s, v in zip(("m1", "0", "p1"), (a, b, c))})
        b, c = ({x: var(f"_{p}{x}") for x in L["state"]} for p in "bc")
        out.append(f"({_r(at(base, b, c), names, L)} + {_r(at(base, base, b), names, L)})")
    return out


def proof(spec: dict, L: dict, r: dict, k: int) -> str:
    check, w = r["check"], r["witness"]
    m = L["m"]
    if check == "conservation" and r["status"] == checks.VERIFIED:
        return (f"{_intro_binders(L)}\n"
                f"refine conserves_of_telescoping (fun qm1 q0 qp1 qp2 : Fin {m} → ℝ => {_phi(spec, L)[k]}) ?_\n"
                "intro qm2 qm1 q0 qp1 qp2 _ _ _ _ _\nbeta_reduce\n" + RING)
    if check == "conservation":
        env = {x: Fraction(v) for x, v in w.items() if x in L["binders"]}
        st = w["state"]
        cells = [[Fraction(s[c]) for c in L["state"]] if isinstance(s, dict) else [Fraction(s)] for s in st]
        u = "![" + ", ".join(_vec(c) for c in cells) + "]"
        dom = "(fun _ => trivial)" if not L["dom"] else "(by intro i; fin_cases i <;> norm_num)"
        return (f"intro h\nhave := h {_args(L, env)} {len(cells) - 1} {u} {dom}\n"
                "simp [stepSum, Fin.sum_univ_succ] at this\nnorm_num at this")
    if check == "consistency" and r["status"] == checks.VERIFIED:
        return f"{_intro_binders(L)} q hq\n" + RING
    if check == "consistency":
        pt = {x: Fraction(v) for x, v in w["point"].items()}
        q = [pt.get(c, Fraction(1 if c in L["dom"] else 0)) for c in L["state"]]
        return f"intro h\nhave := h {_args(L, pt)} {_vec(q)} (by norm_num)\nnorm_num at this"
    # positivity
    a, coeffs = checks.linear_coefficients(spec)
    if r["status"] == checks.REFUTED:
        kk = checks.STENCIL5.index(w["offending"])
        lam = Fraction(w["violating_nu"]) / a
        return ("intro h\nexact not_nonnegComb " f"{kk} (by norm_num [unitVec, Fin.ext_iff]) "
                f"(h {rat(lam)} (by norm_num) (by norm_num) (by norm_num))")
    nu = f"(({a.numerator} : ℝ) / {a.denominator} * lam)"
    cs = []
    for x in checks.STENCIL5:
        p = coeffs.get(x, {})
        terms = [f"{rat(c)} * {nu} ^ {(mono[0][1] if mono else 0)}" for mono, c in p.items()]
        cs.append("(" + (" + ".join(terms) or "0") + ")")
    sign = "first | (norm_num; done) | linarith | nlinarith [mul_nonneg (sub_nonneg.2 hlo) (sub_nonneg.2 hhi)]"
    return ("intro lam hlam hlo hhi\n"
            f"refine nonnegComb_of {' '.join(cs)} ?_ ?_ ?_ ?_ ?_ ?_\n"
            + "".join(f"· {sign}\n" for _ in range(5)) + "· intro w; beta_reduce\n  have := hlam.ne'\n  " + RING)


# ---------------------------------------------------------------- per-cell certificates

SUM = "(by simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ] <;> ring1)"


def _farkas_term(r, pairs, mu_proofs, atom_hyps, names) -> str:
    """`farkas r ![mu...] ![a...] ...` for p = r + sum mu_j a_j."""
    if not pairs:
        return "(by norm_num)"
    mus = "![" + ", ".join(m for m, _ in pairs) + "]"
    ats = "![" + ", ".join(poly_lean(a, names) for _, a in pairs) + "]"
    return (f"farkas {r} {mus} {ats} (by norm_num) (fun j => by fin_cases j; exacts [{', '.join(mu_proofs)}]) "
            f"(fun j => by fin_cases j; exacts [{', '.join(atom_hyps)}]) {SUM}")


def _mu_proof(c: list, a0: Fraction, b0: Fraction, x: str) -> str:
    """0 <= mu(nu) on [a0, b0] from its Bernstein coefficients (affine: from the endpoints)."""
    deg = max((k for k, v in enumerate(c) if v), default=0)
    if deg == 0:
        return "by norm_num"
    if deg == 1:
        return "by linarith"
    b = checks.bernstein(list(c), a0, b0)
    return (f"nonneg_of_bernstein (x := {x}) (lo := {rat(a0)}) (hi := {rat(b0)}) [{', '.join(rat(v) for v in b)}] "
            "(by norm_num) (by norm_num) hA hB (by simp [bernsteinSum, Fin.sum_univ_succ] <;> ring1)")


def _nu_pieces(p, atoms, hint, names) -> str:
    from . import limiters
    lo, hi = hint["nu_interval"]
    cert = limiters.farkas_in_nu(p, hint["cell_atoms"], lo, hi)
    if cert is None:
        return "fail"
    x = names["nu"]
    pieces = []
    for pc in cert["pieces"]:
        a0, b0 = (Fraction(v) for v in pc["nu"])
        rhs = parse(pc["identity"].split(" = ", 1)[1])
        terms, todo = [], [rhs]
        while todo:
            e = todo.pop()
            if e.kind == "add":
                todo += list(e.args)
            elif e.kind == "mul":
                terms.append((P.from_expr(e.args[0]), P.from_expr(e.args[1])))
        haves, pairs, hyps = [], [], []
        for j, (mu, at) in enumerate(terms):
            c = [Fraction(0)] * (1 + max((k for m in mu for _, k in m), default=0))
            for m, v in mu.items():
                c[m[0][1] if m else 0] += v
            haves.append(f"have hm{j} : 0 ≤ {poly_lean(mu, names)} := {_mu_proof(c, a0, b0, x)}")
            pairs.append((poly_lean(mu, names), at))
            hyps.append(f"h{atoms.index(at)}")
        pieces.append((a0, b0, haves + [f"exact {_farkas_term(0, pairs, [f'hm{j}' for j in range(len(terms))], hyps, names)}"]))
    # nest the case split nu <= b0 over the sorted pieces; lo <= nu and nu <= hi are the last two atoms
    n = len(atoms)

    def nest(i):
        a0, b0, body = pieces[i]
        below = f"h{n - 2}" if i == 0 else f"hp{i - 1}"
        lower = f"have hA : {rat(a0)} ≤ {x} := by linarith [{below}]"
        if i == len(pieces) - 1:
            return [lower, f"have hB : {x} ≤ {rat(b0)} := by linarith [h{n - 1}]", *body]
        sub = nest(i + 1)
        return [f"rcases le_total {x} {rat(b0)} with hp{i} | hp{i}", f"· {lower}",
                f"  have hB : {x} ≤ {rat(b0)} := hp{i}", *["  " + l for l in body],
                "· " + sub[0], *["  " + l for l in sub[1:]]]
    return "\n".join(nest(0))


def cell_proof(p, atoms: list, hint) -> str:
    """Proof of `cell_statement(p, atoms)` from the check's certificate: by form (positivity), an affine
    Farkas identity, or Farkas identities in nu with Bernstein multipliers on a split of the nu-range."""
    vs = sorted(P.variables(p).union(*(P.variables(a) for a in atoms)))
    names = {v: "v_" + v.lstrip("_") for v in vs}
    head = "intro " + " ".join([names[v] for v in vs] + [f"h{j}" for j in range(len(atoms))]) + "\n"
    if isinstance(hint, dict) and "nu_interval" in hint:
        return head + _nu_pieces(p, atoms, hint, names)
    if isinstance(hint, dict) and "multipliers" in hint:
        shown = [P.show(a) for a in atoms]
        pairs, hyps = [], []
        for a, m in hint["multipliers"].items():
            pairs.append((rat(Fraction(m)), atoms[shown.index(a)]))
            hyps.append(f"h{shown.index(a)}")
        return head + "exact " + _farkas_term(rat(Fraction(hint["remainder"])), pairs, ["(by norm_num)"] * len(pairs), hyps, names)
    return head + "positivity"


# ---------------------------------------------------------------- exact rational refutations

STEADY = ("first | (norm_num; done) | (field_simp; ring1) | (norm_num; ring1) | (norm_num; field_simp; ring1) "
          "| (simp; field_simp; ring1)")


def refutation_proof(spec: dict, r: dict) -> str:
    check, w = r["check"], r["witness"]
    if check in ("tv_increase", "max_principle_violation"):
        u = [Fraction(x) for x in w["periodic state u^n"]]
        lam = rat(Fraction(w["lam"]))
        bounds = f"{lam} (by norm_num) (by norm_num) (by norm_num)"
        if check == "tv_increase":
            # unfold the sums with literal indices, so Fin.reduceSub and Matrix.cons_val evaluate them
            words = {2: "two", 3: "three", 4: "four", 5: "five", 6: "six", 7: "seven", 8: "eight"}
            unfold = (f"simp only [TV, step, Fin.sum_univ_{words[len(u)]}, Fin.isValue, Fin.reduceSub, Fin.reduceAdd, "
                      "Matrix.cons_val] at this" if len(u) in words else "simp [TV, step, Fin.sum_univ_succ] at this")
            return f"intro h\nhave := h {bounds} {len(u)} {_vec(u)}\n{unfold}\nnorm_num at this"
        i, n, st = w["i"], len(u), [Fraction(x) for x in w["stencil values"]]
        vals = [u[(i + k - 2) % n] for k in range(5)]
        lo, hi = min(st), max(st)
        vals = [v if lo <= v <= hi else lo for v in vals]      # positions H does not read: any value in range
        return (f"intro h\nhave := h {bounds} {_vec(vals)} {rat(lo)} {rat(hi)} "
                "(by intro k; fin_cases k <;> norm_num)\nsimp only [Matrix.cons_val] at this\nnorm_num at this")
    if check == "monotonicity" and "u" in w["counterexample"]:        # five-point: two stencil vectors
        c = w["counterexample"]
        u, v = ([Fraction(c[k][x]) for x in checks.STENCIL5] for k in ("u", "v"))
        return (f"intro h\nhave := h {rat(Fraction(c['lam']))} (by norm_num) (by norm_num) (by norm_num) "
                f"{_vec(u)} {_vec(v)} (by intro k; fin_cases k <;> norm_num)\n"
                "simp only [Matrix.cons_val] at this\nnorm_num at this")
    if check == "monotonicity":
        c = w["counterexample"]
        s0 = [Fraction(x) for x in c["state (um1, u0, up1)"]]
        s1 = [x + (Fraction(c["by"]) if name == c["increased"] else 0) for x, name in zip(s0, checks.STENCIL)]
        args = " ".join(rat(x) for x in s0 + s1)
        return (f"intro h\nhave := h {rat(Fraction(c['lam']))} (by norm_num) {args}"
                + " (by norm_num)" * 9 + "\nnorm_num at this")
    if check == "entropy_stability":
        pt = {k: Fraction(x) for k, x in w["counterexample"]["point"].items()}
        cfl = " (by norm_num)" * len(checks._cfl_atoms(spec))
        return (f"intro h\nhave := h {rat(pt.get('lam', 1))} (by norm_num) {rat(pt['uL'])} {rat(pt['uR'])}{cfl}\n"
                "norm_num at this")
    return ("refine ⟨by norm_num, fun lam hlam => ?_⟩\nhave := hlam.ne'\n"
            "refine ⟨" + ", ".join(["?_"] * _n_identities(spec, check)) + "⟩ <;> " + STEADY)


def _n_identities(spec: dict, check: str) -> int:
    """How many step identities the judge states (three- or five-point tables)."""
    if check == "steady_nonentropy_step":
        wide = checks.stencil_of(variables(checks.update(spec))) != checks.STENCIL
        return len(checks.STEADY_STENCILS5 if wide else checks.STEADY_STENCILS)
    wide = bool(variables(checks.numerical_flux(spec)) & {"uLL", "uRR"})
    return len(checks.STEADY_INTERFACES4 if wide else checks.STEADY_INTERFACES)
