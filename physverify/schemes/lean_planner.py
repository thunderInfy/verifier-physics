"""Planner side of the scheme certificates (untrusted): tactic text for the statements that
`lean_cert.py` writes. It may use anything, the check's witness included; a wrong proof only makes
Lean reject the theorem, and the verdict then keeps its exact-Python guarantee.
"""

from __future__ import annotations

from fractions import Fraction

from ..expr import E, lit, parse, substitute, to_str, var, variables
from . import checks, poly as P, univariate
from .lean_cert import poly_lean, rat, real

def _first(*alts: tuple[str, ...]) -> str:
    """`first | ...` over tactic chains. Each chain's steps are joined by `<;>`, so a step that closes the
    goal early leaves the rest nothing to run on (with `;` they fail with "No goals to be solved")."""
    return "first | " + " | ".join(a[0] if len(a) == 1 else "(" + " <;> ".join(a) + ")" for a in alts)


# `ring` falls back to `ring_nf` without failing, so the alternatives use `ring1` or end in `done`
SQ = "simp only [Real.sq_sqrt, sq_nonneg, Real.sqrt_zero]"
RING = _first(("ring1",), ("field_simp", "ring1"), ("ring_nf", "done"), ("ring_nf", "simp", "done"),
              ("simp", "ring_nf", "done"), ("ring_nf", SQ, "ring1"), ("field_simp", "ring_nf", SQ, "ring1"))


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
    cs, signs = [], []
    box = "mul_nonneg (sub_nonneg.2 hlo) (sub_nonneg.2 hhi)"
    for x in checks.STENCIL5:
        p = coeffs.get(x, {})
        terms = [f"{rat(c)} * {nu} ^ {(mono[0][1] if mono else 0)}" for mono, c in p.items()]
        cs.append("(" + (" + ".join(terms) or "0") + ")")
        hints = [box]
        if x in w.get("exact_decision", {}):
            # p = c * g * h^2 (square-free decomposition): h^2 and h^2 times the CFL box as extra products
            _, factors = univariate.squarefree(checks.nu_coefficients(p))
            h = [Fraction(1)]
            for i, f in factors:
                h = univariate.mul(h, univariate.power(f, i // 2))
            if univariate.deg(h) > 0:
                hl = "(" + " + ".join(f"{rat(v)} * {nu} ^ {j}" for j, v in enumerate(h) if v) + ")"
                hints += [f"sq_nonneg {hl}", f"mul_nonneg ({box}) (sq_nonneg {hl})"]
        signs.append(f"first | (norm_num; done) | linarith | nlinarith [{', '.join(hints)}]")
    return ("intro lam hlam hlo hhi\n"
            f"refine nonnegComb_of {' '.join(cs)} ?_ ?_ ?_ ?_ ?_ ?_\n"
            + "".join(f"· {s}\n" for s in signs) + "· intro w; beta_reduce\n  have := hlam.ne'\n  " + RING)


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


# ---------------------------------------------------------------- TVD through Harten's lemma

def _sqrt_terms(e: E, names: dict, prefix: str = "s") -> tuple[list, E]:
    """For each distinct sqrt(t^2) in e, innermost first: (the Lean text of t with the square roots
    inside it already named s0, s1, ..., which `_pw` generalizes them to; t as a polynomial in the
    flux arguments uLL, uL, uR and _s0, _s1, ...). Also e itself with its square roots so named."""
    ids: dict = {}
    out: list = []

    def named(x: E) -> E:
        if x.kind == "sqrt":
            return var(f"_s{ids[to_str(x)]}")
        return x if not x.args else E(x.kind, tuple(named(y) for y in x.args), name=x.name, q=x.q)

    def walk(x: E) -> None:
        for y in x.args:
            walk(y)
        if x.kind == "sqrt" and to_str(x) not in ids:
            if x.args[0].kind != "powi" or x.args[0].q != 2:
                raise ValueError("a square root of something other than a square")
            t = named(x.args[0].args[0])
            out.append((real(t, {**names, **{f"_s{k}": f"{prefix}{k}" for k in range(len(ids))}}, set(), []), P.from_expr(t)))
            ids[to_str(x)] = len(ids)
    walk(e)
    return out, named(e)


def _cone_point(cons: list, line: str | None) -> bool:
    """Is there (p, q) with every (c_p, c_q, kind) holding, kind ">=" (c.(p, q) >= 0), "<" or ">"
    (strict)? Exact: the constraints are half-planes through 0, so a non-empty intersection contains 0,
    a boundary ray, a ray perpendicular to one, or the sum of two angularly consecutive boundary rays.
    `line` restricts to q = 0 ("p") or p = 0 ("q")."""
    def holds(c, pt):
        v = c[0] * pt[0] + c[1] * pt[1]
        return v >= 0 if c[2] == ">=" else v < 0 if c[2] == "<" else v > 0
    ok = lambda pt: all(holds(c, pt) for c in cons)
    if line:
        e = (1, 0) if line == "p" else (0, 1)
        return any(ok((t * e[0], t * e[1])) for t in (-1, 0, 1))
    rays = {(-cq, cp) for cp, cq, _ in cons if (cp, cq) != (0, 0)} | {(cq, -cp) for cp, cq, _ in cons if (cp, cq) != (0, 0)}
    rays |= {(1, 0), (0, 1), (-1, 0), (0, -1)}
    half = lambda r: 0 if r[1] > 0 or (r[1] == 0 and r[0] > 0) else 1
    import functools
    cmp = lambda r, s: (half(r) - half(s)) or (-1 if r[0] * s[1] - r[1] * s[0] > 0 else 1 if r[0] * s[1] - r[1] * s[0] < 0 else 0)
    order = sorted(rays, key=functools.cmp_to_key(cmp))
    cands = [(0, 0)] + order + [(-r[1], r[0]) for r in order]
    cands += [(r[0] + s[0], r[1] + s[1]) for r, s in zip(order, order[1:] + order[:1])]
    return any(ok(pt) for pt in cands)


def _combination(hyps: list, target: P.Poly, strict: bool) -> str | None:
    """`linear_combination` text: coefficients c (>= 0 on inequalities) with target = sum_i c_i delta_i
    + kappa, kappa >= 0 a constant (for `strict`: target 0, and the strict hypotheses' coefficients sum
    to 1, which proves 0 < 0). hyps: (name, delta = rhs - lhs, "eq" | "le" | "lt"). Exact simplex
    (`limiters.feasible`), and the identity is replayed; None if there is no such combination."""
    from . import limiters
    names = sorted(set(P.variables(target)).union(*(P.variables(d) for _, d, _ in hyps)))
    zero = Fraction(0)

    def vec(p):
        lin = checks._linear(p, names)
        if lin is None:
            raise ValueError("a hypothesis is not affine")
        return [lin[1].get(x, zero) for x in names] + [lin[0]]
    cols, labels = [], []
    for name, d, kind in hyps:
        v = vec(d) + ([Fraction(int(kind == "lt"))] if strict else [])
        cols.append(v)
        labels.append((name, 1))
        if kind == "eq":
            cols.append([-x for x in v])
            labels.append((name, -1))
    cols.append([zero] * len(names) + [Fraction(1)] + ([zero] if strict else []))
    labels.append((None, 1))
    mu = limiters.feasible(cols, vec(target) + ([Fraction(1)] if strict else []))
    if mu is None:
        return None
    coef: dict = {}
    for (name, sgn), m in zip(labels, mu):
        if name is not None and m:
            coef[name] = coef.get(name, zero) + sgn * m
    rest = target
    for name, d, _ in hyps:
        rest = P.add(rest, P.scale(d, coef.get(name, 0)), -1)
    if set(rest) - {()} or rest.get((), zero) < 0:
        return None
    terms = [n if c == 1 else f"{rat(c)} * {n}" for n, c in coef.items() if c]
    return "linear_combination " + (" + ".join(terms) or "0")


def _pw(ts: list, goal: tuple, hyp: tuple | None, line: str | None = None, names: dict | None = None) -> str:
    """Tactic text for a goal that is linear once every sqrt(t^2) is t or -t: name each square root
    (innermost first, so the outer ones are then written with those names), split on the sign of each
    t (`sqrt_sq_cases`), and close every branch by one `linear_combination` computed here: a branch
    whose signs contradict (decided exactly, in the differences p = uL - uLL, q = uR - uL) by 0 < 0,
    a leaf by the goal. goal = (kind, lhs, rhs) as polynomials in the flux arguments and _s0, ...,
    kind "le" or "eq"; `hyp` is h : 0 < difference or difference < 0, as (c_p, c_q, kind). With
    `names` (the Lean terms of the flux arguments), the goal is first replaced by its expanded form
    (`suffices`, one ring check), so the leaves' checks see a short linear goal, not the nested one."""
    sub0 = {"uLL": P.add(P.var("uL"), P.var("_p"), -1), "uR": P.add(P.var("uL"), P.var("_q"))}
    same = {}
    if line == "p":
        sub0["uR"] = same["uR"] = P.var("uL")
    elif line == "q":
        sub0["uLL"] = same["uLL"] = P.var("uL")
    on = lambda p: P.subst(p, same) if same else p           # the atoms Lean has (uR is uL on the line q = 0)
    lines = [f"generalize e{k} : Real.sqrt (({t}) ^ 2) = s{k}" for k, (t, _) in enumerate(ts)]
    base = []
    if hyp:
        d = P.add(P.scale(P.var("uL"), hyp[0] - hyp[1]), P.add(P.scale(P.var("uR"), hyp[1]), P.scale(P.var("uLL"), -hyp[0])))
        base.append(("h", d if hyp[2] == ">" else P.scale(d, -1), "lt"))
    kind, lhs, rhs = goal
    if names is not None:
        nm = {**names, **{f"_s{k}": f"s{k}" for k in range(len(ts))}}
        rel = "≤" if kind == "le" else "="
        lines.append(f"suffices H : {poly_lean(lhs, nm)} {rel} {poly_lean(rhs, nm)} by linear_combination H")
    only = lambda hs: f"linarith only [{', '.join(n for n, _, _ in hs)}]"

    def form(poly, sig):
        env = {**sub0, **{f"_s{j}": x for j, x in enumerate(sig)}}
        got = checks._linear(P.subst(poly, env), ["_p", "_q"])
        if got is None or got[0]:
            raise ValueError("a square-root argument is not a linear form in the differences")
        return got[1].get("_p", Fraction(0)), got[1].get("_q", Fraction(0))

    def tree(k, sig, cons, hs):
        if k == len(ts):
            use = [x for x in hs if x[2] == "eq"] if kind == "eq" else hs
            return [_combination(use, on(P.add(rhs, lhs, -1)), False) or only(hs)]
        t = form(ts[k][1], sig)
        T = on(ts[k][1])
        out = [f"rcases sqrt_sq_cases e{k} with ⟨a{k}, b{k}⟩ | ⟨a{k}, b{k}⟩"]
        for s, kd in ((1, ">="), (-1, "<")):
            c = cons + [(t[0], t[1], kd)]
            h2 = hs + [(f"a{k}", P.add(P.scale(T, s), P.var(f"_s{k}"), -1), "eq"),
                       (f"b{k}", P.scale(T, s), "le" if s == 1 else "lt")]
            if _cone_point(c, line):
                sub = tree(k + 1, sig + [P.add(P.scale(P.var("_p"), s * t[0]), P.scale(P.var("_q"), s * t[1]))], c, h2)
            else:
                lc = _combination(h2, {}, True)
                sub = [f"exact absurd (show (0 : ℝ) < 0 by {lc}) (lt_irrefl 0)" if lc else f"exfalso; {only(h2)}"]
            out += ["· " + sub[0]] + ["  " + x for x in sub[1:]]
        return out
    return "\n".join(lines + tree(0, [], [hyp] if hyp else [], base))


def _nu_poly(c: list, nu: str) -> str:
    terms = [f"{rat(v)} * {nu} ^ {j}" if j else rat(v) for j, v in enumerate(c) if v]
    return "(" + (" + ".join(terms) or "0") + ")"


def _nu_nonneg(c: list, nu: str, lo: Fraction, hi: Fraction) -> str:
    """Tactic text for `0 ≤ c(nu)` from hlo : lo ≤ nu, hhi : nu ≤ hi: the products the positivity proof
    uses (the CFL box, the square part of the square-free decomposition), then Bernstein on [lo, hi]."""
    box = "mul_nonneg (sub_nonneg.2 hlo) (sub_nonneg.2 hhi)"
    hints = [box, "sub_nonneg.2 hlo", "sub_nonneg.2 hhi"]
    c = univariate.trim(c)
    if univariate.deg(c) > 0:
        _, factors = univariate.squarefree(c)
        h = [Fraction(1)]
        for i, f in factors:
            h = univariate.mul(h, univariate.power(f, i // 2))
        for f in [h] + [f for _, f in factors if f != h]:
            if univariate.deg(f) > 0:
                t = _nu_poly(f, nu)
                hints += [f"sq_nonneg {t}", f"mul_nonneg ({box}) (sq_nonneg {t})",
                          f"mul_nonneg (sub_nonneg.2 hlo) (sq_nonneg {t})", f"mul_nonneg (sub_nonneg.2 hhi) (sq_nonneg {t})"]
    alts = ["positivity", "linarith", f"nlinarith [{', '.join(hints)}]"]
    b = checks.bernstein(list(c) or [Fraction(0)], lo, hi)
    if lo < hi and min(b) >= 0:
        alts.append(f"exact nonneg_of_bernstein (x := {nu}) (lo := {rat(lo)}) (hi := {rat(hi)}) [{', '.join(rat(v) for v in b)}] "
                    "(by norm_num) (by norm_num) hlo hhi (by simp [bernsteinSum, Fin.sum_univ_succ] <;> ring1)")
    return "first | " + " | ".join(f"({x})" for x in alts)


class _Harten:
    """The pieces of the proof of `TVD H` from a `harten.certify` certificate, as Lean text."""

    def __init__(self, spec: dict, inc: dict):
        from . import harten, limiters
        self.a = Fraction(inc["a"])
        self.lo, self.hi = limiters._tvd_range(spec)
        self.nu = f"({rat(self.a)} * lam)"
        alpha = {int(m): Fraction(v) for m, v in inc["alpha"].items()}
        beta = {int(m): Fraction(v) for m, v in inc["beta"].items()}
        self.A, self.B = harten.in_nu(alpha, self.a), harten.in_nu(beta, self.a)
        self.form = inc["form"]
        self.rg = {f: tuple(None if x is None else Fraction(x) for x in v) for f, v in inc["ranges"].items()}
        self.L = None
        if beta:                     # L = (F(lam1) - a uL - alpha(lam1) (uR - uL)) / beta(lam1), free of lam
            lam1 = Fraction(inc["lam1"])
            at = lambda co: sum((c * lam1 ** m for m, c in co.items()), Fraction(0))
            F = substitute(checks.numerical_flux(spec), {"lam": lit(lam1)})
            G = E("sub", (E("sub", (F, E("mul", (lit(self.a), var("uL"))))),
                          E("mul", (lit(at(alpha)), E("sub", (var("uR"), var("uL")))))))
            self.L = E("mul", (lit(1 / at(beta)), G))
        self.haves: dict = {}            # name -> (statement, proof), in order of first use

    def P(self, c: list) -> str:
        return _nu_poly(c, self.nu)

    def Ll(self, x: str, y: str, z: str) -> str:
        return real(self.L, {"uLL": x, "uL": y, "uR": z}, set(), [])

    def pw(self, x: str, y: str, z: str, goal, hyp=None, line=None) -> str:
        """`_pw` for a goal about L(x, y, z); goal(L) gives (kind, lhs, rhs) as polynomials, L with its
        square roots named."""
        ts, named = _sqrt_terms(self.L, {"uLL": x, "uL": y, "uR": z})
        return _pw(ts, goal(P.from_expr(named)), hyp, line, {"uLL": x, "uL": y, "uR": z})

    def have(self, name: str, stmt: str, proof: str, closed: bool = False) -> str:
        """`closed`: the statement mentions nothing of the context (no lam), so the proof starts by
        clearing it; the case splits then run about five times faster than beside the earlier haves."""
        self.haves.setdefault(name, (stmt, "clear * -\n" + proof if closed else proof))
        return name

    def nonneg(self, c: list) -> str:
        """The name of a `have` 0 ≤ c(nu)."""
        key = "hn_" + "_".join(str(v).replace("/", "d").replace("-", "m") for v in univariate.trim(c)) if univariate.trim(c) else "hn_0"
        return self.have(key, f"0 ≤ {self.P(c)}", _nu_nonneg(c, self.nu, self.lo, self.hi))

    def fact(self, fam: str, s: str, end: str) -> str:
        """`hf_*`: ∀ x y z, (the family's difference has sign s) → the bound of L/difference at `end`."""
        v = self.rg[fam + s][0 if end == "lo" else 1]
        d = "z - y" if fam == "phi" else "y - x"
        hyp = f"0 < {d}" if s == "+" else f"{d} < 0"
        L, vd = self.Ll("x", "y", "z"), f"{rat(v)} * ({d})"
        lower = (s == "+") == (end == "lo")
        small, big = (vd, L) if lower else (L, vd)
        cone = ((0, 1) if fam == "phi" else (1, 0)) + ((">",) if s == "+" else ("<",))
        dp = P.scale(P.add(P.var("uR"), P.var("uL"), -1) if fam == "phi" else P.add(P.var("uL"), P.var("uLL"), -1), v)
        goal = lambda Ln: ("le", dp, Ln) if lower else ("le", Ln, dp)
        return self.have(f"hf_{fam}{'p' if s == '+' else 'm'}_{end}", f"∀ x y z : ℝ, {hyp} → {small} ≤ {big}",
                         "intro x y z h\n" + self.pw("x", "y", "z", goal, cone), closed=True)

    def sign_goal(self, e0: list, terms: list, d: str) -> str:
        """`(0 < d → 0 ≤ Y) ∧ (d < 0 → Y ≤ 0)`-shaped goals (as left by `div_nonneg_of_sign` and
        `div_le_one_of_sign`), for Y = e0(nu) d + sum_k e_k(nu) L(args_k), each L(args_k) of family phi
        (difference z - y) or xi (y - x) with that difference equal to d: the two bullets."""
        out = []
        for s in "+-":
            hints, corner = [], list(e0)
            for ek, fam, args in terms:
                ek = univariate.trim(ek)
                if not ek:
                    continue
                pos = univariate.nonneg_on(ek, self.lo, self.hi)["nonneg"]
                if not pos and not univariate.nonneg_on(univariate.add([], ek, -1), self.lo, self.hi)["nonneg"]:
                    return "· fail\n· fail"           # a coefficient changes sign on the range: not replayed
                end = "lo" if pos else "hi"
                v = self.rg[fam + s][0 if end == "lo" else 1]
                if v is None:
                    return "· fail\n· fail"
                h = self.nonneg(ek if pos else univariate.add([], ek, -1))
                hints.append(f"mul_nonneg {h} (sub_nonneg.2 ({self.fact(fam, s, end)} {' '.join(args)} hd))")
                corner = univariate.add(corner, [x * v for x in ek])
            hc = self.nonneg(corner)
            hints.append(f"mul_nonneg {hc} hd.le" if s == "+" else f"mul_nonneg {hc} (neg_nonneg.2 hd.le)")
            out.append(f"· intro hd\n  linarith [{', '.join(hints)}]")
        return "\n".join(out)


def harten_proof(spec: dict, r: dict) -> str:
    """Proof of `TVD H` (lean_cert.harten_obligations) from the incremental-form certificate: instantiate
    `tvd_of_incremental` with the certificate's C and D, as functions of the stencil x0..x4 written with
    the limited slope L. The form identity: H - u_i = C Delta_+ - D Delta_- by ring, after
    `Harten.div_mul_of_zero` with the difference-zero identities L(x, y, y) = 0 (and L(y, y, z) = 0
    for the upwind split). The bounds: `div_nonneg_of_sign` / `div_le_one_of_sign`, then on each sign
    of the difference a linear combination of facts proven once (L/difference in the certificate's
    range, by splitting every |.| and linarith; the signs of the nu-coefficients and the corner
    polynomials, by nlinarith or Bernstein)."""
    h = _Harten(spec, r["witness"]["incremental_form"])
    P, nu, A, B = h.P, h.nu, h.A, h.B
    neg = lambda c: univariate.add([], c, -1)
    one, nuc = [Fraction(1)], [Fraction(0), Fraction(1)]
    Bt = univariate.trim(B)
    Lt = (lambda *x: h.Ll(*x)) if Bt else None

    def num(parts: list) -> str:
        """sum of (coefficient text, factor text)"""
        return "(" + " + ".join(f"{c} * {f}" for c, f in parts) + ")"

    def Cnum(x):
        if h.form == "upwind":
            return None
        parts = [(P(neg(A)), f"({x[3]} - {x[2]})")] + ([(P(neg(B)), Lt(x[1], x[2], x[3]))] if Bt else [])
        return num(parts)

    def Dnum(x):
        if h.form == "upwind":
            parts = [(nu, f"({x[2]} - {x[1]})")]
            if Bt:
                parts += [(P(B), Lt(x[1], x[2], x[3])), (P(neg(B)), Lt(x[0], x[1], x[2]))]
            return num(parts)
        parts = [(P(univariate.add(nuc, A, -1)), f"({x[2]} - {x[1]})")] + ([(P(neg(B)), Lt(x[0], x[1], x[2]))] if Bt else [])
        return num(parts)

    xs = [f"x{k}" for k in range(5)]
    Cb = "0" if h.form == "upwind" else f"{Cnum(xs)} / (x3 - x2)"
    Db = f"{Dnum(xs)} / (x2 - x1)"
    if Bt:
        h.have("z1", f"∀ x y : ℝ, {h.Ll('x', 'y', 'y')} = 0", "intro x y\n" + h.pw("x", "y", "y", lambda Ln: ("eq", Ln, {}), line="p"),
               closed=True)
        if h.form == "upwind":
            h.have("z2", f"∀ y z : ℝ, {h.Ll('y', 'y', 'z')} = 0", "intro y z\n" + h.pw("y", "y", "z", lambda Ln: ("eq", Ln, {}), line="q"),
                   closed=True)
    # the form identity
    w = [f"(w {k})" for k in range(5)]
    form = ["· intro w", "  try beta_reduce"]
    rws = []
    if h.form != "upwind":
        zs = " z1 (w 1) (w 2)," if Bt else ""
        form.append(f"  have hc : {Cnum(w)} / ((w 3) - (w 2)) * ((w 3) - (w 2)) = {Cnum(w)} := Harten.div_mul_of_zero "
                    f"(fun h => by\n      have e : w 3 = w 2 := by linarith\n      rw [e,{zs.rstrip(',')}]\n      ring)"
                    if Bt else f"  have hc : {Cnum(w)} / ((w 3) - (w 2)) * ((w 3) - (w 2)) = {Cnum(w)} := "
                    "Harten.div_mul_of_zero (fun h => by\n      have e : w 3 = w 2 := by linarith\n      rw [e]\n      ring)")
        rws.append("hc")
    zd = (" z1 (w 0) (w 1), z2 (w 1) (w 3)" if h.form == "upwind" else " z1 (w 0) (w 1)") if Bt else ""
    form.append(f"  have hd : {Dnum(w)} / ((w 2) - (w 1)) * ((w 2) - (w 1)) = {Dnum(w)} := Harten.div_mul_of_zero "
                f"(fun h => by\n      have e : w 2 = w 1 := by linarith\n      rw [e{',' if zd else ''}{zd}]\n      ring)")
    rws.append("hd")
    form.append(f"  rw [{', '.join(rws)}]")
    if Bt:                  # name the square roots of both interfaces, so ring sees small atoms
        for pre, args in (("sp", ("(w 1)", "(w 2)", "(w 3)")), ("sm", ("(w 0)", "(w 1)", "(w 2)"))):
            ts, _ = _sqrt_terms(h.L, dict(zip(("uLL", "uL", "uR"), args)), pre)
            form += [f"  generalize Real.sqrt (({t}) ^ 2) = {pre}{k}" for k, (t, _) in enumerate(ts)]
    form.append("  " + RING)
    # the bounds
    if h.form == "upwind":
        hC = ["· intro x0 x1 x2 x3 x4", "  exact le_refl 0"]
        terms = ([(B, "xi", ["x1", "x2", "x3"]), (neg(B), "phi", ["x0", "x1", "x2"])] if Bt else [])
        hD = ["· intro x0 x1 x2 x3 x4", "  try beta_reduce", "  apply Harten.div_nonneg_of_sign",
              _indent(h.sign_goal(nuc, terms, "x2 - x1"))]
        # 0 + D(x1..x5) <= 1: 1 - D = ((1 - nu) d - B L_xi + B L_phi) / d, d = x3 - x2
        terms = ([(neg(B), "xi", ["x2", "x3", "x4"]), (B, "phi", ["x1", "x2", "x3"])] if Bt else [])
        hCD = ["· intro x0 x1 x2 x3 x4 x5", "  try beta_reduce", "  rw [zero_add]", "  apply Harten.div_le_one_of_sign",
               _indent(h.sign_goal(univariate.add(one, nuc, -1), terms, "x3 - x2"))]
    else:
        tC = [(neg(B), "phi", ["x1", "x2", "x3"])] if Bt else []
        hC = ["· intro x0 x1 x2 x3 x4", "  try beta_reduce", "  apply Harten.div_nonneg_of_sign",
              _indent(h.sign_goal(neg(A), tC, "x3 - x2"))]
        tD = [(neg(B), "phi", ["x0", "x1", "x2"])] if Bt else []
        hD = ["· intro x0 x1 x2 x3 x4", "  try beta_reduce", "  apply Harten.div_nonneg_of_sign",
              _indent(h.sign_goal(univariate.add(nuc, A, -1), tD, "x2 - x1"))]
        # C(x0..x4) + D(x1..x5) = ((nu - 2A) d - 2B L(x1, x2, x3)) / d, d = x3 - x2; 1 minus it:
        tCD = [(univariate.add([], B, 2), "phi", ["x1", "x2", "x3"])] if Bt else []
        hCD = ["· intro x0 x1 x2 x3 x4 x5", "  try beta_reduce", "  rw [← add_div]", "  apply Harten.div_le_one_of_sign",
               _indent(h.sign_goal(univariate.add(univariate.add(one, nuc, -1), A, 2), tCD, "x3 - x2"))]
    head = ["intro lam hlam hlo hhi", "have hlam' := hlam.ne'"]
    for name, (stmt, proof) in h.haves.items():
        head.append(f"have {name} : {stmt} := by\n" + _indent(proof))
    head.append(f"refine tvd_of_incremental _ (fun x0 x1 x2 x3 x4 => {Cb}) (fun x0 x1 x2 x3 x4 => {Db}) ?_ ?_ ?_ ?_")
    return "\n".join(head + form + hC + hD + hCD)


def _indent(s: str, k: int = 2) -> str:
    return "\n".join(" " * k + line for line in s.splitlines())


# ---------------------------------------------------------------- exact rational refutations

STEADY = _first(("norm_num", "done"), ("field_simp", "ring1"), ("norm_num", "ring1"), ("norm_num", "field_simp", "ring1"),
                ("simp", "field_simp", "ring1"))


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
