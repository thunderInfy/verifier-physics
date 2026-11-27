"""Judge side of the Lean certificates for the exact scheme checks (trusted).

Three families of exact verdicts are stated:
- `conservation`, `consistency`, `positivity` (VERIFIED or REFUTED): the claim itself, or its
  negation, from the spec alone. The update, the numerical flux and the PDE flux are serialized node
  for node as real expressions (`real`); the meaning lives in `lean/PhysVerify/Scheme.lean`
  (`Conserves`, `NonnegComb`). Guarantee "proven (Lean)".
- the cell-based checks `monotonicity`, `tvd_harten`, `depth_positivity_exact` (VERIFIED): every
  per-cell fact the check certifies, p >= 0 on {a_j >= 0}, with p and the a_j re-derived from the spec
  by the check's own (trusted, exact) cell decomposition. The cells and their cover stay in Python, so
  the guarantee is "proven (Lean, per cell; cover in exact Python)".
- exact rational refutations of `tv_increase`, `max_principle_violation`, `monotonicity`,
  `entropy_stability` (a point with Q < 0) and the steady-step identities: the negated claim (`TVD`, `LocalMaxPrinciple`, `MonotoneOn3`) or the step
  identities, checked at the witness's point by norm_num. Guarantee "proven (Lean)".
The untrusted planner (`lean_planner.py`) supplies only tactic text, from the check's witness. All
statements of a run go into one file checked by `lean_backend.check_batch`; a verdict's guarantee is
upgraded only if every theorem behind it is accepted, and otherwise stays the exact-Python label.
Lean never changes a status, only the guarantee.

Junk values: Lean has x/0 = 0 and sqrt(x) = 0 for x < 0. A statement is written only if every
denominator is a monomial in variables that the statement assumes > 0 (lam = dt/dx, the spec's
positive parameters and positive state components), so no division in it can be by 0; every sqrt
gets a separate theorem `<name>_sqrt` that its argument is >= 0 on the statement's domain.
"""

from __future__ import annotations

from fractions import Fraction

from .. import lean_backend
from ..expr import E, diff, substitute, var, variables
from . import checks, poly as P, systems

LEAN = "proven (Lean)"
SCOPE = ("conservation", "consistency", "positivity")
SLOTS = {"m2": "qm2", "m1": "qm1", "0": "q0", "p1": "qp1", "p2": "qp2"}
IFACE = ("LL", "L", "R", "RR")


class Unsupported(Exception):
    """The statement cannot be written faithfully (e.g. a division by a sign-indefinite term)."""


def rat(q) -> str:
    q = Fraction(q)
    return f"({q.numerator} : ℝ)" if q.denominator == 1 else f"(({q.numerator} : ℝ) / {q.denominator})"


def real(e: E, names: dict, positive: set, roots: list) -> str:
    """e as a fully parenthesized real expression; `names` maps variables to Lean terms. Square-root
    arguments are appended to `roots` (as Lean text)."""
    k, a = e.kind, e.args
    r = lambda x: real(x, names, positive, roots)
    if k == "var":
        if e.name not in names:
            raise Unsupported(f"free variable {e.name}")
        return names[e.name]
    if k == "lit":
        return rat(e.q)
    if k == "neg":
        return f"(-{r(a[0])})"
    if k in ("add", "sub", "mul"):
        return f"({r(a[0])} {dict(add='+', sub='-', mul='*')[k]} {r(a[1])})"
    if k == "div":
        _nonzero(a[1], positive)
        return f"({r(a[0])} / {r(a[1])})"
    if k == "powi":
        if e.q < 0:
            _nonzero(a[0], positive)
            return f"(({r(a[0])})⁻¹ ^ ({-e.q} : ℕ))"
        return f"({r(a[0])} ^ ({e.q} : ℕ))"
    if k == "sqrt":
        roots.append(r(a[0]))
        return f"(Real.sqrt {roots[-1]})"
    raise Unsupported(f"{k} is not in the scheme fragment")


def _nonzero(d: E, positive: set) -> None:
    """A denominator must be a non-zero literal or a monomial in variables assumed > 0."""
    if d.kind == "lit" and d.q != 0:
        return
    if d.kind == "var" and d.name in positive:
        return
    if d.kind == "mul":
        return _nonzero(d.args[0], positive) or _nonzero(d.args[1], positive)
    if d.kind == "powi":
        return _nonzero(d.args[0], positive)
    raise Unsupported("a denominator is not a monomial in positive variables")


def layout(spec: dict) -> dict:
    """Components, positive variables, binders and the domain predicate shared by the statements."""
    if systems.is_system(spec):
        sys = systems.read(spec)
        state, params, dom = sys["state"], sorted(sys["params"]), sys["domain"]
        update, nf, flux = sys["update"], sys["nf"], sys["flux"]
    else:
        state, params, dom = ["u"], [], set()
        F = checks.numerical_flux(spec)
        update, nf, flux = [checks.update(spec)], (None if F is None else [F]), [checks.pde_flux(spec)]
    binders = ["lam"] + params
    pos_names = set(binders) | {f"{c}{s}" for c in dom for s in [*SLOTS, *IFACE, ""]}
    d = " ∧ ".join(f"0 < q {state.index(c)}" for c in state if c in dom) or "True"
    return {"state": state, "m": len(state), "binders": binders, "positive": pos_names,
            "update": update, "nf": nf, "flux": flux, "domain": f"(fun q : Fin {len(state)} → ℝ => {d})",
            "dom": dom}


def _head(L: dict) -> str:
    """`∀ (lam g : ℝ), 0 < lam → 0 < g →`: lam = dt/dx and the positive parameters."""
    return f"∀ ({' '.join(L['binders'])} : ℝ), " + "".join(f"0 < {b} → " for b in L["binders"])


def _stencil_names(L: dict) -> dict:
    out = {b: b for b in L["binders"]}
    for j, c in enumerate(L["state"]):
        out.update({f"{c}{s}": f"({q} {j})" for s, q in SLOTS.items()})
    return out


def _with_roots(name: str, stmt: str, roots: list, prefix: str) -> list:
    """The statement and, if it has square roots, the theorem that their arguments are >= 0."""
    out = [(name, stmt)]
    if roots:
        out.append((f"{name}_sqrt", prefix + " ∧ ".join(f"0 ≤ {x}" for x in dict.fromkeys(roots))))
    return out


def conservation_statement(L: dict, k: int) -> tuple[str, str, list]:
    """(statement, binder prefix for the sqrt theorem, sqrt arguments) for component k."""
    roots: list = []
    H = real(L["update"][k], _stencil_names(L), L["positive"], roots)
    g = f"(fun qm2 qm1 q0 qp1 qp2 : Fin {L['m']} → ℝ => {H} - q0 {k})"
    qs = f"∀ qm2 qm1 q0 qp1 qp2 : Fin {L['m']} → ℝ, " + "".join(f"{L['domain']} {q} → " for q in SLOTS.values())
    return f"{_head(L)}PhysVerify.Scheme.Conserves {L['domain']} {g}", _head(L) + qs, roots


def consistency_statement(L: dict, k: int) -> tuple[str, str, list]:
    roots: list = []
    names = {b: b for b in L["binders"]}
    for j, c in enumerate(L["state"]):
        names.update({f"{c}{s}": f"(q {j})" for s in [*IFACE, ""]})
    F = real(L["nf"][k], names, L["positive"], roots)
    f = real(L["flux"][k], names, L["positive"], roots)
    q = f"∀ q : Fin {L['m']} → ℝ, {L['domain']} q → "
    return f"{_head(L)}{q}{F} = {f}", _head(L) + q, roots


def positivity_statement(spec: dict, L: dict) -> tuple[str, str, list]:
    if L["m"] != 1:
        raise Unsupported("positivity is a scalar check")
    lo, hi = (Fraction(x) for x in spec["claims"]["positive_cfl"])
    a, _ = checks.linear_coefficients(spec)
    roots: list = []
    names = {"lam": "lam", **{x: f"(w {i})" for i, x in enumerate(checks.STENCIL5)}}
    H = real(L["update"][0], names, {"lam"}, roots)
    if roots:
        raise Unsupported("square root in a linear update")
    nu = f"({rat(a)} * lam)"
    return (f"∀ lam : ℝ, 0 < lam → {rat(lo)} ≤ {nu} → {nu} ≤ {rat(hi)} → "
            f"PhysVerify.Scheme.NonnegComb (fun w : Fin 5 → ℝ => {H})"), "", []


def obligations(spec: dict, r: dict, tag: str, planner=None) -> list[tuple[str, str, str]]:
    """(name, statement, proof) for one exact check result. The planner (default `lean_planner`)
    supplies only the proofs. Raises Unsupported if the verdict cannot be stated faithfully."""
    if planner is None:
        from . import lean_planner as planner
    L = layout(spec)
    check, refuted = r["check"], r["status"] == checks.REFUTED
    w = r["witness"]
    if check == "conservation":
        ks = [L["state"].index(c) for c, x in w["sum_change"].items() if x != "0"][:1] \
            if refuted and isinstance(w.get("sum_change"), dict) else [0] if refuted else range(L["m"])
        made = [(k, *conservation_statement(L, k)) for k in ks]
    elif check == "consistency":
        if L["nf"] is None:
            raise Unsupported("the flux recovered from an update is not certified yet")
        ks = [L["state"].index(w.get("component", L["state"][0]))] if refuted else range(L["m"])
        made = [(k, *consistency_statement(L, k)) for k in ks]
    else:
        made = [(0, *positivity_statement(spec, L))]
    out = []
    for k, stmt, prefix, roots in made:
        prop = f"¬ ({stmt})" if refuted else stmt
        for n, s in _with_roots(f"{tag}_{check}_{k}", prop, roots, prefix):
            proof = (planner.sqrt_proof(L, len(dict.fromkeys(roots))) if n.endswith("_sqrt")
                     else planner.proof(spec, L, r, k))
            out.append((n, s, proof))
    return out


# ---------------------------------------------------------------- per-cell certificates (Farkas class)

LEAN_CELLS = "proven (Lean, per cell; cover in exact Python)"
CELL_SCOPE = ("monotonicity", "tvd_harten", "depth_positivity_exact")


def poly_lean(p: P.Poly, names: dict) -> str:
    """A normal-form polynomial (plain variables, exponents >= 0) as a Lean real expression."""
    terms = []
    for m, c in sorted(p.items(), key=lambda mc: P._key(mc[0])):
        if any(a[0] != "v" or k < 0 for a, k in m):
            raise Unsupported("a cell polynomial has a square root or a negative power")
        factors = [names[a[1]] if k == 1 else f"{names[a[1]]} ^ ({k} : ℕ)" for a, k in m]
        terms.append(" * ".join(([] if c == 1 and factors else [rat(c)]) + factors))
    return "(" + (" + ".join(terms) or "0") + ")"


def cell_statement(p: P.Poly, atoms: list) -> str:
    """`∀ x..., 0 ≤ a_1 → ... → 0 ≤ p`: p >= 0 on the closed cell {a_j >= 0}."""
    vs = sorted(P.variables(p).union(*(P.variables(a) for a in atoms)))
    names = {v: "v_" + v.lstrip("_") for v in vs}
    hyps = "".join(f"0 ≤ {poly_lean(a, names)} → " for a in atoms)
    return (f"∀ {' '.join(names[v] for v in vs)} : ℝ, " if vs else "") + f"{hyps}0 ≤ {poly_lean(p, names)}"


def _monotone_goals(spec: dict, r: dict) -> list:
    """The facts `checks.monotonicity` certifies, re-derived from the spec as it derives them: on each
    sign cell (intersected with the scaled CFL region) every scaled partial of H is >= 0, or the cell is
    empty (-1 >= 0 on it). Each goal is (p, atoms, the check's certificate as a hint for the planner)."""
    e = checks.update(spec)
    if checks.stencil_of(variables(e)) != checks.STENCIL:
        raise Unsupported("the cells of limiters.monotonicity_wide are not stated yet")
    region = [checks._scaled(a)[0] for a in checks._monotone_cfl_atoms(spec, Fraction(spec["claims"]["monotone_cfl"]))]
    region.append(P.var("lam"))
    out = []
    for (Hc, atoms), row in zip(checks.sign_cells(e), r["witness"]["cells"], strict=True):
        reg = [checks._scaled(a)[0] for a in atoms] + region
        if "empty" in row:
            out.append((P.const(-1), reg, row["empty"]))
            continue
        out += [(checks._scaled(P.derivative(Hc, x))[0], reg, row["partials"][x]["certificate"]) for x in checks.STENCIL]
    return out


def _depth_goals(spec: dict, r: dict) -> list:
    """The facts `systems.depth_positivity_exact` certifies, re-derived as it derives them: on each cell
    every scaled depth coefficient c_j >= 0, and one c_j (or their sum) minus eps*t is >= 0 (t = 1 or
    z_j). The variables are the relaxed ones of the check (z_j = lam*sqrt(g h_j) only known >= 0)."""
    S = systems
    c = Fraction(spec["claims"]["riemann"]["cfl"])
    e = S.read(spec)["update"][0]
    cells, roots = S._depth_cells(substitute(e, {f"m{j}": E("mul", (var(f"h{j}"), var(f"u{j}"))) for j in S.SLOTS}))
    zs, ws = [f"z_{j}" for j in S.SLOTS], [f"w_{j}" for j in S.SLOTS]
    region = ([P.add(P.const(c), P.add(P.scale(P.var(w), s), P.var(z)), -1) for w, z in zip(ws, zs) for s in (1, -1)]
              + [P.var(z) for z in zs] + [P.var("lam")] + [P.var(t) for t in roots])
    out = []
    for (Hc, atoms), row in zip(cells, r["witness"]["cells"], strict=True):
        reg = [S._depth_scaled(a) for a in atoms] + region
        if "empty" in row:
            out.append((P.const(-1), reg, row["empty"]))
            continue
        scaled = {h: S._depth_scaled(S._depth_coefficients(Hc).get(h, {})) for h in S.DEPTH}
        out += [(p, reg, row["certificates"][h]) for h, p in scaled.items()]
        total = P.add(P.add(scaled["hm1"], scaled["h0"]), scaled["hp1"])
        cands = sorted(((h, p) for h, p in scaled.items() if p), key=lambda x: len(P.variables(x[1])))
        strict = None
        for _, p in cands + [("sum", total)]:
            cellvars = {v[2:] for v in P.variables(p) if v.startswith(("w_", "z_"))}
            for t in [P.var(z) for z in zs if z[2:] in cellvars] + [P.const(1)]:
                q = P.add(p, P.scale(t, S.DEPTH_EPS), -1)
                if strict is None and (cert := S._depth_certify(q, reg)):
                    strict = (q, reg, cert)
        if strict is None:
            raise Unsupported("strict positivity certificate not re-derived")
        out.append(strict)
    return out


def _tvd_goals(spec: dict, r: dict) -> list:
    """The facts `limiters.tvd_harten` certifies, re-derived as it derives them: on each retained half-cell,
    Harten's two conditions as polynomials >= 0 for every nu in [lo, hi] (nu is a variable with the
    atoms nu - lo >= 0, hi - nu >= 0)."""
    from . import limiters as Lm
    lo, hi = Lm._tvd_range(spec)
    a = Lm._advection(spec)
    delta = P.add(P.var("u0"), P.var("um1"), -1) if a > 0 else P.add(P.var("up1"), P.var("u0"), -1)
    nu_atoms = [P.add(Lm.NU, P.const(lo), -1), P.add(P.const(hi), Lm.NU, -1)]
    out = []
    for c in Lm.cells(checks.update(spec))["cells"]:
        N = Lm._in_nu(P.add(c["poly"], P.var("u0"), -1), a)
        for s in (1, -1):
            sd = P.scale(delta, s)
            atoms = c["atoms"] + [sd]
            if Lm.lower_dimensional(atoms):
                continue
            goals = ([P.scale(N, -s), P.scale(P.add(N, delta), s)] if a > 0
                     else [P.scale(N, s), P.scale(P.add(delta, N, -1), s)])
            out += [(g, atoms + nu_atoms, {"nu_interval": (lo, hi), "cell_atoms": atoms}) for g in goals]
    return out


CELL_GOALS = {"monotonicity": _monotone_goals, "depth_positivity_exact": _depth_goals, "tvd_harten": _tvd_goals}


def cell_obligations(spec: dict, r: dict, tag: str, planner=None) -> list[tuple[str, str, str]]:
    if planner is None:
        from . import lean_planner as planner
    return [(f"{tag}_{r['check']}_{j}", cell_statement(p, atoms), planner.cell_proof(p, atoms, hint))
            for j, (p, atoms, hint) in enumerate(CELL_GOALS[r["check"]](spec, r))]


# ---------------------------------------------------------------- exact rational refutations

REF_SCOPE = ("tv_increase", "max_principle_violation", "monotonicity", "steady_nonentropy_step",
             "steady_nonentropy_step_semidiscrete", "entropy_stability")


def _at(e: E, vals: dict, extra: dict, roots: list) -> str:
    """e with stencil (or flux) variables replaced by exact rationals."""
    return real(e, {**extra, **{x: rat(v) for x, v in vals.items()}}, {"lam"}, roots)


def refutation_obligations(spec: dict, r: dict, tag: str, planner=None) -> list[tuple[str, str, str]]:
    """The negated claim (or, for a steady step, the step identities) for an exact refutation; the
    planner proves it at the witness's rational point with norm_num."""
    if planner is None:
        from . import lean_planner as planner
    check, w = r["check"], r["witness"]
    e, roots = checks.update(spec), []
    if check in ("tv_increase", "max_principle_violation"):
        from . import limiters
        lo, hi = limiters._tvd_range(spec)
        nu = f"({rat(limiters._advection(spec))} * lam)"
        H = real(e, {"lam": "lam", **{x: f"(w {i})" for i, x in enumerate(checks.STENCIL5)}}, {"lam"}, roots)
        pred = "TVD" if check == "tv_increase" else "LocalMaxPrinciple"
        head = f"∀ lam : ℝ, 0 < lam → {rat(lo)} ≤ {nu} → {nu} ≤ {rat(hi)} → "
        stmt, prefix = f"¬ ({head}PhysVerify.Scheme.{pred} (fun w : Fin 5 → ℝ => {H}))", f"{head}∀ w : Fin 5 → ℝ, "
    elif check == "monotonicity" and checks.stencil_of(variables(e)) != checks.STENCIL:
        # limiters.monotonicity_wide: linear advection, the CFL bound |a*lam| <= c is on lam only
        from . import limiters
        a, c = limiters._advection(spec), Fraction(spec["claims"]["monotone_cfl"])
        H = real(e, {"lam": "lam", **{x: f"(w {i})" for i, x in enumerate(checks.STENCIL5)}}, {"lam"}, roots)
        head = f"∀ lam : ℝ, 0 < lam → {rat(-c)} ≤ {rat(a)} * lam → {rat(a)} * lam ≤ {rat(c)} → "
        stmt, prefix = f"¬ ({head}PhysVerify.Scheme.MonotoneVec (fun w : Fin 5 → ℝ => {H}))", f"{head}∀ w : Fin 5 → ℝ, "
    elif check == "monotonicity":
        cfl = checks._monotone_cfl_atoms(spec, Fraction(spec["claims"]["monotone_cfl"]))[:2]   # the um1 pair
        C = " ∧ ".join(f"0 ≤ {poly_lean(a, {'lam': 'lam', 'um1': 'x'})}" for a in cfl)
        H = real(e, {x: x for x in ("um1", "u0", "up1", "lam")}, {"lam"}, roots)
        stmt = (f"¬ (∀ lam : ℝ, 0 < lam → PhysVerify.Scheme.MonotoneOn3 (fun x : ℝ => {C}) "
                f"(fun um1 u0 up1 : ℝ => {H}))")
        prefix = "∀ lam : ℝ, 0 < lam → ∀ um1 u0 up1 : ℝ, "
    elif check == "entropy_stability":
        # Q = -[v](F - F*) = [psi] - [v] F, as [v] F* = [psi]: no division by uR - uL. The defaults are
        # those schemes.check runs the check with when the spec claims nothing about entropy
        spec = {**spec, "claims": {"entropy_stability": {}, **spec.get("claims", {})}}
        eta, q, _ = checks.entropy_pair(spec)
        v = diff(eta, "u")
        psi = E("sub", (E("mul", (v, checks.pde_flux(spec))), q))
        jump = lambda x: E("sub", (substitute(x, {"u": var("uR")}), substitute(x, {"u": var("uL")})))
        Q = E("sub", (jump(psi), E("mul", (jump(v), checks.numerical_flux(spec)))))
        names = {x: x for x in ("uL", "uR", "lam")}
        cfl = "".join(f"0 ≤ {poly_lean(a, names)} → " for a in checks._cfl_atoms(spec))
        prefix = "∀ lam : ℝ, 0 < lam → ∀ uL uR : ℝ, " + cfl
        stmt = f"¬ ({prefix}0 ≤ {real(Q, names, {'lam'}, roots)})"
    else:
        uL, uR = Fraction(w["uL"]), Fraction(w["uR"])
        fp = P.derivative(P.from_expr(checks.pde_flux(spec)), "u")
        facts = f"({rat(uL)} < {rat(uR)} ∧ {poly_lean(fp, {'u': rat(uL)})} < {poly_lean(fp, {'u': rat(uR)})})"
        v = {"L": uL, "R": uR}
        if check == "steady_nonentropy_step":
            wide = checks.stencil_of(variables(e)) != checks.STENCIL
            names, table = (checks.STENCIL5, checks.STEADY_STENCILS5) if wide else (checks.STENCIL, checks.STEADY_STENCILS)
            eqs = [f"{_at(e, {x: v[c] for x, c in zip(names, s)}, {'lam': 'lam'}, roots)} = {rat(v[t])}"
                   for _, s, t in table]
        else:
            F = checks.numerical_flux(spec)
            wide = bool(variables(F) & {"uLL", "uRR"})
            names, table = ((list(checks.FLUX_ARGS), checks.STEADY_INTERFACES4) if wide
                            else (["uL", "uR"], checks.STEADY_INTERFACES))
            at = lambda s: _at(F, {x: v[c] for x, c in zip(names, s)}, {"lam": "lam"}, roots)
            eqs = [f"{at(a)} = {at(b)}" for _, a, b in table]
        stmt, prefix = f"{facts} ∧ ∀ lam : ℝ, 0 < lam → " + " ∧ ".join(eqs), "∀ lam : ℝ, 0 < lam → "
    name = f"{tag}_{check}_ref"
    return [(n, s, planner.sqrt_proof(None, len(dict.fromkeys(roots))) if n.endswith("_sqrt")
             else planner.refutation_proof(spec, r))
            for n, s in _with_roots(name, stmt, roots, prefix)]


# ---------------------------------------------------------------- one run

def certify(pairs: list[tuple[dict, dict]], timeout: int | None = None, planner=None) -> dict:
    """Kernel-check the exact verdicts in scope of every (spec, report) pair with one Lean run and
    upgrade the guarantee of those whose theorems are all accepted. Returns {theorem: LeanResult}."""
    items, owner = [], []
    for i, (spec, report) in enumerate(pairs):
        for r in report["checks"]:
            cell = r["check"] in CELL_SCOPE and r["status"] == checks.VERIFIED
            if cell:
                make = cell_obligations
            elif r["check"] in SCOPE and r["status"] in (checks.VERIFIED, checks.REFUTED):
                make = obligations
            elif r["check"] in REF_SCOPE and r["status"] == checks.REFUTED:
                make = refutation_obligations
            else:
                continue
            try:
                obs = make(spec, r, f"s{i}", planner)
            except (Unsupported, checks.NotLinear, P.Undecided, KeyError, ValueError) as ex:
                r["lean"] = f"not stated: {ex}"
                continue
            items += obs
            owner.append((r, [n for n, _, _ in obs], LEAN_CELLS if cell else LEAN))
    # one file for the whole run; the limit grows with it (about 1 s per theorem when warm, 1.4 s on the first run
    # after a build, more under load: README, costs of a full pass)
    timeout = timeout or 600 + 10 * len(items)
    results = lean_backend.check_batch(items, preamble="set_option linter.all false\nset_option maxHeartbeats 1000000", timeout=timeout,
                                       module="PhysVerify.Scheme", opens="PhysVerify PhysVerify.Scheme") if items else {}
    for r, names, label in owner:
        if names and all(results[n].ok for n in names):
            # keep a check's own caveat (the entropy check's "semi-discrete inequality only")
            r["guarantee"] = label + r["guarantee"][len(checks.EXACT):] if r["guarantee"].startswith(checks.EXACT) else label
            r["lean"] = f"{len(names)} theorems accepted"
        else:
            r["lean"] = "not proven: " + ", ".join(n for n in names if not results[n].ok)
    for _, report in pairs:
        relabel_claims(report)
    return results


def verdict_label(labels: list[str]) -> str | None:
    """The Lean guarantee of a verdict whose checks carry `labels`, or None unless every one is a Lean
    label: the weaker label if any of them is per cell, then the caveats of all of them."""
    from . import claims as C
    if not labels or not all(x.startswith("proven (Lean") for x in labels):
        return None
    return C.with_caveats(LEAN_CELLS if any(x.startswith(LEAN_CELLS) for x in labels) else LEAN, labels)


def relabel_claims(report: dict) -> None:
    """A claim decided exactly gets a Lean guarantee when every check it rests on (the deciding checks
    and the exact checks their rows require) has one."""
    from . import claims as C
    by = {r["check"]: r for r in report["checks"]}
    for v in report["claims"]:
        if not v["guarantee"].startswith(C.EXACT):
            continue
        need = C.rests_on(v["claim"], v["decided_by"])
        v["guarantee"] = verdict_label([by.get(c, {}).get("guarantee") or "" for c in need]) or v["guarantee"]
