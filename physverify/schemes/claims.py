"""Trusted judge: which checks bear on which claims, and how strongly.

A check returns its own status, but a check is evidence about a claim, not the claim. Tadmor's
inequality is sufficient for "the method-of-lines scheme selects the entropy solution" (it says
nothing about time stepping) and equivalent to "entropy stable in Tadmor's sense"; the shock-speed study is only necessary for "conservative". The
relation lives here, in a fixed table, so no tool can report the strength of its own evidence.

The guarantee is orthogonal to the relation, and it also comes from this table: a check listed as
empirical can never produce VERIFIED or REFUTED, whatever status string it returns. An exact check
gives VERIFIED/REFUTED; an empirical one NOT_REFUTED/REFUTED_EMPIRICALLY. An empirical pass never
counts as a verification at all, even under a SUFFICIENT or EQUIVALENT row: a finite-grid study
can fail to refute a claim, not prove it. An empirical failure stays decisive.

Per (relation, outcome of one check):
    SUFFICIENT  pass -> verified      fail -> unknown
    NECESSARY   pass -> not refuted   fail -> refuted
    EQUIVALENT  pass -> verified      fail -> refuted
and an UNKNOWN (or NOT_APPLICABLE) outcome gives unknown. A row may also require other exact checks
to be VERIFIED on the same spec (monotonicity proves the entropy limit only for a conservative,
consistent scheme); if one is not, the row gives unknown whatever its own check says. Over several checks for one claim, any
refutation refutes and any verification verifies; both at once is INCONSISTENT, which is a bug in
a checker, a spec or this table, never a physics result.
"""

from __future__ import annotations

from .. import claimkinds

SUFFICIENT, NECESSARY, EQUIVALENT = "SUFFICIENT", "NECESSARY", "EQUIVALENT"
EXACT, EMPIRICAL = "exact", "empirical"
VERIFIED, REFUTED, NOT_REFUTED, REFUTED_EMPIRICALLY = "VERIFIED", "REFUTED", "NOT_REFUTED", "REFUTED_EMPIRICALLY"
UNKNOWN, SUSPICIOUS, INCONSISTENT = "UNKNOWN", "SUSPICIOUS", "INCONSISTENT"
FAILURES = (REFUTED, REFUTED_EMPIRICALLY, SUSPICIOUS, INCONSISTENT)

# The strength of each check, fixed here rather than read from the check's own result.
GUARANTEE = {"consistency": EXACT, "conservation": EXACT, "positivity": EXACT, "entropy_stability": EXACT,
             "order/combined": EMPIRICAL, "order/space": EMPIRICAL, "order/time": EMPIRICAL,
             "monotonicity": EXACT, "shock_speed": EMPIRICAL, "entropy_rarefaction": EMPIRICAL,
             "truncation_order": EXACT, "von_neumann": EXACT, "lax_richtmyer_scope": EXACT,
             "steady_nonentropy_step": EXACT, "steady_nonentropy_step_semidiscrete": EXACT,
             "von_neumann_small_cfl": EXACT, "hyperbolicity": EXACT,
             "depth_positivity": EMPIRICAL, "riemann_l1": EMPIRICAL, "depth_positivity_exact": EXACT,
             "tvd_harten": EXACT, "tv_increase": EXACT, "truncation_branches": EXACT, "truncation_smooth_data": EXACT,
             "max_principle_violation": EXACT, "tvd_linear": EXACT, "max_principle_linear": EXACT,
             "order_l1/combined": EMPIRICAL, "order_linf/combined": EMPIRICAL}
GUARANTEE.update({"flux_lipschitz": EXACT, "shock_scope_monotone": EXACT, "shock_scope_tvd": EXACT})  # shockspeed.py
GUARANTEE.update({"stationary_rh_violation": EXACT, "stationary_shock_rh_violation": EXACT})  # fixedjump.py
GUARANTEE.update({"stated_identity": EXACT})  # identity.py

_ORDER = ("only on the spec's smooth test problem and grids; blind to conservation (a non-conservative "
          "scheme converges at order 1 on smooth data)")
_TADMOR = ("sufficiency needs the scheme to converge, and uses that for a convex scalar flux one strictly "
           "convex entropy inequality singles out the entropy solution")

_CRANDALL_MAJDA = ("Crandall-Majda (1980): a conservative, consistent, monotone scheme converges to the entropy "
                   "solution as dx -> 0 at fixed dt/dx (initial data in L1 and BV, with values in the CFL range; "
                   "a monotone consistent scheme keeps them there by the maximum principle); also needs the "
                   "conservation and consistency checks to pass")

_STEADY_STEP = ("a scheme with a steady non-entropy step converges, trivially, to that step on its Riemann data "
                "(a non-entropy weak solution if the scheme is conservative and f(uL) = f(uR), otherwise not even "
                "a weak solution); for convex f with f'(uL) < f'(uR) the entropy solution is the rarefaction fan, "
                "so the limit is not the entropy solution")
_STEADY_STEP_SEMI = ("a numerical flux with F(uL, uL) = F(uL, uR) = F(uR, uR) makes the step uL | uR, jump at a cell "
                     "interface, a steady state of the method of lines on every grid (the unique solution, F being "
                     "locally Lipschitz), so the semi-discrete scheme converges, trivially, to that step on its "
                     "Riemann data; for convex f with f'(uL) < f'(uR) the entropy solution is the rarefaction fan, "
                     "so the limit is not the entropy solution")
_SMALL_CFL = ("linear constant-coefficient schemes on periodic grids, nu = a*dt/dx of the sign of a; VERIFIED is a "
              "von Neumann (l2) certificate on [0, nu1]. On a periodic grid the Fourier modes are eigenvectors of "
              "the update, so |g| > 1 on an open theta-set (which a REFUTED witness gives for every nu in (0, nu1]) "
              "means unbounded growth in every norm, max norm included, once N is large enough for a grid mode "
              "2*pi*j/N to land there: the refutation also refutes max-norm stability")

_LAX_RICHTMYER = ("Lax-Richtmyer equivalence: consistent of order p plus stable implies convergence of order p for "
                  "smooth initial data; linear constant-coefficient schemes on periodic grids only. The order is "
                  "in the discrete l2 norm (von Neumann stability is l2 stability), which gives the same order in "
                  "L1 on the unit periodic grid by Cauchy-Schwarz; the L-infinity order is not covered. Asymptotic: it "
                  "says nothing about the error constant, and gives order at least p; also needs the von Neumann "
                  "check and the structural scope check (linear update, combined refinement at a stable dt/dx, "
                  "consistency order = claimed order, smooth data) to pass")

_HARTEN = ("Harten's lemma (1983): an update u_i - C_{i-1/2} Delta_{i-1/2} + D_{i+1/2} Delta_{i+1/2} with C, D >= 0 "
           "and C_{i+1/2} + D_{i+1/2} <= 1 for every state is TVD; certified either with the upwind split (D = 0 for "
           "a > 0) on sign cells that cover the state space, or with general C, D read off the numerical flux of a "
           "flux-limited scheme (harten.py). The form is not unique, so a failure says nothing")
_HARTEN_MP = ("the Harten certificate shows u_i^{n+1} = (1 - C_{i-1/2} - D_{i+1/2}) u_i + C_{i-1/2} u_{i-1} + "
              "D_{i+1/2} u_{i+1} with C, D >= 0 and C_{i-1/2} + D_{i+1/2} <= 1 for every state (with the upwind split, "
              "D = 0 and C in [0, 1]): a convex combination of stencil values")
_LINEAR_TVD = ("linear constant-coefficient schemes u_i' = sum_k c_k(nu) u_{i+k} with sum_k c_k = 1 only: the differences "
               "evolve by the same convolution, whose l1 norm on zero-sum (difference) vectors is sum_k |c_k|, and with "
               "sum_k c_k = 1 that is <= 1 iff every c_k >= 0 (decided exactly on the claimed nu-range, Bernstein or "
               "square-free decomposition + Sturm). The TVD direction holds on every periodic grid and on the line; the "
               "refutation's box data (differences e_0 - e_w, w the stencil width) needs a periodic grid of N >= 2w "
               "cells, or the line, for the two images not to overlap: on smaller periodic grids a scheme with a "
               "negative coefficient can still be TVD")
_LINEAR_MP = ("linear constant-coefficient schemes u_i' = sum_k c_k(nu) u_{i+k} with sum_k c_k = 1 only: every c_k >= 0 "
              "makes u_i' a convex combination of its stencil values; a negative c_j gives u_i' = c_j < 0 for the data 1 "
              "at i + j and 0 elsewhere in the stencil (any periodic grid with at least as many cells as the stencil, "
              "or the line); nonnegativity decided exactly on the claimed nu-range")
_TV_INCREASE = "one explicit periodic rational state whose total variation grows in one step at a nu in the claimed range"
_BRANCHES = ("on each sign cell (the cells cover the state space) the update is a linear scheme; if each has "
             "truncation order >= p, every stencil sampled from smooth data lies in a cell whose linear scheme has "
             "truncation error O(dx^p), with a constant bounded by the data's derivatives, uniformly over the "
             "finitely many cells")
_SMOOTH_DATA = ("one explicit polynomial exact solution u = U(x - a t) and grid placement whose stencil lies in a "
                "lower-order branch for all small dx; this is the local truncation error only, which says nothing "
                "about the global error (a nonlinear scheme has no Lax-Richtmyer theorem, and it may damp local errors)")
_NORM = ("only on the spec's test problem, grids and dt/dx; a refinement study refutes or fails to refute, it never "
         "proves an order (no Lax-Richtmyer theorem for nonlinear schemes)")
_DEPTH_STEP = ("induction over n: if h_j^n > 0 and the CFL condition holds on every stencil i-1, i, i+1, the step gives "
               "h_i^{n+1} > 0, so positive initial data stay positive at every step at which the CFL condition holds; "
               "the converse: a positive stencil state a | b | c within the CFL bound whose step gives h <= 0, embedded "
               "in the grid a, ..., a, b, c, ..., c (every cell within the bound), is positive initial data whose "
               "first step has h <= 0. Shallow water, three-point schemes, any boundary that copies grid states "
               "into ghost cells; wet/dry states (h = 0) are outside the claim")

# shock speed and weak limits (scalar 1D conservation laws, refinement dx -> 0 at fixed dt/dx)
_LAX_WENDROFF = ("Lax-Wendroff theorem (1960): for a conservative scheme with a consistent, locally Lipschitz numerical "
                 "flux, any limit u of the scheme as dx -> 0 at fixed dt/dx that is bounded and a.e. (hence L1_loc) is a "
                 "weak solution; conditional: it says nothing about whether the scheme converges, and nothing about "
                 "entropy (the limit may be a non-entropy weak solution); also needs the consistency and flux_lipschitz "
                 "checks to pass")
_CM_SHOCK = ("Crandall-Majda (1980): a conservative, consistent, monotone scheme with a locally Lipschitz numerical flux "
             "converges as dx -> 0 at fixed dt/dx (the whole sequence, in L1_loc) to the entropy solution, for data in "
             "L-infinity and BV with values in the CFL range (Riemann data reduce to compactly supported data by finite "
             "propagation speed at fixed dt/dx); the entropy solution is a weak solution, so across each of its shocks "
             "the Rankine-Hugoniot condition holds and they move at the Rankine-Hugoniot speed; scalar 1D laws only; "
             "also needs the conservation, consistency and flux_lipschitz checks to pass and every dt/dx of the shock "
             "study to lie inside the certified monotone range (shock_scope_monotone)")
_HELLY_LW = ("TVD for BV and L1 data gives uniform L-infinity and total-variation bounds, and conservative form with a "
             "Lipschitz numerical flux gives L1-Lipschitz continuity in time; by Helly's compactness theorem a "
             "subsequence converges in L1_loc, and by the Lax-Wendroff theorem every such limit is a weak solution, so "
             "its discontinuities move at the Rankine-Hugoniot speed. Subsequence only; the limit may contain an "
             "entropy-violating discontinuity that still moves at the Rankine-Hugoniot speed; says nothing about "
             "uniqueness or entropy. Also needs the conservation, consistency and flux_lipschitz checks to pass and "
             "every dt/dx of the shock study inside the certified TVD range (shock_scope_tvd); linear advection only "
             "today, where the discontinuities are contacts moving at speed a")
_FIXED_JUMP = ("if the step uL | uR (uL != uR), jump at a cell interface, is an exact fixed point of the full discrete "
               "update at every stencil position (far-field constants included), then at every dx (fixed dt/dx) the "
               "numerical solution from that Riemann data is that same jump; its L1_loc limit is the stationary jump, "
               "which is bounded, and a stationary jump is a weak solution iff f(uL) = f(uR). So with f(uL) != f(uR) "
               "the limit is not a weak solution. Scalar 1D laws, refinement at fixed dt/dx, infinite grid or "
               "transmissive boundaries; no flux form needed, so it covers non-conservative updates")
_FIXED_JUMP_ENTROPY = (_FIXED_JUMP + ". The entropy solution is a weak solution, so a limit that is not a weak solution "
                       "is not the entropy solution; this holds for any frozen pair with f(uL) != f(uR), shock or "
                       "expansion")
_FIXED_SHOCK = (_FIXED_JUMP + ". Used for the shock speed only when uL | uR is a Lax shock: f'' >= 0 on [uR, uL] "
                "(certified by non-negative Bernstein coefficients) and f'(uL) > f'(uR), so the entropy solution of "
                "this Riemann problem (it takes values in [uR, uL] only) is the single shock uL | uR moving at the "
                "Rankine-Hugoniot speed (f(uL) - f(uR))/(uL - uR), which is not 0, while the scheme's discontinuity "
                "stays at speed 0. A frozen expansion (f'(uL) < f'(uR)) has a rarefaction as exact solution, so it "
                "shows a wrong limit but no shock at a wrong speed, and does not count here")

# claim -> (statement, ((check, relation, premise[, requires]), ...)). The premise is what the relation
# rests on; it is carried into the verdict as an assumption. `requires` lists exact checks that must be
# VERIFIED on the same spec for the row to count at all; otherwise the row gives UNKNOWN.
CLAIMS = {
    "consistent": ("the numerical flux is consistent: F(u, u) = f(u)",
                   (("consistency", EQUIVALENT, ""),)),
    "conservative": ("the update is in flux form, so the total of u (of each component, for a system) is conserved "
                     "on periodic grids",
                     (("conservation", EQUIVALENT, ""),
                      ("shock_speed", NECESSARY, "a conservative scheme's translating shock profile moves at the "
                       "Rankine-Hugoniot speed; a non-conservative one can match it by accident on one state pair"))),
    "positive_under_cfl": ("the linear update is a non-negative combination of u_{i-1}, u_i, u_{i+1} on the "
                           "claimed CFL range", (("positivity", EQUIVALENT, ""),)),
    "entropy_stable_tadmor": ("entropy stable in Tadmor's semi-discrete sense: Q = -[v](F - F*) >= 0",
                              (("entropy_stability", EQUIVALENT, ""),)),
    "selects_entropy_solution_semidiscrete": ("the method-of-lines scheme's limit is the entropy solution",
                                              (("entropy_stability", SUFFICIENT, _TADMOR),
                                               # exact: its failure refutes; finding no steady step gives nothing
                                               ("steady_nonentropy_step_semidiscrete", NECESSARY, _STEADY_STEP_SEMI))),
    "monotone_under_cfl": ("H is non-decreasing in each argument for states with lam*|f'(u)| <= c",
                           (("monotonicity", EQUIVALENT, ""),)),
    # the fully discrete scheme: Tadmor's inequality says nothing about time stepping; monotonicity does
    "selects_entropy_solution": ("the limit of the scheme is the entropy solution, not another weak solution",
                                 (("entropy_rarefaction", NECESSARY, "on the spec's rarefaction data only"),
                                  # exact: its failure refutes; finding no steady step gives nothing
                                  ("steady_nonentropy_step", NECESSARY, _STEADY_STEP),
                                  ("monotonicity", SUFFICIENT, _CRANDALL_MAJDA, ("conservation", "consistency")),
                                  # exact: its failure refutes; finding no fixed jump gives nothing
                                  ("stationary_rh_violation", NECESSARY, _FIXED_JUMP_ENTROPY))),
    "consistent_order_p": ("the local truncation error is O(dx^p) at fixed dt/dx for the claimed p (linear schemes)",
                           (("truncation_order", EQUIVALENT, ""),)),
    "von_neumann_stable_under_cfl": ("|g(theta)| <= 1 for every theta and every nu = a*dt/dx in the claimed range",
                                     (("von_neumann", EQUIVALENT, ""),)),
    "stable_for_small_cfl": ("there is nu0 > 0 such that |g(theta)| <= 1 for every theta and every nu = a*dt/dx in "
                             "(0, nu0] (linear constant-coefficient schemes)",
                             (("von_neumann_small_cfl", EQUIVALENT, _SMALL_CFL),)),
    "converges_order_p": ("converges to smooth solutions of the PDE at the order p claimed for each study",
                          tuple((f"order/{k}", NECESSARY, _ORDER) for k in ("combined", "space", "time"))
                          # the row cannot fire for a nonlinear scheme: lax_richtmyer_scope is NOT_APPLICABLE there
                          + (("truncation_order", SUFFICIENT, _LAX_RICHTMYER, ("von_neumann", "lax_richtmyer_scope")),)),
    "correct_shock_speed": ("shocks move at the Rankine-Hugoniot speed in the limit dx -> 0",
                            (("shock_speed", NECESSARY, "on the spec's Riemann data and grids only"),
                             ("monotonicity", SUFFICIENT, _CM_SHOCK,
                              ("conservation", "consistency", "flux_lipschitz", "shock_scope_monotone")),
                             ("tvd_harten", SUFFICIENT, _HELLY_LW,
                              ("conservation", "consistency", "flux_lipschitz", "shock_scope_tvd")),
                             # exact: its failure refutes; finding no frozen Lax shock gives nothing
                             ("stationary_shock_rh_violation", NECESSARY, _FIXED_SHOCK))),
    "limit_is_weak_solution": ("every bounded a.e. (L1_loc) limit of the scheme as dx -> 0 at fixed dt/dx is a weak "
                               "solution, so its discontinuities move at the Rankine-Hugoniot speed (conditional on "
                               "convergence)",
                               (("conservation", SUFFICIENT, _LAX_WENDROFF, ("consistency", "flux_lipschitz")),
                                ("stationary_rh_violation", NECESSARY, _FIXED_JUMP))),
    # limited schemes (limiters.py)
    "tvd_under_cfl": ("TVD: the total variation sum_i |u_{i+1} - u_i| does not increase in one step, for every "
                      "state and every nu = a*dt/dx in the claimed range",
                      (("tvd_harten", SUFFICIENT, _HARTEN),
                       ("tv_increase", NECESSARY, _TV_INCREASE),
                       ("tvd_linear", EQUIVALENT, _LINEAR_TVD))),
    "local_max_principle_under_cfl": ("local maximum principle: u_i^{n+1} lies between the smallest and largest "
                                      "values of its stencil, for every state and every nu = a*dt/dx in the claimed range",
                                      (("tvd_harten", SUFFICIENT, _HARTEN_MP),
                                       ("max_principle_violation", NECESSARY, "one explicit periodic rational state "
                                        "and a nu in the claimed range with u_i^{n+1} outside its stencil's range"),
                                       ("max_principle_linear", EQUIVALENT, _LINEAR_MP))),
    "truncation_order_smooth_data": ("pointwise local truncation order p: the local truncation error is O(dx^p) at "
                                     "fixed dt/dx at every grid point of every smooth solution, extrema included "
                                     "(a statement about the truncation error, not the global error)",
                                     (("truncation_branches", SUFFICIENT, _BRANCHES),
                                      ("truncation_smooth_data", NECESSARY, _SMOOTH_DATA))),
    "converges_order_p_l1": ("the global error in the discrete L1 norm, sum_i |u_i - u(x_i)| dx, is O(dx^p) for the "
                             "claimed p, refining dx at fixed dt/dx, on the spec's smooth test problem",
                             (("order_l1/combined", NECESSARY, _NORM),)),
    "converges_order_p_linf": ("the global error in the max norm, max_i |u_i - u(x_i)|, is O(dx^p) for the claimed p, "
                               "refining dx at fixed dt/dx, on the spec's smooth test problem",
                               (("order_linf/combined", NECESSARY, _NORM),)),
    # systems (systems.py); `consistent` and `conservative` above apply componentwise
    "hyperbolic": ("the PDE is strictly hyperbolic on the stated domain: df/dq has real, distinct eigenvalues",
                   # equivalent for 2x2 systems; the check is UNKNOWN for n > 2
                   (("hyperbolicity", EQUIVALENT, ""),)),
    "positive_depth_under_cfl": ("the depth h stays positive under the claimed CFL number",
                                 (("depth_positivity", NECESSARY, "on the spec's Riemann data, grids and dt/dx only"),
                                  ("depth_positivity_exact", EQUIVALENT, _DEPTH_STEP))),
    "converges_to_riemann_solution": ("the scheme converges in L1 to the exact (entropy) Riemann solution",
                                      (("riemann_l1", NECESSARY, "on the spec's Riemann data, grids and dt/dx only"),)),
    # printed formulas (identity.py): the check decides the stated identity both ways
    "stated_identity": ("the stated expressions satisfy the stated identity: LHS - RHS = 0 for all states in the "
                        "stated domain", (("stated_identity", EQUIVALENT, ""),)),
}
claimkinds.require("schemes", CLAIMS)            # one reading per name, shared with the other layers

# (relation, outcome) -> polarity of the evidence for the claim
_POLARITY = {(SUFFICIENT, "pass"): "verified", (SUFFICIENT, "fail"): "unknown",
             (NECESSARY, "pass"): "not_refuted", (NECESSARY, "fail"): "refuted",
             (EQUIVALENT, "pass"): "verified", (EQUIVALENT, "fail"): "refuted"}
_LABEL = {("verified", EXACT): VERIFIED,
          ("refuted", EXACT): REFUTED, ("refuted", EMPIRICAL): REFUTED_EMPIRICALLY}


def outcome(status: str) -> str:
    """pass | fail | suspicious | unknown, from a check's status string."""
    return {"VERIFIED": "pass", "NOT_REFUTED": "pass", "REFUTED": "fail", "REFUTED_EMPIRICALLY": "fail",
            "SUSPICIOUS": "suspicious"}.get(status, "unknown")


def strength(check: str, status: str) -> str:
    """Exact only if the table says the check is exact and the check claims an exact result."""
    return EXACT if GUARANTEE.get(check) == EXACT and status in (VERIFIED, REFUTED) else EMPIRICAL


def bear(relation: str, check: str, status: str) -> tuple[str, str]:
    """(polarity, guarantee) that one check result gives the claim it bears on."""
    o = outcome(status)
    polarity = _POLARITY[relation, o] if o in ("pass", "fail") else o
    g = strength(check, status)
    if polarity == "verified" and g == EMPIRICAL:                # a finite-grid study never verifies
        polarity = "not_refuted"
    return polarity, g


def label(polarity: str, guarantee: str) -> str:
    return _LABEL.get((polarity, guarantee)) or {"not_refuted": NOT_REFUTED, "suspicious": SUSPICIOUS}.get(polarity, UNKNOWN)


def unmet_requirements(requires, by_check: dict) -> list[str]:
    """The required checks that are not exactly VERIFIED on this spec, as 'check: status'."""
    status = lambda c: by_check[c]["status"] if c in by_check else "not run"
    return [f"{c}: {status(c)}" for c in requires if not (status(c) == VERIFIED and strength(c, VERIFIED) == EXACT)]


CAVEAT = "; "      # separates a guarantee label from its caveats, as in checks.ENTROPY_EXACT


def caveats(guarantee: str) -> list[str]:
    """The caveats a guarantee label carries after its base, which is a word and an optional
    parenthesised detail: "exact (Python Fraction arithmetic; Lean certificate pending); semi-discrete
    inequality only, time stepping not certified" carries one, "proven (Lean)" and "exact" none."""
    word = guarantee.split(CAVEAT, 1)[0]
    end = guarantee.index(")") + 1 if "(" in word else len(word)
    return [c for c in guarantee[end:].split(CAVEAT) if c]


def with_caveats(label: str, guarantees) -> str:
    """A verdict's guarantee: `label`, then every caveat of the check guarantees it rests on, once each
    in the order given. A verdict never claims more than its checks; without caveats it is `label`."""
    return CAVEAT.join([label, *dict.fromkeys(c for g in guarantees for c in caveats(g))])


def rests_on(name: str, decided_by, table=CLAIMS) -> list[str]:
    """The checks a verdict rests on: the deciding checks and the exact checks their rows require, sorted."""
    rows = {row[0]: row for row in table[name][1]}
    return sorted(set(decided_by) | {c for d in decided_by for c in (rows[d][3] if len(rows[d]) > 3 else ())})


def validate(names, table=CLAIMS) -> None:
    bad = [n for n in names if n not in table]
    if bad:
        raise ValueError(f"unknown named claims {bad}; known: {sorted(table)}")


def judge_one(name: str, results: list[dict], table=CLAIMS) -> dict:
    statement, links = table[name]
    by_check = {r["check"]: r for r in results}
    evidence = []
    for check, relation, premise, *requires in links:
        r = by_check.get(check)
        if r is None:
            continue
        polarity, g = bear(relation, check, r["status"])
        unmet = unmet_requirements(requires[0] if requires else (), by_check)
        if unmet:                                        # the relation's premises fail, so the row says nothing
            polarity, g = "unknown", ""
        evidence.append({"check": check, "relation": relation, "status": r["status"], "polarity": polarity,
                         "guarantee": g, "gives": label(polarity, g),
                         "assumes": ([premise] if premise else []) + r.get("assumptions", [])})
        if unmet:
            evidence[-1]["unmet"] = unmet
    pick = lambda p: [e for e in evidence if e["polarity"] == p]
    ver, ref = pick("verified"), pick("refuted")
    if ver and ref:
        verdict, guarantee, decided = INCONSISTENT, "", ver + ref
    elif ref or ver:
        decided = ref or ver
        guarantee = EXACT if any(e["guarantee"] == EXACT for e in decided) else EMPIRICAL
        decided = [e for e in decided if e["guarantee"] == guarantee]
        verdict = label("refuted" if ref else "verified", guarantee)
        if guarantee == EXACT:
            need = rests_on(name, [e["check"] for e in decided], table)
            guarantee = with_caveats(EXACT, [by_check[c].get("guarantee") or "" for c in need if c in by_check])
    elif pick("suspicious"):
        verdict, guarantee, decided = SUSPICIOUS, EMPIRICAL, pick("suspicious")
    elif pick("not_refuted"):
        verdict, guarantee, decided = NOT_REFUTED, EMPIRICAL, pick("not_refuted")
    else:
        verdict, guarantee, decided = UNKNOWN, "", []
    assumes = list(dict.fromkeys(a for e in decided for a in e.pop("assumes")))
    for e in evidence:
        e.pop("assumes", None)
    detail = ("checker, spec or claims-table bug: " + ", ".join(f"{e['check']} gives {e['gives']}" for e in decided)
              if verdict == INCONSISTENT else "" if evidence else "no check bearing on this claim was run")
    return {"claim": name, "statement": statement, "verdict": verdict, "guarantee": guarantee,
            "decided_by": [e["check"] for e in decided], "evidence": evidence, "assumes": assumes, "detail": detail}


def judge(names, results: list[dict], table=CLAIMS) -> list[dict]:
    """One verdict per named claim the spec makes. The spec declares the claims; no check does."""
    validate(names, table)
    return [judge_one(n, results, table) for n in names]
