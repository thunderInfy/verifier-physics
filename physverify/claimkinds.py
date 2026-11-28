"""One registry of claim kinds, shared by every layer.

Usage: python -m physverify.claimkinds [--write]

Each claim name has ONE meaning here, whatever layer uses it: `consistent_order_p` means
"order at least p" for schemes and for variational integrators alike. Each layer keeps its own
relation table (which checks decide a claim, with which polarity); only the names and their
reading live here, and every layer checks its names against `KINDS` at import (`require`).

Fields of an entry:
  gloss       one plain-English line
  quantifier  the quantifier structure in one line
  layers      where the name is used: schemes, variational, conserved, derivation, theory, reconstruction
  meaning     the Lean theorem that gives the claim its proven semantics, or None (gloss only)
  params      {label: {layer: key}}: for each parameter of the claim, where each layer reads it.
              schemes: a dotted path from the spec root (`claims.consistent_order`), with a final `?`
                when the key is optional (the check then uses a default);
              variational, reconstruction: `claims[].p`, a key of the claim's own entry in the spec's
                `claims` list (a final `?` again marks an optional key);
              theory: `args.law`, `args.evidence`, an argument of the obligation, which the planning
                tool fills from the theory file (a law's name) or an evidence file (its id), not a
                spec key.
              `tests/test_claimkinds.py` checks each key against the code and every spec using it.

`--write` rewrites the "Claim kinds" table in README.md between the two marker comments;
without it the table is printed. `tests/test_claimkinds.py` fails if the README drifts.
"""

from __future__ import annotations

import sys
from pathlib import Path

LAYERS = ("schemes", "variational", "conserved", "derivation", "theory", "reconstruction")

KINDS: dict[str, dict] = {
    # discrete schemes (physverify/schemes/claims.py, CLAIMS)
    "consistent": {
        "gloss": "the numerical flux is consistent with the PDE flux",
        "quantifier": "for all states u: F(u, ..., u) = f(u), as an identity",
        "layers": ["schemes"], "meaning": None, "params": {}},
    "conservative": {
        "gloss": "the update is in flux form, so the total of u (of each component) is conserved on periodic grids",
        "quantifier": "for every periodic grid of any size and every state in the domain: sum_i (u_i^{n+1} - u_i^n) = 0",
        "layers": ["schemes"], "meaning": "conserves_of_telescoping", "params": {}},
    "positive_under_cfl": {
        "gloss": "the linear update is a non-negative combination of its stencil values, so non-negative data stay "
                 "non-negative",
        "quantifier": "for all nu = a*dt/dx in the claimed range: every stencil weight is >= 0",
        "layers": ["schemes"], "meaning": "NonnegComb.step_nonneg",
        "params": {"nu_range": {"schemes": "claims.positive_cfl"}}},
    "entropy_stable_tadmor": {
        "gloss": "entropy stable in Tadmor's semi-discrete sense for the declared entropy pair (by default "
                 "u^2/2, u^3/3 when the flux is Burgers' u^2/2)",
        "quantifier": "for all states uL, uR: Q = -[v](F - F*) >= 0, with v = eta'(u)",
        "layers": ["schemes"], "meaning": None,
        "params": {"eta": {"schemes": "claims.entropy_stability.eta?"},
                   "q": {"schemes": "claims.entropy_stability.q?"}}},
    "selects_entropy_solution_semidiscrete": {
        "gloss": "the method-of-lines scheme's limit is the entropy solution",
        "quantifier": "for all admissible data: the dx -> 0 limit of the semi-discrete solution is the entropy "
                      "solution",
        "layers": ["schemes"], "meaning": None, "params": {}},
    "monotone_under_cfl": {
        "gloss": "the update H is non-decreasing in each stencil value under the claimed CFL bound",
        "quantifier": "for all states with lam*|f'(u)| <= c: H is non-decreasing in each argument",
        "layers": ["schemes"], "meaning": None,
        "params": {"c": {"schemes": "claims.monotone_cfl"}}},
    "selects_entropy_solution": {
        "gloss": "the limit of the fully discrete scheme is the entropy solution, not another weak solution",
        "quantifier": "for all admissible data: the dx -> 0 limit at fixed dt/dx is the entropy solution",
        "layers": ["schemes"], "meaning": None, "params": {}},
    "consistent_order_p": {
        "gloss": "the discrete equations are consistent with the continuous ones to order at least p in the step "
                 "(dx at fixed dt/dx for a linear scheme, h for a variational integrator)",
        "quantifier": "for all smooth solutions: truncation error = O(dx^p) (schemes), (1/h)·DEL + EL = O(h^p) "
                      "(variational); at least p, so a higher order also verifies",
        "layers": ["schemes", "variational"], "meaning": None,
        "params": {"p": {"schemes": "claims.consistent_order", "variational": "claims[].p"}}},
    "exact_order_p": {
        "gloss": "the DEL is consistent with the continuous EL equations to order exactly p",
        "quantifier": "exactly p: at least p and not p + 1 (the h^p coefficient of (1/h)·DEL + EL is not "
                      "identically 0)",
        "layers": ["variational"], "meaning": None,
        "params": {"p": {"variational": "claims[].p"}}},
    "von_neumann_stable_under_cfl": {
        "gloss": "von Neumann (l2) stable on the claimed CFL range (linear constant-coefficient schemes)",
        "quantifier": "for all nu = a*dt/dx in the claimed range and all theta: |g(theta)| <= 1",
        "layers": ["schemes"], "meaning": None,
        "params": {"nu_range": {"schemes": "claims.von_neumann_cfl"}}},
    "stable_for_small_cfl": {
        "gloss": "von Neumann stable for every small enough CFL number (linear constant-coefficient schemes)",
        "quantifier": "there is nu0 > 0 such that for all nu in (0, nu0] and all theta: |g(theta)| <= 1",
        "layers": ["schemes"], "meaning": None, "params": {}},
    "converges_order_p": {
        "gloss": "the scheme converges to smooth solutions at order at least p, for each claimed refinement study "
                 "(claims.order maps a study to its p)",
        "quantifier": "for each claimed study (combined, space, time): global error = O(step^p) on smooth data; at "
                      "least p, but an empirical study above p + TOL is reported SUSPICIOUS, a gap, never a "
                      "refutation",
        "layers": ["schemes"], "meaning": None,
        "params": {"p": {"schemes": "claims.order"}}},
    "correct_shock_speed": {
        "gloss": "shocks move at the Rankine-Hugoniot speed in the limit dx -> 0 at fixed dt/dx",
        "quantifier": "for Riemann data whose entropy solution is a shock: the limit's shock moves at "
                      "(f(uL) - f(uR))/(uL - uR)",
        "layers": ["schemes"], "meaning": None, "params": {}},
    "limit_is_weak_solution": {
        "gloss": "every bounded a.e. limit of the scheme as dx -> 0 at fixed dt/dx is a weak solution "
                 "(conditional on convergence)",
        "quantifier": "for all data and every limit u (bounded, a.e., in L1_loc): u is a weak solution",
        "layers": ["schemes"], "meaning": None, "params": {}},
    "tvd_under_cfl": {
        "gloss": "one step never increases the total variation, on the claimed CFL range",
        "quantifier": "for every periodic state and every nu = a*dt/dx in the claimed range: TV(u^{n+1}) <= TV(u^n)",
        "layers": ["schemes"], "meaning": None,
        "params": {"nu_range": {"schemes": "claims.tvd_cfl"}}},
    "local_max_principle_under_cfl": {
        "gloss": "each new value lies between the smallest and largest values of its stencil, on the claimed CFL range",
        "quantifier": "for every state, every nu = a*dt/dx in the claimed range and every i: "
                      "min(stencil) <= u_i^{n+1} <= max(stencil)",
        "layers": ["schemes"], "meaning": None,
        "params": {"nu_range": {"schemes": "claims.tvd_cfl"}}},
    "truncation_order_smooth_data": {
        "gloss": "pointwise local truncation order at least p at every grid point of every smooth solution, "
                 "extrema included",
        "quantifier": "for all smooth u and every grid point: local truncation error = O(dx^p) at fixed dt/dx",
        "layers": ["schemes"], "meaning": None,
        "params": {"p": {"schemes": "claims.smooth_truncation"}}},
    "converges_order_p_l1": {
        "gloss": "the global error in the discrete L1 norm is O(dx^p) at fixed dt/dx, on the spec's smooth test problem",
        "quantifier": "on the spec's test problem: sum_i |u_i - u(x_i)| dx = O(dx^p) as dx -> 0; at least p, but an "
                      "empirical study above p + TOL is reported SUSPICIOUS, a gap, never a refutation",
        "layers": ["schemes"], "meaning": None,
        "params": {"p": {"schemes": "claims.order_l1.combined"}}},
    "converges_order_p_linf": {
        "gloss": "the global error in the max norm is O(dx^p) at fixed dt/dx, on the spec's smooth test problem",
        "quantifier": "on the spec's test problem: max_i |u_i - u(x_i)| = O(dx^p) as dx -> 0; at least p, but an "
                      "empirical study above p + TOL is reported SUSPICIOUS, a gap, never a refutation",
        "layers": ["schemes"], "meaning": None,
        "params": {"p": {"schemes": "claims.order_linf.combined"}}},
    "hyperbolic": {
        "gloss": "the system is strictly hyperbolic on the stated domain",
        "quantifier": "for all q in the domain: df/dq has real, distinct eigenvalues",
        "layers": ["schemes"], "meaning": None, "params": {}},
    "positive_depth_under_cfl": {
        "gloss": "the water depth h stays positive under the claimed CFL number (shallow water)",
        "quantifier": "for all positive data and every step at which the CFL condition holds on every stencil: "
                      "h_i^{n+1} > 0",
        "layers": ["schemes"], "meaning": None,
        "params": {"c": {"schemes": "claims.riemann.cfl"}}},
    "converges_to_riemann_solution": {
        "gloss": "the scheme converges in L1 to the exact (entropy) Riemann solution",
        "quantifier": "on the spec's Riemann data: ||u_dx - u_exact||_L1 -> 0 as dx -> 0 at fixed dt/dx",
        "layers": ["schemes"], "meaning": None, "params": {}},
    "stated_identity": {
        "gloss": "a formula the source prints (numerical entropy flux, entropy pair, viscosity coefficient Q, "
                 "amplification factor g) satisfies the identity that defines it (scalar 1D laws)",
        "quantifier": "for all states (and lam, nu, theta) in the stated domain with every denominator non-zero: "
                      "LHS - RHS = 0, as a rational function (Laurent polynomial in z = e^{i theta} for g)",
        "layers": ["schemes"], "meaning": None,
        "params": {"form": {"schemes": "claims.stated_identity.form"},
                   "eta": {"schemes": "claims.stated_identity.eta?"},
                   "q": {"schemes": "claims.stated_identity.q?"},
                   "entropy_flux": {"schemes": "claims.stated_identity.entropy_flux?"},
                   "dissipation": {"schemes": "claims.stated_identity.dissipation?"},
                   "Q": {"schemes": "claims.stated_identity.Q?"},
                   "g": {"schemes": "claims.stated_identity.g?"},
                   "let": {"schemes": "claims.stated_identity.let?"},
                   "domain": {"schemes": "claims.stated_identity.domain?"}}},
    "ssp_preserves": {
        "gloss": "an explicit Runge-Kutta method with SSP coefficient C keeps a convex property (positivity, TVD, the "
                 "global maximum principle) that the spec's forward-Euler step keeps up to CFL cfl/C",
        "quantifier": "for every state and every nu = a*dt/dx in [0, cfl]: every stage of the Runge-Kutta step, "
                      "u^{n+1} included, has the property, given forward Euler has it on [0, cfl/C]",
        "layers": ["schemes"], "meaning": "ssp_preserves_meaning",
        "params": {"method": {"schemes": "claims.ssp.method"}, "property": {"schemes": "claims.ssp.property"},
                   "cfl": {"schemes": "claims.ssp.cfl"}}},
    # variational integrators and explicit update maps (physverify/variational.py)
    # TODO: `consistent_order_p`, `exact_order_p` and the scheme orders stay gloss only; a Lean
    # meaning needs Taylor expansion with remainder over smooth solutions.
    "del_equations": {
        "gloss": "the claimed update is the discrete Euler–Lagrange equations of L_d",
        "quantifier": "for every triple (q_k, q_k+1, q_k+2) in D: DEL(L_d) = 0 iff the claimed update holds",
        "layers": ["variational"], "meaning": "del_verified_meaning", "params": {}},
    "discrete_momentum_conserved": {
        "gloss": "J(q0, q1) is constant, exactly, along every solution of the DEL equations that stays in D "
                 "(a Noether momentum or any other such J)",
        "quantifier": "for every N and every discrete trajectory q_0..q_N+1 in D solving the DEL: "
                      "J(q_N, q_N+1) = J(q_0, q_1)",
        "layers": ["variational"], "meaning": "dmomentum_meaning", "params": {}},
    "update_conserves": {
        "gloss": "the explicit update map z' = Phi(z) conserves J exactly (for a straight-line kernel, Phi is "
                 "exec prog, run by Lean: kernel_conserves_meaning)",
        "quantifier": "for all z in D: J(Phi(z)) = J(z); so along every orbit in D, J(z_N) = J(z_0)",
        "layers": ["variational"], "meaning": "update_conserves_meaning", "params": {}},
    "update_conserves_order_p": {
        "gloss": "the explicit update map (or kernel) conserves J to order at least p, per step: the drift of one "
                 "step is O(h^{p+1}); nothing is claimed about orbits over a time T",
        "quantifier": "for all z in D: J(Phi(z)) - J(z) = h^{p+1} R(z, h) with R a polynomial, so |J(Phi(z)) - J(z)| "
                      "<= M h^{p+1} wherever |R| <= M (on every compact set some M works)",
        "layers": ["variational"], "meaning": "update_order_meaning",
        "params": {"p": {"variational": "claims[].p"}}},
    # reconstructions (physverify/reconstruction.py)
    "reconstruction_order_p": {
        "gloss": "a WENO-type reconstruction (or its conservative difference) is accurate to order at least p, in "
                 "the stated regime (f' != 0, or a critical point of order n_cp) and for the stated eps = c dx^m",
        "quantifier": "for every smooth f in the regime: reconstruction - exact value = O(dx^p) (form point), or the "
                      "difference of the errors at x_{i+1/2} and x_{i-1/2}, over dx, = O(dx^p) (form "
                      "flux_difference); at least p",
        "layers": ["reconstruction"], "meaning": None,
        "params": {"p": {"reconstruction": "claims[].p"}, "form": {"reconstruction": "claims[].form?"},
                   "regime": {"reconstruction": "claims[].regime"}, "n_cp": {"reconstruction": "claims[].n_cp?"},
                   "eps": {"reconstruction": "claims[].eps?"}}},
    "cell_average_max_principle": {
        "gloss": "one cell-average step fed by polynomials of degree <= k keeps the new average in [m, M] whenever the "
                 "stated point values (or other linear functionals) of the polynomials lie in [m, M]",
        "quantifier": "for every lam = dt/dx in the claimed range, all polynomials of degree <= k per cell and all "
                      "m <= M: every hypothesis in [m, M] => the updated average in [m, M]",
        "layers": ["reconstruction"], "meaning": None,
        "params": {"lam": {"reconstruction": "claims[].lam"}}},
    "eno_sign_property": {
        "gloss": "the jump of an ENO interpolation of point values at x_{i+1/2} has the sign of w_{i+1} - w_i "
                 "(weak form: zero allowed, and zero where the difference is zero)",
        "quantifier": "for all real data w: (w^-_{i+1} - w^+_i)(w_{i+1} - w_i) >= 0, and w^-_{i+1} = w^+_i where "
                      "w_{i+1} = w_i",
        "layers": ["reconstruction"], "meaning": None, "params": {}},
    "eno_jump_ratio_at_most": {
        "gloss": "the jump of an ENO interpolation of point values is at most c times the jump of the data",
        "quantifier": "for all real data w with w_{i+1} != w_i: (w^-_{i+1} - w^+_i) / (w_{i+1} - w_i) <= c",
        "layers": ["reconstruction"], "meaning": None,
        "params": {"c": {"reconstruction": "claims[].c"}}},
    "limiter_keeps_average": {
        "gloss": "the scaling limiter p~ = c + theta (p - c) keeps the cell average of a polynomial of degree <= k",
        "quantifier": "for all polynomials p of degree <= k on the cell and all m <= M (c in [m, M] if assumed): "
                      "avg(p~) = avg(p)",
        "layers": ["reconstruction"], "meaning": None,
        "params": {"average_in_bounds": {"reconstruction": "claims[].average_in_bounds?"}}},
    "limiter_bounds": {
        "gloss": "the scaling limiter puts p~ in [m, M] at the stated points (or on the whole cell)",
        "quantifier": "for all polynomials p of degree <= k and all m <= M (ubar in [m, M] if assumed): "
                      "m <= p~(y) <= M for every y in `on`",
        "layers": ["reconstruction"], "meaning": None,
        "params": {"on": {"reconstruction": "claims[].on"},
                   "average_in_bounds": {"reconstruction": "claims[].average_in_bounds?"}}},
    "limiter_accuracy": {
        "gloss": "the scaling limiter changes p by at most a constant times its overshoot of [m, M], so a (k+1)-th "
                 "order accurate p stays (k+1)-th order accurate",
        "quantifier": "there is C such that for all polynomials p of degree <= k and all m <= M (ubar in [m, M] if "
                      "assumed): max_cell |p~ - p| <= C max_cell dist(p(y), [m, M])",
        "layers": ["reconstruction"], "meaning": None,
        "params": {"average_in_bounds": {"reconstruction": "claims[].average_in_bounds?"}}},
    # continuous conserved quantities (physverify/conserved.py)
    "conserved": {
        "gloss": "Q is constant along every solution of the Euler–Lagrange equations of L that stays in D",
        "quantifier": "for every trajectory twice differentiable on an open interval, with jet in D and solving "
                      "the EL equations there: Q is constant on that interval",
        "layers": ["conserved"], "meaning": "conserved_meaning", "params": {}},
    # equations of motion (physverify/derivation.py)
    "el_equations": {
        "gloss": "the claimed equations of motion are the Euler–Lagrange equations of L on D",
        "quantifier": "for every trajectory twice differentiable at t with jet in D: the EL equations of L hold at t "
                      "iff the claimed equations hold at t",
        "layers": ["derivation"], "meaning": "verified_meaning_at", "params": {}},
    # theory refutation obligations (physverify/obligations.py); each one, if proven, refutes the theory
    "dim_mismatch": {
        "gloss": "a law of the theory is not dimensionally homogeneous",
        "quantifier": "the two sides of the law have different dimensions under the theory's symbol dimensions",
        "layers": ["theory"], "meaning": "Law.dimMismatch_refutes",
        "params": {"law": {"theory": "args.law"}}},
    "law_vs_evidence": {
        "gloss": "a law of the theory fails everywhere in the box of a piece of evidence",
        "quantifier": "for all values inside the evidence's hard bounds: the law does not hold",
        "layers": ["theory"], "meaning": None,
        "params": {"law": {"theory": "args.law"}, "evidence": {"theory": "args.evidence"}}},
    "orbit_excluded": {
        "gloss": "the central force law admits no orbit with a perihelion and an aphelion in the observed boxes",
        "quantifier": "for every angular momentum and every radial trajectory: no local min of r in the "
                      "perihelion box together with a local max in the aphelion box",
        "layers": ["theory"], "meaning": "EccentricExcluded.refutes",
        "params": {"evidence": {"theory": "args.evidence"}}},
    "trajectory_vs_evidence": {
        "gloss": "no trajectory of the theory's dynamics from the evidence's initial box is inside the observed box "
                 "at the observation time",
        "quantifier": "for all initial states and parameters in the evidence box: the state at t_obs is outside "
                      "the observed box (validated interval arithmetic, not Lean)",
        "layers": ["theory"], "meaning": None,
        "params": {"evidence": {"theory": "args.evidence"}}},
}


def require(layer: str, names) -> None:
    """Every layer calls this at import with the claim names it uses: each must be in `KINDS`
    and list `layer`, so a new name, or one used in a layer it was not written for, fails."""
    bad = [n for n in names if n not in KINDS or layer not in KINDS[n]["layers"]]
    if bad:
        raise ValueError(f"claim names {bad} of layer {layer!r} are not registered for it in physverify/claimkinds.py")


BEGIN, END = "<!-- claim-kinds:begin -->", "<!-- claim-kinds:end -->"
README = Path(__file__).resolve().parent.parent / "README.md"


def _cell(s: str) -> str:
    return s.replace("|", "\\|")


def table() -> str:
    """The README block between the markers, markers excluded."""
    rows = ["Kinds with a Lean meaning theorem have a proven semantics; the rest have a gloss only (a reading "
            "a person chose, checked by review).", "",
            "Params gives where each layer reads a parameter (see `params` in the module docstring; `?` marks an "
            "optional key).", "",
            "| Name | Gloss | Quantifier | Layers | Params | Lean meaning |", "|---|---|---|---|---|---|"]
    for name, k in KINDS.items():
        params = "; ".join(f"{label}: " + ", ".join(f"`{key}`" + (f" ({layer})" if len(k["layers"]) > 1 else "")
                                                     for layer, key in keys.items())
                           for label, keys in k["params"].items())
        meaning = f"`{k['meaning']}`" if k["meaning"] else "gloss only"
        rows.append(f"| `{name}` | {_cell(k['gloss'])} | {_cell(k['quantifier'])} | "
                    f"{', '.join(k['layers'])} | {_cell(params) or 'none'} | {meaning} |")
    return "\n".join(rows)


def readme_block(text: str) -> str:
    """The current block between the markers in `text`."""
    return text.split(BEGIN, 1)[1].split(END, 1)[0].strip("\n")


def main(argv: list[str]) -> int:
    if "--write" in argv:
        text = README.read_text()
        head, rest = text.split(BEGIN, 1)
        README.write_text(f"{head}{BEGIN}\n{table()}\n{END}{rest.split(END, 1)[1]}")
        return 0
    print(table())
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
