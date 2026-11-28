"""Usage: uv run python benchmark/outside_v2/errata_checks.py

Exact checks of the post-freeze re-derivations to FALSE in ERRATA.md (rule 6 of phase B, the EXACT-CHECK RULE): each
counterexample is evaluated in rational arithmetic (fractions.Fraction) at the stencil, data and CFL that ERRATA.md
states. A re-derivation counts as FALSE in rows (E) and (D) only if its case here is CONFIRMED; otherwise it is UNSURE.

Scorer code, standalone: it imports nothing from physverify. Each case returns a dict with `confirmed`, the exact
numbers and what was evaluated; tests/test_outside_v2_scores.py asserts each one.

The schemes, as ERRATA.md and the reader view state them:
- Kurganov-Tadmor (KT) semi-discrete scheme, scalar: u_j' = -(H_{j+1/2} - H_{j-1/2})/dx, with
  H_{j+1/2} = (f(u^+) + f(u^-))/2 - a_{j+1/2} (u^+ - u^-)/2, u^- = u_j + (dx/2)(u_x)_j,
  u^+ = u_{j+1} - (dx/2)(u_x)_{j+1}, minmod-like slopes (4.9) with parameter theta. The local speed is either the
  endpoint form (4.19), max(|f'(u^-)|, |f'(u^+)|), or the interval form (4.10), max of |f'| over [u^-, u^+].
  The 2D scheme with g = 0 on data constant in y has zero y-differences, so its update is the 1D one (the y-flux
  terms are evaluated and found zero).
- The fully discrete schemes of KT Table 5.1, (5.7): u^(1) = u^n + dt C[u^n],
  u^(l+1) = eta_l u^n + (1 - eta_l)(u^(l) + dt C[u^(l)]), u^{n+1} = the last stage.
- Cockburn-Shu, k = 0 DG (piecewise constants), f(u) = u, upwind flux: L(u)_i = -(u_i - u_{i-1})/dx.
"""

from __future__ import annotations

import json
import sys
from fractions import Fraction as Fr


def minmod(*xs: Fr) -> Fr:
    if all(x > 0 for x in xs):
        return min(xs)
    if all(x < 0 for x in xs):
        return max(xs)
    return Fr(0)


def kt_rhs(u: list[Fr], f, df, theta: Fr, speed: str, dx: Fr = Fr(1)) -> list[Fr]:
    """C[u]_j = -(H_{j+1/2} - H_{j-1/2})/dx on a periodic grid."""
    n = len(u)
    s = [minmod(theta * (u[j] - u[j - 1]), (u[(j + 1) % n] - u[j - 1]) / 2, theta * (u[(j + 1) % n] - u[j]))
         for j in range(n)]            # dx (u_x)_j
    H = []
    for j in range(n):
        um, up = u[j] + s[j] / 2, u[(j + 1) % n] - s[(j + 1) % n] / 2
        if speed == "endpoint":                                     # (4.19)
            a = max(abs(df(um)), abs(df(up)))
        else:                                                       # (4.10), |f'| maximised exactly below
            a = interval_max_abs(df, min(um, up), max(um, up))
        H.append((f(up) + f(um)) / 2 - a * (up - um) / 2)
    return [-(H[j] - H[j - 1]) / dx for j in range(n)]


def interval_max_abs(df, lo: Fr, hi: Fr) -> Fr:
    """max |f'| on [lo, hi] for the quadratic f' of the cases here (f' = 3u^2 - 3 or a constant): the endpoints and
    the vertex u = 0 of f' when it lies inside."""
    pts = [lo, hi] + ([Fr(0)] if lo < 0 < hi else [])
    return max(abs(df(x)) for x in pts)


def tv(u: list[Fr]) -> Fr:
    return sum(abs(u[j] - u[j - 1]) for j in range(len(u)))


def kt_06() -> dict:
    """KT:06, 2D maximum principle without the CFL (5.3): f(u) = u, g = 0, a single spike, lambda = dt/dx = 2."""
    u = [Fr(0)] * 8
    u[3] = Fr(1)
    lam = Fr(2)
    C = kt_rhs(u, lambda x: x, lambda x: Fr(1), Fr(1), "endpoint")
    y_terms = [Fr(0)] * len(u)       # data constant in y and g = 0: G_{k+1/2} - G_{k-1/2} = 0 exactly
    new = [u[j] + lam * C[j] - lam * y_terms[j] for j in range(len(u))]
    slopes_zero = all(minmod(u[j] - u[j - 1], (u[(j + 1) % 8] - u[j - 1]) / 2, u[(j + 1) % 8] - u[j]) == 0
                      for j in range(8))
    upwind = all(new[j] == u[j] - lam * (u[j] - u[j - 1]) for j in range(8))
    return {"id": "kurganov_tadmor_2000_central:06", "max_before": max(u), "max_after": max(new),
            "u_j+1_after": new[4], "slopes_zero": slopes_zero, "is_upwind": upwind,
            "confirmed": slopes_zero and upwind and new[4] == 2 and max(new) > max(u),
            "evaluated": "one forward-Euler step of the KT scheme (theta = 1, speeds (4.19) = (4.10) = 1) on 8 periodic "
                         "cells, spike u_3 = 1, lambda = 2; exact"}


F3 = (lambda x: x ** 3 - 3 * x, lambda x: 3 * x ** 2 - 3)
KT_LAM = Fr(99, 100) / 24


def kt_jump_data() -> list[Fr]:
    return [Fr(-1)] * 8 + [Fr(1)] * 8


def kt_08() -> dict:
    """KT:08: f(u) = u^3 - 3u, data -1 | 1, speeds (4.19) at the endpoints, lambda = 0.99/24 within (5.3)."""
    u, (f, df) = kt_jump_data(), F3
    out = {}
    for speed in ("endpoint", "interval"):
        C = kt_rhs(u, f, df, Fr(1), speed)
        out[speed] = max(u[j] + KT_LAM * C[j] for j in range(len(u)))
    cfl = KT_LAM * interval_max_abs(df, Fr(-1), Fr(1))
    m = out["endpoint"]
    return {"id": "kurganov_tadmor_2000_central:08", "lambda": KT_LAM, "cfl_5_3": cfl, "cfl_ok": cfl <= Fr(1, 8),
            "max_after_endpoint_speeds": m, "max_after_interval_speeds": out["interval"],
            "equals_1_plus_2_lambda": m == 1 + 2 * KT_LAM, "rounded": float(m),
            "confirmed": cfl <= Fr(1, 8) and m == Fr(433, 400) and m > 1 and out["interval"] <= 1,
            "evaluated": "one forward-Euler step, 16 periodic cells (8 at -1, 8 at 1), theta = 1 (all slopes are 0, so "
                         "theta does not matter), with the endpoint speeds (4.19); the interval speeds (4.10) are "
                         "evaluated too and keep the maximum; exact"}


def kt_09() -> dict:
    """KT:09: the same data with the Table 5.1 schemes (5.7), one step; slopes are nonzero after stage 1, so theta
    matters: theta = 1 and theta = 2 are both evaluated."""
    u0, (f, df) = kt_jump_data(), F3
    quoted = {"second order (eta_1 = 1/2)": ([Fr(1, 2)], 1.0675),
              "third order (eta_1 = 3/4, eta_2 = 1/3)": ([Fr(3, 4), Fr(1, 3)], 1.0659)}
    res = {}
    for name, (etas, q) in quoted.items():
        for theta in (Fr(1), Fr(2)):
            C = lambda v: kt_rhs(v, f, df, theta, "endpoint")      # noqa: E731
            stage = [a + KT_LAM * c for a, c in zip(u0, C(u0))]
            for eta in etas:
                stage = [eta * a + (1 - eta) * (b + KT_LAM * c) for a, b, c in zip(u0, stage, C(stage))]
            m = max(stage)
            res[f"{name}, theta = {theta}"] = {"max_after": str(m), "decimal": round(float(m), 6),
                                               "quoted": q, "agrees_4_digits": round(float(m), 4) == q,
                                               "above_1": m > 1}
    confirmed = all(r["above_1"] for r in res.values())
    return {"id": "kurganov_tadmor_2000_central:09", "lambda": KT_LAM, "runs": res, "confirmed": confirmed,
            "evaluated": "one step of each Table 5.1 scheme in the Shu-Osher form (5.7), 16 periodic cells, endpoint "
                         "speeds (4.19), minmod slopes (4.9) at theta = 1 and theta = 2; confirmed if every run "
                         "exceeds max u^n = 1; agreement with ERRATA's quoted decimals reported separately; exact"}


def cockburn_06() -> dict:
    """Cockburn-Shu:06: a two-stage method with beta_21 = -1/2 meeting every printed condition; TV grows."""
    alpha = [[Fr(1)], [Fr(1, 2), Fr(1, 2)]]
    beta = [[Fr(1)], [Fr(1), Fr(-1, 2)]]
    lam = Fr(1, 4)
    printed = (all(a >= 0 for row in alpha for a in row) and all(sum(row) == 1 for row in alpha)
               and all(a != 0 for ra, rb in zip(alpha, beta) for a, b in zip(ra, rb) if b != 0))
    cfl = max(abs(b / a) for ra, rb in zip(alpha, beta) for a, b in zip(ra, rb)) * lam
    u = [Fr(0)] * 8 + [Fr(1)] * 8
    L = lambda v: [-(v[i] - v[i - 1]) for i in range(len(v))]       # noqa: E731  dx = 1, dt = lam
    stages = [u]
    for ra, rb in zip(alpha, beta):
        stages.append([sum(a * stages[l][i] + b * lam * L(stages[l])[i] for l, (a, b) in enumerate(zip(ra, rb)))
                       for i in range(len(u))])
    new = stages[-1]
    return {"id": "cockburn_shu_2001_rkdg_review:06", "printed_conditions_hold": printed,
            "beta_21": beta[1][1], "max_abs_beta_over_alpha_times_lambda": cfl, "tv_before": tv(u), "tv_after": tv(new),
            "confirmed": printed and cfl == Fr(1, 2) and tv(u) == 2 and tv(new) == Fr(17, 8),
            "evaluated": "k = 0, f(u) = u, upwind flux, dt/dx = 1/4, 8 zeros then 8 ones, periodic; exact. That "
                         "max |beta/alpha| dt/dx = 1/2 satisfies (2.13) is ERRATA's statement, not re-derived here"}


def barsukow_03() -> dict:
    """barsukow:03: H(a, b, c) = b + D(c) - D(b), D(x) = [x >= 1]. Evaluated: H(0,0,0) = 0; the sum is kept on
    finitely supported data; and every flux form of H has fhat(a, b) = K - D(b)/lambda, which jumps by 1/lambda at
    b = 1. The last step: q - lambda (F(b, c) - F(a, b)) = H(a, b, c) for all a, b, c rearranges to
    g(b, c) = g(a, b) with g(x, y) = F(x, y) + D(y)/lambda, so g is constant (set a = b' and vary each argument);
    the evaluation checks the rearrangement and the jump on a grid of rational triples."""
    D = lambda x: Fr(1) if x >= 1 else Fr(0)                      # noqa: E731
    H = lambda a, b, c: b + D(c) - D(b)                           # noqa: E731
    lam = Fr(1, 2)
    F = lambda a, b: -D(b) / lam                                  # noqa: E731  the flux form with K = 0
    data = [[Fr(0), Fr(3, 2), Fr(1), Fr(-2), Fr(1, 3), Fr(0), Fr(0)], [Fr(0), Fr(1), Fr(1), Fr(1), Fr(0), Fr(0)]]
    kept = all(sum(H(q[i - 1], q[i], q[(i + 1) % len(q)]) for i in range(len(q))) == sum(q) for q in data)
    grid = [Fr(k, 4) for k in range(-8, 9)]
    form = all(H(a, b, c) == b - lam * (F(b, c) - F(a, b)) for a in grid for b in grid for c in grid)
    rearranged = all((H(a, b, c) == b - lam * (F(b, c) - F(a, b))) ==
                     (F(b, c) + D(c) / lam == F(a, b) + D(b) / lam) for a in grid for b in grid for c in grid)
    jump = F(0, Fr(1)) - F(0, Fr(1) - Fr(1, 10 ** 9))
    return {"id": "barsukow_uzh_notes:03", "H_000": H(0, 0, 0), "sum_kept": kept, "flux_form_holds": form,
            "rearrangement_holds": rearranged, "flux_jump_at_b_1": jump,
            "confirmed": H(0, 0, 0) == 0 and kept and form and rearranged and jump == -1 / lam,
            "evaluated": "exact evaluation of H, its sum on two finitely supported data (periodic padding of zeros), "
                         "the flux form on 17^3 rational triples and the jump of fhat at b = 1; the step 'g is constant' "
                         "is the two-line argument in the docstring, not an evaluation"}


CASES = (kt_06, kt_08, kt_09, cockburn_06, barsukow_03)


def results() -> dict:
    return {c.__name__: c() for c in CASES}


def confirmed() -> dict:
    """item id -> True if its re-derivation to FALSE is exactly confirmed."""
    return {r["id"]: r["confirmed"] for r in results().values()}


def _jsonable(x):
    if isinstance(x, Fr):
        return str(x)
    if isinstance(x, dict):
        return {k: _jsonable(v) for k, v in x.items()}
    return x


def main() -> int:
    print(json.dumps(_jsonable(results()), indent=1))
    return 0


if __name__ == "__main__":
    sys.exit(main())
