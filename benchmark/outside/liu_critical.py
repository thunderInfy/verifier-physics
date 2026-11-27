"""Usage: uv run python benchmark/outside/liu_critical.py [--quick]

The r = 3 WENO of Liu, Osher and Chan (smoothness measurement (2.20) of jiang_shu_1995_weno, spec
`specs/jiang-shu-weno5-liu-fd.json`) at a first-order critical point (f' = 0, f'' != 0), eps -> 0: what
`reconstruction_order_p` decides, the leading coefficients from the module's own series, and the numerics.
Note: `notes/liu-critical-point.md`.

1. The checker's verdicts at n_cp = 1, both forms, eps = 0 (and eps = dx^0, a fixed eps).
2. From the module's series (Jet, to_series, _numerator): the indicators and the weights at leading order
   on the stencil of x_{i+1/2} and on the stencil of x_{i-1/2} (shifted one cell left), the candidate errors,
   and the leading coefficients of the face error (dx^3) and of the flux-difference error (dx^2), with the
   identity that gives them.
3. Numerics in mpmath (the face() and u() of js_tables.py): face and flux-difference errors on a grid with a
   point exactly at a critical point, and on a grid offset from it, N up to 5120, eps = 0 and 10^-6, for
   sin(pi x) at x = 1/2 (a symmetric extremum: f''' = 0 there) and for g(x) = sin(pi x) + sin(2 pi x)/2 at
   x = 1/3 (f' = 0, f'' = -(3 sqrt 3 / 2) pi^2, f''' = (3/2) pi^3 != 0).
4. A float64 run of the tables' test (u_t + u_x = 0, t = 1, RK4, dt = dx^(5/4)/2) for g, eps = 0 and 10^-6:
   the solution error, the quantity the report's Tables 3-4 print.

Prints tables; stores nothing. Not trusted code (the checker's verdicts do not use it).
"""

from __future__ import annotations

import json
import sys
from fractions import Fraction as F
from pathlib import Path

import mpmath as mp
import numpy as np

import js_tables as JT
from physverify import reconstruction as R

HERE = Path(__file__).resolve().parent
LIU = json.loads((HERE / "specs" / "jiang-shu-weno5-liu-fd.json").read_text())["reconstruction"]


# ---------------------------------------------------------------- 1. the checker
def verdicts():
    print("## 1. reconstruction_order_p, Liu measurement (2.20), n_cp = 1\n")
    print("| form | eps | p | verdict | leading order | detail |\n|---|---|---|---|---|---|")
    for form in ("point", "flux_difference"):
        for eps, label in (("0", "0"), ({"c": 1, "m": 0}, "1 (fixed)")):
            for p in (2, 3, 4, 5):
                r = R.check_claim(LIU, {"claim": "reconstruction_order_p", "p": p, "form": form,
                                        "regime": "critical", "n_cp": 1, "eps": eps})
                detail = (f"k = {r['k']}, coefficient {r['coefficient']} at {r['jet']}"
                          if r["verdict"] == R.REFUTED else "")
                print(f"| {form} | {label} | {p} | {r['verdict']} | {r.get('leading_order', '')} | {detail} |")


# ---------------------------------------------------------------- 2. the series
def series():
    print("\n## 2. the series at n_cp = 1, eps = 0 (f_n = f^(n)(x_i), f_1 = 0)\n")
    Rp = R.parse_reconstruction(LIU)
    n = 6
    jet = R.Jet("point_values", "primitive", 1, 1, 12)
    nv = jet.nv

    def mono(**e):
        return tuple(e.get(f"f{i}", 0) for i in range(nv))

    d = Rp["d"]
    omega0 = {}
    for shift in (0, -1):
        where = "x_{i+1/2} (stencil of x_i)" if shift == 0 else "x_{i-1/2} (stencil of x_{i-1})"
        b = [R.to_series(beta, jet, shift, jet.cap) for beta in Rp["beta"]]
        lead = []
        for k, bk in enumerate(b):
            assert bk[:4] == [{}] * 4 and set(bk[4]) == {mono(f2=2)}, (k, bk[:5])
            lead.append(bk[4][mono(f2=2)])
        # eps = 0, power 2: omega_k(0) = (d_k / c_k^2) / sum_j (d_j / c_j^2), IS_k = c_k (f2 dx^2)^2 + O(dx^5)
        al = [dk / c ** 2 for dk, c in zip(d, lead)]
        w = [a / sum(al) for a in al]
        omega0[shift] = w
        # the module's own weights agree: A_k(0) / D(0)
        A, D = R._weights(Rp, jet, shift, n, None, 2, [])
        dk0 = D[0]
        assert all(len(a[0]) == 1 and len(dk0) == 1 and set(a[0]) == set(dk0) for a in A)
        (key, val), = dk0.items()
        assert [a[0][key] / val for a in A] == w
        print(f"face {where}: IS_k = c_k (f2 dx^2)^2 + O(dx^5), c = {[str(c) for c in lead]}; "
              f"omega_k(dx = 0) = {[str(x) for x in w]} (optimal {[str(x) for x in d]})")
    # candidate errors at x_{i+1/2}: q_k - h = A_k f3 dx^3 + O(dx^4)
    exact = jet.exact(F(1, 2))
    Acoef = []
    for qk in Rp["q"]:
        err = R.sadd(R.to_series(qk, jet, 0, n), exact, -1)
        assert err[:3] == [{}, {}, {}] and set(err[3]) == {mono(f3=1)}
        Acoef.append(err[3][mono(f3=1)])
    print(f"candidate errors q_k - h at the face: A_k f3 dx^3 + O(dx^4), A = {[str(a) for a in Acoef]}; "
          f"sum d_k A_k = {sum(x * y for x, y in zip(d, Acoef))}")
    cp = sum(x * y for x, y in zip(omega0[0], Acoef))
    cm = sum(x * y for x, y in zip(omega0[-1], Acoef))
    print(f"face error at x_{{i+1/2}}: sum_k omega_k(0) A_k f3 dx^3 = {cp} f3 dx^3")
    print(f"face error at x_{{i-1/2}}: sum_k omega'_k(0) A_k f3 dx^3 = {cm} f3 dx^3")
    print(f"flux difference: ({cp} - ({cm})) f3 dx^2 = {cp - cm} f3 dx^2")

    # the module's numerators: leading coefficients, compared with the identity
    for form, s in (("point", 0), ("flux_difference", 1)):
        Np, Dp = R._numerator(Rp, jet, 0, n, None, 2, [])
        if form == "point":
            N, dens = Np, [Dp]
        else:
            Nm, Dm = R._numerator(Rp, jet, -1, n, None, 2, [])
            N, dens = R.sadd(R.smul(Np, Dm, n), R.smul(Nm, Dp, n), -1), [Dp, Dm]
        j0 = R.first_nonzero(N)
        den = {(0,) * nv: F(1)}
        for D_ in dens:
            den = R.pmul(den, D_[0])
        (dm, dc), = den.items()
        lead = {tuple(a - b for a, b in zip(m, dm)): c / dc for m, c in N[j0].items()}
        print(f"module, form {form}: E = ({R.show(lead)}) dx^{j0 - s} + O(dx^{j0 - s + 1})")
        want = cp if form == "point" else cp - cm
        assert lead == {mono(f3=1): want}, lead
        # next coefficient when f3 = 0 (a symmetric extremum, e.g. sin at x = 1/2)
        nxt = {m: c for m, c in N[j0 + 1].items() if m[3] == 0}
        nlead = {tuple(a - b for a, b in zip(m, dm)): c / dc for m, c in nxt.items()}
        print(f"  with f3 = 0 as well: E = ({R.show(nlead)}) dx^{j0 + 1 - s} + O(dx^{j0 + 2 - s})")
    return cp, cm


# ---------------------------------------------------------------- 3. numerics around one critical point
JT.DATA["g"] = [("sin", 1, 1), ("sin", F(1, 2), 2)]
CENTRE = {"sin": mp.mpf(1) / 2, "g": mp.mpf(1) / 3}


def u2(name, x, k):
    """k-th derivative of the datum (k = 2, 3), for the predicted coefficients."""
    out = mp.mpf(0)
    for kind, c, w in JT.DATA[name]:
        a = w * mp.pi * x
        c = mp.mpf(c.numerator) / c.denominator if isinstance(c, F) else mp.mpf(c)
        base = [mp.sin(a), mp.cos(a), -mp.sin(a), -mp.cos(a)] if kind == "sin" else \
            [mp.cos(a), -mp.sin(a), -mp.cos(a), mp.sin(a)]
        out += c * (w * mp.pi) ** k * base[k % 4]
    return out


def local(name, N, eps, theta, M=6):
    """Errors at the faces x_c + (m + theta + 1/2) dx and the points x_c + (m + theta) dx, |m| <= M."""
    dx = mp.mpf(2) / N
    xc = CENTRE[name] + theta * dx
    d = tuple(mp.mpf(x.numerator) / x.denominator for x in JT.D)
    hs = {}
    for m in range(-M - 1, M + 1):
        x = xc + m * dx
        hs[m] = JT.face([JT.u(name, x + k * dx) for k in range(-2, 3)], "original", eps, d)
    fe = {m: hs[m] - JT.u(name, xc + m * dx + dx / 2, dx=dx) for m in range(-M - 1, M + 1)}
    de = {m: (hs[m] - hs[m - 1]) / dx - JT.u(name, xc + m * dx, deriv=1) for m in range(-M, M + 1)}
    return fe, de


def numerics(quick: bool, cp, cm):
    print("\n## 3. errors around one critical point (mpmath, 50 digits), Liu measurement\n")
    Ns = [10 * 2 ** i for i in range(6 if quick else 10)]
    for name in ("sin", "g"):
        f3 = u2(name, CENTRE[name], 3)
        print(f"\n{name} at x = {mp.nstr(CENTRE[name], 6)}: f'' = {mp.nstr(u2(name, CENTRE[name], 2), 6)}, "
              f"f''' = {mp.nstr(f3, 6)}; predicted on the aligned grid (eps = 0): face at x_c + dx/2 "
              f"{mp.nstr(cp * f3, 6)} dx^3, difference at x_c {mp.nstr((cp - cm) * f3, 6)} dx^2")
        for theta, glabel in ((0, "aligned: a grid point at the critical point"),
                              (mp.mpf(1) / 3, "offset: the critical point dx/3 left of a grid point")):
            for eps in (mp.mpf(0), mp.mpf("1e-6")):
                print(f"\n{name}, {glabel}, eps = {mp.nstr(eps, 2)}")
                print("| N | face at x_c+dx/2 | /dx^3 | max face (|m| <= 6) | order | diff. at x_c | /dx^2 "
                      "| max diff. (|m| <= 6) | order | max diff. at m |\n|---|---|---|---|---|---|---|---|---|---|")
                prev = None
                for N in Ns:
                    dx = mp.mpf(2) / N
                    fe, de = local(name, N, eps, theta)
                    mf = max(abs(v) for v in fe.values())
                    md = max(abs(v) for v in de.values())
                    at = max(de, key=lambda m: abs(de[m]))
                    of, od = (JT.order(prev[0], mf), JT.order(prev[1], md)) if prev else (float("nan"),) * 2
                    print(f"| {N} | {mp.nstr(fe[0], 3)} | {mp.nstr(fe[0] / dx ** 3, 5)} | {mp.nstr(mf, 3)} | "
                          f"{of:.2f} | {mp.nstr(de[0], 3)} | {mp.nstr(de[0] / dx ** 2, 5)} | {mp.nstr(md, 3)} | "
                          f"{od:.2f} | {at} |", flush=True)
                    prev = (mf, md)


# ---------------------------------------------------------------- 4. the solution error (float64)
def run(N, eps, measure="original"):
    dx = 2.0 / N
    x = -1 + dx * np.arange(N)

    def g(x):
        return np.sin(np.pi * x) + 0.5 * np.sin(2 * np.pi * x)

    def L(w):
        v = [np.roll(w, -k) for k in range(-2, 3)]
        h = JT.face(v, measure, eps, tuple(float(x) for x in JT.D))
        return -(h - np.roll(h, 1)) / dx

    steps = int(np.ceil(1 / (0.5 * dx ** 1.25)))
    dt = 1.0 / steps
    w = g(x)
    for _ in range(steps):
        k1 = L(w)
        k2 = L(w + dt / 2 * k1)
        k3 = L(w + dt / 2 * k2)
        k4 = L(w + dt * k3)
        w = w + dt / 6 * (k1 + 2 * k2 + 2 * k3 + k4)
    e = np.abs(w - g(x - 1.0))
    return e.max(), e.mean()


def solution(quick: bool):
    print("\n## 4. solution error at t = 1 for g (float64, RK4, dt = dx^(5/4)/2), Liu measurement\n")
    print("| N | eps = 0: L_inf | order | L1 | order | eps = 1e-6: L_inf | order | L1 | order |")
    print("|---|---|---|---|---|---|---|---|---|")
    prev = None
    for N in [20 * 2 ** i for i in range(5 if quick else 9)]:
        r = run(N, 0.0) + run(N, 1e-6)
        o = [np.log2(a / b) for a, b in zip(prev, r)] if prev else [float("nan")] * 4
        print(f"| {N} | {r[0]:.2e} | {o[0]:.2f} | {r[1]:.2e} | {o[1]:.2f} | {r[2]:.2e} | {o[2]:.2f} | "
              f"{r[3]:.2e} | {o[3]:.2f} |", flush=True)
        prev = r


if __name__ == "__main__":
    q = "--quick" in sys.argv
    JT._check_against_specs()
    verdicts()
    cp, cm = series()
    numerics(q, cp, cm)
    solution(q)
