"""Usage: uv run python benchmark/outside/js_tables.py [--quick]

The accuracy test of Tables 3 and 4 of the ICASE report of jiang_shu_1995_weno (pp. 10-12; the brief calls
them Tables 1-2): u_t + u_x = 0 on [-1, 1], periodic, t = 1, u0 = sin(pi x) (Table 3, N = 10 .. 320) and
u0 = sin^4(pi x) (Table 4, N = 20 .. 640), eps = 10^-6, WENO-RF-4 (r = 3 with the original measurement (2.20))
against WENO-RF-5 (the new measurement (3.2)-(3.4)). For f = u, Roe splitting is the upwind flux f+ = u.

Two parts, both for the two measurements:
1. The reconstruction alone, at t = 0, in mpmath (50 digits): the face error h^_{j+1/2} - h(x_{j+1/2}), with h
   the exact primitive of the flux form (each Fourier mode e^{ikx} of u scaled by (k dx/2)/sin(k dx/2)), and the
   flux-difference error (h^_{j+1/2} - h^_{j-1/2})/dx - u'(x_j), in L_inf and L1 (the mean of |e_j|, which is
   the report's normalisation: its CENTRAL-5 L1/L_inf ratio on sin is 2/pi). eps = 10^-6 and eps = 0, N up to
   5120, with the order between successive N, the place of the largest error, and the share of the L1 error
   from points within 0.1 of a critical point of u.
2. A float64 replica of the report's run (RK4, dt = dx^(5/4)/2, t = 1), to check that the setup is theirs:
   its errors should be close to the printed ones.

The script prints tables; nothing is stored. It is not trusted code (the checker's verdicts do not use it).
"""

from __future__ import annotations

import sys
from fractions import Fraction

import mpmath as mp
import numpy as np

mp.mp.dps = 50
D = (Fraction(1, 10), Fraction(6, 10), Fraction(3, 10))


def betas(v, measure):
    """IS_0..IS_2 from v = (v_-2, .., v_2): 'original' (2.20) or 'new' (3.2)-(3.4)."""
    a, b, c, d, e = v
    if measure == "original":
        return ((((b - a) ** 2 + (c - b) ** 2) / 2 + (c - 2 * b + a) ** 2),
                (((c - b) ** 2 + (d - c) ** 2) / 2 + (d - 2 * c + b) ** 2),
                (((d - c) ** 2 + (e - d) ** 2) / 2 + (e - 2 * d + c) ** 2))
    return (13 * (a - 2 * b + c) ** 2 / 12 + (a - 4 * b + 3 * c) ** 2 / 4,
            13 * (b - 2 * c + d) ** 2 / 12 + (b - d) ** 2 / 4,
            13 * (c - 2 * d + e) ** 2 / 12 + (3 * c - 4 * d + e) ** 2 / 4)


def face(v, measure, eps, lin=D):
    """h^_{j+1/2} of WENO5 (2.10), (2.15)-(2.16) with p = 2, linear weights d."""
    a, b, c, d, e = v
    q = ((2 * a - 7 * b + 11 * c) / 6, (-b + 5 * c + 2 * d) / 6, (2 * c + 5 * d - e) / 6)
    al = [dk / (eps + bk) ** 2 for dk, bk in zip(lin, betas(v, measure))]
    return sum(x * y for x, y in zip(al, q)) / sum(al)


def _check_against_specs():
    """The hand-coded formulas are the ones of the outside specs (exact, at a rational stencil)."""
    import json
    from pathlib import Path

    from physverify import reconstruction as R
    from physverify.expr import parse
    here = Path(__file__).resolve().parent / "specs"
    v = [Fraction(x) for x in (3, -1, 2, 5, Fraction(1, 3))]
    env = dict(zip(range(-2, 3), v))
    for name, measure in (("jiang-shu-weno5-liu-fd.json", "original"), ("jiang-shu-weno5-js-fd.json", "new")):
        rec = json.loads((here / name).read_text())["reconstruction"]
        spec = [R._eval(parse(x), env) for x in rec["weights"]["beta"]]
        assert spec == list(betas(v, measure)), name


# ---------------------------------------------------------------- the data
# u0 = sum of modes (c, k): c cos(k pi x) or sin; stored as (kind, coefficient, wavenumber in units of pi)
DATA = {"sin": [("sin", 1, 1)], "sin4": [("cos", Fraction(3, 8), 0), ("cos", Fraction(-1, 2), 2),
                                           ("cos", Fraction(1, 8), 4)]}
CRIT = {"sin": [-0.5, 0.5], "sin4": [-1.0, -0.5, 0.0, 0.5, 1.0]}  # critical points of u0 (sin4: also x = 0, +-1)


def u(name, x, deriv=0, dx=None):
    """u0, its derivative, or (dx given) the primitive h with sliding average u0."""
    out = mp.mpf(0)
    for kind, c, k in DATA[name]:
        w = k * mp.pi
        val = (mp.sin(w * x) if kind == "sin" else mp.cos(w * x))
        if deriv:
            val = w * (mp.cos(w * x) if kind == "sin" else -mp.sin(w * x))
        if dx is not None and k:
            val *= (w * dx / 2) / mp.sin(w * dx / 2)
        out += mp.mpf(c.numerator) / c.denominator * val if isinstance(c, Fraction) else c * val
    return out


def errors(name, N, measure, eps):
    dx = mp.mpf(2) / N
    xs = [-1 + j * dx for j in range(N)]
    vals = [u(name, x) for x in xs]
    d = tuple(mp.mpf(x.numerator) / x.denominator for x in D)
    hs = [face([vals[(j + k) % N] for k in range(-2, 3)], measure, eps, d) for j in range(N)]
    fe = [hs[j] - u(name, xs[j] + dx / 2, dx=dx) for j in range(N)]
    de = [(hs[j] - hs[j - 1]) / dx - u(name, xs[j], deriv=1) for j in range(N)]
    near = [min(abs(float(x) - c) for c in CRIT[name]) < 0.1 for x in xs]
    out = {}
    for label, e, pts in (("face", fe, [x + dx / 2 for x in xs]), ("difference", de, xs)):
        a = [abs(x) for x in e]
        jmax = max(range(N), key=lambda j: a[j])
        dist = min(abs(float(pts[jmax]) - c) for c in CRIT[name])
        far = sum((x for x, n in zip(a, near) if not n), mp.mpf(0)) / N
        out[label] = (max(a), sum(a) / N, float(dist / float(dx)), float(sum(x for x, n in zip(a, near) if n) / sum(a)),
                      far)
    return out


def order(e1, e2):
    return float(mp.log(e1 / e2, 2)) if e1 and e2 else float("nan")


def reconstruction_alone(quick: bool):
    for name, n0 in (("sin", 10), ("sin4", 20)):
        Ns = [n0 * 2 ** i for i in range(6 if quick else 10 if name == "sin" else 9)]
        for measure in ("original", "new"):
            for eps in (mp.mpf("1e-6"), mp.mpf(0)):
                rows = {N: errors(name, N, measure, eps) for N in Ns}
                for label in ("face", "difference"):
                    print(f"\n{name}, {measure} measurement, eps = {mp.nstr(eps, 2)}, {label} error")
                    print("| N | L_inf | order | L1 | order | max at (dx from crit. pt) | L1 share within 0.1 "
                          "| L1 beyond 0.1 | order |")
                    print("|---|---|---|---|---|---|---|---|---|")
                    prev = None
                    for N in Ns:
                        li, l1, dist, share, far = rows[N][label]
                        oi, o1, of = ((order(prev[0], li), order(prev[1], l1), order(prev[2], far)) if prev
                                      else (float("nan"),) * 3)
                        print(f"| {N} | {mp.nstr(li, 3)} | {oi:.2f} | {mp.nstr(l1, 3)} | {o1:.2f} | {dist:.1f} | "
                              f"{share:.2f} | {mp.nstr(far, 3)} | {of:.2f} |", flush=True)
                        prev = (li, l1, far)


# ---------------------------------------------------------------- float64 replica of the run
def replica(name, N, measure, eps=1e-6):
    dx = 2.0 / N
    x = -1 + dx * np.arange(N)

    def u0(x):
        return np.sin(np.pi * x) if name == "sin" else np.sin(np.pi * x) ** 4

    def L(w):
        v = [np.roll(w, -k) for k in range(-2, 3)]
        h = face(v, measure, eps, tuple(float(x) for x in D))
        return -(h - np.roll(h, 1)) / dx

    steps = int(np.ceil(1 / (0.5 * dx ** 1.25)))
    dt = 1.0 / steps
    w = u0(x)
    for _ in range(steps):
        k1 = L(w)
        k2 = L(w + dt / 2 * k1)
        k3 = L(w + dt / 2 * k2)
        k4 = L(w + dt * k3)
        w = w + dt / 6 * (k1 + 2 * k2 + 2 * k3 + k4)
    e = np.abs(w - u0(x - 1.0))
    return e.max(), e.mean()


def replica_tables():
    for name, n0, table in (("sin", 10, 3), ("sin4", 20, 4)):
        for measure, label in (("original", "WENO-RF-4"), ("new", "WENO-RF-5")):
            print(f"\nreplica of Table {table}, {label} ({name}, eps = 1e-6, RK4, dt = dx^(5/4)/2)")
            print("| N | L_inf | order | L1 | order |\n|---|---|---|---|---|")
            prev = None
            for N in [n0 * 2 ** i for i in range(6)]:
                li, l1 = replica(name, N, measure)
                o = (np.log2(prev[0] / li), np.log2(prev[1] / l1)) if prev else (float("nan"),) * 2
                print(f"| {N} | {li:.2e} | {o[0]:.2f} | {l1:.2e} | {o[1]:.2f} |")
                prev = (li, l1)


if __name__ == "__main__":
    _check_against_specs()
    replica_tables()
    reconstruction_alone("--quick" in sys.argv)
