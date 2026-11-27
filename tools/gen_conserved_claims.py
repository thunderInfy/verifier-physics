"""Writes the conserved-quantity benchmark in claims/conserved/ (uv run python tools/gen_conserved_claims.py).

The expected verdicts were written before the checker was first run on these claims.
"""
import json
from pathlib import Path

OUT = Path(__file__).resolve().parents[1] / "claims" / "conserved"
OUT.mkdir(parents=True, exist_ok=True)

PEND = {"coordinates": ["th"],
        "symbols": {"th": {"dim": "1"}, "m": {"dim": "M"}, "l": {"dim": "L"}, "g": {"dim": "L T^-2"}},
        "lagrangian": "m*l^2*th_dot^2/2 + m*g*l*cos(th)",
        "domain": ["m > 0", "l > 0", "g > 0"]}
KEP = {"coordinates": ["r", "th"],
       "symbols": {"r": {"dim": "L"}, "th": {"dim": "1"}, "m": {"dim": "M"}, "GM": {"dim": "L^3 T^-2"}},
       "lagrangian": "m/2*(r_dot^2 + r^2*th_dot^2) + GM*m/r",
       "domain": ["m > 0", "r > 0", "GM > 0"]}
# uniform B along z in the gauge A = (-B y, 0, 0): x is cyclic, its canonical momentum is
# m x_dot - qe B y; the kinetic momentum m x_dot is not conserved (the Lorentz force turns it)
MAG = {"coordinates": ["x", "y"],
       "symbols": {"x": {"dim": "L"}, "y": {"dim": "L"}, "m": {"dim": "M"}, "qe": {"dim": "I T"},
                   "B": {"dim": "M T^-2 I^-1"}},
       "lagrangian": "m/2*(x_dot^2 + y_dot^2) - qe*B*y*x_dot",
       "domain": ["m > 0"]}
OSC = {"coordinates": ["x1", "x2"],
       "symbols": {"x1": {"dim": "L"}, "x2": {"dim": "L"}, "m1": {"dim": "M"}, "m2": {"dim": "M"},
                   "k1": {"dim": "M T^-2"}, "k2": {"dim": "M T^-2"}, "kc": {"dim": "M T^-2"}},
       "lagrangian": "m1/2*x1_dot^2 + m2/2*x2_dot^2 - k1/2*x1^2 - k2/2*x2^2 - kc/2*(x1 - x2)^2",
       "domain": ["m1 > 0", "m2 > 0", "kc > 0"]}

PEND_E = "m*l^2/2*th_dot^2 - m*g*l*cos(th)"
KEP_E = "m/2*(r_dot^2 + r^2*th_dot^2) - GM*m/r"

CLAIMS = {
    "pendulum-energy": (PEND, "pendulum energy", True, "VERIFIED", PEND_E,
                        "dE/dt = th_dot * EL_th"),
    "pendulum-energy-wrong-sign": (PEND, "pendulum energy with the potential's sign flipped", False,
                                   "REFUTED", "m*l^2/2*th_dot^2 + m*g*l*cos(th)",
                                   "on the EL surface dQ/dt = -2 m g l th_dot sin(th)"),
    "kepler-angular-momentum": (KEP, "Kepler angular momentum", True, "VERIFIED", "m*r^2*th_dot",
                                "th is cyclic; Q = dL/d(th_dot)"),
    "kepler-angular-momentum-wrong-power": (KEP, "Kepler 'angular momentum' m r th_dot", False,
                                            "REFUTED", "m*r*th_dot",
                                            "on the EL surface dQ/dt = -m r_dot th_dot"),
    "kepler-energy": (KEP, "Kepler energy", True, "VERIFIED", KEP_E,
                      "L has no explicit t; E = sum qdot dL/dqdot - L"),
    "kepler-energy-wrong-potential-sign": (KEP, "Kepler energy with + GM m / r", False, "REFUTED",
                                           "m/2*(r_dot^2 + r^2*th_dot^2) + GM*m/r",
                                           "dQ/dt = -2 GM m r_dot / r^2 on the EL surface"),
    "kepler-lrl-x": (KEP, "Kepler Laplace-Runge-Lenz vector, x component", True, "VERIFIED",
                     "m^2*(r^2*th_dot*(r_dot*sin(th) + r*th_dot*cos(th)) - GM*cos(th))",
                     "A = p x L - m GM m r_hat; x component in polar coordinates"),
    "magnetic-canonical-momentum": (MAG, "charged particle in uniform B: canonical x momentum", True,
                                    "VERIFIED", "m*x_dot - qe*B*y", "x is cyclic in this gauge"),
    "magnetic-kinetic-momentum": (MAG, "charged particle in uniform B: kinetic x momentum", False,
                                  "REFUTED", "m*x_dot",
                                  "m x_ddot = qe B y_dot: the Lorentz force changes m x_dot"),
    "coupled-oscillators-energy": (OSC, "coupled oscillators: total energy", True, "VERIFIED",
                                   "m1/2*x1_dot^2 + m2/2*x2_dot^2 + k1/2*x1^2 + k2/2*x2^2 + kc/2*(x1 - x2)^2",
                                   "L has no explicit t"),
    "coupled-oscillators-one-energy": (OSC, "coupled oscillators: energy of oscillator 1 alone",
                                       False, "REFUTED", "m1/2*x1_dot^2 + k1/2*x1^2",
                                       "the coupling kc > 0 exchanges energy: dQ/dt = kc x1_dot (x2 - x1)"),
    # degenerate L (lam_dot does not appear): EL_lam is the constraint x = a, so x is constant
    # on every solution; but the jet x = a, x_dot = 1 satisfies the EL system and has
    # dx/dt = 1. Only a REFUTED that demands an invertible Hessian rejects it.
    "constraint-multiplier-position": ({"coordinates": ["x", "lam"],
                                        "symbols": {"x": {"dim": "L"}, "lam": {"dim": "M L T^-2"},
                                                    "m": {"dim": "M"}, "a": {"dim": "L"}},
                                        "lagrangian": "m/2*x_dot^2 + lam*(x - a)",
                                        "domain": ["m > 0"]},
                                       "position under a Lagrange-multiplier constraint x = a", True,
                                       "UNKNOWN", "x",
                                       "true (x = a on every solution) but no Noether multipliers "
                                       "exist, and the EL-consistent jets with x_dot != 0 lie on no "
                                       "solution; the Hessian is singular, so no REFUTED either"),
    "pendulum-energy-over-length": ({**PEND, "domain": ["m > 0", "g > 0"]},
                                    "pendulum energy divided by l, with l unconstrained", None,
                                    "UNKNOWN", f"({PEND_E})/l",
                                    "ill-posed: l = 0 is in the domain and Q divides by l "
                                    "(Lean's x/0 = 0 would make dQ/dt = 0 there)"),
}

for stem, (base, name, true, expect, Q, why) in CLAIMS.items():
    spec = {"kind": "conserved", "name": name, "true": true, "expect": expect, "why": why,
            **base, "quantity": Q}
    (OUT / f"{stem}.json").write_text(json.dumps(spec, indent=2) + "\n")
print(f"wrote {len(CLAIMS)} claims to {OUT}")
