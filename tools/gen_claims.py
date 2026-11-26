"""Writes the derivation-claim benchmark in claims/ (uv run python tools/gen_claims.py)."""
import json
from pathlib import Path

OUT = Path(__file__).resolve().parents[1] / "claims"
OUT.mkdir(exist_ok=True)

PEND = {"coordinates": ["th"],
        "symbols": {"th": {"dim": "1"}, "m": {"dim": "M"}, "l": {"dim": "L"}, "g": {"dim": "L T^-2"}},
        "lagrangian": "m*l^2*th_dot^2/2 + m*g*l*cos(th)",
        "domain": ["m > 0", "l > 0", "g > 0"]}
KEP = {"coordinates": ["r", "th"],
       "symbols": {"r": {"dim": "L"}, "th": {"dim": "1"}, "m": {"dim": "M"}, "GM": {"dim": "L^3 T^-2"}},
       "lagrangian": "m/2*(r_dot^2 + r^2*th_dot^2) + GM*m/r",
       "domain": ["m > 0", "r > 0", "GM > 0"]}
CHG = {"coordinates": ["x", "y"],
       "symbols": {"x": {"dim": "L"}, "y": {"dim": "L"}, "m": {"dim": "M"}, "qe": {"dim": "I T"},
                   "B": {"dim": "M T^-2 I^-1"}, "Ef": {"dim": "M L T^-3 I^-1"}},
       "lagrangian": "m/2*(x_dot^2 + y_dot^2) + qe*B/2*(x*y_dot - y*x_dot) + qe*Ef*x",
       "domain": ["m > 0"]}
OSC = {"coordinates": ["x1", "x2"],
       "symbols": {"x1": {"dim": "L"}, "x2": {"dim": "L"}, "m1": {"dim": "M"}, "m2": {"dim": "M"},
                   "k1": {"dim": "M T^-2"}, "k2": {"dim": "M T^-2"}, "kc": {"dim": "M T^-2"}},
       "lagrangian": "m1/2*x1_dot^2 + m2/2*x2_dot^2 - k1/2*x1^2 - k2/2*x2^2 - kc/2*(x1 - x2)^2",
       "domain": ["m1 > 0", "m2 > 0"]}
DP = {"coordinates": ["a", "b"],
      "symbols": {"a": {"dim": "1"}, "b": {"dim": "1"}, "m1": {"dim": "M"}, "m2": {"dim": "M"},
                  "l1": {"dim": "L"}, "l2": {"dim": "L"}, "g": {"dim": "L T^-2"}},
      "lagrangian": ("(m1 + m2)/2*l1^2*a_dot^2 + m2/2*l2^2*b_dot^2 + m2*l1*l2*a_dot*b_dot*cos(a - b)"
                     " + (m1 + m2)*g*l1*cos(a) + m2*g*l2*cos(b)"),
      "domain": ["m1 > 0", "m2 > 0", "l1 > 0", "l2 > 0", "g > 0"]}


# x is dimensionless (a real power needs a dimensionless base), so m is a moment of inertia
ROOT_POT = {"coordinates": ["x"],
            "symbols": {"x": {"dim": "1"}, "m": {"dim": "M L^2"}, "k": {"dim": "M L^2 T^-2"}},
            "lagrangian": "m/2*x_dot^2 - k*x^(1/2)"}
HO = {"coordinates": ["x"],
      "symbols": {"x": {"dim": "L"}, "m": {"dim": "M"}, "k": {"dim": "M T^-2"}},
      "lagrangian": "m/2*x_dot^2 - k/2*x^2"}


def eq(l, r): return {"lhs": l, "rhs": r}


# Double pendulum, solved for the accelerations (Cramer's rule on the 2x2 mass matrix,
# determinant written as m2 l1^2 l2^2 (m1 + m2 - m2 cos^2(a - b))).
_den = "(m1 + m2 - m2*cos(a - b)^2)"
_f1 = "(-m2*l1*l2*b_dot^2*sin(a - b) - (m1 + m2)*g*l1*sin(a))"   # generalized force on a
_f2 = "(m2*l1*l2*a_dot^2*sin(a - b) - m2*g*l2*sin(b))"            # generalized force on b
DP_A = f"(m2*l2^2*{_f1} - m2*l1*l2*cos(a - b)*{_f2})/(m2*l1^2*l2^2*{_den})"
DP_B = f"((m1 + m2)*l1^2*{_f2} - m2*l1*l2*cos(a - b)*{_f1})/(m2*l1^2*l2^2*{_den})"
# The usual textbook form, with double angles
DP_A_TXT = ("(-g*(2*m1 + m2)*sin(a) - m2*g*sin(a - 2*b) - 2*sin(a - b)*m2*(b_dot^2*l2 + a_dot^2*l1*cos(a - b)))"
            "/(l1*(2*m1 + m2 - m2*cos(2*a - 2*b)))")
DP_B_TXT = ("(2*sin(a - b)*(a_dot^2*l1*(m1 + m2) + g*(m1 + m2)*cos(a) + b_dot^2*l2*m2*cos(a - b)))"
            "/(l2*(2*m1 + m2 - m2*cos(2*a - 2*b)))")

CLAIMS = {
    "pendulum": (PEND, "simple pendulum", "VERIFIED",
                 "textbook: m l^2 th'' = -m g l sin th, divided by m l^2 > 0",
                 [eq("th_ddot", "-(g/l)*sin(th)")]),
    "pendulum-rearranged": (PEND, "simple pendulum, rearranged", "VERIFIED",
                            "l th'' + g sin th = 0 is the same equation; certificate factor m l",
                            [eq("l*th_ddot + g*sin(th)", "0")]),
    "pendulum-rescaled": (PEND, "simple pendulum, torque form", "VERIFIED",
                          "the equation times m l^2; certificate factor 1",
                          [eq("m*l^2*th_ddot", "-m*g*l*sin(th)")]),
    "pendulum-sin-vs-cos": (PEND, "simple pendulum, cos instead of sin", "REFUTED",
                            "at th = 0 the claim gives th'' = -g/l, the EL equation th'' = 0",
                            [eq("th_ddot", "-(g/l)*cos(th)")]),
    "pendulum-small-angle": (PEND, "simple pendulum, small-angle law claimed for all angles", "REFUTED",
                             "sin th < th for th > 0, so th'' = -(g/l) th fails at th = 1/2",
                             [eq("th_ddot", "-(g/l)*th")]),
    "pendulum-wrong-dimension": (PEND, "simple pendulum, length dropped", "REFUTED",
                                 "th'' = -g sin th has the wrong dimension and fails wherever l != 1",
                                 [eq("th_ddot", "-g*sin(th)")]),
    "kepler-polar": (KEP, "Kepler problem in polar coordinates", "VERIFIED",
                     "r'' = r th'^2 - GM/r^2, th'' = -2 r' th'/r; mass matrix diag(m, m r^2)",
                     [eq("r_ddot", "r*th_dot^2 - GM/r^2"), eq("th_ddot", "-2*r_dot*th_dot/r")]),
    "kepler-angular-momentum": (KEP, "Kepler problem, rescaled and as d/dt(r^2 th') = 0", "VERIFIED",
                                "both equations multiplied by r^2; certificate matrix diag(m/r^2, m)",
                                [eq("r^2*r_ddot", "r^3*th_dot^2 - GM"),
                                 eq("r^2*th_ddot + 2*r*r_dot*th_dot", "0")]),
    "kepler-centrifugal-sign": (KEP, "Kepler problem, sign error in the centrifugal term", "REFUTED",
                                "off by 2 r th'^2, non-zero whenever th' != 0",
                                [eq("r_ddot", "-r*th_dot^2 - GM/r^2"), eq("th_ddot", "-2*r_dot*th_dot/r")]),
    "kepler-missing-factor-2": (KEP, "Kepler problem, missing factor 2 in the Coriolis term", "REFUTED",
                                "th'' = -r' th'/r is off by r' th'/r, non-zero whenever r' th' != 0",
                                [eq("r_ddot", "r*th_dot^2 - GM/r^2"), eq("th_ddot", "-r_dot*th_dot/r")]),
    "charged-particle": (CHG, "charged particle in uniform E (x) and B (z) fields", "VERIFIED",
                         "A = B(-y, x)/2, phi = -E x give m x'' = qE + qB y', m y'' = -qB x'",
                         [eq("x_ddot", "(qe*Ef + qe*B*y_dot)/m"), eq("y_ddot", "-qe*B*x_dot/m")]),
    "charged-particle-wrong-mass": (CHG, "charged particle, 2m in the magnetic term", "REFUTED",
                                    "same dimension, half the Lorentz force; fails whenever q B x' != 0",
                                    [eq("x_ddot", "(qe*Ef + qe*B*y_dot)/m"), eq("y_ddot", "-qe*B*x_dot/(2*m)")]),
    "coupled-oscillators": (OSC, "two coupled oscillators", "VERIFIED",
                            "m1 x1'' = -k1 x1 - kc (x1 - x2), m2 x2'' = -k2 x2 + kc (x1 - x2)",
                            [eq("x1_ddot", "(-k1*x1 - kc*(x1 - x2))/m1"),
                             eq("x2_ddot", "(-k2*x2 + kc*(x1 - x2))/m2")]),
    "coupled-oscillators-reordered": (OSC, "two coupled oscillators, force form, listed in reverse", "VERIFIED",
                                      "the equations times the masses, x2 first: anti-diagonal certificate matrix",
                                      [eq("m2*x2_ddot + (k2 + kc)*x2", "kc*x1"),
                                       eq("m1*x1_ddot + (k1 + kc)*x1", "kc*x2")]),
    "coupled-oscillators-dropped-coupling": (OSC, "two coupled oscillators, coupling dropped in x1", "REFUTED",
                                             "misses -kc (x1 - x2)/m1, non-zero whenever x1 != x2",
                                             [eq("x1_ddot", "-k1*x1/m1"),
                                              eq("x2_ddot", "(-k2*x2 + kc*(x1 - x2))/m2")]),
    "coupled-oscillators-swapped-mass": (OSC, "two coupled oscillators, m2 instead of m1 in x1", "REFUTED",
                                         "dimensionally consistent, wrong whenever m1 != m2 and the force on x1 != 0",
                                         [eq("x1_ddot", "(-k1*x1 - kc*(x1 - x2))/m2"),
                                          eq("x2_ddot", "(-k2*x2 + kc*(x1 - x2))/m2")]),
    "double-pendulum": (DP, "double pendulum, solved by Cramer's rule", "VERIFIED",
                        "non-diagonal mass matrix; det = m2 l1^2 l2^2 (m1 + m2 sin^2(a - b)) > 0",
                        [eq("a_ddot", DP_A), eq("b_ddot", DP_B)]),
    "double-pendulum-textbook": (DP, "double pendulum, textbook form with double angles", "UNKNOWN",
                                 "true, but equal to the EL equations only via double-angle identities "
                                 "our tactics do not try",
                                 [eq("a_ddot", DP_A_TXT), eq("b_ddot", DP_B_TXT)]),
    "root-potential": ({**ROOT_POT, "domain": ["m > 0", "x > 0"]}, "potential k x^(1/2)", "VERIFIED",
                       "m x'' = -(k/2) x^(-1/2) for x > 0",
                       [eq("x_ddot", "-k/(2*m)*x^(-1/2)")]),
}
# Ill-posed claims (`"true": null`): any decisive verdict is wrong.
ILL_POSED = {
    "pendulum-empty-domain": ({**PEND, "domain": ["m > 0", "l > 0", "g > 0", "th > 1/2", "th < -1/2"]},
                              "small-angle pendulum on an empty domain", "UNKNOWN",
                              "|th| < 1/2 mistyped as th > 1/2 and th < -1/2: no point satisfies it, "
                              "so a VERIFIED certificate would be vacuous",
                              [eq("th_ddot", "-(g/l)*th")]),
    "root-potential-negative-x": ({**ROOT_POT, "domain": ["m > 0", "x != 0"]},
                                  "potential k x^(1/2), domain x != 0", "UNKNOWN",
                                  "for x < 0 the Lagrangian is not real; Lean's x^(1/2) = 0 there "
                                  "makes the claim hold on all of x != 0 only through junk values",
                                  [eq("x_ddot", "-k/(2*m)*x^(-1/2)")]),
    "oscillator-sqrt-frequency": ({**HO, "domain": ["m > 0"]},
                                  "oscillator with w = sqrt(k/m), sign of k not fixed", "UNKNOWN",
                                  "x'' = -sqrt(k/m)^2 x is right for k > 0; for k < 0 Lean's "
                                  "sqrt(k/m) = 0 would give a junk counterexample",
                                  [eq("x_ddot", "-sqrt(k/m)^2*x")]),
}

for fn, (base, name, expect, why, eom) in CLAIMS.items():
    spec = {"name": name, "true": expect != "REFUTED", "expect": expect, "why": why, **base, "eom": eom}
    (OUT / f"{fn}.json").write_text(json.dumps(spec, indent=2) + "\n")
for fn, (base, name, expect, why, eom) in ILL_POSED.items():
    spec = {"name": name, "true": None, "expect": expect, "why": why, **base, "eom": eom}
    (OUT / f"{fn}.json").write_text(json.dumps(spec, indent=2) + "\n")
print(len(CLAIMS) + len(ILL_POSED), "claims written to", OUT)
