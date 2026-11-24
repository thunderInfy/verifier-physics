#!/usr/bin/env python3
"""Rebuild the evidence registry (data/*.json) from primary sources.

Every file records: source URLs, retrieval date, the raw values as published, and how each
hard bound was derived (rounding of the published digits + an explicit, justified margin).
Margins are set from independent physical estimates, never by fitting the theory under test.

    uv run python tools/fetch_data.py
"""

from __future__ import annotations

import datetime as dt
import html
import json
import re
import urllib.request
from decimal import Decimal as Dec
from pathlib import Path

OUT = Path(__file__).resolve().parent.parent / "data"
TODAY = dt.date.today().isoformat()
FACT = "https://nssdc.gsfc.nasa.gov/planetary/factsheet/{}fact.html"
JPL_CONST = "https://ssd.jpl.nasa.gov/astro_par.html"
HORIZONS = ("https://ssd.jpl.nasa.gov/api/horizons.api?format=text&COMMAND='{cmd}'&OBJ_DATA='NO'"
            "&EPHEM_TYPE='VECTORS'&CENTER='500@10'&START_TIME='{t0}'&STOP_TIME='{t1}'"
            "&STEP_SIZE='{days}d'&OUT_UNITS='KM-S'&REF_PLANE='ECLIPTIC'&VEC_TABLE='2'&CSV_FORMAT='YES'")
SBDB = "https://ssd-api.jpl.nasa.gov/sbdb.api?sstr={}&full-prec=1"
PLANETS = ["mercury", "venus", "earth", "mars", "jupiter", "saturn", "uranus", "neptune"]
M_SUN_1e24 = Dec("1988400")  # NASA Sun fact sheet, 10^24 kg (only used for the tiny m/M ratio)


def get(url: str) -> str:
    return urllib.request.urlopen(url, timeout=60).read().decode("latin-1")


def text(url: str) -> str:
    return " ".join(html.unescape(re.sub(r"<[^>]*>", " ", get(url))).split())


def num(t: str, pat: str) -> Dec:
    m = re.search(pat + r"\s+([-\d.,]+)", t)
    if not m:
        raise ValueError(f"{pat!r} not found")
    return Dec(m.group(1).replace(",", ""))


def half_ulp(s: Dec) -> Dec:
    """Half a unit in the last published digit (rounding uncertainty)."""
    return Dec(1).scaleb(s.as_tuple().exponent) / 2


def b(lo: Dec, hi: Dec) -> list[str]:
    return [str(lo.normalize()), str(hi.normalize())]


def gm_sun() -> Dec:
    t = text(JPL_CONST)
    m = re.search(r"heliocentric gravitational constant GM sun ([\d.]+) x 10 20", t)
    return Dec(m.group(1)) * Dec(10) ** 20


def write(name: str, ev: dict) -> None:
    (OUT / f"{name}.json").write_text(json.dumps(ev, indent=1, ensure_ascii=False) + "\n")
    print("wrote", name)


def main() -> None:
    GM = gm_sun()
    gm_src = f"{JPL_CONST} (DE440 heliocentric GM = {GM})"
    for p in PLANETS:
        t = text(FACT.format(p))
        a = num(t, r"Semimajor axis \(10 6 km\)")
        T = num(t, r"Sidereal orbit period \(days\)")
        q = num(t, r"Perihelion \(10 6 km\)")
        Q = num(t, r"Aphelion \(10 6 km\)")
        m = num(t, r"Mass \(10 24 kg\)")
        mu_hi = GM * (1 + m / M_SUN_1e24)  # two-body GM = G(M_sun + m_planet)
        gm_b = b(GM * Dec("0.999999999"), mu_hi * Dec("1.000000001"))
        raw = {"semimajor_axis_1e6km": str(a), "sidereal_period_days": str(T),
               "perihelion_1e6km": str(q), "aphelion_1e6km": str(Q), "mass_1e24kg": str(m)}
        write(f"kepler-{p}", {
            "id": f"kepler-{p}",
            "source": f"NASA NSSDCA fact sheet {FACT.format(p)}; {gm_src}; retrieved {TODAY}",
            "kind": "hard_bounds",
            "raw": raw,
            "derivation": {
                "a": "published digits ± half ulp",
                "T": "sidereal period ± 1%: mean elements include planetary perturbations, which "
                     "shift the effective two-body period by up to ~0.6% (Saturn/Neptune great "
                     "inequalities); the margin absorbs that so the two-body idealisation is testable",
                "GM": "[GM_sun, GM_sun·(1 + m_planet/M_sun)] widened by 1e-9 (two-body reduced mass)"},
            "quantities": {
                "a": {"dim": "L", "bounds": b((a - half_ulp(a)) * Dec(10) ** 9, (a + half_ulp(a)) * Dec(10) ** 9)},
                "T": {"dim": "T", "bounds": b(T * Dec("0.99") * 86400, T * Dec("1.01") * 86400)},
                "GM": {"dim": "L^3 T^-2", "bounds": gm_b}}})
        write(f"orbit-{p}", {
            "id": f"orbit-{p}",
            "source": f"NASA NSSDCA fact sheet {FACT.format(p)}; retrieved {TODAY}",
            "kind": "hard_bounds",
            "raw": raw,
            "derivation": {"r_peri, r_aph": "published digits ± 0.5% (osculating elements drift; "
                                            "only the existence of a min and a max is used)"},
            "quantities": {
                "r_peri": {"dim": "L", "bounds": b(q * Dec("0.995") * Dec(10) ** 9, q * Dec("1.005") * Dec(10) ** 9)},
                "r_aph": {"dim": "L", "bounds": b(Q * Dec("0.995") * Dec(10) ** 9, Q * Dec("1.005") * Dec(10) ** 9)},
                "GM": {"dim": "L^3 T^-2", "bounds": gm_b}},
            "orbit": {"perihelion": "r_peri", "aphelion": "r_aph"}})

    # Halley's comet: very eccentric, so it discriminates force laws strongly
    d = json.loads(get(SBDB.format("1P")))
    el = {e["name"]: Dec(e["value"]) for e in d["orbit"]["elements"]}
    AU = Dec(149597870700)
    write("orbit-halley", {
        "id": "orbit-halley",
        "source": f"JPL SBDB {SBDB.format('1P')} (epoch JD {d['orbit']['epoch']}); retrieved {TODAY}",
        "kind": "hard_bounds",
        "raw": {"q_au": str(el["q"]), "Q_au": str(el["ad"]), "e": str(el["e"])},
        "derivation": {"r_peri, r_aph": "q and Q ± 2% (planetary perturbations change them by "
                                        "~1% between apparitions)"},
        "quantities": {
            "r_peri": {"dim": "L", "bounds": b(el["q"] * Dec("0.98") * AU, el["q"] * Dec("1.02") * AU)},
            "r_aph": {"dim": "L", "bounds": b(el["ad"] * Dec("0.98") * AU, el["ad"] * Dec("1.02") * AU)},
            "GM": {"dim": "L^3 T^-2", "bounds": b(GM * Dec("0.999999999"), GM * Dec("1.000000001"))}},
        "orbit": {"perihelion": "r_peri", "aphelion": "r_aph"}})

    # Mercury, 10 days of heliocentric motion
    t0, t1, days = "2024-01-01", "2024-01-11", 10
    url = HORIZONS.format(cmd="199", t0=t0, t1=t1, days=days)
    rows = re.search(r"\$\$SOE(.*?)\$\$EOE", get(url), re.S).group(1).strip().splitlines()
    s0, s1 = ([Dec(v) * 1000 for v in r.split(",")[2:8]] for r in rows)
    dpos, dvel, obs = Dec(1000), Dec("0.001"), Dec(500000)
    q = {"GM": {"dim": "L^3 T^-2", "bounds": b(GM * Dec("0.999999999"),
                                                GM * (1 + Dec("0.33010") / M_SUN_1e24) * Dec("1.000000001"))}}
    for i, v in enumerate(["x", "y", "z"]):
        q[f"{v}0"] = {"dim": "L", "bounds": b(s0[i] - dpos, s0[i] + dpos)}
        q[f"v{v}0"] = {"dim": "L T^-1", "bounds": b(s0[i + 3] - dvel, s0[i + 3] + dvel)}
        q[f"{v}1"] = {"dim": "L", "bounds": b(s1[i] - obs, s1[i] + obs)}
    write("trajectory-mercury-10d", {
        "id": "trajectory-mercury-10d",
        "source": f"JPL Horizons DE440 heliocentric ecliptic J2000 vectors {t0} and {t1}: {url}; retrieved {TODAY}",
        "kind": "hard_bounds",
        "raw": {"state0_km_kms": [str(v / 1000) for v in s0], "state1_km_kms": [str(v / 1000) for v in s1]},
        "derivation": {
            "initial state": "± 1 km, ± 1 mm/s (ephemeris accuracy for Mercury is far better)",
            "final position": "± 500 km: perturbations ignored by a two-body model (Venus ≲ 1.3e-7 m/s² "
                              "→ ≲ 50 km in 10 days; Jupiter, Earth, GR smaller) times 10"},
        "quantities": q,
        "trajectory": {"initial": {"x": "x0", "y": "y0", "z": "z0", "vx": "vx0", "vy": "vy0", "vz": "vz0"},
                       "t_obs": str(days * 86400), "observe": {"x": "x1", "y": "y1", "z": "z1"}}})


# Statistical evidence, transcribed from primary review tables (PDF page references below).
# One family => one family-wise error budget α shared by every measurement in it.
FAMILY = "registry-2026"
WILL = "Will, Living Rev. Relativ. 17, 4 (2014), arXiv:1403.7377"
KR = "Kostelecký & Russell, Data Tables for Lorentz and CPT Violation, arXiv:0801.0287 (Jan 2026 ed.)"


def statistical() -> None:
    write("ppn-will2014", {
        "id": "ppn-will2014", "kind": "gaussian", "family": FAMILY,
        "source": f"{WILL}: γ from §3.4 (Cassini, Bertotti et al. 2003); others Table 4; retrieved {TODAY}",
        "derivation": {
            "gamma": "γ − 1 = (2.1 ± 2.3)e-5: a reported 1σ Gaussian result",
            "beta, xi, alpha1, alpha2": "Table 4 'Limit' column, no confidence level stated: "
                                        "INTERPRETED as a 1σ scale around 0 (an assumption)"},
        "quantities": {
            "gamma": {"dim": "1", "value": "1.000021", "sigma": "0.000023"},
            "beta": {"dim": "1", "value": "1", "sigma": "0.00008"},
            "xi": {"dim": "1", "value": "0", "sigma": "4e-9"},
            "alpha1": {"dim": "1", "value": "0", "sigma": "1e-4"},
            "alpha2": {"dim": "1", "value": "0", "sigma": "2e-9"}}})
    write("sme-photon-kappa-em", {
        "id": "sme-photon-kappa-em", "kind": "gaussian", "family": FAMILY,
        "source": f"{KR}, Table D20 (photon sector d = 4, part 1), sapphire cavity oscillators [168]; "
                  f"retrieved {TODAY}",
        "derivation": {"all": "reported value ± 1σ, Sun-centred frame"},
        "quantities": {
            "kappa_em_XY": {"dim": "1", "value": "-0.7e-18", "sigma": "1.6e-18"},
            "kappa_em_XZ": {"dim": "1", "value": "-5.5e-18", "sigma": "4.0e-18"},
            "kappa_em_YZ": {"dim": "1", "value": "-1.9e-18", "sigma": "3.2e-18"}}})


if __name__ == "__main__":
    import sys
    if "--statistical-only" not in sys.argv:
        main()
    statistical()
