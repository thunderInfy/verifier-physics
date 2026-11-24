"""Evidence registry: loads evidence and compiles statistical evidence into simultaneous boxes.

A *family* is every gaussian evidence file in `data/` that names it. All K scalar
measurements of the family share one family-wise error budget α: each value ± σ becomes the
box value ± z·σ with z = Φ⁻¹(1 − α / 2K) (Bonferroni, rounded up). If every reported σ is a
correct Gaussian marginal, then with probability ≥ 1 − α *all* true values lie in their boxes
simultaneously, and on that event no true theory can be excluded — however many theories are
checked and however the planner picks its tests. (Bonferroni needs no independence assumption.)

K is counted over the whole family on disk, not over the files a caller happens to pass, so
choosing which evidence to show the judge cannot buy a smaller z.
"""

from __future__ import annotations

import json
import math
from fractions import Fraction
from pathlib import Path
from statistics import NormalDist

from .theory import Evidence, load_evidence

DATA = Path(__file__).resolve().parent.parent / "data"
DEFAULT_ALPHA = Fraction(1, 100)


def family_size(family: str, data_dir: Path = DATA) -> int:
    k = 0
    for p in data_dir.glob("**/*.json"):
        spec = json.loads(p.read_text())
        if spec.get("kind") == "gaussian" and spec.get("family") == family:
            k += sum(1 for v in spec["quantities"].values() if "sigma" in v)
    return k


def z_value(alpha: Fraction, k: int) -> Fraction:
    z = NormalDist().inv_cdf(1 - float(alpha) / (2 * k))
    return Fraction(math.ceil(z * 10_000), 10_000) + Fraction(1, 10_000)  # round up, conservatively


def compile_evidence(ev: Evidence, alpha: Fraction = DEFAULT_ALPHA, data_dir: Path = DATA) -> Evidence:
    if not ev.statistical:
        return ev
    k = family_size(ev.family, data_dir)
    if k < len(ev.gauss):
        raise ValueError(f"{ev.id}: family {ev.family!r} is not registered in {data_dir}")
    z = z_value(alpha, k)
    ev.bounds = {q: (v - z * s, v + z * s) for q, (v, s) in ev.gauss.items()}
    ev.stat = {"alpha": alpha, "K": k, "z": z}
    return ev


def load(paths, alpha: Fraction = DEFAULT_ALPHA) -> list[Evidence]:
    return [compile_evidence(load_evidence(p), alpha) for p in paths]
