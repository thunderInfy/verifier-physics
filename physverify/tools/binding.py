"""Which evidence quantities bind which theory symbols (same name *and* same dimension)."""

from __future__ import annotations

from fractions import Fraction

from ..theory import Evidence, Theory


def bind(th: Theory, ev: Evidence) -> dict[str, tuple[Fraction, Fraction]]:
    """Evidence bounds for theory symbols, plus the theory's own constants and parameter ranges.

    Ranges are the theory's claim ("ω ∈ [0, 1000]"), so a refutation covers the whole range.
    """
    out = {s: (v, v) for s, v in th.values.items()}
    out.update(th.ranges)
    out.update({q: b for q, b in ev.bounds.items() if q in th.dims and th.dims[q] == ev.dims[q]
                and q not in th.values and q not in th.ranges})
    return out
