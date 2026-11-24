"""Step 2 — dimensional homogeneity.

Proposes a refutation for every law whose sides have different dimensions. The Lean
obligation `Law.dimMismatch ctx law = true` is discharged by `decide` (kernel evaluation of
the verified checker); `Law.dimMismatch_refutes` turns it into "not unit-covariant".
"""

from __future__ import annotations

from .. import units
from ..core import Candidate
from ..theory import Theory

NAME = "dimension"


def well_typed_errors(th: Theory) -> list[str]:
    """Sub-expressions that are not well-dimensioned (contract violations, not refutations)."""
    errs = []
    for l in th.laws:
        for side in (l.lhs, l.rhs):
            try:
                units.dim_of(side, th.dims)
            except units.DimError as ex:
                errs.append(f"law {l.name}: {ex}")
    return errs


def propose(th: Theory, evidence=()) -> list[Candidate]:
    out = []
    for l in th.laws:
        try:
            dl, dr = units.dim_of(l.lhs, th.dims), units.dim_of(l.rhs, th.dims)
        except units.DimError:
            continue
        if dl != dr:
            out.append(Candidate(NAME, "dim_mismatch", {"law": l.name}, "decide",
                                 note=f"lhs {units.fmt_dim(dl)} vs rhs {units.fmt_dim(dr)}"))
    return out
