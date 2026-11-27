# Proposed corrections to expected values (dev half)

Proposals only. The team decides; `items.jsonl` and `ERRATA.md` are unchanged.

| id | field | current | proposed | reason |
|---|---|---|---|---|
| `jiang_shu_1995_weno:02` | with_hypotheses | TRUE | UNSURE (or FALSE if "instead of the 4th order" means "only 4th") | The sentence says the original measurement (2.18)/(2.20) gives "the 4th order" (p. 7: "can only give 4th order accuracy"). The eps -> 0 reading of p. 7 is REFUTED by `reconstruction_order_p`: with eps negligible (the item's hypothesis) and f' != 0 it VERIFIES fifth order for the original measurement as well, for one reconstruction and for the flux difference, leading order 5, every coefficient below dx^5 zero as a polynomial in the Taylor jet. Direct exact evaluation confirms it (error/dx^4 -> 0). The O(h) weight errors d_k (4/5 - 4(k-1)) (f''/f') h cancel against the candidate errors (-1/4, 1/12, -1/12) f''' h^3 at O(h^4); the argument on p. 7 uses the sufficient condition (2.14). The report's Tables 3-4 (eps = 10^-6) are consistent with this: their sub-fifth orders come from the critical points of sin and sin^4 on grids where eps does not yet dominate IS_k there, and away from those points the order is 5 (`notes/jiang-shu-tables.md`). The justification's "the original measurement gives 4th order there (p. 7), so the comparison part holds as well" takes p. 7 at face value. Found by the checker, not by reading the literature: we know of no published statement of it. |

One proposed, from the WENO formalisation (`DEV_RESULTS.md` §3); otherwise no reading gave a verdict against an
expected value. Three we looked at closely and left alone:

- `jiang_shu_1995_weno:02` and `:05` (alone FALSE): FALSE holds when eps is small against the smoothness
  indicators (eps = 0 or eps = dx^4: the WENO5 flux difference drops to order 3 at a first-order critical point,
  WENO3 to order 1). It fails for the fixed eps = 10^-6 that the source uses (fifth order at critical points too,
  since IS_k = O(dx^4) << eps). The justification names the family ("when eps does not dominate the indicators"),
  so FALSE stands; the fields are unformalised because the sentence does not.

- `mfa_oslo_notes:02` (FALSE both): "the energy grows at every time step for any choice of ∆x, ∆t". FALSE rests
  on reading "grows" strictly: data with U^{n+1} = U^n (constants, or (−1)^j on an even periodic grid) keep the
  energy unchanged. The notes clearly mean "never decreases, and grows for generic data", which is TRUE. The
  README's rule is to judge sentences as printed, so FALSE stands, but the item measures a literal reading.
- `mfa_oslo_notes:15` (FALSE both): the time-continuity bound holds if C_F is the Lipschitz constant for the max
  norm on (a, b) and fails for the l1 and Euclidean conventions. The justification already says so and points out
  that the notes use the l1 convention for Q on p. 57, so FALSE stands.
