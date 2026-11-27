# Outside benchmark, dev half: what the checker can state and decide

The 99 dev items (9 sources, split in `FROZEN.md`) were read against the checker as it was on main
(physverify/schemes, no changes). **Re-scored after three checker additions.** (1) A checker fix (commit 055abd1):
exact univariate nonnegativity in `positivity` and the linear TVD equivalence `tvd_linear`, both general, closed
the two gaps on `harten_1982_highres:05`; no reading, spec or expected value changed, and no other verdict moved.
(2) The `stated_identity` claim kind (a printed formula satisfies its defining identity,
`physverify/schemes/identity.py`) gave readings to two more items, tecno:04 and tecno:02. (3) The
`reconstruction_order_p` claim kind (exact order of WENO-type reconstructions, `physverify/reconstruction.py`,
commit 2feeea8) gave a reading to jiang_shu_1995_weno:05 (with hypotheses, MATCH). jiang_shu_1995_weno:02 stays
unformalised in both fields, now for a stated reason other than `reconstruction`: §3 has the details. The numbers
below include all three; the first-round numbers (before any of them) are given where they changed: 9 of 99 items
stated, 12 of 14 readings decided, 7 / 6 MATCH, 0 WRONG. Readings and reasons are in `dev_readings.json`, following the rules and the gap
taxonomy in `README.md` (committed before any item was classified). `run_dev.py` recomputes every verdict in about
5 s; `tests/test_outside_dev.py` checks that the stored verdicts and scores are what the checker gives now. No
heldout item was opened, formalised or run. The eight claim names used (`consistent`, `positive_under_cfl`,
`von_neumann_stable_under_cfl`, `local_max_principle_under_cfl`, `tvd_under_cfl`, `truncation_order_smooth_data`,
`stated_identity`, `reconstruction_order_p`)
are checked against the claim-kind registry `physverify/claimkinds.py` by `tests/test_claimkinds.py`, and each is
used in the registry's reading.

Every verdict below is exact (Python `Fraction` arithmetic, polynomial identities and explicit rational
witnesses); none is empirical and none is a Lean proof. Three decisions also rest on a bridge lemma written in the
reading (the reading's own reasoning, not checked by the code): `fjordholm_mishra_tadmor_2012_tecno:03`, the
global-to-local maximum principle in `zhang_shu_2010_maxprinciple:04`, and the first reading of
`harten_1982_highres:05` (TVD iff non-negative coefficients, through `positive_under_cfl`). Its second reading,
through `tvd_under_cfl`, uses the same equivalence as a row of the claims table (`tvd_linear`) instead.

## 1. Statable fraction

**12 of 99 dev items** have at least one formal reading: 10 for the `alone` field, 10 for `with_hypotheses`
(first round: 9 of 99, 8 and 7).

| property | stated / items | stated items |
|---|---|---|
| positivity | 2 / 26 | zhang_shu_2010_maxprinciple:02, :04 |
| order | 4 / 24 | harten_1982_highres:01, fjordholm_mishra_tadmor_2012_tecno:02 (its entropy clause only), :03, jiang_shu_1995_weno:05 (with hypotheses) |
| stability | 3 / 11 | mfa_oslo_notes:03, :04, :05 |
| entropy | 1 / 11 | fjordholm_mishra_tadmor_2012_tecno:04 |
| convergence | 1 / 8 | harten_1982_highres:11 (its order clause only) |
| other | 0 / 8 | |
| tvd | 1 / 8 | harten_1982_highres:05 |
| monotone | 0 / 2 | |
| conservation | 0 / 1 | |

Every one of the 17 readings narrows its sentence: linear advection (a = 1) for a general flux or sign of a, one
viscosity Q, a scalar instance of a system (Burgers with u^2/2 for the two TeCNO identities), a two-stage SSP method for "SSP high order time discretizations",
a Courant range [0, 2] standing for "no CFL restriction", or (WENO, jiang_shu_1995_weno:05) one split flux
component, the order as the truncation error at one point, and eps = 0 for "eps negligible". Each narrowing is recorded in the reading. A narrowed
VERIFIED verifies the instance only.

## 2. Decided fraction

**16 of 17 readings are decided** (8 VERIFIED, 8 REFUTED, all exact; first round 12 of 14). The one undecided
reading is tecno:02's (expected UNSURE): its entropy-conservation clause is VERIFIED by `stated_identity`, but its
second-order clause has no named claim, so the conjunction is UNKNOWN. Before the checker fix the two readings of
`harten_1982_highres:05` (Harten's scheme with Q(x) = x^2 + 1/4 on linear advection, TVNI for nu up to
433/500 < sqrt(3)/2) were UNKNOWN, both from checker gaps, not hard cases:

- `positive_under_cfl` was UNKNOWN: the coefficient of u_{i+1} is (nu - 1/2)^2/2, non-negative with a double
  root inside the interval, which no Bernstein test (subdivided or not) certifies unless a cut lands on the
  root. Now `positivity` decides it exactly: square-free decomposition, no root of odd multiplicity in the open
  interval (Sturm count), positive at a sample point.
- `tvd_under_cfl` was UNKNOWN: `tvd_harten` certifies Harten's form only with the upwind split (D = 0), and this
  centred scheme needs both C and D positive. Now `tvd_linear` decides it: for a linear update with
  sum_k c_k = 1, TVD for all data iff every c_k >= 0 on the range. `tvd_harten` is still UNKNOWN here.

Scores per field (fields with no reading count as GAP when the expected value is TRUE/FALSE):

| field | MATCH | WRONG | GAP | UNSCORED (UNSURE) |
|---|---|---|---|---|
| alone | 9 | 0 | 59 | 31 |
| with hypotheses | 9 | 0 | 58 | 32 |

All 18 matches rest on narrowed readings. Of the 68 alone and 67 with-hypotheses fields that have a TRUE/FALSE
expectation, the checker decides 9 and 9, about 13% (first round 7 and 6).

## 3. Wrong count

**0 WRONG in both fields** (and no INCONSISTENT verdict). There is nothing to diagnose as a checker bug, a
misformalisation or a wrong expected value.

That zero says little about soundness on outside claims, because the readings that reached the checker are
the easy kind (linear schemes, a CFL range, one smooth extremum). Two naive readings that we rejected would have
been WRONG. We ran both once to check; neither is stored or scored:

- `fjordholm_mishra_tadmor_2012_tecno:04` (FALSE both ways: the printed entropy flux ^Q has the wrong sign). Read
  as "the scheme (3.2) is entropy stable", `entropy_stable_tadmor` on Burgers with D = 1 gives VERIFIED. The
  sentence's content is an identity for the printed ^Q, which in the first round no named claim looked at. A
  misformalisation of this kind is the likeliest route to a WRONG: the named claim checks the property the paper
  means, not the formula it prints. The item now has the reading it needed: `stated_identity` on the identity
  (3.3) with ^Q as transcribed, REFUTED (below). We re-read the printed formula on the publisher PDF (p. 551) and
  it has the plus sign the collector transcribed; no erratum or later version was found
  (`notes/tecno04-transcription.md`).
- `mfa_oslo_notes:02` (FALSE: "the energy grows at every time step" fails for data with U^{n+1} = U^n). Read as
  "the central scheme is not von Neumann stable for any nu", the checker refutes stability (REFUTED on
  [0, 1] and for every small CFL number), so the negated reading would be VERIFIED on a FALSE item.

Where a reading's truth would differ from the sentence's, we left the item unformalised (rule in `README.md`),
which is why these two have no reading.

The WENO items added a third case of this kind, and a finding about the source. Each was run once to check and
is neither stored nor scored:

- **jiang_shu_1995_weno:02 and :05, alone (FALSE).** The truth depends on how eps scales with dx, and the bare
  sentence does not fix it. Jiang and Shu define eps as a fixed constant (p. 6, after (2.16): "we will take
  eps = 10^-6"), derive the order with eps left out ((2.17), (3.8)-(3.9)), and on p. 7 explain fixed-eps
  convergence on fine grids as an artefact ("since the smoothness measurements IS_k for all k are relatively
  smaller than the non-zero constant eps in (2.16), the weights become close to the optimal weights"). The FALSE
  value rests on Henrick, Aslam and Powers "when eps does not dominate the indicators". With eps = 0 or eps = dx^4,
  `reconstruction_order_p` on the flux difference at a first-order critical point is REFUTED for p = 5 (leading
  order 3; r = 2: order 1). With eps = 10^-6 fixed it is VERIFIED at n_cp = 1 (fifth order; the drop needs eps
  small against IS_k = O(dx^4)). The team's rule for this case was "one reading per eps family". But the fixed-eps
  reading picks an instance whose truth differs from the expected value (forbidden by the README), and the
  eps << IS_k reading alone is the family that makes the checker match. So both alone fields are unformalised
  (`family_unspecified`, a gap in the source: the content is not definite until the eps family is; these two
  entries were `not-checkable` before reconstruction v2).
- **jiang_shu_1995_weno:02, with hypotheses (TRUE).** The item's hypothesis "eps treated as negligible" does fix
  the family, but the sentence also says the original measurement (2.18)/(2.20) gives "the 4th order", and p. 7
  says it "can only give 4th order accuracy". The checker finds otherwise: with eps -> 0 and f' != 0 the original
  measurement is fifth order too, for one reconstruction and for the flux difference (VERIFIED for p = 5, leading
  order 5). Direct exact evaluation of the formulas confirms it (error/dx^4 -> 0 at rational dx = 2^-6 .. 2^-12;
  `tests/test_reconstruction.py`). The O(h) terms of (2.23)-(2.25) are -2, 0, +2 times f''h/f', linear in k, and
  weight errors of that form cancel against the candidate errors (1/4, -1/12, 1/12) f''' h^3 at O(h^4). The
  source's argument uses only the sufficient condition (2.14). Read as "4th and not 5th" the sentence is false; read
  as "at least 4th" it is true. The text does not decide, so the field is unformalised (`not-checkable`) and
  `ERRATA_PROPOSED.md` lists it for the team.

The decided readings, with the witness or certificate each verdict rests on:

| item | field | verdict | what decides it |
|---|---|---|---|
| zhang_shu_2010_maxprinciple:02 | with hyp. | VERIFIED | SSP-RK2 of upwind has coefficients 1/2 + (1-nu)^2/2, nu(1-nu), nu^2/2, all >= 0 on [0, 1] (Bernstein) |
| zhang_shu_2010_maxprinciple:02 | alone | REFUTED | the coefficient nu(1-nu) of u_{i-1} is negative at a nu in (1, 2] |
| zhang_shu_2010_maxprinciple:04 | with hyp. | VERIFIED | local maximum principle from Harten's upwind form on [0, 1] |
| zhang_shu_2010_maxprinciple:04 | alone | REFUTED | an explicit periodic state whose update leaves its stencil's range at a nu in [0, 2] |
| harten_1982_highres:05 | both | VERIFIED | c_{+1} = (nu - 1/2)^2/2 >= 0 by the square-free/Sturm decision, c_{-1}, c_0 by Bernstein, on [0, 433/500]; TVD by the linear equivalence (re-scored) |
| harten_1982_highres:01 | alone | REFUTED | U(x) = 1 - x^2/2 at x_i = 0: the stencil sits in a minmod branch with tau = O(dx), not O(dx^2) |
| harten_1982_highres:11 | alone | REFUTED | the same witness (the order clause; the convergence clause is unformalised) |
| mfa_oslo_notes:03 | with hyp. | VERIFIED | von Neumann certificate 1 - \|g\|^2 = (1 - z) Q, Q >= 0 on [0, 1] |
| mfa_oslo_notes:03 | alone | REFUTED | \|g\| > 1 at a nu in (1, 2] |
| mfa_oslo_notes:04 | both | VERIFIED | stable on [0, 1] and (negated) not stable on [0, 2] |
| mfa_oslo_notes:05 | with hyp. | VERIFIED | upwind coefficients 1 - nu, nu >= 0 on [0, 1] |
| mfa_oslo_notes:05 | alone | REFUTED | 1 - nu < 0 at a nu in (1, 2] |
| fjordholm_mishra_tadmor_2012_tecno:03 | with hyp. | REFUTED | with the printed normalization alpha_1 = 1/2, F(u, u) - f(u) = -u^2/4 (witness at u = 1) |
| jiang_shu_1995_weno:05 | with hyp. | VERIFIED | flux difference with eps = 0 where f' != 0: r = 2 (IS (2.19)) order 3 and r = 3 (IS (3.2)-(3.4)) order 5, the coefficients of dx^0 .. dx^(p-1) zero as polynomials in the Taylor jet; the leading term of every IS_k (both stencils) is (f' dx)^2, positive by form (re-scored) |
| fjordholm_mishra_tadmor_2012_tecno:04 | both | REFUTED | identity (3.3) as transcribed, Burgers, D = 1: LHS - RHS = (u_{i+1}^2 - 2 u_i^2 + u_{i-1}^2)/2, which is 1/2 at (u_{i-1}, u_i, u_{i+1}) = (0, 0, 1); with the minus sign of Lemma 3.2 it normalises to 0 |

## 4. Gap taxonomy

Primary reason per unformalised field (the first in the README's order that blocks a reading; 87 items have no
reading at all, and 4 lack one for a single field):

| reason | primary (fields entries) | items, any mention | what it would take |
|---|---|---|---|
| `scheme-class` | 27 | 27 | theorems about every scheme with a property (monotone ⇒ TVD, conservative ⇔ flux form, Lax–Wendroff, Crandall–Majda, Harten's lemma). A spec is one scheme. This needs statements over parametrised schemes, i.e. Lean proofs with the flux as a variable, not more checks |
| `reconstruction` | 21 | 48 | WENO/ENO stencil selection and smoothness indicators (the order of one WENO scheme in a stated regime is now `reconstruction_order_p`), polynomial reconstructions with point values (Gauss–Lobatto), DG/FV cell-average schemes and their limiters. The largest roadmap item for this literature |
| `multi-d` | 15 | 16 | 2D rectangles and triangles (the two maximum-principle sources and TeCNO), plus one d-dimensional WENO theorem |
| `system` | 9 | 18 | Euler, general systems with entropy variables, constant-coefficient systems with several fields. Counted only where a scalar narrowing would change the truth or lose the point |
| `claim-kind-missing` | 6 | 22 | listed below |
| `not-checkable` | 8 | 8 | numerical observations (3), a comparison with the literature (1), vague or existential wording (3), a clause whose reading is a judgment call (1: jiang_shu_1995_weno:02 with hypotheses, "4th order", §3) |
| *gap in the source* | | | |
| `family_unspecified` | 2 | 2 | the source fixes eps = 10^-6 but leaves its scaling with dx open, and the truth depends on it (jiang_shu_1995_weno:02 and :05, alone, §3). Fixed by choosing the family where the expected value is owned, not by the checker. Split out of `not-checkable` in reconstruction v2; no score changed |
| `illegible` | 2 | 2 | osher_tadmor_1985_convergence:02, :05 (the displays they depend on are illegible in the scan) |
| `variable-coefficients` | 1 | 7 | a velocity that changes from cell to cell (vorticity schemes) |
| `not-expressible` | 1 | 2 | harten_1982_highres:08: Q(nu + gamma) Delta v divides by a state difference for any non-constant Q |
| `time-stepping` | 0 | 10 | SSP Runge–Kutta / multistep beyond a five-point update (never primary: those items also need reconstruction) |

Claim kinds the notes ask for (22 mentions; for the class items they would be needed on top of class
statements): semi-discrete
order of accuracy (tadmor_1987_viscosity:01, tecno:02, tecno:03 alone), order away from extrema / Harten's flux
condition (3.6) (harten:01 and :11 with hypotheses, harten:06), an exact energy identity or strict energy growth
(mfa:01, mfa:02), E-fluxes (osher_tadmor:01, :09), "no new local extrema" (harten:12), time continuity (mfa:15), an
l1-distance identity (zhang_shu_2011_survey:06), and nonlinearity of the update (heoc:03). The first two are the
most reusable. The identity for a stated numerical entropy flux (tecno:04) and entropy conservation as an equality
(tecno:02) were on this list in the first round; `stated_identity` now covers both for scalar laws. The energy
identity of mfa:01 is a fully discrete identity summed over the grid, which `stated_identity` does not state.

**First class theorems (added after scoring; nothing here is re-scored).** `lean/PhysVerify/Harten.lean` proves
Harten's lemma (`harten_tvd`, `harten_tvd_of_form`) and monotone ⇒ TVD for three-point conservative schemes
(`monotone_tvd`), on a periodic grid of any size (README, "Class theorems"). Of the 27 `scheme-class` dev items, these
would state three: harten_1982_highres:04 (C_{-,j+1/2}, C_{+,j+1/2} ≥ 0 and their sum ≤ 1 give TVNI: `harten_tvd`,
with C = C_+ and D = C_-), mfa_oslo_notes:12 (the same condition (4.57) with C^n, D^n: `harten_tvd`, one step at a
time), and mfa_oslo_notes:14 (a monotone three-point scheme is TVD: `monotone_tvd`, which needs neither the
consistency nor the CFL hypothesis of the sentence). Partly: harten_1982_highres:02 ("a monotone scheme is TVNI")
for three-point schemes only; the sentence is about (2K+1)-point schemes. Two caveats hold for all four: the sources
work on the whole line with finite TV, and we proved the periodic version; and none of it is wired into a verdict, so
the rows above still count these items as gaps. The SSP item (mfa_oslo_notes:20, a convex combination of forward
Euler steps is TVD) and the L∞ bound under (4.59) (mfa_oslo_notes:13) look like short additions to the same module;
they are not done.

## 5. Alone versus with hypotheses

The two expectations differ on **30 of 99** items: FALSE alone / TRUE with hypotheses 15, FALSE / UNSURE 8,
UNSURE / TRUE 6, UNSURE / FALSE 1. In almost all of them the dropped hypothesis is a CFL bound, a smoothness or
point-value condition, or the convergence of the scheme.

Eight of the 30 are stated, and the checker gets every scored field right:

| item | alone | with hypotheses | dropped hypothesis |
|---|---|---|---|
| zhang_shu_2010_maxprinciple:02 | FALSE: MATCH | TRUE: MATCH | the time step bound dt <= c dt_0 |
| zhang_shu_2010_maxprinciple:04 | FALSE: MATCH | TRUE: MATCH | the CFL bound lambda a <= 1 |
| mfa_oslo_notes:03 | FALSE: MATCH | TRUE: MATCH | the CFL bound |
| mfa_oslo_notes:05 | FALSE: MATCH | TRUE: MATCH | the CFL bound |
| harten_1982_highres:01 | FALSE: MATCH | TRUE: GAP | "away from u_x = 0" (no named claim for order away from extrema) |
| harten_1982_highres:11 | FALSE: MATCH | UNSURE: unscored | the same |
| fjordholm_mishra_tadmor_2012_tecno:03 | UNSURE: unscored | FALSE: MATCH | here the printed hypothesis (the normalization of alpha) is what makes it false |
| jiang_shu_1995_weno:05 | FALSE: GAP (unformalised, §3) | TRUE: MATCH | f' != 0 and eps negligible; the drop at critical points needs the eps family fixed |

So on dropped CFL bounds the checker is reliable: the with-hypotheses reading verifies on the stated range and the
alone reading refutes on [0, 2], both exactly. The dropped smoothness condition ("away from extrema") is half
covered: the checker refutes the unqualified claim at an extremum, but cannot state the qualified one. The other
22 differing items are unformalised, mostly `reconstruction` and `scheme-class`, so the checker says nothing about
whether their hypotheses matter.

## Caveats

- The formalisation was not blind: we read every expected value and justification while writing the readings.
  Three alone readings take their instance from the justification's counterexample
  (`instance_from_justification` in the file: zhang_shu_2010_maxprinciple:02 and :04, tecno:03). The rule that
  class theorems are never narrowed to an instance, even a refuting one, was fixed in the README before
  classifying, to keep that from turning into cherry-picking FALSE items.
- The [0, 2] range for "no CFL restriction" is our choice. A refutation on [0, 2] refutes "for every nu". A
  verification on it would not have verified "for every nu", but none occurred.
- Low coverage is the result, not a failure to look: the dev sources are mostly about high-order reconstruction,
  2D meshes and theorems over classes of schemes, which are outside what a spec can say today.

## Proposals

The two small, general proposals from the gaps above are implemented (commit 055abd1), in a different form from
the one first proposed:

1. `checks.positivity`: subdividing the Bernstein test would not have been enough (an interior double root is
   certified only by a cut landing on it), so the fallback is an exact decision instead
   (`physverify/schemes/univariate.py`: square-free decomposition + Sturm counts, or an exact counterexample).
2. `tvd_under_cfl` and `local_max_principle_under_cfl` on a linear update: the EQUIVALENT rows `tvd_linear` and
   `max_principle_linear` (TVD, and the local maximum principle, iff every coefficient is non-negative, with
   sum_k c_k = 1). `tvd_harten` with a general C, D split is still open.

Larger items, in order of how many dev items they would open: claims over classes of schemes (27), reconstruction
(48 mentions), semi-discrete order and order away from extrema (about 6).

Expected-value corrections: one proposed (jiang_shu_1995_weno:02, with hypotheses, §3); see `ERRATA_PROPOSED.md`.
