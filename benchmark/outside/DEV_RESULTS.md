# Outside benchmark, dev half: what the checker can state and decide

The 99 dev items (9 sources, split in `FROZEN.md`) were read against the checker as it was on main
(physverify/schemes, no changes). **Re-scored after four checker additions; the fourth is tuned on these items.**
(1) A checker fix (commit 055abd1):
exact univariate nonnegativity in `positivity` and the linear TVD equivalence `tvd_linear`, both general, closed
the two gaps on `harten_1982_highres:05`; no reading, spec or expected value changed, and no other verdict moved.
(2) The `stated_identity` claim kind (a printed formula satisfies its defining identity,
`physverify/schemes/identity.py`) gave readings to two more items, tecno:04 and tecno:02. (3) The
`reconstruction_order_p` claim kind (exact order of WENO-type reconstructions, `physverify/reconstruction.py`,
commit 2feeea8) gave a reading to jiang_shu_1995_weno:05 (with hypotheses, MATCH). jiang_shu_1995_weno:02 stays
unformalised in both fields, now for a stated reason other than `reconstruction`: §3 has the details. (4)
Reconstruction v3, **tuned on the dev items**: we surveyed the 48 dev items that list `reconstruction`
(`notes/reconstruction-survey.md`, commit 1b3ff25, written before any checker change), and built the two
mechanisms that cover the most of them (commit d184a85; bench specs and expected verdicts first, commit a764f2e):
`cell_average_max_principle` (`physverify/cellaverage.py`), motivated by zhang_shu_2010_maxprinciple:05 and
zhang_shu_2011_survey:04 and :13, and `eno_sign_property` / `eno_jump_ratio_at_most` (`physverify/eno.py`),
motivated by fjordholm_mishra_tadmor_2012_tecno:06, :07 and :08. Because the claim kinds were chosen by their
coverage of these items, their 6 readings (flagged `tuned_on` in `dev_readings.json`) and the 8 MATCH fields
resting only on them measure how far the tuning reached, not how the checker does on unseen claims. The same
survey found a reading for jiang_shu_1995_weno:01 (with hypotheses) that needed no checker change, and moved its
alone field to `family_unspecified`. The numbers below include all four; the numbers before (4) were 12 of 99
items stated, 16 of 17 readings decided, 9 / 9 MATCH; the first-round numbers (before any of them) are 9 of 99
items stated, 12 of 14 readings decided, 7 / 6 MATCH, 0 WRONG. Readings and reasons are in `dev_readings.json`, following the rules and the gap
taxonomy in `README.md` (committed before any item was classified). `run_dev.py` recomputes every verdict in about
5 s; `tests/test_outside_dev.py` checks that the stored verdicts and scores are what the checker gives now. No
heldout item was opened, formalised or run. The eleven claim names used (`consistent`, `positive_under_cfl`,
`von_neumann_stable_under_cfl`, `local_max_principle_under_cfl`, `tvd_under_cfl`, `truncation_order_smooth_data`,
`stated_identity`, `reconstruction_order_p`, `cell_average_max_principle`, `eno_sign_property`,
`eno_jump_ratio_at_most`)
are checked against the claim-kind registry `physverify/claimkinds.py` by `tests/test_claimkinds.py`, and each is
used in the registry's reading.

Every verdict below is exact (Python `Fraction` arithmetic, polynomial identities and explicit rational
witnesses); none is empirical and none is a Lean proof. Three decisions also rest on a bridge lemma written in the
reading (the reading's own reasoning, not checked by the code): `fjordholm_mishra_tadmor_2012_tecno:03`, the
global-to-local maximum principle in `zhang_shu_2010_maxprinciple:04`, and the first reading of
`harten_1982_highres:05` (TVD iff non-negative coefficients, through `positive_under_cfl`). Its second reading,
through `tvd_under_cfl`, uses the same equivalence as a row of the claims table (`tvd_linear`) instead. A
fourth bridge is in `fjordholm_mishra_tadmor_2012_tecno:08` (reconstruction v3): the paper's identification (3.20)
of the scaled ENO reconstruction with plain ENO on the data mu^{i+1}, in the scalar case.

## 1. Statable fraction

**19 of 99 dev items** have at least one formal reading: 16 for the `alone` field, 17 for `with_hypotheses`
(before reconstruction v3: 12 of 99, 10 and 10; first round: 9 of 99, 8 and 7). Six of the 19 are stated only
with the claim kinds tuned on these items (marked *tuned* below).

| property | stated / items | stated items |
|---|---|---|
| positivity | 5 / 26 | zhang_shu_2010_maxprinciple:02, :04, :05 (*tuned*), zhang_shu_2011_survey:04, :13 (*tuned*) |
| order | 5 / 24 | harten_1982_highres:01, fjordholm_mishra_tadmor_2012_tecno:02 (its entropy clause only), :03, jiang_shu_1995_weno:01, :05 (with hypotheses) |
| stability | 3 / 11 | mfa_oslo_notes:03, :04, :05 |
| entropy | 1 / 11 | fjordholm_mishra_tadmor_2012_tecno:04 |
| convergence | 1 / 8 | harten_1982_highres:11 (its order clause only) |
| other | 3 / 8 | fjordholm_mishra_tadmor_2012_tecno:06, :07, :08 (*tuned*) |
| tvd | 1 / 8 | harten_1982_highres:05 |
| monotone | 0 / 2 | |
| conservation | 0 / 1 | |

Every one of the 24 readings narrows its sentence: linear advection (a = 1) for a general flux or sign of a, one
viscosity Q, a scalar instance of a system (Burgers with u^2/2 for the two TeCNO identities), a two-stage SSP method for "SSP high order time discretizations",
a Courant range [0, 2] standing for "no CFL restriction", or (WENO, jiang_shu_1995_weno:05) one split flux
component, the order as the truncation error at one point, and eps = 0 for "eps negligible", or (reconstruction
v3) f(u) = u with the Lax–Friedrichs flux and degrees k <= 3 for the Gauss–Lobatto items, k = 2, 3 for the ENO
items, read in the weak form of the sign property (the strict form fails on linear data for every k >= 2; see
`benchmark/reconstruction/eno/README.md`). Each narrowing is recorded in the reading. A narrowed
VERIFIED verifies the instance only.

## 2. Decided fraction

**23 of 24 readings are decided** (15 VERIFIED, 8 REFUTED, all exact; before reconstruction v3 16 of 17; first
round 12 of 14). All 7 new readings are VERIFIED. The one undecided
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
| alone | 13 | 0 | 55 | 31 |
| with hypotheses | 14 | 0 | 53 | 32 |

All 27 matches rest on narrowed readings, and 8 of them (zhang_shu_2010_maxprinciple:05, zhang_shu_2011_survey:04,
:13 and fjordholm_mishra_tadmor_2012_tecno:08, both fields each) rest only on readings made with the checker tuned
on these items. Of the 68 alone and 67 with-hypotheses fields that have a TRUE/FALSE expectation, the checker
decides 13 and 14, about 20% (before reconstruction v3 9 and 9; without the tuned readings 9 and 10; first round
7 and 6).

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
  says it "can only give 4th order accuracy". The eps -> 0 reading of p. 7 is REFUTED by `reconstruction_order_p`:
  with eps -> 0 and f' != 0 the original measurement is fifth order too, for one reconstruction (the face value at
  x_{i+1/2}) and for the flux difference (at x_i), VERIFIED for p = 5 with leading order 5 in both forms, as
  identities in the Taylor jet at a grid point. Direct exact evaluation of the formulas confirms it (error/dx^4 -> 0
  at rational dx = 2^-6 .. 2^-12; `tests/test_reconstruction.py`). The mechanism, checked exactly in
  `tests/test_reconstruction_zm.py`: (2.20) gives IS_k = (f'h)^2 + 2(k-1) f'f'' h^3 + O(h^4), so the weights are
  omega_k = d_k + d_k (4/5 - 4(k-1)) (f''/f') h + O(h^2) = d_k + (12/25, 12/25, -24/25) (f''/f') h + O(h^2): only
  O(h), not the O(h^2) of the sufficient condition (2.14). The candidate errors are q_k - h_{i+1/2} =
  (-1/4, 1/12, -1/12) f''' h^3 + O(h^4), and the O(h^4) term of the face error,
  sum_k (omega_k - d_k)(q_k - h), has coefficient (12/25)(-1/4) + (12/25)(1/12) + (-24/25)(-1/12) = 0 (because
  sum_k d_k A_k = 0 and sum_k k d_k A_k = 0). The face error is then C(x_i) h^5 with C smooth where f' != 0, so the
  difference is O(h^5) too. The report's numerical Tables 3-4 (the tables p. 7 cites) are consistent with this:
  our replica of their run reproduces the printed WENO-RF-4 errors to 2-3 digits, and the reconstruction alone
  (mpmath, N up to 5120) shows that their sub-fifth orders come from the critical points of sin and sin^4 (L_inf 3
  and L1 4 for the difference within O(dx) of f' = 0), on grids where eps = 10^-6 does not yet dominate IS_k near
  those points; away from them the order is 5, and with eps = 10^-6 every order rises to 5 and above from N = 320
  (`notes/jiang-shu-tables.md`). Read as "4th and not 5th" the sentence is false; read as "at least 4th" it is
  true. The text does not decide, so the field is unformalised (`not-checkable`: the reading of a clause, not the
  eps family) and `ERRATA_PROPOSED.md` lists it for the team.

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
| jiang_shu_1995_weno:01 | with hyp. | VERIFIED | Liu, Osher and Chan's weights (2.18), flux difference, eps = 0 where f' != 0: r = 2 order 3 (p = 3) and r = 3 order 5 (p = 4 asked), as identities in the Taylor jet; no checker change (found by the v3 survey) |
| zhang_shu_2010_maxprinciple:05 | both | VERIFIED (*tuned*) | f(u) = u, Lax–Friedrichs, k = 1, 2, 3: the new average is u0l/2 + (1/2 - lam) u0r + lam um1r (k = 1) or u0l/6 + 2 u0c/3 + (1/6 - lam) u0r + lam um1r (k = 2, 3), an identity in the polynomial coefficients, weights >= 0 on [0, min w_alpha] (Sturm); the average hypothesis is implied (Simpson, exact for k <= 3) |
| zhang_shu_2011_survey:04 | both | VERIFIED (*tuned*) | the same three, plus Lax–Friedrichs with alpha = 2 for k = 2 on [0, 1/12]: weights 1/6 - lam/2, 2/3, 1/6 - 3 lam/2, lam/2, 3 lam/2 |
| zhang_shu_2011_survey:13 | both | VERIFIED (*tuned*) | k = 2, 3, with p(x*) = (ubar - u0l/6 - u0r/6)/(2/3): the new average is (2/3) p(x*) + u0l/6 + (1/6 - lam) u0r + lam um1r |
| fjordholm_mishra_tadmor_2012_tecno:06 | both (UNSURE) | VERIFIED (*tuned*) | ENO of point values, k = 2, 3, both tie rules: every failing system (D > 0 and J < 0, D = 0 and J != 0, ...) on each of the 14 (k = 2) or 88 (k = 3) non-empty selection branches is infeasible (Fourier–Motzkin, exact) |
| fjordholm_mishra_tadmor_2012_tecno:07 | both (UNSURE) | VERIFIED (*tuned*) | J / D <= 2 (k = 2) and <= 7/2 (k = 3), both tie rules, the same way; the constants are the exact suprema (C_3 = 7/2 is our computation, not a published value we checked) |
| fjordholm_mishra_tadmor_2012_tecno:08 | both | VERIFIED (*tuned*) | as tecno:06, through the bridge (3.20): in the scalar case the scaled reconstruction is plain ENO on the data mu^{i+1}, onto all data |
| fjordholm_mishra_tadmor_2012_tecno:04 | both | REFUTED | identity (3.3) as transcribed, Burgers, D = 1: LHS - RHS = (u_{i+1}^2 - 2 u_i^2 + u_{i-1}^2)/2, which is 1/2 at (u_{i-1}, u_i, u_{i+1}) = (0, 0, 1); with the minus sign of Lemma 3.2 it normalises to 0 |

## 4. Gap taxonomy

Primary reason per unformalised field (the first in the README's order that blocks a reading; 87 items have no
reading at all, and 4 lack one for a single field):

| reason | primary (fields entries) | items, any mention | what it would take |
|---|---|---|---|
| `scheme-class` | 27 | 27 | theorems about every scheme with a property (monotone ⇒ TVD, conservative ⇔ flux form, Lax–Wendroff, Crandall–Majda, Harten's lemma). A spec is one scheme. This needs statements over parametrised schemes, i.e. Lean proofs with the flux as a variable, not more checks |
| `reconstruction` | 14 | 41 | what is left after reconstruction v3 (`notes/reconstruction-survey.md`): the scaling limiter and its accuracy (3 primary items), WENO at discontinuities (1), ENO accuracy and the no-Gibbs clause (1), FV/DG schemes as a whole with time stepping (5), an l1 identity, nonlinearity, a semi-discrete invariant region (3, not reconstruction claims). Before v3: 21 primary, 48 any |
| `multi-d` | 15 | 16 | 2D rectangles and triangles (the two maximum-principle sources and TeCNO), plus one d-dimensional WENO theorem |
| `system` | 9 | 18 | Euler, general systems with entropy variables, constant-coefficient systems with several fields. Counted only where a scalar narrowing would change the truth or lose the point |
| `claim-kind-missing` | 6 | 22 | listed below |
| `not-checkable` | 8 | 8 | numerical observations (3), a comparison with the literature (1), vague or existential wording (3), a clause whose reading is a judgment call (1: jiang_shu_1995_weno:02 with hypotheses, "4th order", §3) |
| *gap in the source* | | | |
| `family_unspecified` | 3 | 3 | the source fixes eps = 10^-6 but leaves its scaling with dx open, and the truth depends on it (jiang_shu_1995_weno:01, :02 and :05, alone, §3; :01 moved here from `reconstruction` in v3). Fixed by choosing the family where the expected value is owned, not by the checker. Split out of `not-checkable` in reconstruction v2; no score changed |
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

Nine of the 30 are stated, and the checker gets every scored field right:

| item | alone | with hypotheses | dropped hypothesis |
|---|---|---|---|
| zhang_shu_2010_maxprinciple:02 | FALSE: MATCH | TRUE: MATCH | the time step bound dt <= c dt_0 |
| zhang_shu_2010_maxprinciple:04 | FALSE: MATCH | TRUE: MATCH | the CFL bound lambda a <= 1 |
| mfa_oslo_notes:03 | FALSE: MATCH | TRUE: MATCH | the CFL bound |
| mfa_oslo_notes:05 | FALSE: MATCH | TRUE: MATCH | the CFL bound |
| harten_1982_highres:01 | FALSE: MATCH | TRUE: GAP | "away from u_x = 0" (no named claim for order away from extrema) |
| harten_1982_highres:11 | FALSE: MATCH | UNSURE: unscored | the same |
| fjordholm_mishra_tadmor_2012_tecno:03 | UNSURE: unscored | FALSE: MATCH | here the printed hypothesis (the normalization of alpha) is what makes it false |
| jiang_shu_1995_weno:01 | FALSE: GAP (unformalised, §3) | TRUE: MATCH | the same (Liu, Osher and Chan's weights, r = 2, 3: order r + 1 where f' != 0) |
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
(41 mentions after reconstruction v3, the scaling limiter first), semi-discrete order and order away from
extrema (about 6).

Expected-value corrections: one proposed (jiang_shu_1995_weno:02, with hypotheses, §3); see `ERRATA_PROPOSED.md`.
