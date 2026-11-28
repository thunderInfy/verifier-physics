# Outside benchmark v2: spec translation (phase B, rule 3b)

The readers drafted specs but did not write them. Before any checker run, the scorer wrote them under `specs/`:
A1's 11 drafts (the `specs` map of `readings.json`) and A2's two `spec_needed` descriptions (`readings_a2.json`,
items `barsukow_uzh_notes:06` and `:07`) under `specs/a2/`. The translation is committed on its own, before the first
checker run, and `tests/test_outside_v2_scores.py` asserts that the specs at HEAD equal that commit byte for byte.

## Who translated, and what they had seen

The translator is the phase-B scorer. It was not one of the blind readers. At translation time it had seen no
checker verdict on any v2 spec or reading, and it was blind to the per-item frozen expected values and
justifications in `items.jsonl`. It had seen these things, which we state as a confound:

- the readings themselves (`readings.json`, `readings_a2.json`) and the reader view (`stripped.jsonl`, the WENO-Z
  items 01 and 04);
- `ERRATA.md` in full, including the 20 post-freeze re-derivations of `expected_alone` (per item), and the first
  lines of `standing_conditions.jsonl`. The team's ordering amendment (translate before opening these files) arrived
  after these reads. Of the translated specs, only `gp-p1-1d-advection.json` belongs to an item with an ERRATA row
  (`guermond_popov_2016_invariant_domains:04`, TRUE -> TRUE);
- an aggregate tally of the frozen (expected_alone, expected_with_hypotheses) pairs over all 95 items (no ids) and
  the item count per source;
- the first 1500 characters of `items.jsonl`: the first item's id, location, sentence and part of its scheme, with
  no expected value or justification.

Ten of A1's drafts are copied verbatim, so these reads could only bear on the three specs where the translator made
choices (WENO-Z and the two A2 specs). Those choices are listed below.

## Validation

`validate_specs.py` is parse-only. It loads each spec, runs every expression through `physverify.expr.parse`, checks
the variables against the stencil names the scheme layer reads (`uLL, uL, uR, uRR, lam` in a numerical flux,
`um2 ... up2, lam` in an update, plus the spec's `params`), checks that each named claim exists, and runs the
WENO-Z spec through `reconstruction.parse_reconstruction` and A1's params through `parse_claim`. It runs no check
and no judge. All 13 specs parse.

## Draft -> file

| draft (reader) | file | mapping |
|---|---|---|
| A1 `gp-p1-1d-advection.json` | `specs/gp-p1-1d-advection.json` | verbatim (the draft's JSON, indent 1) |
| A1 `kt-semidiscrete-minmod-theta1-advection.json` | `specs/kt-semidiscrete-minmod-theta1-advection.json` | verbatim |
| A1 `kt-semidiscrete-minmod-theta2-advection.json` | `specs/kt-semidiscrete-minmod-theta2-advection.json` | verbatim |
| A1 `chen-shu-godunov-burgers.json` | `specs/chen-shu-godunov-burgers.json` | verbatim |
| A1 `chen-shu-hll-rusanov-burgers.json` | `specs/chen-shu-hll-rusanov-burgers.json` | verbatim |
| A1 `barsukow-upwind-advection.json` | `specs/barsukow-upwind-advection.json` | verbatim |
| A1 `barsukow-modified-lf-burgers.json` | `specs/barsukow-modified-lf-burgers.json` | verbatim |
| A1 `barsukow-lax-wendroff-advection.json` | `specs/barsukow-lax-wendroff-advection.json` | verbatim |
| A1 `barsukow-beam-warming-advection.json` | `specs/barsukow-beam-warming-advection.json` | verbatim |
| A1 `barsukow-slope-fromm-advection.json` | `specs/barsukow-slope-fromm-advection.json` | verbatim |
| A1 `borges-wenoz-fd.json` | `specs/borges-wenoz-fd.json` | written from the description, choices W1-W5 |
| A2 `barsukow_uzh_notes:06` `spec_needed` | `specs/a2/barsukow-modified-lf-burgers-update.json` | choices A1-A2 below |
| A2 `barsukow_uzh_notes:07` `spec_needed` | `specs/a2/barsukow-modified-lf-burgers-flux.json` | choice A3 below |

The verbatim drafts already use the spec language's syntax (`min`, `max`, `abs`, `minmod` are parser functions), so no
notation had to be mapped. Their `name` strings are kept as the readers wrote them.

## Choices

WENO-Z (A1's draft is a description: "a reconstruction-layer spec, to be written as the dev WENO specs are"):

- W1. Structure, candidates, data, target and point are copied from `benchmark/outside/specs/jiang-shu-weno5-js-fd.json`,
  as the draft says. The reader view does not print the candidate coefficients c_kj (it cites (4)-(5)), so they are
  the dev spec's standard fifth-order ones.
- W2. Weights: `kind: z`, `tau: [0, 2]` (tau_5 = |beta_0 - beta_2|), `q: 1` (the draft's "p = 1"). The checker's z
  kind is alpha_k = d_k (1 + (tau/(eps + beta_k))^q). The view prints alpha^Z_k = d_k / beta^Z_k with
  beta^Z_k = (beta_k + eps)/(beta_k + tau_5) and tau_5 = max(|beta_0 - beta_2|, eps). That is
  d_k (beta_k + tau_5)/(beta_k + eps). At eps = 0, the only eps any reading uses (A1's component has eps = "0"),
  it equals d_k (1 + tau/beta_k), the checker's form. At eps > 0 the two differ (the printed max(., eps) and the
  form of beta^Z_k). No reading is affected.
- W3. Ideal weights and indicators are paired as in the dev spec: d = (1/10, 6/10, 3/10) with the left, middle and
  right stencils. The view prints d_0 = 3/10, d_1 = 3/5, d_2 = 1/10 with fhat_k = sum_j c_kj f_{i-k+j}, and prints
  beta_0 on f_{i-2}..f_i. Taken literally, those indices put d_0 with a different stencil from beta_0. We read the
  index convention of the extraction as mixed and used the standard pairing (the one the draft points to). tau is
  symmetric in beta_0 and beta_2, so it is unaffected. We expect that a literal pairing would not give fifth order
  even at smooth points, but we did not check it.
- W4. The indicators beta_k are the Jiang-Shu ones (8)-(10), printed in the view and identical to the dev spec's.
- W5. The spec has no `claims` list. The claim's parameters (p = 5, flux_difference, critical, n_cp = 1, eps = 0)
  come from A1's component `params`, as for every reconstruction reading.

A2 (each `spec_needed` written word for word):

- A1. `barsukow_uzh_notes:06`: A2 names the update form first and the flux form (9.10) as an equivalent. We wrote
  the update form, `scheme.update = (um1 + 2*u0 + up1)/4 - lam*(up1^2/2 - um1^2/2)/2`, with `pde.flux = u^2/2` and
  `named_claims = [conservative]`. This file is not the same as A1's `barsukow-modified-lf-burgers.json` byte for
  byte, but it has the same pde, update and named claim.
- A2. Both of A2's readings of item 06 (alone, with hypotheses) map to this one spec. The second says "as for the
  with-hypotheses reading".
- A3. `barsukow_uzh_notes:07`: `scheme.numerical_flux = (uL^2/2 + uR^2/2)/2 - (uR - uL)/(4*lam)`,
  `claims.monotone_cfl = "1/2"` (a string, as A2 wrote it; the checker reads it with `Fraction`),
  `named_claims = [monotone_under_cfl]`. Both of A2's readings of item 07 map to it.

None of these choices changes a flux, CFL range, stencil, eps or limiter parameter that the draft fixes. No spec is
UNTRANSLATABLE.

## Repairs after the first checker run

Only pure key-name typos may be repaired, each listed here as a diff. See V2_RESULTS.md, section "SPEC_ERROR and
syntax fixes".
