# Outside benchmark: claims about numerical schemes from published sources

Sentences copied from published papers, technical reports and lecture notes on schemes for conservation laws. Each
sentence's expected truth value was fixed by reading the literature, before any checker was run on it. It
complements our own benchmark, which we wrote ourselves and which therefore can't show how a checker does on claims
as real papers phrase them.

The items were collected blind: the collectors did not look at our checker, its benchmark, tests, Lean code or
papers.

## Files

- `SOURCES.md`: the sources, with an access check (committed before any item was collected), plus the sources we
  dropped and why.
- `SAMPLING.md`: the sampling rule (committed with `SOURCES.md`): every property-asserting sentence about a scheme
  from the abstract, theorem-type statements and conclusions.
- `items.jsonl`: the benchmark, one JSON object per line. Fields: `id`, `source_id`, `location`, `sentence`
  (verbatim), `scheme` (`definition`, `location`), `hypotheses` (list of `hypothesis`, `location`),
  `expected_alone`, `expected_with_hypotheses` (TRUE / FALSE / UNSURE), `justification`, `property`, and optionally
  `text_note: "ocr_normalized"` when split words or OCR characters were fixed.
- `skipped.jsonl`: sentences in the sampled parts that were too vague to be claims, or illegible in a scan.
- `COVERAGE.md`: per source, every sampled part and what became of it.
- `known_false.jsonl`: a separate set of published claims that the literature itself later refuted. Same fields,
  plus `refutation` (source, URL, location, verbatim quote) and `original_source`. Never mixed into `items.jsonl`.
- `FROZEN.md`: the dev/heldout split (by source hash) and the tallies at freeze time.
- `ERRATA.md`: corrections after the freeze, with before/after values. Empty at freeze.

## Reading the expected values

- `expected_alone`: the sentence by itself, read the way a careful reader would (no CFL bound, smoothness or
  convexity unless the sentence states it).
- `expected_with_hypotheses`: the sentence plus every hypothesis the source states for it.
- Sentences are judged **as printed**. Where a misprint makes the printed statement false (e.g. a wrong factor or
  sign in an entropy flux), the value is FALSE and the justification says what the intended statement was.
- UNSURE means the literature we read does not settle it (no proof given, proof deferred to a paper we did not read,
  or only numerical evidence).
- A few FALSE values rest on a short counterexample that we worked out ourselves, not on a published one. Their
  justifications say so and give the computation.

## Known limits

- Five sources are scans with OCR. Their displayed formulas are often illegible: those `scheme` fields say so, and
  sentences with an illegible part were moved to `skipped.jsonl`. This leaves few items from
  `osher_tadmor_1985_convergence` (4) and `heoc_1986_eno3` (3).
- Expected values are our reading of the sources and are open to correction through `ERRATA.md`.
- Only 4 known-false entries, and 3 of them depend on how the original sentence is read (their
  `expected_with_hypotheses` is UNSURE).

`tests/test_outside_bench_schema.py` checks the schema, the enum values and that the split in `FROZEN.md` matches the
hash rule.

## Formalising the dev half

Only the dev half (9 sources, 99 items) is formalised and run; the heldout half is run once, later, with the
checker commit pinned. `dev_readings.json` holds, for every dev item and each expected field (`alone`,
`with_hypotheses`), either one or more formal readings or the reason there is none. The readings' specs are in
`specs/`. `DEV_RESULTS.md` has the scores; `run_dev.py` recomputes them
(`uv run python benchmark/outside/run_dev.py [--write]`), and `tests/test_outside_dev.py` checks the stored ones.
`ERRATA_PROPOSED.md` collects expected values we think are wrong, for the team to decide (none so far).

### Readings

A reading is a spec (the scheme as the source defines it, as closely as the spec language allows) plus a
conjunction of named claims from `physverify/schemes/claims.py`, with the relations of
`physverify/schemes/bench.py` (`same`, `necessary`, `sufficient`) and a `bridge` where the named claim is not
literally the sentence's property. A component may also be `negated` (the reading asserts that the named claim
fails, e.g. "not unconditionally stable"). Each reading says which expected field it is scored against.

A reading may **narrow** the sentence: a specific flux f, viscosity Q or Courant range for the free data of a
named or constructed scheme, 1D for a system, a rational sub-range of an irrational CFL bound. Every narrowing is
recorded in the reading's `narrowing` field. A narrowing must keep the sentence's truth value: a TRUE sentence
narrowed to an instance must stay TRUE on it, and a FALSE one is narrowed only to an instance on which it fails
(where the instance comes from the item's justification, the reading says so). We never pick an instance whose
truth differs from the sentence's. A narrowed VERIFIED verifies the instance, not the sentence; the results
count narrowed matches separately.

Theorems about every scheme with some property ("a monotone scheme is TVNI", "conservative iff flux form", the
Lax–Wendroff theorem) are not narrowed to an instance: they are UNFORMALIZED as `scheme-class`, whatever their
expected value.

### Why an item has no reading (fixed before classifying)

One primary reason per unformalised field, the first that applies in this order, plus any further reasons:

| reason | meaning |
|---|---|
| `not-checkable` | no definite mathematical content we could check: numerical observations, comparisons with the literature, vague or existential wording ("can be used to construct") |
| `illegible` | the formula the sentence depends on is illegible in the scan |
| `scheme-class` | a theorem about every scheme with a property, not about one scheme |
| `multi-d` | two space dimensions or unstructured meshes |
| `system` | a system of conservation laws beyond the 2x2 shallow-water specs (Euler, general systems with entropy variables) |
| `reconstruction` | high-order reconstruction or polynomial data: WENO/ENO stencil selection and smoothness indicators, piecewise polynomials with point-value hypotheses, DG or finite-volume cell-average schemes and their limiters |
| `time-stepping` | multi-stage or multistep time discretisation that a five-point update cannot hold |
| `variable-coefficients` | a given velocity field or other coefficients that vary in space |
| `not-expressible` | a scalar 1D scheme on at most five points, but its formula needs an operation the spec language lacks (e.g. division by a state difference) |
| `claim-kind-missing` | the scheme can be written as a spec but no named claim expresses the property (energy identities, semi-discrete order, E-fluxes, numerical entropy flux identities, order away from extrema, ...) |
