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
