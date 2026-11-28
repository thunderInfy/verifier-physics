# Outside benchmark v2

Sentences about finite-difference, finite-volume, DG and continuous-FE schemes for conservation laws, copied from
published, openly readable sources, each with expected truth values fixed before any checker was run on them. All of
v2 is held out for the next checker version; there is no dev half. See `FROZEN.md`.

It was collected blind: the collector did not open the checker code, the tests, v1's items or results, or any
notes, and read `benchmark/outside/SOURCES.md` only to exclude its sources.

## Files

- `SOURCES.md`: the sources, the URL each was read from, and the ones dropped (with the reason).
- `items.jsonl`: one claim per line. Fields: `id`, `source_id`, `location`, `sentence`, `scheme`, `hypotheses`
  (list of `{hypothesis, location}`), `expected_alone`, `expected_with_hypotheses` (TRUE / FALSE / UNSURE),
  `justification`, `property`.
- `skipped.jsonl`: every sentence or statement in the sampled regions that was not made an item, with the reason
  (too vague, not about a scheme, over the per-source cap, ...).
- `known_false.jsonl`: claims refuted in the published literature. Empty in this version (step 4 was not done).
- `FROZEN.md`, `ERRATA.md`: the freeze statement and the place for later corrections.

## Sampling rule

From each source: every sentence of the abstract, of each theorem/proposition/lemma/corollary statement and of the
conclusions that asserts a property of a named or explicitly defined numerical scheme, in document order, at most 15
per source. A multi-sentence theorem statement is one item. Sources without a conclusions section, or without
theorems, are noted in `skipped.jsonl`. For the RKDG review the two "Concluding Remarks" subsections were taken as
the conclusions.

## Conventions

- `sentence` is verbatim up to: line-break hyphens rejoined, words split by the PDF text layer rejoined, and
  displayed or inline mathematics transcribed into plain text or Unicode from the extracted text. Where the text
  layer lost a sign, bar or digit, the item says so in `scheme` or `justification` instead of silently fixing it.
- `scheme` gives the formulas the claim depends on, with equation numbers, as read in the source; when the source
  does not define something (e.g. a cited scheme), it says where it is defined.
- `expected_alone` is the default reading a careful reader gives the sentence by itself, including the standing
  implicit conditions of the field (a suitable CFL condition for explicit schemes, smooth solutions for order of
  accuracy, the semi-discrete setting for "entropy stable" semi-discretizations). It is FALSE or UNSURE when the
  sentence claims more than that reading supports.
- `expected_with_hypotheses` adds every hypothesis the source states for the claim anywhere.
- Unhedged performance claims with no defined property ("less dissipative", "carbuncle free") are UNSURE; hedged
  reports of the source's own experiments ("numerical examples suggest ...") are judged as reports.
- Narrowing polarity (added after the first score; opt-in for future runs, `physverify/schemes/narrowing.py`,
  POSTHOC_NARROWING.md): a reading narrowed to an instance bears on the sentence through the sentence's quantifier
  over the narrowed parameter. For a universal sentence the instance is NECESSARY (it can only refute); for an
  existential sentence it is SUFFICIENT (it can only verify); if the quantifier is not recorded, the result is
  UNKNOWN. V2_RESULTS.md, the frozen first score, does not use it.
- Justifications rest on the source's proof, on our own check of it, or on a counterexample we worked out and
  wrote down. Results we know but did not read in this collection are named as such, and do not by themselves turn
  an item TRUE or FALSE.
