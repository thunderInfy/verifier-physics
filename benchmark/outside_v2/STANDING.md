# Standing-condition audit (phase A0)

**Readers (phases A1, A2): do not open this file, `standing_conditions.jsonl` or `ERRATA.md`.** They are built
from the expected values and justifications. Readers see only `stripped.jsonl`.

## Rule

Fixed by the team before any reading of v2 (2026-11-28): `expected_alone` may assume a condition the sentence does
not state only if the source prints it

- at the start of the paper (abstract, introduction, or the opening of the first technical section before its
  first subsection),
- at the start of the section the item is in, or
- in the theorem block (its statement and the sentence introducing it).

We also counted the definition of a method the sentence names (one case, `barsukow_uzh_notes:07`).

## What was audited

Every item whose `justification` (or the README's "Conventions": CFL for explicit schemes, smooth solutions for
order of accuracy, the semi-discrete setting for entropy stability) shows that its `expected_alone` uses a
condition the sentence does not state. Each source was reopened from the URL in `SOURCES.md` (full-text
extraction; the downloads are in an untracked scratch directory, not in the repo). The scheme's own definition
(e.g. the numerical flux the sentence names) is not a standing condition and is not listed. `borges_costa_don_2006_wenoz`
has no such item, since all four are UNSURE for reasons unrelated to any condition.

## `standing_conditions.jsonl`

One line per (item, condition) pair, so an item with two conditions has two lines. Fields:

- `id`: item id in `items.jsonl`.
- `condition`: the condition `expected_alone` relied on.
- `location`: where the source prints it, if that place is allowed by the rule; otherwise `null`.
- `quote`: the source's words where it prints the condition (from the text extraction, math flattened to plain
  text), or `null` if it does not print it anywhere.
- `printed_at`: where the source prints the condition anywhere (page, equation or section), even if the rule does
  not allow that place; `null` if nowhere.
- `derived`: `true` if the source prints the condition nowhere and we inferred it ourselves, `false` if it is printed.
- `note`: why the location does or does not count.

So `printed` = rows with `derived: false`, and `printed+derived` = all rows.

## Counts

- 44 rows over 38 items.
- 21 rows have a `location` (allowed place). 23 have `location: null`: 18 printed somewhere else in the source,
  5 printed nowhere (`derived: true`).
- 20 items have at least one null-location row. Each is re-derived without that condition in `ERRATA.md`, section
  "Post-freeze: standing-condition rule (2026-11-28)": 13 change (5 to FALSE, 8 to UNSURE), 7 stay TRUE. The 7 that
  stay TRUE all rely only on smoothness for an order-of-accuracy or viscosity-size claim (read as part of what
  the claim means) or, in one case, on a condition we show is not needed.

## Doubts

- The "start of the paper" boundary is our reading of the rule. Under a looser reading (any paragraph before the
  first theorem of the section), `hu_adams_shu_2013_pp_flux_limiter:01/05` would still fail, because CFL <= 1/2 sits
  in the middle of Sec. 2.2.
- `chen_shu_2017_esdg:03` (semi-discrete, printed in the abstract about the DG methods the paper extends) and
  `chen_shu_2017_esdg:05` (printed at the start of Sec. 3.3 only by reference to (3.23)) were counted as printed.
  Under a strict reading both would go to null, and both would need re-deriving.
- Treating smoothness as part of the meaning of "order of accuracy" keeps 6 items TRUE. A stricter reading
  would make them UNSURE.
