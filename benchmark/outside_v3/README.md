# Outside benchmark v3

Sentences about numerical schemes for conservation laws, copied from published sources (`SOURCES.md`), with expected
truth values fixed before any checker was run on them. All of v3 is held-out (`FROZEN.md`). It was collected without
looking at the checker's code, tests, earlier results or notes.

## Files

- `SOURCES.md`: the sources, the access check, and the dropped candidates.
- `items.jsonl`: one claim per line (fields below).
- `skipped.jsonl`: every sentence in the sampling region that was not taken, with the reason (`source_id`, `location`,
  `sentence` (null when a whole region is described), `reason`).
- `known_false.jsonl`: claims the literature itself refutes. Empty in v3 (the optional step was not done).
- `FROZEN.md`: counts and the freeze statement. `ERRATA.md`: corrections after the freeze, with before/after.

## Sampling rule

From each source we took every sentence that asserts a property of a named or explicitly defined numerical scheme,
from the abstract, the statements of theorems, propositions, lemmas and corollaries, and the conclusions, in document
order, at most 15 per source. Remarks, appendices and the running text were not sampled. A theorem statement that runs
over several sentences is one item. Sentences too vague to be claims, or that describe the paper rather than a scheme,
are in `skipped.jsonl`. Statements whose text could not be read in a scanned source are skipped, not reconstructed.

## Item fields

- `id` (`<source_id>:<nn>`), `source_id`, `location` (page, section, theorem or equation number).
- `sentence`: the sentence as printed. Prose is verbatim (including typos and hyphenation from the text layer).
  Mathematics is transcribed into plain notation (`sum_{i,j}`, `≤`, subscripts with `_`), because the PDF text layers
  scramble it; where a symbol was not legible the item says so in `scheme`.
- `scheme`: the scheme as the source defines it, with the location of each definition and the formulas the claim
  depends on. For scanned reports many displays are illegible; the field then says which parts could not be read.
- `hypotheses`: every hypothesis the source states for the claim, anywhere: `text`, `location` (null if we believe it
  is assumed but could not find it printed), `standing` (true for an assumption stated once for a section or paper).
- `quantifier`, `quantifier_kind` (`universal` / `existential` / `none`, for the main parameter), `quantified_over`.
- `expected_alone`: TRUE / FALSE / UNSURE for the sentence read by itself, the default reading of a careful reader.
  **This reading excludes hypotheses printed elsewhere, including standing ones.** Hypotheses written inside the
  sentence (e.g. a theorem's own "if ..." clause) are part of it.
- `expected_with_hypotheses`: TRUE / FALSE / UNSURE for the sentence plus all its listed hypotheses.
- `justification`: why, citing the source's proof, another theorem, or an explicit counterexample. A FALSE always comes
  with a counterexample written out. UNSURE means what we read does not settle it (for instance, an empirical claim
  supported only by the paper's own experiments, or a proof we could not check).
- `property`: conservation, order, monotone, tvd, positivity (also used for maximum principles), entropy, convergence,
  stability, shock_speed (also used for shock and contact resolution), other.

## Judgement notes

- Several "at most first order" statements in `shu_am257_notes` (Godunov-type and TVD accuracy barriers) are marked
  FALSE as written: the exact translation u_j^{n+1} = u_{j-1}^n for u_t + u_x = 0 at CFL number 1 is linear, monotone,
  TVD and exact. The underlying theorems hold once such trivial schemes are excluded, but the sentences do not
  exclude them. If the team prefers the reading that excludes them, the change goes to `ERRATA.md`.
- Empirical comparisons (most of `yee_1989_tvd_tm`, parts of `shu_osher_1988_eno2`) are UNSURE in both readings.
