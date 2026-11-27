# Sampling rule (fixed before collecting)

Written and committed together with `SOURCES.md`, before any item was collected.

## Population

From each sampled source in `SOURCES.md`, take **every** sentence that asserts a property of a named or explicitly
defined numerical scheme (or of a stated class of schemes, e.g. "monotone schemes", "TVD Runge–Kutta methods"),
from these parts of the text:

1. the abstract (for lecture notes without an abstract: the preface or "About these notes" section);
2. the statements of every numbered or named Theorem, Proposition, Lemma and Corollary (the statement only, not the
   proof or remarks);
3. the conclusions (a section titled Conclusion(s), Concluding remarks or Summary, if there is one).

Properties: conservation, consistency, order of accuracy, stability (von Neumann, L2, energy, linear), monotonicity,
TVD/TVB/TVNI, positivity / maximum principle, entropy stability / entropy condition / entropy conservation,
convergence (to weak or entropy solutions), shock speed, shock resolution, and other definite mathematical properties
of a scheme (e.g. efficiency claims are out; "is a monotone scheme" is in).

## Not in the population

- Sentences about the PDE or its exact solutions, or about ODE solvers in the abstract with no scheme property.
- Sentences that only describe what the paper does ("we construct", "we present") without asserting a property.
- Statements inside proofs, remarks, examples and numerical sections.

These are not logged.

## Logged as skipped

A sentence in the sampled parts that mentions a scheme and reads like a property claim but is too vague to have a
truth value ("performs well", "high resolution", "remarkable capability") goes to `skipped.jsonl` with the reason.

## Units

One item per sentence. A theorem statement whose hypotheses take several sentences ("Let ... . Assume ... . Then the
scheme is TVD.") gives one item for the sentence that asserts the property; the earlier sentences become
`hypotheses`. If a sentence asserts several properties, it is still one item; `property` is the first property it
names and the justification addresses every part (the sentence is TRUE only if every part is).

## Verbatim policy

`sentence` is copied from the text we read. For born-digital sources it is the text layer with line breaks and
hyphenation joined. For text layers that split words or drop ligatures (`jiang_shu_1995_weno`) and for OCR scans, we
rejoin split words and correct character-level OCR errors only (e.g. "ccaputaiton" → "computation"); such items carry
`"text_note": "ocr_normalized"`. Inline math is written in plain text or LaTeX. Nothing is reconstructed from memory:
if a part of a sentence is illegible the item is not collected and the sentence is logged in `skipped.jsonl` as
illegible.

## Expected values

Fixed by reading the sources (the source's proof, a later theorem in a source we read, or a published counterexample
we read). UNSURE when the literature we read does not settle it. No checker is run on any item.
