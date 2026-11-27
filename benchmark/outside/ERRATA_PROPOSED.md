# Proposed corrections to expected values (dev half)

Proposals only. The team decides; `items.jsonl` and `ERRATA.md` are unchanged.

| id | field | current | proposed | reason |
|---|---|---|---|---|

None proposed from the dev formalisation. No reading gave a verdict against an expected value, and reading the
justifications turned up no value we think is wrong. Two we looked at closely and left alone:

- `mfa_oslo_notes:02` (FALSE both): "the energy grows at every time step for any choice of ∆x, ∆t". FALSE rests
  on reading "grows" strictly: data with U^{n+1} = U^n (constants, or (−1)^j on an even periodic grid) keep the
  energy unchanged. The notes clearly mean "never decreases, and grows for generic data", which is TRUE. The
  README's rule is to judge sentences as printed, so FALSE stands, but the item measures a literal reading.
- `mfa_oslo_notes:15` (FALSE both): the time-continuity bound holds if C_F is the Lipschitz constant for the max
  norm on (a, b) and fails for the l1 and Euclidean conventions. The justification already says so and points out
  that the notes use the l1 convention for Q on p. 57, so FALSE stands.
