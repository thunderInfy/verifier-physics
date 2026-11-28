# Heldout run: pin

Fixed on 2026-11-28, at the start of phase A0, before any reading of the heldout split.

- Checker commit (main HEAD at A0 start): `b2cafbebed25a0aab659616eaafcd8db90c49426`
- Lean toolchain (`lean/lean-toolchain`): `leanprover/lean4:v4.30.0-rc1`
- Mathlib rev (`lean/lake-manifest.json`): `f369f66ea08e49c46a2fffaceb6699e6bef11555`
- The measured Lean run at this pin is `papers/scheme-claims/lean_measured_b2cafbe.json`.

The checker is frozen at this commit for the heldout run: no new claim kinds, checks or Lean modules went into
it. The heldout result belongs to this commit, not to main: main may change the checker afterwards, and the
merge gate then checks the record below instead of re-scoring (`run_heldout.record_errors`).

## Reader view

`strip_heldout.py` writes `heldout_stripped.jsonl` (77 heldout items; fields item_id, sentence, scheme,
hypotheses, location only) and `heldout_subset_a2.txt` (24 items, `int(sha256(item_id).hexdigest(), 16) % 4 == 0`)
for the reader-agreement pass. Readers see only `heldout_stripped.jsonl`.

## Readings commit

Recorded by phase B (each is the last commit touching its file; `run_heldout.py` and
`tests/test_outside_heldout.py` assert the file at HEAD is byte-identical to it):

- `heldout_readings.json` (reader A1, 77 items): `2774e571164a245189a89a1fe7584340ddc3aac7`
- `heldout_readings_a2.json` (reader A2, 24-item subset): `0d16ffeda6c295d35c21f03c905998fd3086cd58`

## Verdicts

`heldout_verdicts.json` as `run_heldout.py --write` wrote it with the checker of the pin, in commit
`909197cc828aca04416ed510806670593d8e81c4` (the last commit touching it); recorded 2026-11-28:

- `heldout_verdicts.json` sha256: `cfc13cf04d3107529887a6a9f29a993880d362c44bf1889eceb55bf6a40afb86`
