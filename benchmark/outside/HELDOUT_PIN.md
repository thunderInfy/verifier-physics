# Heldout run: pin

Fixed on 2026-11-28, at the start of phase A0, before any reading of the heldout split.

- Checker commit (main HEAD at A0 start): `b2cafbebed25a0aab659616eaafcd8db90c49426`
- Lean toolchain (`lean/lean-toolchain`): `leanprover/lean4:v4.30.0-rc1`
- Mathlib rev (`lean/lake-manifest.json`): `f369f66ea08e49c46a2fffaceb6699e6bef11555`
- The measured Lean run (`papers/scheme-claims/lean_measured.json`) is at this pin.

The checker is frozen at this commit: no new claim kinds, checks or Lean modules for the heldout run.

## Reader view

`strip_heldout.py` writes `heldout_stripped.jsonl` (77 heldout items; fields item_id, sentence, scheme,
hypotheses, location only) and `heldout_subset_a2.txt` (24 items, `int(sha256(item_id).hexdigest(), 16) % 4 == 0`)
for the reader-agreement pass. Readers see only `heldout_stripped.jsonl`.

## Readings commit

(recorded by phase B)
