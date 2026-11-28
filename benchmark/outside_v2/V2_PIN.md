# Outside benchmark v2: pins

Fixed on 2026-11-28, at the start of phase A0, before any reading of v2.

The same readings are scored at both pins.

| pin | commit | Lean toolchain (`lean/lean-toolchain`) | Mathlib rev (`lean/lake-manifest.json`) | measured Lean run |
|---|---|---|---|---|
| OLD (the v1 heldout pin, `benchmark/outside/HELDOUT_PIN.md`) | `b2cafbebed25a0aab659616eaafcd8db90c49426` | `leanprover/lean4:v4.30.0-rc1` | `f369f66ea08e49c46a2fffaceb6699e6bef11555` | `papers/scheme-claims/lean_measured_b2cafbe.json` |
| NEW (main at A0 start, with the SSP class theorem) | `3792caf54dbc66099d9855ec2d3d38b8d4242088` | `leanprover/lean4:v4.30.0-rc1` | `f369f66ea08e49c46a2fffaceb6699e6bef11555` | `papers/scheme-claims/lean_measured_d8fb00a.json` |

Toolchain and Mathlib are the same at both pins, so a difference between the two scores comes from the checker,
not from Lean or Mathlib.

## Items

`items.jsonl` (95 items, all held out) is the file frozen in commit `63337e1`, sha256
`df9b49aaff107752a728313039f165dfb1338c77da70e082b55d2314cd1b7f05`. It is not edited; corrections go to
`ERRATA.md`.

## Reader view

`strip_v2.py` writes `stripped.jsonl` (all 95 items; fields id, sentence, scheme, hypotheses, location only) and
`subset_a2.txt` (22 items, `int(sha256(id.encode("utf-8")).hexdigest(), 16) % 4 == 0`) for the reader-agreement
pass. Readers see only `stripped.jsonl`. They do not open `items.jsonl`, `ERRATA.md`, `STANDING.md` or
`standing_conditions.jsonl`.

## Contaminated items

The repo's `benchmark/reconstruction/weno5-z-fd.json` and `weno5-z2-fd.json` were built from the WENO-Z report
(source `borges_costa_don_2006_wenoz`), so its 4 items are contaminated:

- `borges_costa_don_2006_wenoz:01`
- `borges_costa_don_2006_wenoz:02`
- `borges_costa_don_2006_wenoz:03`
- `borges_costa_don_2006_wenoz:04`

Results report the 91 clean items as the headline and these 4 separately.

## Expected values

The standing-condition audit (`STANDING.md`, `standing_conditions.jsonl`) re-derived `expected_alone` for the
items whose value leaned on a condition the source does not print where the rule allows. The new values are in
`ERRATA.md`, section "Post-freeze: standing-condition rule (2026-11-28)"; `items.jsonl` keeps the frozen ones.

## Readings commit

(recorded by phase B)
