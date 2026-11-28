# Bench v2: post-hoc effect of the narrowing polarity rule on the P row

**POST-HOC, NOT A RESULT.** We wrote the rule (`physverify/schemes/narrowing.py`, benchmark/outside/README.md) and
the quantifier annotation below after seeing v2's items, expected values and frozen verdicts. It changes no frozen
file. The scores are recomputed in memory from `verdicts_new.json` with `run_v2.evaluate(narrowing_rule=True)`
(`posthoc.py`, asserted in `tests/test_narrowing.py`). V2_RESULTS.md keeps the old scoring.

## The rule

A narrowed reading's verdict is about an instance. Its bearing on the sentence comes from the sentence's quantifier
over each narrowed parameter, through the checker's relation table:

- universal (every flux, slope, method, every CFL number in a range): NECESSARY. An instance REFUTED gives REFUTED;
  an instance VERIFIED gives NOT_REFUTED (scored GAP), never VERIFIED or TRUE.
- existential (stable for some or every small enough CFL number, there is a limiter ...): SUFFICIENT. VERIFIED
  gives VERIFIED; REFUTED gives UNKNOWN.
- mixed, or not recorded and not fixed by the claim kind: UNKNOWN.

A1's v2 readings carry no `narrowed` field, so under the rule as written every narrowed reading gives UNKNOWN
("unrecorded" below). We also annotated the quantifiers by hand (`posthoc.NARROWED`, "annotated"). Every
parameter A1 narrowed in a decided reading is universal in its sentence: the advection speed c, the scalar flux,
the slope, the system and entropy, the admissible HLL speeds, the mesh and the dimension. No decided reading
narrows an existential CFL quantifier. In `barsukow_uzh_notes:12` and `:13` the existential ("conditionally
stable", "stable" read as stable for small CFL) is in the claim kind `stable_for_small_cfl` itself, and the CFL
number is not narrowed. So the existential rows of the rule never fire on v2, and both variants give the same
scores.

## Effect on the frozen (P) row, pin NEW, A1

| | MATCH | of which narrowed | WRONG | GAP | UNSCORED | decided fields |
|---|---|---|---|---|---|---|
| frozen scoring (V2_RESULTS.md) | 14 | 14 | 2 | 140 | 30 | 16 |
| rule, quantifiers unrecorded | 0 | 0 | 0 | 156 | 30 | 0 |
| rule, quantifiers annotated | 0 | 0 | 0 | 156 | 30 | 0 |

- `barsukow_uzh_notes:13` (FALSE, "for every slope"), narrowed to the central slope: instance VERIFIED, sentence
  NOT_REFUTED, **WRONG -> GAP** in both fields (2 fields).
- **14 MATCH -> GAP** ("not refuted"): every MATCH of the frozen P row rested on a narrowed VERIFIED of a TRUE
  sentence. The 7 items are `kurganov_tadmor_2000_central:07`, `guermond_popov_2016_invariant_domains:01`, `:02`,
  `:05` and `barsukow_uzh_notes:01`, `:06`, `:12`, each in both fields.
- Nothing else moves. `chen_shu_2017_esdg:08`, `:09` stay SPEC_ERROR, and `guermond:04` and `borges:04` stay
  UNKNOWN. The (E) row moves the same way: 14 MATCH -> GAP and 2 WRONG -> GAP.

So under the rule A1's v2 readings decide nothing. That is the price of scoring instance evidence honestly: a blind
reader who narrows a universal sentence can only refute it. A reading that should count as a verification has to
state the sentence without narrowing, or narrow only an existential parameter.

One argument the rule does not use: for linear advection the schemes depend on c only through nu = c dt/dx, so
the instance c = 1 is equivalent to every c > 0 (barsukow:01, :12, :13). The readers wrote "mirror image" for c < 0.
An instance that is EQUIVALENT by such a symmetry would keep its verdict, but the reading would have to record that
relation, and the checker would have to check it. Neither happens today, so we do not count it.
