# Outside benchmark v3: freeze

**All of v3 is held-out for the next checker version.** There is no development half.

Collected 2026-11-28 by sampling (rule in `README.md`) from the sources in `SOURCES.md`, without opening the checker's
code, tests, earlier benchmark items, results or notes. No checker has been run on these items.

## Sources and item counts

| source_id | type | items |
|---|---|---|
| `jiang_shu_1993_dg_cell_entropy` | paper | 3 |
| `shu_osher_1988_eno2` | paper | 2 |
| `ranocha_etal_2020_rrk_entropy` | paper | 15 (cap reached) |
| `osher_chakravarthy_1983_entropy` | paper | 13 |
| `yee_1989_tvd_tm` | notes | 10 |
| `perthame_shu_1993_positivity` | paper | 7 |
| `shu_am257_notes` | notes | 11 |
| `yang_xiong_qiu_xu_2014_mpp_fv` | paper | 8 |
| **total** | | **69** |

`skipped.jsonl`: 32 entries. `known_false.jsonl`: 0 items.

## Expected values

| | TRUE | FALSE | UNSURE |
|---|---|---|---|
| `expected_alone` | 33 | 7 | 29 |
| `expected_with_hypotheses` | 46 | 5 | 18 |

Pairs (alone, with hypotheses): (TRUE, TRUE) 33; (UNSURE, UNSURE) 17; (UNSURE, TRUE) 12; (FALSE, FALSE) 5;
(FALSE, UNSURE) 1; (FALSE, TRUE) 1.

## quantifier_kind

universal 42, existential 13, none 14.

## property

order 21, entropy 17, positivity 9, other 7, convergence 5, monotone 3, stability 2, shock_speed 2, tvd 2,
conservation 1.

Expected values are frozen as of this commit; any correction goes to ERRATA.md with before/after.
