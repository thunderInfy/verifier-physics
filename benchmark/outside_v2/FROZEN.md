# Outside benchmark v2: freeze

All of v2 is held-out for the next checker version.

Collected 2026-11-28, blind (see `README.md`), from the 9 sources in `SOURCES.md`. No checker has been run on any
item.

## Sources and item counts

| source_id | type | items |
|---|---|---|
| `hu_adams_shu_2013_pp_flux_limiter` | paper | 7 |
| `borges_costa_don_2006_wenoz` | paper | 4 |
| `ketcheson_2019_relaxation_rk` | paper | 15 |
| `kurganov_tadmor_2000_central` | paper | 10 |
| `chandrashekar_2013_kep_es` | paper | 15 |
| `guermond_popov_2016_invariant_domains` | paper | 7 |
| `chen_shu_2017_esdg` | paper | 15 |
| `cockburn_shu_2001_rkdg_review` | paper | 7 |
| `barsukow_uzh_notes` | notes | 15 |
| **total** | | **95** |

`skipped.jsonl`: 66 entries. `known_false.jsonl`: 0 entries.

## Expected values

| field | TRUE | FALSE | UNSURE |
|---|---|---|---|
| `expected_alone` | 76 | 2 | 17 |
| `expected_with_hypotheses` | 80 | 2 | 13 |

Properties: entropy 26, stability 16, positivity (incl. maximum principle / invariant domain) 12, order 10, other 10,
conservation 9, tvd 8, monotone 2, convergence 2.

Expected values are frozen as of this commit; any correction goes to ERRATA.md with before/after.
