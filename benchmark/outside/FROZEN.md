# Freeze record

## Split rule

The split is by source, never by sentence:
`int(hashlib.sha256(source_id.encode()).hexdigest(), 16) % 2`, where 0 gives `dev` and 1 gives `heldout`.
The sources were fixed in `SOURCES.md` before any item was collected, and none was re-picked after the split was
computed.

## Sources per half

| source_id | half | items | type |
|---|---|---|---|
| `shu1997_icase_notes` | heldout | 5 | notes |
| `jiang_shu_1995_weno` | dev | 6 | paper |
| `gottlieb_shu_1998_tvdrk` | heldout | 9 | paper |
| `gottlieb_shu_tadmor_2001_ssp` | heldout | 19 | paper |
| `zhang_shu_2010_maxprinciple` | dev | 18 | paper |
| `zhang_shu_2010_euler_positivity` | heldout | 9 | paper |
| `zhang_shu_2011_survey` | dev | 15 | paper |
| `tadmor_1987_viscosity` | dev | 6 | paper |
| `tadmor_2003_acta` | heldout | 24 | paper |
| `heoc_1986_eno3` | dev | 3 | paper |
| `osher_tadmor_1985_convergence` | dev | 4 | paper |
| `harten_1982_highres` | dev | 10 | paper |
| `mfa_oslo_notes` | dev | 20 | notes |
| `fjordholm_mishra_tadmor_2012_tecno` | dev | 17 | paper |
| `henrick_aslam_powers_2005_mapped` | heldout | 11 | paper |

- `dev`: 9 sources (8 papers, 1 set of notes), 99 items.
- `heldout`: 6 sources (5 papers, 1 set of notes), 77 items.

Each half has both papers and notes.

## Expected-value tallies

| | items | alone TRUE | alone FALSE | alone UNSURE | with hyp. TRUE | with hyp. FALSE | with hyp. UNSURE |
|---|---|---|---|---|---|---|---|
| dev | 99 | 41 | 27 | 31 | 62 | 5 | 32 |
| heldout | 77 | 35 | 22 | 20 | 55 | 5 | 17 |
| total | 176 | 76 | 49 | 51 | 117 | 10 | 49 |

Property tags: dev has positivity 26, order 24, stability 11, entropy 11, convergence 8, tvd 8, other 8, monotone 2,
conservation 1. Heldout has order 24, entropy 16, tvd 13, stability 13, other 6, positivity 5.

`skipped.jsonl`: 51 sentences. `known_false.jsonl` (kept apart, never mixed into either half): 4 entries
(alone: 4 FALSE; with hypotheses: 1 FALSE, 3 UNSURE).

Expected values are frozen as of this commit; any correction goes to ERRATA.md with before/after.
