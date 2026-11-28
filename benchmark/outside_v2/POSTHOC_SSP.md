# Bench v2: post-hoc re-score of the 11 SSP-relevant items with the new SSP kinds

**POST-HOC, NOT A RESULT.** We wrote everything here after seeing the items, their expected values, the readers'
readings and the frozen verdicts (V2_RESULTS.md, section "SSP analysis"). Bench v2 is now the dev set for
`ssp_class_preserves` and `ssp_coefficient`, so none of this is out of sample. Nothing frozen was edited:
`V2_RESULTS.md`, `verdicts_*.json`, `items.jsonl`, the readings and `specs/` are unchanged. The specs below are new
files in `posthoc_specs/`, written by us rather than by a blind reader, and run with the current checker through
`posthoc.py` (`uv run python benchmark/outside_v2/posthoc.py`). `tests/test_narrowing.py` asserts every verdict
quoted here.

Sentence verdicts use the quantifier-aware narrowing rule (POSTHOC_NARROWING.md). A kind that quantifies over more
than the sentence does (every convex property, where the sentence names one) is SUFFICIENT for it. An instance of a
sentence that is universal over methods, gamma or fluxes is NECESSARY. A component left unformalized makes the
conjunction UNKNOWN at best.

## Count

Of the 5 items V2_RESULTS.md calls "too narrow", **2 become statable**: `cockburn_shu_2001_rkdg_review:06` with
`ssp_class_preserves` and `ketcheson_2019_relaxation_rk:11` with `ssp_coefficient` (as instances). The other 3 stay
out (`ketcheson:10`, `ketcheson:14`, `kurganov_tadmor:10`). That is the low end of our estimate of 2-3. Two items
outside the "too narrow" five also get a new-kind component: `cockburn:01` (the class, not "regardless of its
accuracy") and `kurganov_tadmor:09` (the time-stepping half). So 4 of the 11 items now have a component in a new
kind, and 6 are still not statable.

**No score changes.** None of the 11 items gets a decided sentence verdict at the frozen (P) row. Each new component
is either SUFFICIENT and REFUTED (says nothing), NECESSARY and VERIFIED (not refuted), or sits beside an unformalized
component. The P row stays at 0 MATCH, 0 WRONG for these items.

## Items

| id | P (alone / with hyp.) | new kind used, or why still not statable | component verdict(s) | sentence verdict (rule) | P score |
|---|---|---|---|---|---|
| `cockburn_shu_2001_rkdg_review:06` | TRUE / TRUE (E: FALSE / TRUE) | `ssp_class_preserves`: the printed conditions (alpha >= 0, unit row sums, \|beta\| <= alpha, c = 1, s = 2; no beta >= 0), `cockburn-06-printed-class.json` | REFUTED: the method alpha = [[1], [1, 0]], beta = [[-1], [-1, 0]] (backward forward-Euler steps) is in the class, and with S = [0, inf), F(1) = 5, F(x) = -x elsewhere (forward Euler keeps S on [0, 1]), u0 = 1, dt = 1 it gives u_1 = u_2 = -4 | UNKNOWN: the kind is over every convex property and the sentence is about one (the TVDM bound of limited RKDG), so SUFFICIENT, and a refutation says nothing. The sentence-level refutation is still the TV growth in errata_checks.py | GAP |
| `ketcheson_2019_relaxation_rk:11` | TRUE / TRUE | `ssp_coefficient`, three instances of C(A, gamma b) >= C(A, b): SSPRK(3,3) at gamma = 3/2 (= gamma\*) and 1/2, SSPRK(2,2) at gamma = 2 (= gamma\*), `ketcheson-11-instances.json` | VERIFIED x 3 (each C = 1 = C(A, b), exact) | NOT_REFUTED: universal over methods and gamma, so each instance is NECESSARY | GAP |
| `ketcheson_2019_relaxation_rk:10` | TRUE / TRUE | still not statable: an iff over every method absolutely monotonic at -r. Neither kind states "for every (A, b)", and the condition is nonlinear in the tableau. One side at one (A, b, gamma, r) could be written as `ssp_coefficient`; we did not | none | GAP (no reading) | GAP |
| `ketcheson_2019_relaxation_rk:14` | TRUE / TRUE | still not statable: the relaxation weights gamma_n b depend on the solution, and "many" methods is not a fixed list | none | GAP | GAP |
| `kurganov_tadmor_2000_central:10` | UNSURE / UNSURE | still not statable: the multi-level methods (5.8) are not one-step Shu-Osher methods (they read u^{n-s}), the scheme is 2D, and Table 5.2's coefficients did not survive extraction | none | - | UNSCORED |
| `cockburn_shu_2001_rkdg_review:01` | UNSURE / UNSURE | partly: `ssp_class_preserves` states the "special class" (alpha, beta >= 0, unit row sums, c beta <= alpha) for s = 3, c = 1, `cockburn-01-ssp-class.json`; "regardless of its accuracy" (members of every order) is not statable | VERIFIED (24 Farkas certificates) | UNKNOWN: the accuracy clause is unformalized (and s, c are narrowed, universal) | UNSCORED |
| `kurganov_tadmor_2000_central:09` | TRUE / TRUE (E: FALSE / TRUE) | partly: `ssp_class_preserves` for the family (5.7) at s = 2 and s = 3, every eta in [0, 1] (Table 5.1's values included), c = 1, `kt-09-family-s2.json`, `kt-09-family-s3.json`; the 2D forward-Euler maximum principle (Theorem 5.1) is not statable (multi-d) | VERIFIED, VERIFIED | UNKNOWN: the forward-Euler half is unformalized | GAP |
| `guermond_popov_2016_invariant_domains:04` | TRUE / TRUE | the SSP clause with the existing `ssp_preserves`: SSPRK(3,3) (third order, checked exactly in posthoc.py) on A1's P1 upwind reduction, max_principle, cfl 1/2, `gp-04-ssprk33.json` | VERIFIED | UNKNOWN: the clause is existential in the method (SUFFICIENT) but the instance also narrows the system to scalar advection (universal), so the quantifiers are mixed. A1's first-order component is NOT_REFUTED (universal narrowing) | GAP |
| `hu_adams_shu_2013_pp_flux_limiter:01` | TRUE / TRUE | still not statable: the limiter is for the Euler system and every high-order base scheme; SSP enters only through the stages | none | GAP | GAP |
| `hu_adams_shu_2013_pp_flux_limiter:05` | TRUE / TRUE | still not statable: as item 01 | none | GAP | GAP |
| `kurganov_tadmor_2000_central:06` | TRUE / TRUE (E: FALSE / TRUE) | still not statable: the TVD part is semi-discrete (no time stepper), the maximum-principle part is 2D | none | GAP | GAP |

## What this says

The new kinds move the gap rather than the score. Class and coefficient statements can now be written and decided
exactly. But in these 11 items the class statements sit inside larger sentences (2D schemes, systems, a specific
limited DG method), and the coefficient statements are universal over methods, so a finite set of instances can
only fail to refute them. To score MATCH on `ketcheson:11`, a kind would need "for every (A, b)" with the
coefficient condition as a polynomial identity in the tableau. On `cockburn:06` we would need the scheme-specific
property (TVDM of k = 0 DG with the upwind flux). `ssp_preserves` can already state that for one method given as
Shu-Osher arrays, such as the errata's beta_21 = -1/2 method; we did not write that spec here.
