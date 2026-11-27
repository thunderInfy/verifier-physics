# Coverage log

For each sampled source: every part covered by the sampling rule (abstract, each theorem-type statement,
conclusions) and what became of it: an item, a skipped entry, or "not in population" with the reason.

Two later edits are not reflected in the per-source text below:
- Items whose sentence contained an illegible display were moved to `skipped.jsonl` (reason "illegible", with the
  draft id), as SAMPLING.md requires: `harten_1982_highres` draft ids :07 and :09, `osher_tadmor_1985_convergence`
  draft ids :03, :04, :06, :07, :08, :10, :11. Item ids were not renumbered, so ids have gaps.
- Expected values changed during review before the freeze (Shu notes Lemmas 4.3/4.4, Tadmor 2003 Corollaries
  8.1/8.2); the values in `items.jsonl` are the frozen ones.

---

## `shu1997_icase_notes`

# Coverage: shu1997_icase_notes

Source: C.-W. Shu, "Essentially Non-Oscillatory and Weighted Essentially Non-Oscillatory Schemes for Hyperbolic
Conservation Laws", ICASE Report 97-65 / NASA CR-97-206253, November 1997. Read from `shu1997_icase_notes`
(printed page = pdf page - 1).

## Abstract (p. 1, pdf p. 2)
The notes have an Abstract, which is sampled in place of a preface.
1. "In these lecture notes we describe the construction, analysis, and application of ENO ... and WENO ... schemes ..." - not in population (describes what the notes do).
2. "ENO and WENO schemes are high order accurate finite difference schemes designed for problems with piecewise smooth solutions containing discontinuities." - item shu1997_icase_notes:01
3. "The key idea lies at the approximation level, ..." - skipped (vague)
4. "ENO and WENO schemes have been quite successful in applications, ..." - skipped (vague)
5. "These lecture notes are basically self-contained." - not in population (about the notes)
6. "It is our hope that with these notes ... the reader can understand the algorithms and code them up for applications." - not in population (about the notes)
7. "Sample codes are also available from the author." - not in population (about the notes)

## Theorem / Proposition / Lemma / Corollary statements
The notes have no Theorem, Proposition or Corollary. A search of both text files finds only Lemmas 4.1-4.4.
- Lemma 4.1 (p. 43, Sect. 4.2.1, TVD Runge-Kutta, nonnegative coefficients) - item shu1997_icase_notes:02
- Lemma 4.2 (p. 44, Sect. 4.2.1, TVD Runge-Kutta with adjoint operator L~) - item shu1997_icase_notes:03
- Lemma 4.3 (p. 47, Sect. 4.2.2, TVD multi-step, nonnegative coefficients) - item shu1997_icase_notes:04
- Lemma 4.4 (p. 48, Sect. 4.2.2, TVD multi-step with adjoint operator L~) - item shu1997_icase_notes:05

Not sampled (not a numbered or named Theorem/Proposition/Lemma/Corollary): the unlabelled list of three properties
of ENO interpolation on p. 15, Sect. 2.2.1 (accuracy in smooth cells, monotone in shocked cells, TVB), attributed to [39].

## Conclusions / Summary
None. The notes end with Sect. 5.3 (semiconductor device simulation applications, p. 73) and go straight to
References. The "In summary, ..." paragraphs in Sects. 2.2-2.3 introduce algorithm procedures; they are not
Conclusions/Summary sections.

---

## `jiang_shu_1995_weno`

# Coverage: jiang_shu_1995_weno

Text used: `jiang_shu_1995_weno` (split words and dropped ligatures rejoined; all items carry `ocr_normalized`). `jiang_shu_1995_weno` was checked and is worse (one word fragment per line). Printed page = pdf page − 1 (the abstract page is numbered "i").

The paper has one numbered result (Theorem 6.1). There are no Propositions, Lemmas or Corollaries. The mention of "Strang's theorem (Theorem I in [18])" on p. 14 is body text paraphrasing a cited theorem, not a statement of this paper, so it is not in the population.

## Abstract (p. i)
1. "In this paper, we further analyze, test, modify and improve the high order WENO ... schemes of Liu, Osher and Chan [9]." Not in population (describes what the paper does).
2. "It was shown by Liu et al. that WENO schemes constructed from the r th order ... are (r+1) th order accurate." Item :01.
3. "We propose a new way of measuring the smoothness ... results in a 5th order WENO scheme for the case r = 3, instead of the 4th order ..." Item :02.
4. "This 5th order WENO scheme is as fast as the 4th order WENO scheme of Liu et al. and, both schemes are about twice as fast as the 4th order ENO schemes ..." Not in population (efficiency).
5. "For Euler systems of gas dynamics, we suggest to compute the weights from pressure and entropy ..." Not in population (describes a proposal).
6. "The resulting WENO schemes are about twice as fast ... and work well for problems which do not contain strong shocks ..." Skipped (vague plus efficiency).
7. "We also prove that, for conservation laws with smooth solutions, all WENO schemes are convergent." Item :03.
8. "Many numerical tests ... demonstrate the remarkable capability of the WENO schemes ..." Skipped (vague).
9. "We have also applied Yang's artificial compression method to the WENO schemes to sharpen contact discontinuities." Not in population (describes what is done).

## Theorem 6.1 (p. 15)
- Main sentence ("For the initial value problem of (1.1) with m = 1 ... satisfy u(x0,t0;Δx) = v(x0,t0) + O(Δx^r) for appropriately chosen CFL number."): item :04.
- "Here q0 is a small constant integer (see [18])." Not in population (definition, not a property).

## Section 9 Conclusion (p. 37)
1. "With the new smooth measurement ... can be made (2r-1) th order accurate in smooth regions ..., at least for r = 2, 3." Item :05.
2. "However, at discontinuities, all WENO schemes are just r th accurate ..." Item :06.
3. "The 4th order WENO scheme of Liu et al. and the 5th order WENO scheme ... are found to be at least twice as fast as the 4th order ENO schemes ..." Not in population (efficiency).
4. "Many 1D and 2D numerical tests suggest that both WENO schemes are very robust for shock calculations." Skipped (vague).
5. "The 4th order WENO scheme of Liu et al. is slightly more accurate than the 5th order WENO scheme on coarse grids ... but becomes less accurate on finer grids." Skipped (empirical comparison).
6. "For Euler systems, we also suggest computing the weights from pressure and entropy instead of the projected values." Not in population (proposal).
7. "The resulting WENO schemes are about twice as fast ... and work well for problems which do not contain strong shocks ..." Skipped (vague plus efficiency).
8. "More detailed numerical results for WENO schemes can be found in [6]." Not in population.
9. "We have also adopted the artificial compression method of Yang [20] to enhance the performance of WENO schemes at contact discontinuities." Skipped (vague).
10. "However, the CPU cost is increased by as much as 100% when a Lax-Friedrichs building block is used." Not in population (cost).
11. "We believe the idea of artificial compression method can be adapted directly into the weight definition ..." Not in population (conjecture or plan, no scheme property).
12. "This will be investigated in the future." Not in population.

Totals: 6 items, 6 skipped.

---

## `gottlieb_shu_1998_tvdrk`

# Coverage: gottlieb_shu_1998_tvdrk

Source: S. Gottlieb and C.-W. Shu, Total variation diminishing Runge-Kutta schemes, Math. Comp. 67 (1998), 73–85.
Text read: `gottlieb_shu_1998_tvdrk` (checked against `gottlieb_shu_1998_tvdrk`). Printed page numbers.

## Abstract (p. 73)
- S1 "In this paper we further explore a class of high order TVD ... suitable for solving hyperbolic conservation laws with stable spatial discretizations.": skipped (vague)
- S2 "We illustrate with numerical examples that non-TVD but linearly stable Runge-Kutta time discretization can generate oscillations ...": item gottlieb_shu_1998_tvdrk:01
- S3 "We then explore the issue of optimal TVD Runge-Kutta methods for second, third and fourth order, and for low storage Runge-Kutta methods.": not in population (describes what the paper does)

## Theorem / Proposition / Lemma / Corollary statements
- Lemma 1.1 (p. 74): item gottlieb_shu_1998_tvdrk:02
- Lemma 1.2 (p. 75): item gottlieb_shu_1998_tvdrk:03
- Proposition 3.1 (p. 78): item gottlieb_shu_1998_tvdrk:04
- Proposition 3.2 (p. 78): item gottlieb_shu_1998_tvdrk:05
- Proposition 3.3 (p. 79): item gottlieb_shu_1998_tvdrk:06
- There are no other numbered or named theorems, lemmas or corollaries. The appendix (pp. 81–84) holds only the proofs of Propositions 3.2 and 3.3. The claims in the running text (e.g. p. 76, 'Euler forward ... with this second order MUSCL spatial operator is TVD'; p. 80, the low storage search) are outside the sampled parts.

## Conclusions (section 5, Concluding remarks, p. 80)
- S1 "We have given a simple but illustrating numerical example ... much safer ...": skipped (vague)
- S2 "We then explore the optimal second, third and fourth order TVD Runge-Kutta methods.": not in population (describes what the paper does)
- S3 "While for second and third order optimal methods are found with a CFL coefficient equal to one, ...": item gottlieb_shu_1998_tvdrk:07
- S4 "A TVD third order low storage Runge-Kutta method is found, ... CFL coefficient equal to 0.32.": item gottlieb_shu_1998_tvdrk:08
- S5 "Finally, we prove that general four stage fourth order Runge-Kutta methods cannot be TVD without introducing an adjoint operator L̃.": item gottlieb_shu_1998_tvdrk:09

Totals: 9 items, 2 skipped, 2 not in population.

---

## `gottlieb_shu_tadmor_2001_ssp`

# Coverage: gottlieb_shu_tadmor_2001_ssp

Source: S. Gottlieb, C.-W. Shu and E. Tadmor, Strong stability-preserving high-order time discretization methods,
SIAM Review 43 (2001), 89–112. Text read: `gottlieb_shu_tadmor_2001_ssp`; word spacing taken from `gottlieb_shu_tadmor_2001_ssp`, where the
`.p.txt` text layer runs words together. Printed page numbers.

## Abstract (p. 89)
- S1 "In this paper we review and further develop a class of strong stability-preserving (SSP) high-order time discretizations ...": not in population (describes what the paper does)
- S2 "Previously termed TVD (total variation diminishing) time discretizations, these high-order time discretization methods preserve the strong stability properties of first-order Euler time stepping ...": item gottlieb_shu_tadmor_2001_ssp:01
- S3 "The new developments in this paper include the construction of optimal explicit SSP linear Runge–Kutta methods, ...": not in population (lists contributions)

## Theorem / Proposition / Lemma / Corollary statements
- Lemma 2.1 (p. 92): item :02
- Lemma 2.2 (p. 93): item :03
- Lemma 2.3 (p. 93): item :04
- Proposition 3.1 (p. 94): item :05 (its first sentence, 'Consider the family ...', is recorded as a hypothesis)
- Proposition 3.2 (p. 95): item :06
- Proposition 3.3 (p. 98): item :07 (first sentence 'Consider the coercive systems ...' recorded as a hypothesis)
- Proposition 4.1 (p. 100): two sentences, items :08 (second order) and :09 (third order)
- Proposition 4.2 (p. 101): item :10
- Proposition 4.3 (p. 103): item :11
- Proposition 5.1 (p. 103): item :12
- Proposition 5.2 (p. 105): item :13
- Proposition 5.3 (p. 106): item :14
- Proposition 5.4 (p. 106): item :15
- Lemma 6.1 (Harten) (p. 107): item :16
- Proposition 6.2 (p. 110): item :17
- Proposition 6.3 (p. 111): item :18
- Not sampled: Assumption 3.1 and Assumption 3.2 (pp. 97–98) are assumptions, not theorem-type statements, and are used as hypotheses of item :07. The "Claim" inside the proof of Proposition 5.1 (p. 104) is part of a proof. There are no Theorems or Corollaries.

## Conclusions (section 7, Concluding Remarks, p. 112)
- S1 "We have systematically studied SSP time discretization methods, which preserve stability, in any norm, ...": item :19
- S2 "Runge–Kutta and multistep methods are both investigated.": not in population (describes what the paper does)
- S3 "The methods listed here can be used for method of lines numerical schemes for PDEs, especially for hyperbolic problems.": skipped (vague)

Totals: 19 items, 1 skipped, 3 not in population.

---

## `zhang_shu_2010_maxprinciple`

# Coverage: zhang_shu_2010_maxprinciple

Source: X. Zhang and C.-W. Shu, "On maximum-principle-satisfying high order schemes for scalar conservation laws"
(preprint, J. Comput. Phys. 229 (2010)). Read from `zhang_shu_2010_maxprinciple` (cleaner math than `zhang_shu_2010_maxprinciple`, where
"fi"/"ff" ligatures are dropped). Page numbers are the printed page numbers at the foot of each page.

## Abstract (p. 1)
1. "We construct uniformly high order accurate schemes satisfying a strict maximum principle for scalar conservation laws." - item zhang_shu_2010_maxprinciple:01
2. "A general framework (for arbitrary order of accuracy) is established to construct a limiter for finite volume schemes ... with first order Euler forward time discretization solving one dimensional scalar conservation laws." - not in population (describes what the paper does)
3. "Strong stability preserving (SSP) high order time discretizations will keep the maximum principle." - item zhang_shu_2010_maxprinciple:02
4. "It is straightforward to extend the method to two and higher dimensions on rectangular meshes." - skipped (vague)
5. "We also show that the same limiter can preserve the maximum principle for DG or finite volume schemes solving two-dimensional incompressible Euler equations ..., or any passive convection equation with an incompressible velocity field." - item zhang_shu_2010_maxprinciple:03
6. "Numerical tests for both the WENO finite volume scheme and the DG method are reported." - not in population (describes the paper)

## Theorem / Proposition / Lemma / Corollary statements
Searched both text files: Lemma 2.1, Theorem 2.2, Lemma 2.4, Theorem 2.5, Lemma 4.1, Lemma 4.2, Theorem 4.3. Section 3
(2D) has no numbered statement. There are no Propositions or Corollaries.
- Lemma 2.1 (p. 6): sentence 1 ("Under the CFL condition ..., consider the first order Lax-Friedrichs scheme (2.3).") gives the hypotheses; sentence 2 is item zhang_shu_2010_maxprinciple:04
- Theorem 2.2 (p. 7): sentences 1-2 (setting, notation v̂_0, v̂_{N+1}) are hypotheses/definitions; sentence 3 is item zhang_shu_2010_maxprinciple:05
- Lemma 2.4 (p. 9) - item zhang_shu_2010_maxprinciple:06
- Theorem 2.5 (pp. 10-11): sentence 1 ("Assume p_j(x) has degree k, m and M are defined in (1.3).") is a hypothesis; sentence 2 is item zhang_shu_2010_maxprinciple:07; sentence 3 ("See Table 2.1 for the CFL number for 2 ≤ k ≤ 5.") is not in population (pointer to a table)
- Lemma 4.1 (p. 26): sentence 1 (scheme (4.13), u_{j−1}, u_j ∈ [−a, a]) is definition/hypothesis; sentence 2 is item zhang_shu_2010_maxprinciple:08
- Lemma 4.2 (p. 27) - item zhang_shu_2010_maxprinciple:09
- Theorem 4.3 (p. 28): sentences 1-2 (limiter already applied, values in [m, M] on S_ij) are hypotheses; sentence 3 is item zhang_shu_2010_maxprinciple:10

Remarks 2.3, 2.6, 2.7, 2.8, 4.4 and 4.5 are not sampled (remarks), though some are cited in justifications.

## Concluding remarks (Sect. 7, pp. 52-53)
1. "In this paper, we have established a general framework to construct arbitrarily high order accurate maximum-principle-satisfying schemes ..." - item zhang_shu_2010_maxprinciple:11
2. "This is the first time that genuine high order schemes are obtained ..." - skipped (priority claim)
3. "The main difficulty is to get the cell averages in the next time step to be within the range [m, M] with a limiter which does not destroy accuracy." - not in population (describes the difficulty, no property asserted)
4. "The exact time evolution has this property, but it cannot be easily implemented ..." - skipped (vague)
5. "We prove that SSP time discretization can maintain the cell averages in [m, M] as long as ..." - item zhang_shu_2010_maxprinciple:12
6. "The implementation is quite easy." - skipped (vague)
7. "With the addition of the limiter in this paper, ... the numerical solutions will satisfy the maximum principle under suitable CFL condition." - item zhang_shu_2010_maxprinciple:13
8. "We also show that the same result holds for the DG or finite volume schemes solving the two dimensional incompressible Euler equations ..." - item zhang_shu_2010_maxprinciple:14
9. "The result is also valid for any passive convection equation with divergence-free velocity coefficients." - item zhang_shu_2010_maxprinciple:15
10. "We have tested the fifth order finite volume WENO scheme and the DG scheme with limiter on a variety of examples ..." - not in population (describes the tests)
11. "We clearly observe strict maximum principle preserving in all these tests." - item zhang_shu_2010_maxprinciple:16
12. "The SSP multi-step time discretization gives us genuine high order accuracy." - item zhang_shu_2010_maxprinciple:17
13. "The accuracy for the SSP Runge-Kutta time discretization may however degenerate on a fine mesh, ..." - item zhang_shu_2010_maxprinciple:18
14. "However, this effect is mainly of theoretic interest as it can only be observed for very fine meshes." - skipped (vague)
15. "In this paper we have only shown a straightforward extension of the one dimensional algorithm to two dimensional finite volume or DG schemes on a rectangular mesh." - not in population (describes scope)
16. "For triangular meshes, the idea of rewriting the scheme as a convex combination of monotone schemes is still plausible and will be explored in the future." - not in population (future work)
17. "Generalizations to finite difference schemes, and to nonlinear systems ... constitute our ongoing work." - not in population (future work)

Not sampled: the Introduction paragraph "The main conclusion of this paper is as follows: ..." (p. 4), which is in the
Introduction, not in a sampled part.

Totals: 18 items, 5 skipped.

---

## `zhang_shu_2010_euler_positivity`

# Coverage: zhang_shu_2010_euler_positivity

Source: X. Zhang and C.-W. Shu, "On positivity preserving high order discontinuous Galerkin schemes for compressible
Euler equations on rectangular meshes" (preprint, J. Comput. Phys. 229 (2010)). Read from `zhang_shu_2010_euler_positivity`
(cleaner math than `zhang_shu_2010_euler_positivity`, which drops "fi" ligatures). Page numbers are the printed page numbers at the foot of each page.

## Abstract (p. 1)
1. "We construct uniformly high order accurate discontinuous Galerkin (DG) schemes which preserve positivity of density and pressure for Euler equations of compressible gas dynamics." - item zhang_shu_2010_euler_positivity:01
2. "The same framework also applies to high order accurate finite volume (e.g. ... ENO ... or WENO) schemes." - skipped (vague)
3. "Motivated by [20, 26], a general framework, for arbitrary order of accuracy, is established to construct a positivity preserving limiter ..." - not in population (describes what the paper does)
4. "The limiter can be proven to maintain high order accuracy and is easy to implement." - item zhang_shu_2010_euler_positivity:02
5. "Strong stability preserving (SSP) high order time discretizations will keep the positivity property." - item zhang_shu_2010_euler_positivity:03
6. "Following the idea in [26], we extend this framework to higher dimensions on rectangular meshes in a straightforward way." - not in population (describes what the paper does)
7. "Numerical tests for the third order DG method are reported to demonstrate the effectiveness of the methods." - not in population (describes the tests)

## Theorem / Proposition / Lemma / Corollary statements
Searched both text files: Theorem 2.1, Lemma 2.5, Theorem 3.1. Numbers 2.2-2.4, 2.6, 2.7 are Remarks (not sampled). There are no
Propositions or Corollaries.
- Theorem 2.1 (p. 6) - item zhang_shu_2010_euler_positivity:04
- Lemma 2.5 (p. 10) - item zhang_shu_2010_euler_positivity:05
- Theorem 3.1 (p. 17) - item zhang_shu_2010_euler_positivity:06

Not sampled: the unnumbered accuracy argument for the limiter (p. 11) and Remarks 2.2-2.4, 2.6, 2.7 (cited in
justifications).

## Concluding remarks (Sect. 5, p. 31)
1. "In this paper, we improved the general framework in [20] to construct arbitrarily high order accurate finite volume and discontinuous Galerkin positivity preserving schemes ... in one dimension." - item zhang_shu_2010_euler_positivity:07
2. "An efficient and easy implementation is achieved by a simple linear scaling limiter, which can be proven to maintain high order accuracy and positivity of density and pressure." - item zhang_shu_2010_euler_positivity:08
3. "Then we extend the method to schemes on rectangular meshes for two dimensional Euler equations." - not in population (describes the paper)
4. "Conceptually, extension of this technique to three dimensions is straightforward." - skipped (vague)
5. "With the addition of the positivity limiter in this paper, ... the density and pressure of the cell average are positive under suitable CFL condition." - item zhang_shu_2010_euler_positivity:09
6. "We have tested the third order DG scheme with the positivity limiter on a variety of examples ..." - not in population (describes the tests)
7. "Implementation details and numerical results for finite volume schemes using this positivity limiter will be reported elsewhere." - not in population (future work)
8. "In this paper we have only shown a straightforward extension of the one dimensional algorithm to two dimensional finite volume or DG schemes on a rectangular mesh." - not in population (describes scope)
9. "For triangular meshes, the idea of rewriting the scheme as a convex combination of positive first order schemes is still plausible ..., see [28] for such an extension." - not in population (future work / pointer)
10. "For the astrophysical jets, the model with radiative cooling, ... makes more sense physically, but it is more difficult to preserve the positivity." - not in population (about the model, no scheme property)
11. "For radially-symmetric problems, ... we can consider the Euler systems in radially-symmetric form, ..." - not in population (about the PDE formulation)
12. "Generalizations to positivity preserving high order schemes for Euler systems with a source term also constitute our ongoing work." - not in population (future work)

Not sampled: the Introduction paragraph "The main conclusion of this paper is, ..." (p. 5).

Totals: 9 items, 2 skipped.

---

## `zhang_shu_2011_survey`

# Coverage: zhang_shu_2011_survey

Source: X. Zhang and C.-W. Shu, "Maximum-principle-satisfying and positivity-preserving high order schemes for
conservation laws: Survey and new developments", Proc. R. Soc. A (2011), preprint. Read from `zhang_shu_2011_survey`.
Page numbers are the printed page numbers.

## Abstract (p. 1)
The text has no "Abstract" heading. The unlabelled paragraph before "1. Introduction" is the abstract.
1. "In Zhang & Shu (2010b), genuinely high order accurate finite volume and discontinuous Galerkin schemes satisfying a strict maximum principle for scalar conservation laws were developed." - item zhang_shu_2011_survey:01
2. "The main advantages of such schemes are their provable high order accuracy and their easiness for generalization to multi-dimensions ..." - item zhang_shu_2011_survey:02
3. "The same idea can be used to construct high order schemes preserving the positivity of certain physical quantities, ..." - item zhang_shu_2011_survey:03
4. "These schemes have been applied in computational fluid dynamics, computational astronomy and astrophysics, plasma simulation, population models and traffic flow models." - not in population (applications, no property)
5. "In this paper, we first review the main ideas ..., then present a simpler implementation which will result in a significant reduction of computational cost especially for ... WENO ... schemes." - not in population (describes the paper; efficiency claim)

## Theorem / Proposition / Lemma / Corollary statements
Searched both text files: Theorems 1-11 and Lemma 1. There are no Propositions or Corollaries. Unnumbered "Remark" paragraphs are not sampled.
- Theorem 1 (p. 6): sentence 1 ("Consider a finite volume scheme ... in the sense that ...") is the setting; sentence 2 is item zhang_shu_2011_survey:04
- Lemma 1 (p. 7) - item zhang_shu_2011_survey:05
- Theorem 2 (p. 9) - item zhang_shu_2011_survey:06
- Theorem 3 (pp. 11-12): sentence 1 is the setting; sentence 2 is item zhang_shu_2011_survey:07
- Theorem 4 (p. 14): sentence 1 is item zhang_shu_2011_survey:08; sentence 2 ("Here ŵ1 is still the quadrature weight ...") is not in population (definition)
- Theorem 5 (p. 15) - item zhang_shu_2011_survey:09
- Theorem 6 (p. 17) - item zhang_shu_2011_survey:10
- Theorem 7 (p. 17) - item zhang_shu_2011_survey:11
- Theorem 8 (p. 19) - item zhang_shu_2011_survey:12
- Theorem 9 (p. 22) - item zhang_shu_2011_survey:13
- Theorem 10 (p. 23): sentence 1 (existence of (x*_i, y*_j) with (5.3)) is treated as a definition/hypothesis and checked in the justification; sentence 2 is item zhang_shu_2011_survey:14
- Theorem 11 (p. 23): sentence 1 (existence of (x*_K, y*_K)) is treated as a definition/hypothesis; sentence 2 is item zhang_shu_2011_survey:15

## Concluding remarks (Sect. 6, p. 24)
1. "We have given a review of the recently developed maximum-principle-satisfying high order finite volume or DG schemes ..." - not in population (describes the paper)
2. "We also propose a simpler and less expensive implementation especially for the finite volume WENO schemes, and provide several numerical examples to demonstrate their performance." - not in population (describes the paper; efficiency)

Totals: 15 items, 0 skipped.

---

## `tadmor_1987_viscosity`

# Coverage: tadmor_1987_viscosity (Tadmor, The numerical viscosity of entropy stable schemes for systems of conservation laws. I, Math. Comp. 49 (1987) 91-103)

Source text: source tadmor_1987_viscosity (OCR scan). Many displayed formulas are garbled; where a scheme formula was needed it was read from the readable fragments plus the later restatement in tadmor_2003_acta, and each such case is marked in the item. No Conclusions/Summary section exists.

## Abstract (p. 91), sentence by sentence
1. "Discrete approximations to hyperbolic systems of conservation laws are studied." : not in population (describes the paper)
2. "We quantify the amount of numerical viscosity present in such schemes, and relate it to their entropy stability by means of comparison." : not in population (describes the paper)
3. "To this end, conservative schemes which are also entropy conservative are constructed." : not in population ("are constructed" describes the work)
4. "These entropy conservative schemes enjoy second-order accuracy: moreover, ..." : item tadmor_1987_viscosity:01
5. "We then show that conservative schemes are entropy stable, if and—for three-point schemes—only if ..." : item tadmor_1987_viscosity:02

## Theorems / Lemmas / Corollaries (statements only)
- Theorem 4.1 (p. 96), main sentence: skipped (illegible)
- Theorem 4.1, "Here, G*_{ν+1/2} is the consistent numerical entropy flux given by (4.10b)": not in population (defines the entropy flux; the formula is also garbled)
- Lemma 5.1 (p. 99): item tadmor_1987_viscosity:03
- Theorem 5.2 (i) (p. 100), first sentence: item tadmor_1987_viscosity:04
- Theorem 5.2 (i), "Moreover, the entropy aps ... (5.13a)": skipped (illegible)
- Theorem 5.2 (i), "Here, G_{ν+1/2} ... is the consistent numerical entropy flux (5.13b)": not in population (definition)
- Theorem 5.2 (ii) (p. 101): item tadmor_1987_viscosity:05
- Theorem 5.3 (p. 101): item tadmor_1987_viscosity:06

## Conclusions
None in this source.

## Totals
6 items, 2 skipped.

---

## `tadmor_2003_acta`

# Coverage: tadmor_2003_acta (Tadmor, Entropy stability theory..., Acta Numerica 2003, pp. 451-512)

Printed page = pdf page + 450. No Conclusions/Summary section exists (Section 9 "Higher-order extensions" is the last section). The paper has a single abstract paragraph, pp. 451-452.

## Abstract (pp. 451-452), sentence by sentence
1. "We study the entropy stability of difference approximations ..." : not in population (describes the paper)
2. "We employ a comparison principle as the main tool ..." : not in population (describes method)
3. "To this end, we introduce general families of entropy-conservative schemes, interesting in their own right." : not in population (describes construction)
4. "The present treatment of such schemes extends our earlier recipe ..." : not in population (describes the paper)
5. "The new families of entropy-conservative schemes offer two main advantages, ..." : item tadmor_2003_acta:01
6. "A comparison with the numerical viscosities ... provides a useful framework ..." : skipped (vague)
7. "We employ this framework for a detailed study of entropy stability for a host of first- and second-order accurate schemes." : not in population (describes the paper)
8. "The comparison approach yields a precise characterization ..." : skipped (vague)
9. "We extend these results to fully discrete schemes." : not in population (describes the paper)
10. "Here, spatial entropy dissipation is balanced by the entropy production ..." : item tadmor_2003_acta:02
11. "Finally, we revisit the question ... homotopy arguments." : not in population (describes the paper)
12. "We prove entropy stability under optimal CFL conditions." : item tadmor_2003_acta:03

## Theorems / Lemmas / Corollaries (statements only)
- Theorem 2.2 (p. 461): not in population (a priori estimate for entropy solutions of the PDE)
- Corollary 2.3 (p. 462): not in population (L1 contraction of PDE entropy solutions, Kruzkov)
- Theorem 3.1 (p. 464): item tadmor_2003_acta:04
- Corollary 4.1 (pp. 465-466): item tadmor_2003_acta:05
- Lemma 4.5 (p. 468): item tadmor_2003_acta:06 (first sentence "Consider the conservative schemes (4.3) with viscosity coefficient ... Lipschitz-continuous." is a hypothesis)
- Corollary 5.1 (p. 472): item tadmor_2003_acta:07
- Theorem 5.3 (p. 476): item tadmor_2003_acta:08
- Theorem 5.4 (pp. 476-477): item tadmor_2003_acta:09 (first sentence and the "Here γ ... (5.28)" sentence are hypotheses)
- Theorem 5.7 (p. 478): item tadmor_2003_acta:10
- Theorem 5.9 (pp. 479-480): item tadmor_2003_acta:11 ("Here ε_k > 0 are arbitrary parameters" is a hypothesis)
- Theorem 6.1 (p. 483): item tadmor_2003_acta:12 ("Here, ψ is the entropy flux potential ..." is a definition/hypothesis)
- Corollary 6.2 (p. 485): item tadmor_2003_acta:13 (the "Given a complete path ..." sentence is a hypothesis)
- Theorem 6.3 (p. 486): item tadmor_2003_acta:14
- Corollary 6.4 (p. 488): sentence 1 is item tadmor_2003_acta:15; sentence 2 is item tadmor_2003_acta:16
- Corollary 6.5 (p. 488): sentence 1 (with display (6.14)) is item tadmor_2003_acta:17; trailing sentence is item tadmor_2003_acta:18 (counted as part of the statement, see the doubt in the item)
- Corollary 7.4 (p. 494): item tadmor_2003_acta:19
- Corollary 8.1 (pp. 496-497): item tadmor_2003_acta:20 (the CFL sentence is a hypothesis)
- Corollary 8.2 (p. 498): item tadmor_2003_acta:21 (the CFL sentence is a hypothesis)
- Theorem 9.1 (p. 502): item tadmor_2003_acta:22 (the "Consider the semi-discrete scheme ..." and "Here, Q** is a secondary viscosity coefficient ..." sentences are definitions)
- Lemma A1 (p. 508): item tadmor_2003_acta:23 (the eigensystem assumption (A.4) is a hypothesis)
- Lemma A2 (p. 510): item tadmor_2003_acta:24 (the first two sentences are definitions/hypotheses)

Not sampled (examples, remarks, proofs): Examples 2.1, 4.2-4.4, 4.6-4.9, 5.2, 5.5, 5.6, 5.8, 5.10, 5.11, 7.1-7.3, 8.3, 8.4 and all Remarks.

## Conclusions
None in this source.

## Totals
24 items, 2 skipped.

---

## `heoc_1986_eno3`

# Coverage: heoc_1986_eno3 (ICASE 86-22, April 1986; OCR scan; source heoc_1986_eno3, source heoc_1986_eno3)

Printed page = pdf page - 2 from the Introduction on; the abstract page (pdf p. 2) carries no printed number.
The report has no numbered or named Theorem, Proposition, Lemma or Corollary (searched both extractions) and no
Conclusion(s) / Concluding remarks / Summary section (Section 7, Numerical experiments, is followed directly by the
Appendix). So the sampled part is the abstract only.

## Abstract (pdf p. 2)
- "In this paper, a third in a series we continue the construction and the analysis of essentially non-oscillatory shock capturing methods ..." not in population (describes the paper)
- "We present an hierarchy of uniformly high order accurate schemes which generalizes Godunov's scheme and its second order accurate MUSCL extension to arbitrary order of accuracy." item heoc_1986_eno3:01
- "The design involves an essentially non-oscillatory, piecewise polynomial reconstruction of the solution from its cell averages, time evolution ..., and averaging of this approximate solution over each cell." not in population (describes the construction)
- "The reconstruction algorithm is derived from a new interpolation technique that when applied to piecewise smooth data gives high-order accuracy whenever the function is smooth but avoids a Gibbs phenomenon at discontinuities." item heoc_1986_eno3:02
- "Unlike standard finite difference methods this procedure uses an adaptive stencil of grid points and consequently the resulting schemes are highly nonlinear." item heoc_1986_eno3:03

## Theorem / Lemma / Proposition / Corollary statements
- none in this report

## Conclusions
- none in this report

Totals: 3 items, 0 skipped.

---

## `osher_tadmor_1985_convergence`

# Coverage: osher_tadmor_1985_convergence (ICASE 85-28, OCR scan; source osher_tadmor_1985_convergence, source osher_tadmor_1985_convergence)

Printed page numbers (the report's "-N-" headers). There is no Conclusions / Summary section (the Introduction's list of "notable conclusions", p. 3, is not a sampled part). Nearly all displayed formulas are illegible in both extractions; items whose asserted property sits inside an illegible display were skipped as illegible.

## Abstract (p. i)
- "We present a unified treatment of ... approximations to scalar conservation laws." not in population (describes the paper)
- "The schemes are assumed only to have conservation form and incremental form." not in population (states an assumption, no property)
- "We introduce a modified flux and a viscosity coefficient and obtain results in terms of the latter." not in population (describes the paper)
- "The existence of a cell entropy inequality is discussed and such an equality ... first order accurate in general." item osher_tadmor_1985_convergence:01
- "Convergence for TVD-SOR schemes approximating convex or concave conservation laws ..." item osher_tadmor_1985_convergence:02

## Theorem / Lemma / Proposition / Corollary statements
- Lemma 1.2 (p. 8): item :03
- Lemma 3.2 (pp. 12-13): skipped (illegible)
- Theorem 4.2 (p. 18): skipped (illegible)
- Theorem 4.3 (p. 19): item :04
- Theorem 4.7 (p. 21): item :05
- Corollary 4.9 (p. 23): item :06 (hypothesis sentences "Consider the 3-point scheme (4.20a) and assume the TVD-like constraint ... holds." are its hypotheses; "Here, g_v is the flux correction, given by (4.21b) where (4.21c)" is a definition)
- Lemma 5.1 (p. 27): item :07 ("Equivalently, (5.5b) can be rewritten ..." is a restatement of the same inequality, not a separate claim)
- Lemma 6.1 (p. 29): not in population (asserts that the auxiliary function g^{(v+1/2)} is a well-defined piecewise linear function; no scheme property)
- Lemma 6.2 (pp. 31-32): skipped (illegible)
- Theorem 6.4 (p. 33): skipped (illegible)
- Theorem 6.5 (p. 34): skipped (illegible)
- Lemma 6.7 (p. 36): skipped (illegible)
- Lemma 6.8 (p. 39): skipped (illegible)
- Theorem 6.10 (p. 40): skipped (illegible)
- Theorem 6.11 (p. 41): skipped (illegible)
- Theorem 7.1 (p. 46): item :08
- Theorem 7.3 (p. 50): item :09
- Lemma 8.1 (p. 54): skipped (illegible)
- Proposition 8.2 (p. 56): skipped (illegible)
- Lemma 8.3 (p. 57): skipped (illegible)
- Theorem 8.4 (p. 59): item :10
- Theorem 8.5 (p. 61): item :11

## Conclusions
- none in this report (not in population)

Totals: 11 items, 12 skipped.

---

## `harten_1982_highres`

# Coverage: harten_1982_highres (Courant DOE/ER/03077-175, March 1982; poor OCR scan; source harten_1982_highres, source harten_1982_highres)

Printed page numbers ("- N -" headers; abstract on p. iv). There is no Conclusions / Summary section (Section 8, Numerical experiments, ends with remarks inside the numerical section, not sampled).

## Abstract (p. iv)
- "This paper presents a class of new explicit second order accurate finite difference schemes ..." item harten_1982_highres:01
- "These highly nonlinear schemes are obtained by applying a nonoscillatory first order accurate scheme to an appropriately modified flux function." not in population (describes the construction)
- "The so derived second order accurate schemes achieve high resolution while preserving the robustness ..." skipped (vague)
- "Numerical experiments are presented to demonstrate the performance of these new schemes." not in population (describes the paper)

## Theorem / Lemma / Proposition / Corollary statements
- Theorem 2.1 (p. 6): two sentences, items :02 (part i) and :03 (part ii)
- Lemma 2.2 (p. 10): item :04
- Lemma 3.1 (p. 12): item :05
- Lemma 3.2 (p. 15): item :06
- Lemma 3.3 (p. 16): item :07
- Lemma 3.4 (p. 18): item :08
- Lemma 4.1 (p. 25): item :09
- Lemma 4.2 (pp. 25-26): item :10
- Corollary 4.3 (p. 26): item :11
- Lemma 5.1 (p. 31): item :12

## Conclusions
- none in this report (not in population)

Totals: 12 items, 1 skipped.

---

## `mfa_oslo_notes`

# Coverage: mfa_oslo_notes

Source: S. Mishra, U. S. Fjordholm, R. Abgrall, "Numerical methods for conservation laws and related equations"
(lecture notes). Files read: `mfa_oslo_notes` (page-marked; printed page = pdf page) and
`mfa_oslo_notes`, used to check the inequality signs: the page-marked file prints `>` where the other
extraction has `⩾`, in (4.57), (4.59), (4.67) and in the proof of Lemma 4.10.

The statement list comes from a search of both files for every "Theorem/Proposition/Lemma/Corollary N.M". There are
no Propositions or Corollaries. The only Summary/Conclusion section is 3.5; there is none for the whole notes.

## About these notes (p. 3)
- Every sentence describes the notes or the Compack software, and none asserts a scheme property: not in population.

## Statements
| Statement | Page | Outcome |
|---|---|---|
| Lemma 2.1 (energy bound) | 12 | not in population (exact smooth solutions of transport eq. (2.1)) |
| Lemma 2.2 (L∞ bound) | 12 | not in population (exact solutions of (2.1)) |
| Lemma 2.3 (central scheme energy) | 14 | items 01 (identity (2.10)), 02 ("energy grows at every time step") |
| Lemma 2.4 (upwind energy stability) | 16 | items 03 (E^{n+1} ⩽ E^n), 04 ("conditionally stable") |
| Lemma 2.5 (upwind L1/L∞) | 18 | item 05 |
| Theorem 3.4 (Rankine–Hugoniot) | 25 | not in population (weak solutions of the PDE) |
| Lemma 3.7 (Kruzkov condition) | 30 | not in population (entropy solutions of the PDE) |
| Theorem 3.8 (entropy condition for shocks) | 30 | not in population (PDE) |
| Theorem 3.10 (well-posedness, L1/L∞/TV bounds) | 32 | not in population (PDE) |
| Theorem 4.5 (conservative iff flux form) | 48 | item 06 |
| Lemma 4.8 (monotonicity of two-point flux schemes) | 50 | item 07 |
| Lemma 4.9 (discrete maximum principle) | 51 | items 08 ((4.47)), 09 ((4.48)) |
| Lemma 4.10 (Crandall–Majda entropy inequality) | 52 | items 10 ((4.50)), 11 ((4.51) L1 bound) |
| Lemma 4.12 (Harten's lemma) | 53 | items 12 (part (i), TVD), 13 (part (ii), L∞) |
| Lemma 4.13 (monotone ⇒ TVD) | 53 | item 14 |
| Lemma 4.14 (time continuity) | 54 | item 15 |
| Theorem 4.15 (Lax–Wendroff) | 55 | item 16 |
| Lemma 4.16 (limit is entropy solution) | 56 | item 17 |
| Theorem 4.17 (Ascoli) | 56 | not in population (functional analysis, no scheme) |
| Theorem 4.18 (Helly) | 56–57 | not in population (functional analysis, no scheme) |
| Theorem 4.19 (convergence of monotone schemes) | 57 | item 18 |
| Lemma 5.2 (first-order accuracy) | 61 | item 19 |
| Lemma 5.10 (SSP-RK2 is TVD) | 76 | item 20 |
| Lemma 8.8 (shock curves, genuinely nonlinear) | 110 | not in population (PDE systems, wave curves) |
| Lemma 8.9 (contact curves, linearly degenerate) | 110 | not in population (PDE) |
| Lemma 8.10 (m simple-wave curves) | 111 | not in population (PDE) |
| Lemma 8.16 (entropy condition across waves) | 113 | not in population (PDE) |
| Lemma 8.17 (admissible shock curve) | 113 | not in population (PDE) |
| Theorem 8.18 (Lax: Riemann problem solution) | 114 | not in population (PDE) |
| Theorem A.1 (Gronwall) | 115 | not in population (real analysis) |

Sentences in a statement that only set up the hypotheses ("Let ...", "Assume ...", "Consider the scheme (4.55).")
went into the `hypotheses` of the item they qualify. They are not separate items.

## Summary / conclusions
- Sec. 3.5 Summary (p. 35): all four bullets are about the PDE (shocks, non-uniqueness of weak solutions, Riemann
  solutions, entropy solutions existing, being unique, L1 stable and TVD): not in population.

## Skipped
- None. No sentence in the sampled parts was vague or illegible (`mfa_oslo_notes.skipped.jsonl` is empty).

Totals: 20 items, 0 skipped.

---

## `fjordholm_mishra_tadmor_2012_tecno`

# Coverage: fjordholm_mishra_tadmor_2012_tecno

Text used: `fjordholm_mishra_tadmor_2012_tecno` (born-digital SIAM text layer). Printed page = pdf page + 543. Some words in the text layer run together; I re-spaced them, expanded ligatures, and marked those items `ocr_normalized`. Overbars (interface averages) are lost in the text layer and are noted in the scheme fields.

## Abstract (p. 544)
1. "We design arbitrarily high-order accurate entropy stable schemes for systems of conservation laws." Item :01. It is framed as "we design", but it attributes definite properties.
2. "The schemes, termed TeCNO schemes, are based on two main ingredients: (i) ... (ii) ..." Not in population (describes the construction).
3. "Numerical experiments ... illustrate the robust numerical performance of the TeCNO schemes." Skipped (vague).

## Theorems, lemmas, corollaries (statements only)
- Theorem 2.1 (p. 547): the hypothesis sentence goes into hypotheses; the property sentence "Then the scheme with numerical flux ~F is second-order accurate and entropy conservative ..." is item :02.
- Theorem 2.2 (p. 550): the hypothesis sentence goes into hypotheses; "Then the finite difference scheme with flux ~F^{2p} is (i) ... (ii) ..." is item :03.
- Lemma 3.1 (p. 551): item :04. It is a single sentence (through "... of the flux ~F_{i+1/2}").
- Lemma 3.2 (p. 552): the hypothesis sentences ("For each i ∈ Z, let R ...", "Let v_i(x) be a polynomial reconstruction ...") go into hypotheses; "Then the scheme with numerical flux (3.8) is entropy stable ..." is item :05.
- Theorem 3.4 (p. 555): the hypothesis sentence goes into hypotheses; "Then the reconstruction satisfies the sign property ..." is item :06; "Furthermore, we have (3.18) ... ≤ C_k ..." is item :07.
- Corollary 3.5 (p. 556): item :08.
- Theorem 4.1 (p. 556): the hypothesis sentences go into hypotheses; "Then the finite difference scheme with numerical flux (3.8) is (i) (k−1)th-order accurate ..., (ii) entropy stable ..." is item :09.
- Theorem 4.3 (p. 557): the hypothesis sentences ("Consider a linear system ...", "Let u_i(t) be the solution computed ...") go into hypotheses; "Then uΔx ⇀ u ..." is item :10.
- Lemma 4.4 (p. 558): the hypothesis sentences ("Let u = u denote the solution ...", "Let {u_i} be the solution computed with the TeCNO flux (3.8) ...") go into hypotheses; "Then, the following L∞ estimate holds ..." is item :11.
- Theorem 6.1 (p. 566): item :12.
- Not in population: "As a corollary, we can sum (3.3) over all i ..." (p. 551) is body text, not a numbered or named corollary. The cited results inside remarks and proofs (Merriam's theorem, p. 553) are not statements of this paper. Remarks 2.3, 3.3 and 4.2 are remarks.

## Section 7 Conclusions (pp. 570-571)
1. "We construct TeCNO finite difference schemes for systems of conservation laws." Not in population (describes what is done).
2. "The schemes do not involve any tuning parameters and are (i) ... (ii) ... (iii) essentially nonoscillatory near discontinuities." Item :13.
3. "Entropy stability implies that the approximate solutions are bounded in Lp for some p." Item :14.
4. "The TeCNO schemes combine high-order accurate entropy conservative fluxes with suitable numerical diffusion operators." Not in population (describes the construction; the flux property is item :03).
5. "The high-order entropy conservative fluxes are constructed by taking linear combinations of two-point entropy conservative fluxes." Not in population (describes the construction).
6. "Computationally inexpensive two-point entropy conservative fluxes are described for several well-known conservation laws." Not in population (efficiency and description).
7. "Numerical diffusion operators of arbitrary order of accuracy are designed by performing an ENO reconstruction in scaled entropy variables." Not in population (describes the construction; the order is covered by item :09). This is a borderline case.
8. "Entropy stability follows as a consequence of the sign property of the ENO reconstruction, shown in a recent paper [10]." Item :15.
9. "We also prove that the TeCNO schemes converge for linear symmetrizable systems." Item :16.
10. "A large number of numerical examples in one and two space dimensions are presented." Not in population.
11. "They show that the TeCNO schemes are robust." Skipped (vague).
12. "Their numerical performance is comparable to and in some cases superior to standard ENO schemes." Skipped (vague).
13. "The computational cost of TeCNO schemes is also comparable to the ENO schemes with reconstruction in characteristic variables." Not in population (cost).
14. "The main difference between TeCNO schemes and other existing very-high-order schemes lies in the fact that the TeCNO are rigorously proved to be stable." Item :17.
15. "Hence, we advocate the use of TeCNO schemes on realistic computations of systems of conservation laws." Not in population.
16. "The extension of TeCNO schemes to several space dimensions requires Cartesian meshes." Not in population (scope of the construction, not a scheme property).
17. "We plan to present TeCNO schemes on unstructured meshes in a forthcoming paper." Not in population.

Totals: 17 items, 3 skipped.

---

## `henrick_aslam_powers_2005_mapped`

# Coverage: henrick_aslam_powers_2005_mapped

Text used: `henrick_aslam_powers_2005_mapped` (born-digital journal text layer). Printed journal page = pdf page + 541. The text layer encodes ε as "/C15", minus as "/C0", apostrophes as "/C213", and drops primes ("f0" = f'); ligatures (ﬁ, ﬃ, ﬄ) were expanded. Because of these character fixes every item carries `ocr_normalized`.

The paper has no numbered or named Theorem, Proposition, Lemma or Corollary, so the sampled parts are the abstract and Section 7 (Conclusion).

Section 6 is titled "Summary of WENO and mapped WENO schemes of 3rd to 11th order". It is a technical body section with new results (eq. (60), Table 10), placed before the separate Section 7 Conclusion. I treated it as not in population: the rule's "Summary" means a concluding section, and this paper has a real one. Its content is still used in justifications. (I flagged this as a doubt in my reply.)

## Abstract (p. 542)
1. "In this paper, a new fifth-order weighted essentially non-oscillatory scheme is developed." Item :01. It is framed as "developed", but it attributes a definite order to the scheme.
2. "Necessary and sufficient conditions on the weights for fifth-order convergence are derived; one more condition than previously published is found." Item :02.
3. "A detailed analysis reveals that the version of this scheme implemented by Jiang and Shu [...] is, in general, only third-order accurate at critical points." Item :03.
4. "This result is verified in a simple example." Not in population (describes what is done).
5. "The magnitude of ε, ... and the level of grid resolution are shown to determine the order of the scheme in a non-trivial way." Item :04.
6. "A simple modification of the original scheme is found to be sufficient to give optimal order convergence even near critical points." Item :05.
7. "This is demonstrated using the one-dimensional linear advection equation." Not in population.
8. "Also, four examples utilizing the compressible Euler equations are used to demonstrate the scheme's improved behavior ..." Skipped (vague).

## Section 7 Conclusion (p. 566)
1. "It has been shown that the previously published constraints for fifth-order accurate WENO schemes are incomplete." Item :06.
2. "The extensions to higher orders are similarly afflicted near critical points." Item :07.
3. "Former algorithms for finding these weights do not satisfy this incomplete set of criteria ... (r − 1)th order convergence for smooth flows." Item :08.
4. "Furthermore, an explanation has been given of the dramatic effect that ε ... has on the convergence of WENO5 schemes." Skipped (vague and descriptive).
5. "A correction is given which achieves the full (2r − 1)th order accuracy in the neighborhood of critical points where f' = 0, even for very small ε." Item :09.
6. "Lastly, while it is clear that the improvement described here allows true fifth-order convergence rates ... more modest when flows with embedded discontinuities are considered." Item :10.
7. "Certainly for such flows, side by side comparisons reveal that the predictions of WENO5M are better than those of WENO5." Skipped (vague).
8. "However, in both cases the rate of convergence dramatically drops to no more than first order." Item :11.
9. "Consequently, the improvement for flows with shocks is proportional rather than geometric." Skipped (vague).
10. "While this is often recognized in much of the computational literature, it is as often unrecognized; the enthusiasm ... should be proportionately tempered." Not in population (no scheme property).

Totals: 11 items, 4 skipped.
