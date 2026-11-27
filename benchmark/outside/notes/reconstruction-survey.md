# Reconstruction survey of the dev half (before reconstruction v3)

Written before any checker change of reconstruction v3, from `dev_readings.json` as it was on main at commit
1e5d001. It lists every dev item whose unformalised entry has `reconstruction` among its reasons (48 items).
For 21 of them `reconstruction` is the primary reason; for 27 it is a further reason behind `multi-d`, `system` or
`not-checkable`. Only the dev half was read. The held-out half was not opened.

Each line gives what the sentence claims and what the checker would need to state it:

- **nothing new**: `reconstruction_order_p` as it is can state it.
- **weight family**: a new WENO weight family.
- **FV**: the finite-volume (cell-average) form. It already exists (`"data": "cell_averages"`, bench spec
  `weno5-js-fv.json`), so no item below needs it as a new mechanism.
- **ENO order**: ENO stencil selection, the order of the selected stencil on smooth data.
- **ENO property**: a property of the ENO selection for *all* data (sign property, jump bound), a statement
  over finitely many grid values, piecewise linear in them.
- **GL decomposition**: a cell-average update fed by polynomials, with a hypothesis on their values at
  Gauss–Lobatto (or other) points: the maximum principle of the cell average under a CFL bound.
- **limiter**: the Zhang–Shu scaling limiter (its accuracy, or the bounds it enforces).
- **DG projection**: DG polynomials as such (they enter here only as "the polynomial p_j", so they fall under GL
  decomposition whenever the claim is about the cell-average step).
- **not reconstruction**: the reconstruction is not what blocks the reading (time stepping, convergence,
  2D, systems, a numerical observation, a missing claim kind).

Fields: A = expected alone, H = expected with hypotheses.

## Primary reason `reconstruction` (21 items)

| item | A / H | what it claims | what it needs |
|---|---|---|---|
| jiang_shu_1995_weno:01 | FALSE / TRUE | WENO of Liu, Osher and Chan built from r-th order ENO is (r+1)-th order | **nothing new** for H: the Liu et al. weights with (2.18) for r = 2 (it coincides with (2.19)) and r = 3 ((2.20), spec `jiang-shu-weno5-liu-fd.json` exists), flux difference, f' != 0, eps -> 0, p = r + 1. A is the same eps-family question as :02 and :05 alone (`family_unspecified`: at a critical point the order falls below r + 1 when eps << IS_k, but not with eps fixed) |
| jiang_shu_1995_weno:03 | FALSE / UNSURE | every WENO scheme converges for smooth solutions | not reconstruction (convergence with Runge–Kutta time stepping) |
| jiang_shu_1995_weno:06 | FALSE / UNSURE | at discontinuities every WENO scheme is r-th order | its own mechanism: discontinuous data (a jump inside a stencil) and what "order at a discontinuity" means; A rests on global L1 rates (numerical) |
| zhang_shu_2010_maxprinciple:01 | FALSE / UNSURE | uniformly high-order FV/DG schemes with a strict maximum principle exist | limiter + time stepping + order of the whole scheme; not one mechanism |
| zhang_shu_2010_maxprinciple:05 | TRUE / TRUE | if every Gauss–Lobatto value of p_j and the neighbouring edge values are in [m, M], the Lax–Friedrichs cell-average step stays in [m, M] under lambda a <= min w_alpha | **GL decomposition** (narrowable to f = u, so a = 1, and degree k = 1, 2, 3, where the Gauss–Lobatto points are rational) |
| zhang_shu_2010_maxprinciple:06 | TRUE / TRUE | the scaling limiter (2.8)-(2.9) is (k+1)-th order accurate | **limiter**: a bound over every polynomial of degree k (max of p over the cell, a compactness constant); its own mechanism |
| zhang_shu_2010_maxprinciple:07 | TRUE / TRUE | the revised scheme is (k+1)-th order and satisfies the maximum principle | **limiter** (order clause, and the bound the limiter enforces at the GL points) + GL decomposition |
| zhang_shu_2010_maxprinciple:11 | FALSE / UNSURE | a general framework for arbitrarily high-order maximum-principle schemes | not one mechanism (limiter, SSP time stepping, order, all k) |
| zhang_shu_2010_maxprinciple:12 | FALSE / TRUE | SSP time stepping keeps the averages in [m, M] if the GL values are, enforced by the limiter | GL decomposition + time stepping (SSP as convex combination) + limiter |
| zhang_shu_2011_survey:01 | FALSE / UNSURE | genuinely high-order FV/DG schemes with a maximum principle were developed | as zhang_shu_2010_maxprinciple:01 |
| zhang_shu_2011_survey:04 | TRUE / TRUE | Theorem 1 of the survey: GL values in [m, M] give u^{n+1} in [m, M] under lambda a <= w_1, any monotone flux | **GL decomposition** (narrowed to f = u with the Lax–Friedrichs flux, one monotone flux) |
| zhang_shu_2011_survey:05 | TRUE / TRUE | the scaling limiter (2.9)-(2.10) is (k+1)-th order accurate | **limiter**, as zhang_shu_2010_maxprinciple:06 |
| zhang_shu_2011_survey:06 | FALSE / UNSURE | an l1-distance identity sum_j abs(u_j - m) preserved by the limited scheme | not reconstruction (claim kind for an l1 identity summed over the grid) |
| zhang_shu_2011_survey:13 | TRUE / TRUE | with p_j(x*_j) and the edge values in [m, M], u^{n+1} in [m, M] under lambda a <= w_1 (x*_j defined by the averaging identity) | **GL decomposition** (p_j(x*_j) is a linear functional of p_j by its definition) |
| heoc_1986_eno3:01 | FALSE / FALSE | an ENO hierarchy of uniformly high-order schemes of arbitrary order | not reconstruction: FALSE rests on the global (cumulative) error, numerically (Shu 1990); the local truncation order of the ENO stencil (**ENO order**) is r, so that reading would verify a FALSE item and is forbidden |
| heoc_1986_eno3:02 | UNSURE / UNSURE | ENO interpolation is high order where the data are smooth and has no Gibbs phenomenon | **ENO order** for the accuracy clause; the no-Gibbs clause needs discontinuous data (as jiang_shu:06) |
| heoc_1986_eno3:03 | TRUE / TRUE | adaptive stencils make the schemes highly nonlinear | claim kind ("nonlinear"; "highly" is vague), ENO of cell averages |
| fjordholm_mishra_tadmor_2012_tecno:06 | UNSURE / UNSURE | k-th order ENO reconstruction has the sign property sign(w^-_{i+1} - w^+_i) = sign(w_{i+1} - w_i) | **ENO property** (for each k a finite statement over 2k grid values; narrowable to k = 2, 3) |
| fjordholm_mishra_tadmor_2012_tecno:07 | UNSURE / UNSURE | (w^-_{i+1} - w^+_i) / (w_{i+1} - w_i) <= C_k | **ENO property** (the supremum of the ratio, per k) |
| fjordholm_mishra_tadmor_2012_tecno:08 | TRUE / TRUE | the ENO reconstruction of the scaled entropy variables has the sign property | **ENO property**, through the paper's identification (3.20) of the scaled reconstruction with plain ENO on the data mu^{i+1} (a bridge), scalar case |
| fjordholm_mishra_tadmor_2012_tecno:11 | FALSE / UNSURE | L-infinity estimate a < u_i(T) < b for scalar TeCNO with a log entropy | not reconstruction (an invariant region of the semi-discrete evolution, on the whole line) |

## `reconstruction` as a further reason (27 items)

| item | primary | what it claims | what it needs beyond the primary |
|---|---|---|---|
| jiang_shu_1995_weno:04 | multi-d | pointwise O(dx^r) convergence of WENO + RK in d dimensions | not reconstruction (convergence, time stepping) |
| zhang_shu_2010_maxprinciple:03 | multi-d | the limiter keeps the maximum principle for 2D incompressible Euler / passive convection | 2D, variable velocity |
| zhang_shu_2010_maxprinciple:09 | multi-d | bounds (4.14)-(4.15) of the formal 1D schemes in the 2D decomposition | 2D, variable velocity |
| zhang_shu_2010_maxprinciple:10 | multi-d | the 2D DG vorticity scheme keeps [m, M] | 2D, variable velocity |
| zhang_shu_2010_maxprinciple:13 | multi-d | DG/ENO/WENO with the limiter satisfy the maximum principle | 2D, time stepping, limiter |
| zhang_shu_2010_maxprinciple:14 | multi-d | same result for 2D incompressible Euler | 2D |
| zhang_shu_2010_maxprinciple:15 | multi-d | same for passive convection with divergence-free velocity | 2D, variable velocity |
| zhang_shu_2010_maxprinciple:17 | not-checkable | SSP multistep gives genuine high order (numerical) | numerical observation |
| zhang_shu_2010_maxprinciple:18 | not-checkable | SSP RK accuracy may degenerate on fine meshes | numerical observation |
| zhang_shu_2011_survey:02 | not-checkable | "main advantages ... easiness for generalization" | vague wording |
| zhang_shu_2011_survey:03 | not-checkable | the same idea gives positivity for Euler, shallow water, Vlasov | existential wording, systems |
| zhang_shu_2011_survey:07 | multi-d | Theorem 1 on rectangles | 2D (GL decomposition in tensor form) |
| zhang_shu_2011_survey:08 | multi-d | sufficient condition on triangles | triangles |
| zhang_shu_2011_survey:09 | system | 1D Euler positivity with GL values in G | system (G = {rho > 0, p > 0} is not an interval); GL decomposition would cover the scalar skeleton only, which loses the point |
| zhang_shu_2011_survey:10 | multi-d | 2D Euler on rectangles | 2D, system |
| zhang_shu_2011_survey:11 | multi-d | 2D Euler on triangles | 2D, system |
| zhang_shu_2011_survey:12 | multi-d | vorticity DG on triangles | 2D, variable velocity |
| zhang_shu_2011_survey:14 | multi-d | Theorem 10 (x* form) on rectangles | 2D |
| zhang_shu_2011_survey:15 | multi-d | Theorem 11 (x* form) on triangles | triangles |
| fjordholm_mishra_tadmor_2012_tecno:01 | system | arbitrarily high-order entropy stable schemes for systems | system, all k |
| fjordholm_mishra_tadmor_2012_tecno:05 | system | the scheme with flux (3.8) satisfies (3.11) | system, semi-discrete entropy inequality with reconstruction |
| fjordholm_mishra_tadmor_2012_tecno:09 | system | TeCNO is (k-1)-th order and entropy stable | system; a scalar order clause would need ENO order inside a flux, plus a semi-discrete order claim |
| fjordholm_mishra_tadmor_2012_tecno:10 | system | weak L2 convergence for linear systems | system, convergence |
| fjordholm_mishra_tadmor_2012_tecno:12 | multi-d | 2D TeCNO order and entropy stability | 2D, system |
| fjordholm_mishra_tadmor_2012_tecno:13 | not-checkable | no tuning parameters, high order, essentially non-oscillatory | vague wording |
| fjordholm_mishra_tadmor_2012_tecno:15 | system | entropy stability follows from the sign property | system, an implication between properties |
| fjordholm_mishra_tadmor_2012_tecno:16 | system | TeCNO converges for linear symmetrizable systems | system, convergence |

## Counts and the choice

Over the 21 primary items:

| needs | items |
|---|---|
| nothing new | 1 (jiang_shu:01, H; A moves to `family_unspecified`) |
| GL decomposition | 3 (zhang_shu_2010:05, zhang_shu_2011:04, :13), all TRUE / TRUE |
| ENO property | 3 (tecno:06, :07 UNSURE / UNSURE; tecno:08 TRUE / TRUE) |
| limiter | 3 (zhang_shu_2010:06, :07, zhang_shu_2011:05) |
| ENO order | 1, partly (heoc:02, accuracy clause only, UNSURE) |
| discontinuous data | 1 (jiang_shu:06) |
| new weight family / FV | 0 |
| not one mechanism or not reconstruction | 9 (jiang_shu:03, zhang_shu_2010:01, :11, :12, zhang_shu_2011:01, :06, heoc:01, heoc:03, tecno:11) |

Of the 27 further-reason items, none would get a reading from a reconstruction mechanism alone: each is also 2D,
a system, or not checkable.

So the cheapest extensions by coverage are, in order: the reading that needs nothing (1 item, 1 scored field), a
GL-decomposition claim (3 items, 6 scored fields), and an ENO-property claim for k = 2, 3 (3 items, 2 scored
fields, and 4 unscored ones). The limiter is the next one (3 items, 6 scored fields), but its claim is a bound
over every polynomial of degree k with a constant from compactness, a mechanism of its own and much larger. The
remaining items each need their own mechanism. The two candidates the brief named come out low: the FV form
already exists and no primary item needs a new weight family, and ENO stencil order covers only the accuracy
clause of one UNSURE item (heoc:02). The one reading where it would have mattered, heoc:01, is forbidden (the
local order is r on a FALSE item).

These extensions are chosen *by dev coverage*. The readings they give are therefore made with a checker tuned on
these items, and are labelled so in DEV_RESULTS. The motivating items, extension by extension:

- reading with nothing new: jiang_shu_1995_weno:01
- GL decomposition (`cell_average_max_principle`): zhang_shu_2010_maxprinciple:05, zhang_shu_2011_survey:04,
  zhang_shu_2011_survey:13
- ENO property (`eno_sign_property`, `eno_jump_ratio_at_most`): fjordholm_mishra_tadmor_2012_tecno:06, :07, :08
