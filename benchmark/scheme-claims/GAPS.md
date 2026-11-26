# Paper-style scheme claims: what the verifier can and cannot decide

`claims.json` holds 22 sentences about 1D linear-advection and Burgers schemes, written the way
papers and models write them. They are split into 40 readings, each formalized into the named
claims of `physverify/schemes/claims.py` or marked unformalized. Run:

```
uv run python -m physverify.schemes.bench benchmark/scheme-claims/          # about 45 s
```

Result now: **30 match, 9 gaps, 1 unscored, 0 wrong decisive verdicts** over 40 readings. History: 14 match,
19 gaps before the monotonicity check and the Crandall–Majda row (gap 3); 17 match, 16 gaps before
the exact order checks for linear schemes; 18 match, 15 gaps over 33 readings once those checks
settled C01 reading 1. The steady non-entropy step check left the counts unchanged but made two
matches exact: C03 and C10 on the fully discrete entropy claim moved from REFUTED_EMPIRICALLY to
REFUTED (see gap 4). Reformalizing readings onto the order and von Neumann checks closed four gaps
(C01 reading 2, C04 reading 2, C19 readings 1 and 3; gaps 2 and 7) and added one reading, C19
reading 4 (upwind's separate space and time orders), which is a gap: 22 match, 12 gaps. Two more
exact checks then closed two expected-false gaps, both now REFUTED: the semi-discrete steady step
(C10 reading 2, gap 4) and stability for every small CFL number (C06, gap 7): 24 match, 10 gaps over
34 readings. Five-point stencils and limiters (gap 1) then made C18 expressible and added six
readings. C18 reading 2 (max-norm order 2 at extrema) is now a match (REFUTED_EMPIRICALLY), and
reading 1 (L1 order 2 without extrema) moved from UNFORMALIZED to NOT_REFUTED, still a gap. The
new readings are C18 reading 3 (pointwise truncation order 2 at smooth extrema: REFUTED, exact), C18
reading 4 (L1 order 2 on sine data: unsettled, unscored), C02 reading 2 (Lax–Wendroff in flux-limiter
form is TVD: REFUTED, exact), C21 (minmod and superbee are TVD on [0, 1]: two VERIFIED) and C22
(superbee is TVD up to 3/2: REFUTED). Result: 30 match, 9 gaps, 1 unscored.

| | expected true | expected false | total |
|---|---|---|---|
| decisive and correct (match) | 15 (all VERIFIED) | 15 (13 REFUTED, 2 REFUTED_EMPIRICALLY) | 30 |
| gap | 7 | 2 | 9 |
| wrong | 0 | 0 | 0 |

One more reading (C18 reading 4) has expected truth "unsettled" and is not scored. The 9 gaps by
verdict: 4 UNFORMALIZED (no named claim expresses the reading), 1 UNKNOWN (a named claim exists but
its checks cannot decide), 4 NOT_REFUTED (only empirical evidence exists).

What works: exact structural facts about three-point schemes. That covers flux form,
consistency, positivity of linear schemes on a stated CFL interval, truncation order, von Neumann
stability and (through Lax–Richtmyer) l2/L1 global order of linear schemes, monotonicity of the
fully discrete update under a stated CFL bound (linear or not), and Tadmor's semi-discrete
inequality for a quadratic entropy. These come out decisive and correct, including when the
scheme is written differently from our own specs: as an update instead of a flux (C14, C15),
with a = 3/2 or a = -1/2 instead of 1, with Engquist–Osher in its integral form (C09), or with
f = u^2 instead of u^2/2 and a declared entropy (C20). False claims are often refuted even when
nothing could verify the true version. Examples: Lax–Wendroff "TVD" (C02), Lax–Wendroff and Roe
"entropy stable" (C03, C10), upwind "unconditionally stable" (C04), and quasilinear upwinding
"captures shocks" (C13).

Limited (high-resolution) schemes of linear advection on five-point stencils now work for TVD, a
local maximum principle and the pointwise truncation order: minmod and superbee are VERIFIED TVD on
[0, 1], and superbee on [0, 3/2], Lax–Wendroff in flux-limiter form and minmod's pointwise second
order at extrema are REFUTED exactly. What does not work is mostly the global order of nonlinear
schemes (empirical only, so a true "second order in L1" stays NOT_REFUTED) and TVD or stability of
nonlinear (Burgers) schemes.

The ranking below was redone after the order and von Neumann checks: order of accuracy, which was
first, is now closed for every linear-scheme reading except separate space and time orders, so
wider stencils move to the top, and von Neumann stability (formerly 4) moves down to 7. Gap 7 is
now closed (C06, through `stable_for_small_cfl`), and so is the semi-discrete half of gap 4. Gap 1
is now closed for limited schemes of linear advection, and the per-norm half of gap 6 with it; we kept
the numbering so that older references stay valid.

## Gaps, ranked by how often we think claims like these appear in papers

The ranking is our judgement from reading the numerical-methods literature, not a measurement.
Cost estimates are rough, for one person who knows this code base.

### 1. High-resolution schemes can't be written down (CLOSED for limited schemes of linear advection: C18, C02 reading 2, C21, C22; open: global order, nonlinear fluxes, WENO)

**Status.** Specs may use `um2, um1, u0, up1, up2` and fluxes F(uLL, uL, uR, uRR); the expression
language has `abs`, `min`, `max` and `minmod` (as |x| = sqrt(x^2), so no new AST node). Conservation
(`telescoping_wide`), consistency, the truncation and von Neumann checks for linear schemes, positivity
and the convergence studies work on the wider stencil. `physverify/schemes/limiters.py` adds sign cells
with certified pruning of lower-dimensional cells and a cover argument (the retained closed cells cover
the state space by construction; every VERIFIED rests on that), a cap (`MAX_CELLS`, past which the
checks give UNKNOWN) and an overlap check (cells agree where they meet). On these cells:
- `tvd_under_cfl`: Harten's incremental form, certified per cell by Farkas identities with multipliers
  polynomial in ν (SUFFICIENT), and an exact periodic state whose total variation grows (NECESSARY).
  Minmod (18 cells) and superbee (50 cells) are VERIFIED on [0, 1]. Superbee on [0, 3/2] is REFUTED
  (TV 2 → 4 at ν = 3/2), and so is Lax–Wendroff in flux-limiter form on [0, 1] (TV 2 → 33/16 at
  ν = 1/4). The checker agrees with the literature range; we did not hard-code it.
- `local_max_principle_under_cfl`: the same certificate (u_i^{n+1} is a convex combination of u_{i-1}
  and u_i), refuted by an explicit state outside its stencil's range.
- `truncation_order_smooth_data`: the per-branch truncation order (SUFFICIENT when every branch has
  order ≥ p) and the exact local truncation error at an explicit polynomial solution (NECESSARY). For
  minmod at U = 1 - x^2/2, x_i = 0: τ = (1 - ν)/4 · dx exactly, so it is REFUTED (C18 reading 3).
- `converges_order_p_l1`, `converges_order_p_linf`: the global error in one named norm, empirical only.
  C18 reading 2 (max norm with extrema) is REFUTED_EMPIRICALLY at dt/dx = 1/2 and at the
  incommensurate 0.37 (observed order 1.3). C18 reading 1 (L1 without extrema, on a C∞ monotone step
  with transmissive boundaries) is NOT_REFUTED at observed order 2.00, and stays a gap: a nonlinear
  scheme has no Lax–Richtmyer theorem.

Still open: the global order of limited schemes (no exact route; a convergence proof for TVD schemes
gives an order only under assumptions we cannot check), limiters on nonlinear fluxes (the Harten check
needs f = a u so that the CFL number is a parameter), MUSCL with a separate reconstruction and Riemann
solver step, and WENO (its weights are rational functions, outside the polynomial fragment).

The original text follows.

MUSCL, minmod, WENO and every TVD limiter use five or more points. Specs are three-point
(`um1, u0, up1`), so "the minmod-limited MUSCL scheme is second order" can't be formalized at all.
This is probably the most common kind of scheme in recent papers.

**Proposal.** Allow stencils `um2..up2` in the spec language. Generalize `telescoping` (the same
argument works for any width), consistency (F(u, ..., u) = f(u)) and the convergence studies, which
only need `_stencil` to roll more neighbours. Tadmor's check is for two-point fluxes. For
reconstructed fluxes the natural exact statement is about the underlying two-point flux plus
reconstruction properties, which is a new claim type. Limiters with min/max become sign cells,
and the number of cells grows quickly.
**Cost:** conservation, consistency and order studies for five-point schemes about 2 days; entropy
and TVD claims for limited schemes are research-sized (weeks).

### 2. Order of accuracy (linear schemes: CLOSED for C01 readings 1–2 and C19 readings 1 and 3; open: C12, C19 reading 4)

**Status.** The exact truncation-order and von Neumann checks for linear schemes are on main
(`physverify/schemes/linear.py`), with a Lax–Richtmyer row for `converges_order_p`. Now VERIFIED:
- C01 reading 1 (Lax–Wendroff conservative and order 2), through the Lax–Richtmyer row.
- C01 reading 2 (Lax–Wendroff truncation error O(dx^2)) and C19 reading 3 (upwind O(dx)), on
  `consistent_order_p`, which is EQUIVALENT to the truncation check. The check needs e_0..e_p = 0
  as identities in ν, i.e. the order holds at every fixed dt/dx; that is the textbook meaning, and
  the bridge says so.
- C19 reading 1 (upwind converges at order 1). Judgement call, recorded in the bridge: for a
  linear scheme "first-order accurate" as a global statement means refinement at fixed dt/dx, the
  combined study, so the reading overrides `claims.order` to `{"combined": 1}` and Lax–Richtmyer's
  scope check applies. The row gives the order in l2 and L1, not L∞, so the reading now says
  "l2 or L1".

Still open:
- C19 reading 4, new: a paper might mean order 1 in Δx and in Δt separately. True (error
  O(Δx + Δt)), but Lax–Richtmyer covers only fixed dt/dx, so only the space and time refinement
  studies bear on it: NOT_REFUTED. An exact route would bound the error by C1 Δx + C2 Δt from the
  truncation terms and stability, which is not a table row.
- C12 (Lax–Friedrichs on Burgers, order 1): nonlinear, so the linear checks are NOT_APPLICABLE and
  the order stays empirical. The Burgers truncation expansion in the original proposal below is
  still the route; even with it, global order for nonlinear schemes has no Lax–Richtmyer theorem.

The original text follows.

Almost every scheme paper says "second-order accurate". There are two readings, and the
verifier can verify neither.
- *Global error on smooth solutions*: `converges_order_p` has only refinement studies (NECESSARY,
  empirical), so the best outcome is NOT_REFUTED. That is by design. A finite study can't prove an
  order.
- *Local truncation error*, which is what "second-order accurate" usually means: no check exists.

**Proposal.** Add an exact truncation-order check. Taylor-expand the update about (x_i, t_n), replace
time derivatives with space derivatives using the PDE, and read off the lowest non-vanishing
order. For linear advection this needs only polynomial arithmetic, which `poly.py` already has. For
Burgers the PDE substitution (u_t = -u u_x, u_tt = ..., Cauchy–Kowalevski) is longer but still
mechanical. Then add a trusted SUFFICIENT row: truncation order p plus exact positivity (stability)
gives global order p for linear schemes (Lax equivalence theorem). The premise is linear,
constant-coefficient and smooth data. For nonlinear schemes no such theorem holds in general, so
global order stays empirical.
**Cost:** linear case 1 to 2 days; Burgers 2 to 3 more; the new row is a one-line table change plus
review.

### 3. Stability and monotonicity of nonlinear schemes (monotonicity: CLOSED for C07 readings 1–2 and C08; open: C07 reading 3, C16 reading 2, TVD)

**Status.** The monotonicity check and the Crandall–Majda row are now on main (`monotonicity` in
`checks.py`, `monotone_under_cfl` and the SUFFICIENT row for `selects_entropy_solution` in
`claims.py`). With them:
- C07 reading 1 (local α, λ max|u| ≤ 1): REFUTED exactly, on main's
  `broken-burgers-rusanov-wide-cfl` spec. The sharp bound the check certifies is 1/3.
- C07 reading 2 (the Rusanov flux is monotone): VERIFIED, through the `sufficient` bridge
  "scheme monotone for every λ > 0 under some CFL bound c > 0 implies the flux is monotone
  everywhere" (choose λ small enough that any given states lie in the CFL box; H depends on
  u_{i-1} only through +λF(u_{i-1}, u_i) and on u_{i+1} only through -λF(u_i, u_{i+1})).
- C08 (Engquist–Osher monotone under λ max|u| ≤ 1, hence entropy limit): VERIFIED; both
  conjuncts are exact, the second through the Crandall–Majda row.

Still open: C07 reading 3 (one global α ≥ max|u| needs a parameter with a side condition on the
data, which the spec cannot state); C16 reading 2 (a fully discrete entropy inequality for *every*
dt/dx is false, and non-monotonicity does not refute it, so only a cell entropy inequality check
could); and TVD for nonlinear schemes (Harten's incremental form, below). C11 cannot be closed
this way: the monotonicity check refutes Roe with Harten's fix (δ = 1/2) as monotone even at
c = 1/10 (exact decreasing pair at λ = 1/3, states (-3/10, 3/20, -3/10)), so the Crandall–Majda
row does not apply there.

The original text follows. "Monotone under CFL ≤ 1", "TVD", "stable under the CFL condition" for Burgers schemes are very
common, and positivity was implemented for linear updates only. C07 shows why this matters. The
sentence "the Rusanov scheme is monotone under max|u| Δt/Δx ≤ 1", which we first expected to be
true, is false for the usual α = max(|uL|, |uR|). Our exact counterexample: at Δt/Δx = 9/10,
H(1, u, -9/10) is 751/4000 at u = 1 and 18011/100000 at u = 101/100. The flux is monotone, and the
scheme with one global α is monotone under λα ≤ 1, but the three-point scheme with local α
needs a smaller step. A human can easily get this wrong, and an exact check would catch it.

**Proposal.**
- (Done.) An exact *nonlinear monotonicity* check: certify ∂H/∂u_k ≥ 0 for k = -1, 0, 1 on each sign cell
  under the CFL atoms. The sign-cell splitter, the CFL atoms and the certifier already exist for
  Tadmor's check. Where certification fails, give an exact rational counterexample from finite
  differences like the one above.
- (Done.) A trusted SUFFICIENT row (Crandall–Majda 1980): monotone, conservative and consistent implies
  `selects_entropy_solution` for the *fully discrete* scheme. Today that claim can never be
  better than NOT_REFUTED. This row would make C08 and the fully discrete parts of the Rusanov,
  Lax–Friedrichs and Engquist–Osher claims VERIFIED.
- TVD through Harten's incremental form (Harten 1983): write
  H = u_i + C_{i+1/2} Δu_{i+1/2} - D_{i-1/2} Δu_{i-1/2} and certify C, D ≥ 0 and C + D ≤ 1. This is
  SUFFICIENT for TVD. For linear schemes we used the lemma "TVD iff all coefficients ≥ 0" as an
  untrusted bridge in C02. It should become a trusted EQUIVALENT row (`tvd` -> positivity, linear
  schemes only).
**Cost:** monotonicity check 2 to 3 days (most of it certifier robustness); Crandall–Majda row
trivial once the check exists; Harten incremental-form TVD 2 days (the split into C and D is not
unique, so we would try the canonical one, C = -λ(F(u_i, u_{i+1}) - F(u_i, u_i))/Δu and so on).

### 4. Entropy claims outside the one-quadratic-entropy fragment (C09 reading 2; C10 reading 2 CLOSED)

**Status.** The semi-discrete steady step is on main: `steady_nonentropy_step` has a second
instantiation, `steady_nonentropy_step_semidiscrete`, with an exact NECESSARY row for
`selects_entropy_solution_semidiscrete`. The step uL | uR, jump at a cell interface, is a steady
state of the method of lines iff F(uL, uL) = F(uL, uR) = F(uR, uR); the check uses that condition
as it stands, so it needs no consistency. Roe without a fix is REFUTED at (-1, 1) (all three
fluxes are 1/2), so C10 reading 2 is now a match. Engquist–Osher, Lax–Friedrichs and Rusanov have
no steady step in the search and stay VERIFIED through Tadmor; a test checks on every spec that a
Tadmor-VERIFIED flux is never refuted by the step check. The E-flux part below is still open.

The original text follows.

"Entropy stable" in papers often means "for all convex entropies" (E-schemes) or "converges to the
entropy solution" for the method of lines. Two concrete gaps:
- The Tadmor check needs one declared quadratic entropy. For scalar laws "entropy stable for every
  convex entropy" is equivalent to the E-flux condition sign(uR - uL)(F(uL, uR) - f(u)) ≤ 0 for u
  between uL and uR (Osher 1984). That is a polynomial inequality in (uL, uR, u) on cells.
- `selects_entropy_solution_semidiscrete` has only a SUFFICIENT row (Tadmor), so a false claim
  can never be refuted (Roe, C10 reading 2). An exact NECESSARY check exists. If uL < uR,
  f(uL) = f(uR) and F(uL, uR) = f(uL), the expansion shock is a steady state of both the
  semi-discrete and the fully discrete scheme, so neither selects the entropy solution. The fully
  discrete half is done: `steady_nonentropy_step` is an exact NECESSARY row for
  `selects_entropy_solution`, and Roe's and Lax–Wendroff's refutations there (C10 reading 1, C03
  reading 2) are now exact. The semi-discrete row (the step is steady when F(uL, uR) = f(uL) =
  f(uR)) is still missing, so C10 reading 2 stays UNKNOWN.
**Cost:** semi-discrete steady-step row an hour or two; E-flux check 1 to 2 days
(three variables, interval constraint on u; may need certifier work).

### 5. "Conservative, so shocks move at the right speed" has no exact route (C12)

Papers often say this. The exact conservation check plus the Lax–Wendroff theorem is sufficient
for `correct_shock_speed`, with the premise that the scheme converges. The same kind of premise is
already accepted for Tadmor's row. Today only the empirical shock study bears on the claim. C12 is
also blocked by gap 2 (its first-order clause).
**Cost:** one SUFFICIENT row in `claims.py`, with its premise, plus review. We have not added it:
trusted-table changes are reviewed separately.

### 6. Regimes and norms the spec can't state (C19 reading 2; the per-norm half CLOSED for C18)

**Status.** The per-norm claims exist now: `claims.order_l1` and `claims.order_linf` feed
`converges_order_p_l1` and `converges_order_p_linf`, which read only their own column of the
combined study. A smooth test problem without extrema (`advection-smooth-step`, a C∞ monotone step
with constant ends and transmissive boundaries, `test.boundary`) and per-spec grids (`test.grids`)
are in `convergence.py`. C18 readings 1, 2 and 4 use them. Both stay empirical. The square-wave half
(C19 reading 2) is still open. The original text follows.

- "First order" for discontinuous solutions is false in L1 (rate O(√Δx), Kuznetsov 1976, sharp by
  Tang and Teng 1995). The order study has only smooth test problems. A square-wave problem is
  easy to add, but it could only ever refute empirically.
- The order study requires L1 *and* L∞ within tolerance together. A paper that claims "second order
  in L1" (true for many limiters away from extrema, false in L∞) can't be stated. The fix is a
  per-norm field in `claims.order`. (For linear schemes the Lax–Richtmyer row now decides the l2
  and L1 order exactly; the gap remains for the refinement studies and for nonlinear schemes.)
**Cost:** half a day each; both stay empirical.

### 7. Linear (von Neumann) stability (CLOSED for C04 reading 2 and C06)

**Status.** The exact von Neumann check is on main (`von_neumann` in `linear.py`, named claim
`von_neumann_stable_under_cfl`, EQUIVALENT row). C04 reading 2 ("upwind is von Neumann stable for
every ν ≥ 0") now uses it on the upwind spec with the range overridden to [0, 2], relation
`necessary` ("every ν ≥ 0" implies the instance [0, 2]): REFUTED exactly, |g|^2 > 1 at a rational
(ν, cos θ) with ν > 1.

C06 is closed by a new claim, `stable_for_small_cfl` ("there is ν0 > 0 with |g| ≤ 1 for all θ and
all ν in (0, ν0]"), with one exact check, `von_neumann_small_cfl`, under an EQUIVALENT row. It
refutes through the lowest term in ν: with G = 1 - |g|^2 = Σ q_k(z) ν^k, if the lowest non-zero q_k
is negative at a rational z0, then G(ν, z0) < 0 for every ν in (0, ν1], with an explicit
ν1 = c/(c + 2M) (c = -q_k(z0), M the largest |q_j(z0)| for j > k) and exact spot values. It verifies
with the Bernstein certificate on [0, ν1] for ν1 = 1, 1/2, ..., 2^-10, and is UNKNOWN otherwise (a
lowest term ≥ 0 with zeros in z settles nothing). FTCS: G = -ν^2 (1 - z^2), z0 = 0, ν1 = 1, so C06
is REFUTED, a match. The refutation covers the max norm too: Fourier modes are eigenvectors of the
update on a periodic grid, so |g| > 1 on an open θ-set grows in every norm once the grid has a
mode there.

The original text follows.

"Stable for ν ≤ 1" in an L2 / von Neumann sense is standard in papers about linear schemes. Today
positivity covers only the *sufficient* direction (non-negative coefficients give |g| ≤ 1). That is
enough to verify Lax–Friedrichs (C05) but cannot refute "upwind is unconditionally L2-stable".
C06, "stable for sufficiently small time steps", also needs an existential over the CFL range,
which the spec cannot state.

**Proposal.** Add an exact von Neumann check. |g(θ)|^2 is a polynomial in c = cos θ ∈ [-1, 1] and ν.
Certify 1 - |g|^2 ≥ 0 on [-1, 1] × [ν_lo, ν_hi] with two-variable Bernstein coefficients, or give
an exact (c, ν) where it fails. For "for some ν0 > 0", check the sign of the lowest-order term in ν
of the failing coefficient or of 1 - |g|^2. A term that is negative for every small ν refutes the
existential exactly.
**Cost:** 1 to 2 days (Bernstein in two variables, a new named claim `stable_von_neumann_under_cfl`
with an EQUIVALENT row).

### 8. The same flux in a different formula gets a different verdict (C17 reading 1)

Godunov's flux for Burgers, transcribed literally as max(f(max(uL, 0)), f(min(uR, 0))) with
max(a, b) = (a + b + |a - b|)/2, gives UNKNOWN for both consistency and entropy stability. The
normalizer leaves √(u^4/4) instead of u²/2, because it only takes square roots of syntactic even
powers. The sign-cell split also produces empty cells (−uL²/2 ≥ 0 with uL ≥ 0) and a quadratic atom
(uL² − uR² ≥ 0) that the linear certifier can't use. Rewritten by hand as max(a, −b)²/2 (reading 2),
the same flux is VERIFIED. This is safe, since UNKNOWN is not a wrong verdict, but an automatic
formalizer would have to search over rewritings. We put it last because it shows up only for
min/max-heavy fluxes. In practice, though, it is the gap a model formalizing claims would hit first.
**Cost:** 1 to 2 days: factor the argument of sqrt into a square before giving up, prune
infeasible cells (an atom −p² ≥ 0 restricts the cell to p = 0), and allow products of cell atoms in
the certificate.

## Soundness notes

- **No wrong decisive verdict.** Every VERIFIED and REFUTED agrees with the expected truth, at the
  reading level and for each component (each component also records the truth of its named claim).
- **The formalization is not trusted code.** The mapping from sentence to named claims lives in
  `claims.json` and `bench.py`. Several readings rely on stated bridge lemmas: linear TVD iff
  non-negative coefficients (C02), linear max-norm stability iff non-negative coefficients (C04,
  C05), positivity sufficient for von Neumann stability (C04, C05), and scheme monotonicity for
  all λ > 0 under a CFL bound sufficient for flux monotonicity (C07 reading 2). The order readings
  add three judgement calls: "truncation error O(dx^p)" means order p at every fixed dt/dx, which
  the truncation check decides as an identity in ν (C01 reading 2, C19 reading 3); "first-order
  accurate" as a convergence statement means refinement at fixed dt/dx in l2 or L1 (C19 reading 1,
  with the separate space and time orders kept as reading 4); and "every ν ≥ 0" is refuted by its
  instance [0, 2] (C04 reading 2). C06 reads "stable (max norm or L2) for sufficiently small time
  steps" as `stable_for_small_cfl`, whose refutation covers both norms (the Fourier-mode argument is
  in the table's premise). Each lemma is in the
  `bridge` field. They are standard and we are confident in them, but a wrong bridge or a wrong
  relation (`same`, `necessary`, `sufficient`) would give a wrong verdict that the trusted table
  can't catch. Gap 3 proposes moving the TVD lemma into the trusted table.
- C11 maps "converges to the fan on transonic rarefactions" to the general `selects_entropy_solution`
  with relation `same`. The named claim is stronger than the sentence, but its only check is the
  rarefaction study on exactly that data, so a refutation would transfer. It is a judgement call
  and it is recorded in the reading's `why`.
- The C07 expectation differs from the example in the task brief ("Rusanov is monotone under
  CFL ≤ 1: true"). We expect *false* for the local-α reading because of the exact counterexample
  above. The verifier now agrees: the monotonicity check refutes it with its own exact
  counterexample and certifies the scheme at the sharp bound 1/3 (gap 3).
- C18 reading 2 cites Osher and Chakravarthy (1984) for "TVD schemes drop to first order at smooth
  extrema" from memory. The fact itself is standard (LeVeque 2002, ch. 6). Our measured max-norm
  order on sine data is about 1.3, not 1, at dt/dx = 1/2, 0.37 and 0.9 up to N = 1600. The reading
  only needs "not 2", so the verdict does not depend on the exact rate, but we have not derived it.
- C18 reading 4 (L1 order 2 on sine data, with extrema) is unsettled on purpose: the measured L1
  order is 1.89–1.95 up to N = 1600 and still rising, and we know no sharp result. It is recorded so
  the number is visible, and it is not scored.
- The limiter readings add bridges: minmod and superbee are written polynomially (no ratio r), and
  superbee's maxmod as max(0, max(m1, m2)) + min(0, min(m1, m2)), equal to it because m1, m2 never have
  opposite signs (C21). The tests replay every limiter witness with the textbook ratio form
  (LeVeque 2002, (6.39)) in exact arithmetic, so a transcription error in the spec would show up there.
  "Order 2 without extrema" is read on one C∞ monotone step at dt/dx = 1/2 (C18 reading 1, relation
  `necessary`).
- Empirical passes come only from existing specs (C01, C11, C12, C19, and the Engquist–Osher
  rarefaction in C08, which now only agrees with the exact Crandall–Majda verification), whose studies already run at an incommensurate dt/dx. The new specs'
  empirical results are refutations (Lax–Wendroff on Burgers keeps the expansion shock at both
  dt/dx = 2/5 and 37/100).

## Sources

LeVeque, *Finite Volume Methods for Hyperbolic Problems*, CUP 2002 (cited by chapter). Sweby,
SINUM 21 (1984). Roe (1985), as cited in LeVeque (2002) ch. 6, for superbee. Toro,
*Riemann Solvers and Numerical Methods for Fluid Dynamics*, 3rd ed., Springer 2009. Godunov, Mat.
Sb. 47 (1959). Lax and Wendroff, CPAM 13 (1960). Rusanov, USSR J. Comput. Math. Math. Phys. 1
(1961). Harten, Hyman and Lax, CPAM 29 (1976). Kuznetsov, USSR Comput. Math. Math. Phys. 16
(1976). van Leer, JCP 32 (1979). Crandall and Majda, Math. Comp. 34 (1980). Engquist and Osher,
Math. Comp. 36 (1981). Harten, JCP 49 (1983). Harten and Hyman, JCP 50 (1983). Osher, SINUM 21
(1984). Osher and Chakravarthy, SINUM 21 (1984). Tadmor, Math. Comp. 49 (1987). Hou and LeFloch,
Math. Comp. 62 (1994). Tang and Teng, Math. Comp. 64 (1995). Tadmor, Acta Numerica 12 (2003).
