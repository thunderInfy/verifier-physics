# Paper-style scheme claims: what the verifier can and cannot decide

`claims.json` holds 20 sentences about 1D linear-advection and Burgers schemes, written the way
papers and models write them. They are split into 33 readings, each formalized into the named
claims of `physverify/schemes/claims.py` or marked unformalized. Run:

```
uv run python -m physverify.schemes.bench benchmark/scheme-claims/          # about 15 s
```

Result now: **14 match, 19 gaps, 0 wrong decisive verdicts.**

| | expected true | expected false | total |
|---|---|---|---|
| decisive and correct (match) | 7 (all VERIFIED) | 7 (4 REFUTED, 3 REFUTED_EMPIRICALLY) | 14 |
| gap | 12 | 7 | 19 |
| wrong | 0 | 0 | 0 |

The 19 gaps by verdict: 10 UNFORMALIZED (no named claim expresses the reading), 5 UNKNOWN (a named
claim exists but its checks cannot decide), 4 NOT_REFUTED (only empirical evidence exists).

What works: exact structural facts about three-point schemes. That covers flux form,
consistency, positivity of linear schemes on a stated CFL interval, and Tadmor's semi-discrete
inequality for a quadratic entropy. These come out decisive and correct, including when the
scheme is written differently from our own specs: as an update instead of a flux (C14, C15),
with a = 3/2 or a = -1/2 instead of 1, with Engquist–Osher in its integral form (C09), or with
f = u^2 instead of u^2/2 and a declared entropy (C20). False claims are often refuted even when
nothing could verify the true version. Examples: Lax–Wendroff "TVD" (C02), Lax–Wendroff and Roe
"entropy stable" (C03, C10), upwind "unconditionally stable" (C04), and quasilinear upwinding
"captures shocks" (C13).

What does not work is mostly the claims papers make most often: order of accuracy, high-resolution
(wider-stencil) schemes, and stability or monotonicity of nonlinear schemes.

## Gaps, ranked by how often we think claims like these appear in papers

The ranking is our judgement from reading the numerical-methods literature, not a measurement.
Cost estimates are rough, for one person who knows this code base.

### 1. Order of accuracy can never be verified (C01 both readings, C12, C19 readings 1 and 3)

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

### 2. High-resolution schemes can't be written down (C18 both readings)

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

### 3. Stability and monotonicity of nonlinear schemes: no check (C07 all three, C08, C16 reading 2)

"Monotone under CFL ≤ 1", "TVD", "stable under the CFL condition" for Burgers schemes are very
common, and positivity is implemented for linear updates only. C07 shows why this matters. The
sentence "the Rusanov scheme is monotone under max|u| Δt/Δx ≤ 1", which we first expected to be
true, is false for the usual α = max(|uL|, |uR|). Our exact counterexample: at Δt/Δx = 9/10,
H(1, u, -9/10) is 751/4000 at u = 1 and 18011/100000 at u = 101/100. The flux is monotone, and the
scheme with one global α is monotone under λα ≤ 1, but the three-point scheme with local α
needs a smaller step. A human can easily get this wrong, and an exact check would catch it.

**Proposal.**
- An exact *nonlinear monotonicity* check: certify ∂H/∂u_k ≥ 0 for k = -1, 0, 1 on each sign cell
  under the CFL atoms. The sign-cell splitter, the CFL atoms and the certifier already exist for
  Tadmor's check. Where certification fails, give an exact rational counterexample from finite
  differences like the one above.
- A trusted SUFFICIENT row (Crandall–Majda 1980): monotone, conservative and consistent implies
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

### 4. Linear (von Neumann) stability: no check (C04 reading 2, C06)

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

### 5. Entropy claims outside the one-quadratic-entropy fragment (C09 reading 2, C10 reading 2)

"Entropy stable" in papers often means "for all convex entropies" (E-schemes) or "converges to the
entropy solution" for the method of lines. Two concrete gaps:
- The Tadmor check needs one declared quadratic entropy. For scalar laws "entropy stable for every
  convex entropy" is equivalent to the E-flux condition sign(uR - uL)(F(uL, uR) - f(u)) ≤ 0 for u
  between uL and uR (Osher 1984). That is a polynomial inequality in (uL, uR, u) on cells.
- `selects_entropy_solution_semidiscrete` has only a SUFFICIENT row (Tadmor), so a false claim
  can never be refuted (Roe, C10 reading 2). An exact NECESSARY check exists. If uL < uR,
  f(uL) = f(uR) and F(uL, uR) = f(uL), the expansion shock is a steady state of both the
  semi-discrete and the fully discrete scheme, so neither selects the entropy solution. For Burgers
  this is a univariate search over uR = -uL with exact arithmetic. It would turn Roe's and
  Lax–Wendroff's empirical refutations into exact ones.
**Cost:** stationary-expansion-shock check half a day plus two table rows; E-flux check 1 to 2 days
(three variables, interval constraint on u; may need certifier work).

### 6. "Conservative, so shocks move at the right speed" has no exact route (C12)

Papers often say this. The exact conservation check plus the Lax–Wendroff theorem is sufficient
for `correct_shock_speed`, with the premise that the scheme converges. The same kind of premise is
already accepted for Tadmor's row. Today only the empirical shock study bears on the claim. C12 is
also blocked by gap 1 (its first-order clause).
**Cost:** one SUFFICIENT row in `claims.py`, with its premise, plus review. We have not added it:
trusted-table changes are reviewed separately.

### 7. Regimes and norms the spec can't state (C19 reading 2, C18 reading 2; C06's quantifier is under gap 4)

- "First order" for discontinuous solutions is false in L1 (rate O(√Δx), Kuznetsov 1976, sharp by
  Tang and Teng 1995). The order study has only smooth test problems. A square-wave problem is
  easy to add, but it could only ever refute empirically.
- The order study requires L1 *and* L∞ within tolerance together. A paper that claims "second order
  in L1" (true for many limiters away from extrema, false in L∞) can't be stated. The fix is a
  per-norm field in `claims.order`.
**Cost:** half a day each; both stay empirical.

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
  `claims.json` and `bench.py`. Three readings rely on stated bridge lemmas: linear TVD iff
  non-negative coefficients (C02), linear max-norm stability iff non-negative coefficients (C04,
  C05), and positivity sufficient for von Neumann stability (C04, C05). Each lemma is in the
  `bridge` field. They are standard and we are confident in them, but a wrong bridge or a wrong
  relation (`same`, `necessary`, `sufficient`) would give a wrong verdict that the trusted table
  can't catch. Gap 3 proposes moving the TVD lemma into the trusted table.
- C11 maps "converges to the fan on transonic rarefactions" to the general `selects_entropy_solution`
  with relation `same`. The named claim is stronger than the sentence, but its only check is the
  rarefaction study on exactly that data, so a refutation would transfer. It is a judgement call
  and it is recorded in the reading's `why`.
- The C07 expectation differs from the example in the task brief ("Rusanov is monotone under
  CFL ≤ 1: true"). We expect *false* for the local-α reading because of the exact counterexample
  above. The verifier does not decide it either way (gap 3).
- C18 reading 2 cites Osher and Chakravarthy (1984) for "TVD schemes drop to first order at smooth
  extrema" from memory. The fact itself is standard (LeVeque 2002, ch. 6).
- Empirical passes come only from existing specs (C01, C11, C12, C19, and the Engquist–Osher
  rarefaction in C08), whose studies already run at an incommensurate dt/dx. The new specs'
  empirical results are refutations (Lax–Wendroff on Burgers keeps the expansion shock at both
  dt/dx = 2/5 and 37/100).

## Sources

LeVeque, *Finite Volume Methods for Hyperbolic Problems*, CUP 2002 (cited by chapter). Toro,
*Riemann Solvers and Numerical Methods for Fluid Dynamics*, 3rd ed., Springer 2009. Godunov, Mat.
Sb. 47 (1959). Lax and Wendroff, CPAM 13 (1960). Rusanov, USSR J. Comput. Math. Math. Phys. 1
(1961). Harten, Hyman and Lax, CPAM 29 (1976). Kuznetsov, USSR Comput. Math. Math. Phys. 16
(1976). van Leer, JCP 32 (1979). Crandall and Majda, Math. Comp. 34 (1980). Engquist and Osher,
Math. Comp. 36 (1981). Harten, JCP 49 (1983). Harten and Hyman, JCP 50 (1983). Osher, SINUM 21
(1984). Osher and Chakravarthy, SINUM 21 (1984). Tadmor, Math. Comp. 49 (1987). Hou and LeFloch,
Math. Comp. 62 (1994). Tang and Teng, Math. Comp. 64 (1995). Tadmor, Acta Numerica 12 (2003).
