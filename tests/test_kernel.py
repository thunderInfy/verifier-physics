"""Fast tests for straight-line kernels (no Lean): the loader, the exact evaluator (`run`, the
mirror of Lean's `exec`), `compose` as a cross-check, the ports of the update-map bench, the
step-semantics traps, and the C printer tested differentially against the exact evaluator."""
import json
import random
import shutil
import subprocess
from fractions import Fraction
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parent.parent
KBENCH = sorted((ROOT / "benchmark/kernels").glob("*.json"))
# kernel file -> the update_map file it ports (same integrator, same claims)
PORTS = {"central-quartic-explicit-euler": "central-quartic-explicit-euler",
         "central-quartic-symplectic-euler": "central-quartic-symplectic-euler",
         "central-quartic-verlet": "central-quartic-verlet",
         "oscillator-symplectic-euler": "oscillator-symplectic-euler-map",
         "oscillator-implicit-midpoint": "oscillator-implicit-midpoint-map"}


def _k(stem):
    from physverify.kernel import load_kernel
    return load_kernel(ROOT / f"benchmark/kernels/{stem}.json")


def _spec(**kw):
    spec = {"kind": "kernel", "name": "t", "state": ["q", "p"],
            "symbols": {"q": {"dim": "L"}, "p": {"dim": "L T^-1"}, "w": {"dim": "T^-1"}},
            "program": [{"set": "p", "to": "p - h*w^2*q"}, {"set": "q", "to": "q + h*p"}],
            "domain": ["w > 0"],
            "claims": [{"claim": "update_conserves", "quantity": "(p^2 + w^2*q^2)/2"}]}
    spec.update(kw)
    return spec


def _same(a, b) -> bool:
    from physverify.expr import E
    from physverify.variational import to_ratfn
    return not to_ratfn(E("sub", (a, b)))[0]


def _verdicts(U):
    """The exact routing of every claim: the order verdict, or the planner's certificate kinds."""
    from physverify.tools import variational as P
    from physverify.variational import ORDER_KINDS, judge_order
    return [judge_order(U, c).verdict if c.kind in ORDER_KINDS else [k for k, _ in P.propose(U, c)]
            for c in U.claims]


def _rand_env(K, rng):
    env = {s: Fraction(rng.randint(-7, 7), rng.randint(1, 4)) for s in K.state}
    env.update({s: Fraction(rng.randint(1, 7), rng.randint(1, 4)) for s in K.params()})
    return env


def test_bench_has_the_ports_and_the_traps():
    stems = {p.stem for p in KBENCH}
    assert set(PORTS) | {"central-quartic-adjoint-symplectic-euler", "oscillator-adjoint-symplectic-euler"} <= stems
    for p in KBENCH:
        K = _k(p.stem)
        for raw, c in zip(K.source["claims"], K.claims):
            assert (raw["true"], c.expect) in {(True, "VERIFIED"), (False, "REFUTED"), (True, "UNKNOWN")}
    assert [len(_k(s).program) for s in ("central-quartic-verlet", "oscillator-symplectic-euler")] == [6, 2]


@pytest.mark.parametrize("stem", sorted(PORTS))
def test_port_matches_the_map_form(stem):
    """The program composes to the old map's Φ, and every claim keeps its expected verdict and
    its exact routing."""
    from physverify.variational import load_update
    K, U = _k(stem), load_update(ROOT / f"benchmark/variational/{PORTS[stem]}.json")
    assert K.state == U.state and all(_same(a, b) for a, b in zip(K.phi, U.phi))
    assert [(c.kind, repr(c.quantity), c.p, c.expect) for c in K.claims] == \
        [(c.kind, repr(c.quantity), c.p, c.expect) for c in U.claims]
    assert _verdicts(K) == _verdicts(U)


@pytest.mark.parametrize("path", KBENCH, ids=lambda p: p.stem)
def test_exact_routing_as_expected(path):
    K = _k(path.stem)
    for c, v in zip(K.claims, _verdicts(K)):
        assert v == c.expect if isinstance(v, str) else v == [c.expect.lower()], (c.kind, c.quantity)
        assert K.dims_check(c) == "ok"


def test_loader_rejects_bad_programs():
    from physverify.kernel import load_kernel
    load_kernel(_spec())
    with pytest.raises(ValueError, match="h or a parameter"):
        load_kernel(_spec(program=[{"set": "w", "to": "2*w"}]))
    with pytest.raises(ValueError, match="h or a parameter"):
        load_kernel(_spec(program=[{"set": "h", "to": "h"}]))
    with pytest.raises(ValueError, match="assigned before it"):
        load_kernel(_spec(program=[{"set": "q", "to": "q + h*t"}, {"set": "t", "to": "p"}]))
    with pytest.raises(ValueError, match="exactly the keys"):
        load_kernel(_spec(program=[{"set": "q", "to": "q", "when": "q > 0"}]))
    with pytest.raises(ValueError, match="empty"):
        load_kernel(_spec(program=[]))
    with pytest.raises(ValueError, match="quantity may not mention"):
        load_kernel(_spec(program=[{"set": "t", "to": "q"}], claims=[{"claim": "update_conserves", "quantity": "t"}]))
    with pytest.raises(ValueError, match="domain atoms may not mention"):
        load_kernel(_spec(program=[{"set": "t", "to": "q"}], domain=["t > 0"]))
    with pytest.raises(ValueError, match="unknown claim kind"):
        load_kernel(_spec(claims=[{"claim": "del_equations", "quantity": "q"}]))


def test_layout_temporaries_after_parameters():
    K = _k("central-quartic-explicit-euler")
    assert K.index() == {"x": 0, "y": 1, "px": 2, "py": 3, "h": 4, "k": 5, "tx": 6, "ty": 7}
    assert K.lean_prog().startswith("([(6, (.var 0)), (7, (.var 1)), (0, (.add (.var 0) (.mul (.var 4) (.var 2)))),")
    v, r = K.lean_statement("verified", K.claims[0]), K.lean_statement("refuted", K.claims[0])
    assert "ProgDims [" in v and "KernelVerified ([(6," in v and r.startswith("KernelRefuted ([(6,")
    from physverify.variational import module_of
    assert module_of(K) == "PhysVerify.Kernel"


@pytest.mark.parametrize("path", KBENCH, ids=lambda p: p.stem)
def test_run_agrees_with_compose(path):
    """`run` (sequential, the mirror of `exec`) against the substituted map, at rational points."""
    from physverify.kernel import Junk, qvalue, run
    K = _k(path.stem)
    rng = random.Random(3)
    n = 0
    for _ in range(20):
        env = _rand_env(K, rng)
        try:
            out = run(K.program, env)
            want = [qvalue(e, env) for e in K.phi]
        except Junk:
            continue
        assert [out[z] for z in K.state] == want
        assert all(out[s] == env[s] for s in K.params())          # h and the parameters unchanged
        n += 1
    assert n >= 10


def test_sequential_semantics_by_hand():
    """Symplectic Euler's drift reads the NEW p; with the assignments swapped the kick reads the
    new q, which is the adjoint method and not explicit Euler (that needs temporaries)."""
    from physverify.expr import parse
    se, adj = _k("oscillator-symplectic-euler"), _k("oscillator-adjoint-symplectic-euler")
    assert _same(se.phi[0], parse("q + h*(p - h*w^2*q)")) and _same(se.phi[1], parse("p - h*w^2*q"))
    assert _same(adj.phi[0], parse("q + h*p")) and _same(adj.phi[1], parse("p - h*w^2*(q + h*p)"))
    ee, qadj = _k("central-quartic-explicit-euler"), _k("central-quartic-adjoint-symplectic-euler")
    assert _same(ee.phi[2], parse("px - h*k*(x^2 + y^2)*x"))                     # old q
    assert _same(qadj.phi[2], parse("px - h*k*((x + h*px)^2 + (y + h*py)^2)*(x + h*px)"))   # new q
    assert not _same(ee.phi[2], qadj.phi[2])


def test_trap_defects_by_hand():
    from physverify.expr import E, parse, substitute
    from physverify.variational import defect_expr, update_defect
    K = _k("oscillator-adjoint-symplectic-euler")
    bad, good = K.claims
    want = parse("(-2*h^2*w^2*p^2 + 2*h^2*w^4*q^2 + 4*h^3*w^4*p*q + 2*h^4*w^4*p^2)/2")
    assert _same(defect_expr(K, bad), want)
    assert not update_defect(K, good)[0]
    Q = _k("central-quartic-adjoint-symplectic-euler")
    assert not update_defect(Q, Q.claims[0])[0]
    ee = _k("central-quartic-explicit-euler")
    L = ee.claims[0].quantity
    assert _same(E("sub", (substitute(L, ee.new_state()), L)),
                 parse("h^2*(py*k*(x^2 + y^2)*x - px*k*(x^2 + y^2)*y)"))


def test_junk_is_checked_per_step():
    """A dead temporary 1/(w - w) vanishes from the composed map, but `run` (like Lean's
    `ExecOK`) evaluates it, so no point of the kernel is junk-free and the planner finds no
    refutation point."""
    from physverify.kernel import Junk, load_kernel, run
    from physverify.tools.kernel import kernel_point_ok, kernel_refutation_point
    from physverify.variational import VClaim
    from physverify.expr import parse
    K = load_kernel(_spec(program=[{"set": "t", "to": "1/(w - w)"}, *_spec()["program"]]))
    assert "(w - w)" in repr(K.program[0][1]) and all("(w - w)" not in repr(e) for e in K.phi)
    env = {"q": Fraction(1), "p": Fraction(2), "h": Fraction(1, 2), "w": Fraction(1), "t": Fraction(0)}
    with pytest.raises(Junk):
        run(K.program, env)
    H = VClaim("update_conserves", quantity=parse("(p^2 + w^2*q^2)/2"))
    assert kernel_point_ok(K, H, env) is None and kernel_refutation_point(K, H) is None


def test_dimension_mismatch_reported():
    from physverify.kernel import load_kernel
    K = load_kernel(_spec(program=[{"set": "p", "to": "p - h*q"}, {"set": "q", "to": "q + h*p"}]))
    assert K.dims_check(K.claims[0]).startswith("mismatch")
    K = load_kernel(_spec(program=[{"set": "t", "to": "q + p"}, {"set": "q", "to": "q"}]))
    assert K.dims_check(K.claims[0]).startswith("mismatch: temporary t")
    assert load_kernel(_spec()).dims_check(K.claims[0]) == "ok"


def test_meaning_theorems_exist_in_lean():
    """The kernel's MEANING strings name theorems of Kernel.lean; its claim names are registered."""
    import re

    from physverify import claimkinds
    from physverify.kernel import Kernel
    lean = (ROOT / "lean/PhysVerify/Kernel.lean").read_text()
    for (kind, _), m in Kernel.MEANING.items():
        assert re.search(rf"^theorem {m.split(':', 1)[0].removeprefix('PhysVerify.')}\s", lean, re.M)
        assert "variational" in claimkinds.KINDS[kind]["layers"]


def test_runner_loads_kernels():
    from physverify.kernel import Kernel
    from physverify.variational import load
    assert all(isinstance(load(p), Kernel) for p in KBENCH)


# ---------------------------------------------------------------- C emission

def test_emit_one_statement_per_assignment():
    from physverify.kernel_c import emit
    src = emit(_k("central-quartic-explicit-euler"))
    body = src[src.index("static inline void step"):]
    stmts = [ln.strip() for ln in body.splitlines() if " = " in ln and not ln.strip().startswith("double")]
    assert [s.split(" = ")[0] for s in stmts] == ["t_tx", "t_ty", "z[0]", "z[1]", "z[2]", "z[3]"]
    assert "double t_tx, t_ty;" in body and "#include <math.h>" in src
    assert "z[2] = (z[2] - (((par[0] * par[1]) * (kp_ipow(t_tx, 2) + kp_ipow(t_ty, 2))) * t_tx));" in body
    with pytest.raises(ValueError, match="not printed"):
        from physverify.expr import parse
        from physverify.kernel import load_kernel
        emit(load_kernel(_spec(program=[{"set": "q", "to": "q*exp(h*w)"}])))


CC = shutil.which("cc")
# Start values and parameters are dyadic, so they are exact doubles and the rational reference
# starts from the same point. Steps: N exact rational steps are cheap for linear kernels; for the
# cubic force the rationals triple in size per step, so N = 8.
STARTS = {
    "central-quartic-explicit-euler": ({"x": "1/2", "y": "-3/4", "px": "1/8", "py": "5/16"}, {"h": "1/16", "k": "1/2"}, 8),
    "central-quartic-symplectic-euler": ({"x": "1/2", "y": "-3/4", "px": "1/8", "py": "5/16"}, {"h": "1/16", "k": "1/2"}, 8),
    "central-quartic-verlet": ({"x": "1/2", "y": "-3/4", "px": "1/8", "py": "5/16"}, {"h": "1/16", "k": "1/2"}, 8),
    "central-quartic-adjoint-symplectic-euler": ({"x": "1/2", "y": "-3/4", "px": "1/8", "py": "5/16"}, {"h": "1/16", "k": "1/2"}, 8),
    "oscillator-symplectic-euler": ({"q": "1", "p": "-1/2"}, {"h": "1/32", "w": "3/4"}, 200),
    "oscillator-adjoint-symplectic-euler": ({"q": "1", "p": "-1/2"}, {"h": "1/32", "w": "3/4"}, 200),
    "oscillator-implicit-midpoint": ({"q": "1", "p": "-1/2"}, {"h": "1/32", "w": "3/4"}, 200),
}
# Norm-wise relative error of the compiled C after N steps against the exact rational orbit. Only
# double rounding separates them: about 10-30 roundings of relative size 2^-53 ≈ 1.1e-16 per step,
# carried forward by maps that are near the identity (h ≤ 1/16), so after N ≤ 200 steps we expect
# at most ~N·30·1.1e-16 ≈ 7e-13. The bound is 1e-12; a printing error (a wrong operator, operand
# or statement order) changes the state at O(h) ≫ 1e-12 in one step.
REL_TOL = 1e-12


def _driver(n_state: int, n_par: int) -> str:
    return f"""#include <stdio.h>
#include <stdlib.h>
#include "kernel.h"
int main(int argc, char **argv) {{
    double z[{n_state}], par[{n_par}];
    int N = atoi(argv[1]), a = 2;
    for (int i = 0; i < {n_state}; i++) z[i] = strtod(argv[a++], 0);
    for (int i = 0; i < {n_par}; i++) par[i] = strtod(argv[a++], 0);
    for (int s = 0; s < N; s++) {{
        step(z, par);
        for (int i = 0; i < {n_state}; i++) printf("%a%c", z[i], i + 1 < {n_state} ? ' ' : '\\n');
    }}
    return 0;
}}
"""


def _run_c(K, env, N, tmp_path, src=None):
    from physverify.kernel_c import emit
    (tmp_path / "kernel.h").write_text(src or emit(K))
    (tmp_path / "main.c").write_text(_driver(K.n, len(K.params())))
    exe = tmp_path / "k"
    subprocess.run([CC, "-O2", "-std=c99", "-ffp-contract=off", "-o", str(exe), str(tmp_path / "main.c"), "-lm"],
                   check=True, capture_output=True)
    args = [str(N)] + [float(env[s]).hex() for s in K.state] + [float(env[s]).hex() for s in K.params()]
    out = subprocess.run([str(exe), *args], check=True, capture_output=True, text=True).stdout.split("\n")
    return [[float.fromhex(x) for x in ln.split()] for ln in out if ln]


@pytest.mark.skipif(CC is None, reason="no C compiler (cc) on PATH")
@pytest.mark.parametrize("stem", sorted(STARTS))
def test_c_differential(stem, tmp_path):
    """Compile the emitted kernel with `cc -O2 -std=c99`, run N steps, and compare: every step
    bit for bit with `run_float` (the same double operations in the same order), and the final
    state with the exact rational orbit to REL_TOL."""
    from physverify.kernel import run, run_float
    K = _k(stem)
    z0, par0, N = STARTS[stem]
    env = {s: Fraction(v) for s, v in {**z0, **par0}.items()}
    assert all(float(v) == v for v in env.values())                 # exact doubles
    rows = _run_c(K, env, N, tmp_path)
    assert len(rows) == N
    fenv, qenv = {s: float(v) for s, v in env.items()}, dict(env)
    for row in rows:
        fenv = run_float(K.program, fenv)
        assert row == [fenv[s] for s in K.state]                        # bit for bit, every step
    for _ in range(N):
        qenv = run(K.program, qenv)
    exact = [qenv[s] for s in K.state]
    err = max(abs(Fraction(c) - e) for c, e in zip(rows[-1], exact))
    scale = max(abs(e) for e in exact)
    assert err <= Fraction(REL_TOL) * scale, (stem, float(err / scale))


@pytest.mark.skipif(CC is None, reason="no C compiler (cc) on PATH")
def test_c_differential_catches_a_misordered_printer(tmp_path):
    """The test has teeth: C printed with the two assignments of symplectic Euler swapped (the
    adjoint method) disagrees with the program in the first step, far beyond REL_TOL."""
    from dataclasses import replace

    from physverify.kernel import run
    from physverify.kernel_c import emit
    K = _k("oscillator-symplectic-euler")
    env = {"q": Fraction(1), "p": Fraction(-1, 2), "h": Fraction(1, 32), "w": Fraction(3, 4)}
    bad = emit(replace(K, program=K.program[::-1]))
    (row,) = _run_c(K, env, 1, tmp_path, src=bad)
    exact = run(K.program, env)
    err = max(abs(Fraction(c) - exact[s]) for c, s in zip(row, K.state))
    assert err > Fraction(REL_TOL) * 10 ** 6
