"""Run the Lean kernel on judge-generated statements with planner-supplied proofs.

The judge writes the theorem *statement*; the (untrusted) planner only supplies the
tactic text after `by`. A certificate is accepted only if Lean compiles it and
`#print axioms` shows nothing beyond Lean's three standard axioms — so `sorry`,
`native_decide`, or new axioms can never authorize a rejection.
"""

from __future__ import annotations

import os
import re
import subprocess
import tempfile
from dataclasses import dataclass
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
LEAN_DIR = ROOT / "lean"
# "local" (default): `lake env lean` in lean/. "vm": a remote build machine via tools/vm.sh.
MODE = os.environ.get("PHYSVERIFY_LEAN", "local")
STD_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
THM = "physverify_certificate"

# Planner text may not touch the environment, only prove the goal.
_DENY = re.compile(
    r"\b(sorry|admit|native_decide|axiom|opaque|unsafe|implemented_by|extern|macro|syntax|"
    r"elab|notation|infix|prefix|postfix|instance|attribute|set_option|import|"
    r"ofReduceBool|ofNat_eq_toNat|run_tac|run_cmd)\b|#|@\[")


@dataclass
class LeanResult:
    ok: bool
    axioms: set[str]
    log: str


def _env() -> dict:
    env = dict(os.environ)
    env["PATH"] = f"{Path.home()}/.elan/bin:" + env.get("PATH", "")
    return env


def _theorem(name: str, statement: str, proof: str) -> str:
    body = "\n".join("  " + line for line in proof.strip().splitlines())
    return f"theorem {name} : {statement} := by\n{body}\n\n#print axioms {name}\n"


def _run(src: str, timeout: int) -> tuple[bool, str]:
    """(exit ok, log) of `lake env lean` on one generated file."""
    if MODE == "local" and not (LEAN_DIR / ".lake/packages/mathlib").is_dir():
        # don't let `lake` start a multi-GB Mathlib download
        return False, "Mathlib not built: run `lake exe cache get && lake build` in lean/"
    with tempfile.NamedTemporaryFile("w", suffix=".lean", dir=LEAN_DIR / "build_certs",
                                     delete=False) as f:
        f.write(src)
        path = Path(f.name)
    cmd = (["lake", "env", "lean", str(path)] if MODE == "local"
           else [str(ROOT / "tools/vm.sh"), "lean", str(path), str(timeout)])
    try:
        r = subprocess.run(cmd, cwd=LEAN_DIR, env=_env(), capture_output=True, text=True,
                           timeout=timeout + 120)
        log = r.stdout + r.stderr
    except subprocess.TimeoutExpired:
        return False, "timeout"
    except FileNotFoundError as ex:  # no Lean toolchain: no certificate can be checked
        return False, f"Lean not available: {ex}"
    finally:
        path.unlink(missing_ok=True)
    return r.returncode == 0 and (MODE == "local" or "EXIT=0" in log), log


def _axioms(name: str, log: str) -> set[str] | None:
    m = re.search(rf"'{re.escape(name)}' depends on axioms: \[([^\]]*)\]", log)
    if m:
        return {a.strip() for a in m.group(1).split(",")}
    return set() if f"'{name}' does not depend on any axioms" in log else None


def check(statement: str, proof: str, preamble: str = "", timeout: int = 300,
          module: str = "PhysVerify") -> LeanResult:
    """Compile `theorem physverify_certificate : <statement> := by <proof>`.

    `module` is the one PhysVerify module the certificate imports (judge-chosen). Importing
    less than all of Mathlib matters on small machines: a full `import Mathlib` maps ~5 GB.
    """
    if _DENY.search(proof):
        return LeanResult(False, set(), f"certificate rejected by sanitizer: {_DENY.search(proof)[0]!r}")
    src = f"import {module}\nopen PhysVerify\n\n{preamble}\n" + _theorem(THM, statement, proof)
    exit_ok, log = _run(src, timeout)
    if not exit_ok or re.search(r":\d+:\d+: error", log):
        return LeanResult(False, set(), log)
    axioms = _axioms(THM, log)
    if axioms is None:
        return LeanResult(False, set(), "could not read axiom report\n" + log)
    return LeanResult(axioms <= STD_AXIOMS, axioms, log)


def check_batch(items: list[tuple[str, str, str]], preamble: str = "", timeout: int = 1800,
                module: str = "PhysVerify", opens: str = "PhysVerify") -> dict[str, LeanResult]:
    """Check many judge-written statements with one `lake env lean`, so the import is paid once.

    items: (theorem name, statement, planner proof). Each result is attributed by its own lines:
    a theorem is accepted only if no error falls inside its declaration and its own `#print axioms`
    shows nothing beyond the standard axioms. An error outside every declaration (the import, the
    preamble) or a non-zero exit with no attributable error rejects every theorem in the file.
    """
    out, src, spans = {}, f"import {module}\nopen {opens}\n\n{preamble}\n", {}
    names = [n for n, _, _ in items]
    if len(set(names)) != len(names) or not all(re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*", n) for n in names):
        raise ValueError("theorem names must be unique identifiers")
    for name, statement, proof in items:
        if _DENY.search(proof):
            out[name] = LeanResult(False, set(), f"certificate rejected by sanitizer: {_DENY.search(proof)[0]!r}")
            continue
        start = src.count("\n") + 1
        src += _theorem(name, statement, proof) + "\n"
        spans[name] = (start, src.count("\n"))
    if not spans:
        return out
    exit_ok, log = _run(src, timeout)
    errors = [int(m.group(1)) for m in re.finditer(r":(\d+):\d+: error", log)]
    stray = [ln for ln in errors if not any(a <= ln <= b for a, b in spans.values())]
    for name, (a, b) in spans.items():
        mine = [ln for ln in errors if a <= ln <= b]
        axioms = _axioms(name, log)
        ok = (not mine and not stray and axioms is not None and axioms <= STD_AXIOMS
              and (exit_ok or bool(errors)))
        out[name] = LeanResult(ok, axioms or set(), log if not ok else "")
    return out


(LEAN_DIR / "build_certs").mkdir(exist_ok=True)
