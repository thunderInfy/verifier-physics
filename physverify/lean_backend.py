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


def check(statement: str, proof: str, preamble: str = "", timeout: int = 300,
          module: str = "PhysVerify") -> LeanResult:
    """Compile `theorem physverify_certificate : <statement> := by <proof>`.

    `module` is the one PhysVerify module the certificate imports (judge-chosen). Importing
    less than all of Mathlib matters on small machines: a full `import Mathlib` maps ~5 GB.
    """
    if _DENY.search(proof):
        return LeanResult(False, set(), f"certificate rejected by sanitizer: {_DENY.search(proof)[0]!r}")
    body = "\n".join("  " + line for line in proof.strip().splitlines())
    src = (
        f"import {module}\n"
        "open PhysVerify\n\n"
        f"{preamble}\n"
        f"theorem {THM} : {statement} := by\n{body}\n\n"
        f"#print axioms {THM}\n"
    )
    with tempfile.NamedTemporaryFile("w", suffix=".lean", dir=LEAN_DIR / "build_certs",
                                     delete=False) as f:
        f.write(src)
        path = Path(f.name)
    if MODE == "local" and not (LEAN_DIR / ".lake/packages/mathlib").is_dir():
        path.unlink(missing_ok=True)  # don't let `lake` start a multi-GB Mathlib download
        return LeanResult(False, set(), "Mathlib not built: run `lake exe cache get && lake build` in lean/")
    cmd = (["lake", "env", "lean", str(path)] if MODE == "local"
           else [str(ROOT / "tools/vm.sh"), "lean", str(path), str(timeout)])
    try:
        r = subprocess.run(cmd, cwd=LEAN_DIR, env=_env(), capture_output=True, text=True,
                           timeout=timeout + 120)
        log = r.stdout + r.stderr
    except subprocess.TimeoutExpired:
        return LeanResult(False, set(), "timeout")
    except FileNotFoundError as ex:  # no Lean toolchain: no certificate can be checked
        return LeanResult(False, set(), f"Lean not available: {ex}")
    finally:
        path.unlink(missing_ok=True)
    exit_ok = r.returncode == 0 and (MODE == "local" or "EXIT=0" in log)
    if not exit_ok or re.search(r":\d+:\d+: error", log):
        return LeanResult(False, set(), log)
    m = re.search(rf"'{THM}' depends on axioms: \[([^\]]*)\]", log)
    axioms = {a.strip() for a in m.group(1).split(",")} if m else set()
    if not m and f"'{THM}' does not depend on any axioms" not in log:
        return LeanResult(False, set(), "could not read axiom report\n" + log)
    return LeanResult(axioms <= STD_AXIOMS, axioms, log)


(LEAN_DIR / "build_certs").mkdir(exist_ok=True)
