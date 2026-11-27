"""Fast checks on the class theorems in lean/PhysVerify/Harten.lean (no Lean; the build is in
tests/test_lean.py)."""
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
HARTEN = ROOT / "lean/PhysVerify/Harten.lean"
THEOREMS = ["harten_tvd", "harten_tvd_of_form", "linear_tvd", "upwind_tvd", "monotone_tvd"]


def test_no_sorry_admit_or_axiom():
    src = HARTEN.read_text()
    found = re.findall(r"\b(sorry|admit|axiom|native_decide)\b", src)
    assert not found, found


def test_theorems_present_and_imported():
    src = HARTEN.read_text()
    for name in THEOREMS:
        assert re.search(rf"^theorem {name}\b", src, re.M), name
    assert "import PhysVerify.Harten" in (ROOT / "lean/PhysVerify.lean").read_text().splitlines()
    assert not re.search(r"^import Mathlib$", src, re.M)
