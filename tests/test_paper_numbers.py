"""Every reproducibility marker in the paper (papers/scheme-claims/main.tex) names a target that exists:
a pytest test `tests/X.py::name` or a function `paper_numbers.py::name` of papers/scheme-claims/paper_numbers.py.
Static only (the files are parsed, nothing is run), so it is fast."""
import ast
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
PAPER = ROOT / "papers" / "scheme-claims"
TARGET = re.compile(r"\{((?:tests/[\w/]+\.py|paper_numbers\.py)::\w+)\}")


def _functions(path: Path) -> set[str]:
    return {n.name for n in ast.parse(path.read_text()).body if isinstance(n, ast.FunctionDef)}


def test_every_repro_target_resolves():
    tex = re.sub(r"(?<!\\)%.*", "", (PAPER / "main.tex").read_text())       # drop comments
    markers = len(re.findall(r"\\rn\{", tex)) + len(re.findall(r"\\repro\{", tex))
    targets = TARGET.findall(tex)
    assert markers > 0 and len(targets) == markers, "a marker has a target that is not FILE::FUNCTION"
    missing = []
    for t in sorted(set(targets)):
        file, name = t.split("::")
        path = PAPER / file if file == "paper_numbers.py" else ROOT / file
        if not path.is_file() or name not in _functions(path):
            missing.append(t)
    assert not missing, missing
