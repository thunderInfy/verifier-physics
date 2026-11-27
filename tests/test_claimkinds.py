"""The claim-kind registry (physverify/claimkinds.py) against every layer, the bench files,
the Lean library and the README. Fast: no Lean."""

import inspect
import json
import re
from pathlib import Path

from physverify import claimkinds, conserved, derivation, obligations, reconstruction, variational
from physverify.claimkinds import KINDS, LAYERS
from physverify.schemes import bench as scheme_bench, claims as scheme_claims

ROOT = Path(__file__).resolve().parent.parent
# directory -> layer of the claim names its JSON files use
FILES = {"schemes": "schemes", "benchmark/scheme-claims": "schemes", "benchmark/outside": "schemes",
         "benchmark/variational": "variational", "benchmark/reconstruction": "reconstruction"}


def _names_in(obj):
    """Every claim name in a JSON value: `"claim": name` and the items of `"named_claims"`."""
    if isinstance(obj, dict):
        if isinstance(obj.get("claim"), str):
            yield obj["claim"]
        yield from obj.get("named_claims", [])
        for v in obj.values():
            yield from _names_in(v)
    elif isinstance(obj, list):
        for v in obj:
            yield from _names_in(v)


def file_usage() -> dict[str, set[str]]:
    used = {layer: set() for layer in LAYERS}
    for d, layer in FILES.items():
        for p in sorted((ROOT / d).rglob("*.json")):
            names = set(_names_in(json.loads(p.read_text())))
            if d == "benchmark/outside":    # the dev readings also use the reconstruction layer's claim
                used["reconstruction"] |= names & set(reconstruction.CLAIMS)
                names -= set(reconstruction.CLAIMS)
            used[layer] |= names
    for p in sorted((ROOT / "claims").rglob("*.json")):    # these files carry a kind, not a claim name
        spec = json.loads(p.read_text())
        used["conserved" if conserved.is_conserved(spec) else "derivation"].add(
            conserved.KIND if conserved.is_conserved(spec) else derivation.KIND)
    return used


def code_usage() -> dict[str, set[str]]:
    return {"schemes": set(scheme_claims.CLAIMS),
            "variational": set(variational.KINDS) | set(variational.UPDATE_KINDS),
            "conserved": {conserved.KIND}, "derivation": {derivation.KIND},
            "theory": set(obligations.KINDS), "reconstruction": set(reconstruction.CLAIMS)}


def usage() -> dict[str, set[str]]:
    code, files = code_usage(), file_usage()
    return {layer: code[layer] | files[layer] for layer in LAYERS}


def test_every_used_name_is_registered_and_every_entry_used():
    used = usage()
    every = set().union(*used.values())
    assert sorted(every - set(KINDS)) == []
    assert sorted(set(KINDS) - every) == []
    # a bench file may only use names its layer's code knows
    code, files = code_usage(), file_usage()
    assert {layer: sorted(files[layer] - code[layer]) for layer in LAYERS} == {layer: [] for layer in LAYERS}


def test_layers_match_usage():
    used = usage()
    for name, k in KINDS.items():
        assert sorted(k["layers"]) == sorted(layer for layer in LAYERS if name in used[layer]), name


def test_entries_are_well_formed():
    for name, k in KINDS.items():
        assert set(k) == {"gloss", "quantifier", "layers", "meaning", "params"}, name
        assert k["gloss"] and k["quantifier"] and "\n" not in k["gloss"] + k["quantifier"], name
        assert k["layers"] and set(k["layers"]) <= set(LAYERS), name
        assert isinstance(k["params"], dict), name
        for label, keys in k["params"].items():
            assert keys and set(keys) <= set(k["layers"]), (name, label)
            for layer, key in keys.items():
                assert key.startswith(ROOTS[layer]), (name, label, key)


def test_theory_kinds_match_the_obligation_table():
    assert set(obligations.KINDS) == set(re.findall(r'kind == "(\w+)"', inspect.getsource(obligations._build)))


def test_order_kinds_have_order_params():
    for name in variational.ORDER_KINDS:
        assert KINDS[name]["params"]["p"]["variational"] == "claims[].p", name


# how each layer's param keys start (claimkinds docstring, `params`), and the code that reads them
ROOTS = {"schemes": "claims.", "variational": "claims[].", "theory": "args.", "reconstruction": "claims[]."}
SOURCES = {"schemes": sorted((ROOT / "physverify/schemes").glob("*.py")),
           "variational": [ROOT / "physverify/variational.py"],
           "theory": [ROOT / "physverify/obligations.py", *sorted((ROOT / "physverify/tools").glob("*.py"))],
           "reconstruction": [ROOT / "physverify/reconstruction.py", ROOT / "physverify/cellaverage.py",
                              ROOT / "physverify/eno.py", ROOT / "physverify/limiter.py"]}


def _params(layer: str):
    """(claim name, param label, key without the root, optional) for every param `layer` reads."""
    for name, k in KINDS.items():
        for label, keys in k["params"].items():
            if layer in keys:
                key = keys[layer].removeprefix(ROOTS[layer])
                yield name, label, key.rstrip("?"), key.endswith("?")


def test_param_keys_are_read_by_their_layer():
    """Every component of a param key is read, as a string literal, in the layer's code."""
    for layer, paths in SOURCES.items():
        code = "\n".join(p.read_text() for p in paths)
        for name, label, key, _ in _params(layer):
            for part in key.split("."):
                assert f'"{part}"' in code, (layer, name, label, part)


def _lookup(obj, key: str) -> bool:
    for part in key.split("."):
        if not isinstance(obj, dict) or part not in obj:
            return False
        obj = obj[part]
    return True


def _scheme_specs():
    """(where, spec) for every scheme spec: the files (and specs nested in them), and every component
    of the claims benchmark as the bench builds it (base spec plus override)."""
    def walk(obj, where):
        if isinstance(obj, dict):
            if "named_claims" in obj:
                yield where, obj
            for k, v in obj.items():
                yield from walk(v, f"{where}/{k}")
        elif isinstance(obj, list):
            for i, v in enumerate(obj):
                yield from walk(v, f"{where}[{i}]")
    for d in ("schemes", "benchmark/scheme-claims/specs"):
        for p in sorted((ROOT / d).rglob("*.json")):
            yield from walk(json.loads(p.read_text()), str(p.relative_to(ROOT)))
    base = ROOT / "benchmark/scheme-claims"
    for c in scheme_bench.components(json.loads((base / "claims.json").read_text())):
        if "unformalized" not in c:
            yield (f"claims.json: {c['spec']} {c.get('override', {})}",
                   scheme_bench._spec(base, c["spec"], c.get("override", {}), [c["claim"]]))


# (where, claim name) -> why a spec using the claim may lack a param key; none today
PARAM_EXCEPTIONS: dict[tuple[str, str], str] = {}


def test_specs_declare_the_param_keys_their_claims_read():
    want = {}
    for name, label, key, optional in _params("schemes"):
        if not optional:
            want.setdefault(name, []).append(key)
    missing = [(where, n, key) for where, spec in _scheme_specs() for n in spec["named_claims"]
               for key in want.get(n, []) if not _lookup(spec.get("claims", {}), key) and (where, n) not in PARAM_EXCEPTIONS]
    for layer in ("variational", "reconstruction"):
        want = {}
        for name, label, key, optional in _params(layer):
            if not optional:
                want.setdefault(name, []).append(key)
        for p in sorted((ROOT / f"benchmark/{layer}").rglob("*.json")):
            for c in json.loads(p.read_text())["claims"]:
                missing += [(p.name, c["claim"], key) for key in want.get(c["claim"], []) if not _lookup(c, key)]
    assert missing == []


def test_theory_tools_fill_the_param_args():
    """Each planning tool names an obligation with exactly the args the registry lists for it."""
    code = "\n".join(p.read_text() for p in SOURCES["theory"])
    made = re.findall(r'Candidate\(NAME, "(\w+)", \{([^}]*)\}', code)
    assert {k for k, _ in made} == set(obligations.KINDS)
    for kind, args in made:
        assert sorted(re.findall(r'"(\w+)":', args)) == sorted(KINDS[kind]["params"]), kind


def test_meaning_theorems_exist_in_lean():
    lean = "\n".join(p.read_text() for p in sorted((ROOT / "lean/PhysVerify").rglob("*.lean")))
    for name, k in KINDS.items():
        if k["meaning"] is not None:
            assert re.search(rf"^theorem {re.escape(k['meaning'])}\s", lean, re.M), (name, k["meaning"])


def test_layer_meanings_agree_with_the_registry():
    """Where a layer names the Lean theorem behind a VERIFIED verdict, it is the registry's."""
    said = {c: m.split(":", 1)[0].removeprefix("PhysVerify.")
            for (c, v), m in variational.MEANING.items() if v == variational.VERIFIED}
    said["conserved"] = conserved.MEANING[conserved.VERIFIED].split(":", 1)[0].removeprefix("PhysVerify.")
    said["el_equations"] = derivation.MEANING[derivation.VERIFIED].split(":", 1)[0].removeprefix("PhysVerify.")
    assert {c: KINDS[c]["meaning"] for c in said} == said


def test_require_rejects_unregistered_or_wrong_layer():
    claimkinds.require("variational", ["consistent_order_p"])
    for layer, names in (("schemes", ["not_a_claim"]), ("schemes", ["update_conserves"])):
        try:
            claimkinds.require(layer, names)
        except ValueError:
            continue
        raise AssertionError((layer, names))


def test_readme_glossary_matches():
    text = (ROOT / "README.md").read_text()
    assert claimkinds.readme_block(text) == claimkinds.table(), \
        "README claim-kinds table drifted: run uv run python -m physverify.claimkinds --write"
