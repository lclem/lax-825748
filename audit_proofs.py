#!/usr/bin/env python3
"""Audit the validated Lax proof graph and frozen source files."""

import hashlib
import json
import re
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parent


def read_json(path):
    return json.loads(path.read_text())


def check_hash(name, source, expected):
    if hashlib.sha256(source.encode()).hexdigest() != expected:
        raise RuntimeError(f"Frozen source changed beyond namespace relocation: {name}")


def substitute_tokens(source, mapping):
    pattern = re.compile(r"\b(" + "|".join(map(re.escape, mapping)) + r")\b")
    return pattern.sub(lambda match: mapping[match.group()], source)


def check_sources():
    """Recover the original frozen bytes by undoing packaging-only renames."""
    packaging = read_json(ROOT / "submission-packaging.json")
    modules = packaging["module_renames"]
    original_modules = {new: old for old, new in modules.items()}
    original_tokens = {
        new: old for old, new in packaging["foundation_token_renames"].items()
    }
    for name, expected in read_json(ROOT / "concept-freeze.json").items():
        source = (ROOT / name).read_text()
        if name == "concepts/Lax825748.lean":
            source = "".join(
                line for line in source.splitlines(keepends=True)
                if line.strip().removeprefix("import ") not in original_modules
            )
        check_hash(name, substitute_tokens(source, original_modules), expected)

    snapshot = read_json(ROOT / "foundation-snapshot.json")
    for name, expected in snapshot["files"].items():
        if name in packaging["foundation_original_roots"]:
            source = packaging["foundation_original_roots"][name]
        else:
            kind, module_path = name.split("/", 1)
            old_module = module_path.removesuffix(".lean").replace("/", ".")
            new_path = modules[old_module].replace(".", "/") + ".lean"
            source = substitute_tokens((ROOT / kind / new_path).read_text(), original_tokens)
        check_hash(name, source, expected)

    # Roots must still enumerate exactly their modules, including the foundation.
    for kind, package in [("concepts", "Lax825748"), ("proofs", "Lax825748Proofs")]:
        expected = "".join(
            f"import {package}.{path.stem}\n"
            for path in sorted((ROOT / kind / package).glob("*.lean"))
        )
        if (ROOT / kind / f"{package}.lean").read_text() != expected:
            raise RuntimeError(f"Root module inventory mismatch: {package}")
    return {new for old, new in modules.items() if old.startswith("Lax208278.")}


def main():
    foundation_modules = check_sources()
    if sys.argv[1:] == ["--sources-only"]:
        print("Approved analytic and foundation sources match their original hashes after undoing namespace relocation.")
        return
    outputs = [(ROOT, read_json(ROOT / "build-output.json"))]
    statements, proofs = {}, {}
    for folder, output in outputs:
        for concept in output["concepts"]:
            if (folder / concept["path"]).read_text() != concept["sourceText"]:
                raise RuntimeError(f"Validated concept source mismatch: {concept['id']}")
            for statement in concept["statements"]:
                name = statement["id"]
                if name in statements:
                    raise RuntimeError(f"Duplicate statement: {name}")
                statements[name] = statement
        for proof in output["proofs"]:
            conclusion = proof["conclusion"]
            if conclusion in proofs:
                raise RuntimeError(f"Multiple proofs for this audit: {conclusion}")
            proofs[conclusion] = proof

    missing = set(statements) - set(proofs)
    unknown = {a for p in proofs.values() for a in p["assumptions"]} - set(statements)
    if missing or unknown:
        raise RuntimeError(f"Missing proofs: {sorted(missing)}; unknown assumptions: {sorted(unknown)}")

    closed, layers = set(), []
    while len(closed) < len(statements):
        layer = sorted(
            name for name in statements
            if name not in closed and set(proofs[name]["assumptions"]) <= closed
        )
        if not layer:
            raise RuntimeError(f"Cyclic or unresolved statements: {sorted(set(statements) - closed)}")
        layers.append(layer)
        closed.update(layer)

    own = sum(name.rsplit(".", 1)[0] not in foundation_modules for name in statements)
    print(f"All {own} analytic statements and {len(statements) - own} foundation statements have proofs.")
    print(f"Dependency graph closes in {len(layers)} layers; no cycles or unresolved assumptions.")
    print("Original approved hashes match after undoing namespace relocation; validated concept sources match.")
    for number, layer in enumerate(layers, 1):
        print(f"\nLayer {number}:")
        for name in layer:
            print(f"  {name}")


if __name__ == "__main__":
    main()
