#!/usr/bin/env python3
"""Audit the validated Lax proof graph and frozen source files."""

import hashlib
import json
from pathlib import Path


ROOT = Path(__file__).resolve().parent


def read_json(path):
    return json.loads(path.read_text())


def check_hashes(root, files):
    for name, expected in files.items():
        actual = hashlib.sha256((root / name).read_bytes()).hexdigest()
        if actual != expected:
            raise RuntimeError(f"Frozen source changed: {root / name}")


def main():
    check_hashes(ROOT, read_json(ROOT / "concept-freeze.json"))
    snapshot = read_json(ROOT / "foundation-snapshot.json")
    foundation = (ROOT / snapshot["snapshot"]).resolve()
    check_hashes(foundation, snapshot["files"])
    outputs = [
        (foundation, read_json(foundation / "build-output.json")),
        (ROOT, read_json(ROOT / "build-output.json")),
    ]
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

    own = sum(name.startswith("Lax825748.") for name in statements)
    print(f"All {own} analytic statements and {len(statements) - own} foundation statements have proofs.")
    print(f"Dependency graph closes in {len(layers)} layers; no cycles or unresolved assumptions.")
    print("Approved concept hashes, foundation hashes, and validated concept sources match.")
    for number, layer in enumerate(layers, 1):
        print(f"\nLayer {number}:")
        for name in layer:
            print(f"  {name}")


if __name__ == "__main__":
    main()
