#!/usr/bin/env python3
"""Check metadata, verified names, source imports, and the proof-side trust boundary."""
import argparse
import hashlib
import json
from pathlib import Path
import re

import jsonschema
import yaml

ROOT = Path(__file__).resolve().parents[1]
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("schema", type=Path, help="Versioned formalization.yaml JSON schema")
args = parser.parse_args()
metadata = yaml.safe_load((ROOT / "formalization.yaml").read_text())
schema_bytes = args.schema.read_bytes()
jsonschema.validate(metadata, json.loads(schema_bytes))
print(f"Validated {metadata['version']} with schema SHA-256 {hashlib.sha256(schema_bytes).hexdigest()}")
checked = json.loads((ROOT / "comparator.components.json").read_text())
overall = json.loads((ROOT / "comparator.json").read_text())
permitted = {"propext", "Classical.choice", "Quot.sound"}
for config in [checked, overall]:
    assert set(config["permitted_axioms"]) == permitted
    assert len(config["theorem_names"]) == len(set(config["theorem_names"]))
assert {result["declaration"] for result in metadata["status"]["main_results"]} == set(overall["theorem_names"])
assert set(overall["theorem_names"]) <= set(checked["theorem_names"])
for result in metadata["status"]["main_results"]:
    assert result["comparator_config"] == "comparator.json"
    assert result["declaration"] in checked["theorem_names"]
    assert result["sorry_count"] == 0 and set(result["axioms"]) <= permitted
    print(f"Metadata result {result['declaration']}")
def lean_code(source):
    """Discard comments and string literals before the supplementary text scan."""
    tokens = re.compile(r'/-|-/|--[^\n]*|"(?:\\.|[^"\\])*"|[^/"\-]+|.', re.S)
    depth = 0
    kept = []
    for token in tokens.findall(source):
        if token == "/-":
            depth += 1
        elif token == "-/" and depth:
            depth -= 1
        elif not depth:
            kept.append(token if not token.startswith(("--", '"')) else " ")
        if depth or token == "-/":
            kept.append("\n" * token.count("\n") + " ")
    return "".join(kept)


# Challenge uses fully qualified namespace blocks and explicit theorem commands.
challenge_names = set()
for namespace, body in re.findall(
    r"^namespace ([\w.]+)\s*$(.*?)^end \1$", lean_code((ROOT / "Challenge.lean").read_text()), re.M | re.S
):
    for name in re.findall(r"^theorem (\w+)", body, re.M):
        challenge_names.add(f"{namespace}.{name}")
assert challenge_names == set(checked["theorem_names"]), "Challenge and component inventories differ"
modules = {path.stem for path in (ROOT / "LpGowers").glob("*.lean")}
todo = [ROOT / "Solution.lean", ROOT / "LpGowers.lean", ROOT / "GeometricBrascampLieb.lean"]
audited = set()
code_pattern = re.compile(r"\b(sorry|admit|sorryAx|native_decide|implemented_by)\b|^\s*(?:private |public )?axiom\s+", re.M)
imports = re.compile(r"^(?:public )?import (\S+)", re.M)
while todo:
    path = todo.pop()
    if path in audited:
        continue
    audited.add(path)
    source = lean_code(path.read_text())
    if code_pattern.search(source):
        raise ValueError(f"Unexpected proof-side trust marker in {path.name}")
    for name in imports.findall(source):
        if name == "Challenge":
            raise ValueError(f"Challenge imported in {path.name}")
        if name.startswith(("LpGowers.", "GeometricBrascampLieb.")):
            todo.append(ROOT / (name.replace(".", "/") + ".lean"))
for folder in ("LpGowers", "GeometricBrascampLieb"):
    missing = set((ROOT / folder).glob("*.lean")) - audited
    assert not missing, f"Unreached modules: {sorted(path.name for path in missing)}"
reports = set(re.findall(r"^#print axioms (\S+)", (ROOT / "Axioms.lean").read_text(), re.M))
assert set(checked["theorem_names"]) <= reports
print(f"Reached all {len(modules)} LpGowers modules from Solution and the umbrella library")
print(f"Scanned all {len(list((ROOT / 'GeometricBrascampLieb').glob('*.lean')))} vendored proof modules")
inputs = sorted([*ROOT.rglob("*.lean")], key=lambda path: path.relative_to(ROOT).as_posix())
digest = hashlib.sha256()
for path in inputs:
    relative = path.relative_to(ROOT)
    if any(part.startswith(".") for part in relative.parts):
        continue
    digest.update(relative.as_posix().encode() + b"\0" + hashlib.sha256(path.read_bytes()).digest())
print(f"Lean source inventory SHA-256 {digest.hexdigest()}")
print(f"{len(checked['theorem_names'])} compared declarations, each with a printed axiom report")
print(f"{len(overall['theorem_names'])} full targets configured")
print("Proof-side trust markers and imports of Challenge: zero")
print("Metadata and inventory checks passed")
