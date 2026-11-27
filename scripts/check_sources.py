"""Check vendored Git objects, primitive code and restricted proof source without a network."""
import hashlib
import json
import re
from pathlib import Path
import subprocess
import sys

root = Path(__file__).resolve().parents[1]
vendor = root / "third_party/cinematic-strawberry-compiler"
pins = json.loads((vendor / "SOURCE_BLOBS.json").read_text())
for module, expected in pins.items():
    data = (vendor / Path(*module.split("."))).with_suffix(".lean").read_bytes()
    key = b"blob " + str(len(data)).encode() + b"\0" + data
    assert hashlib.sha1(key).hexdigest() == expected, module
assert len(pins) == len(list((vendor / "PureSFormal").rglob("*.lean")))
for base in [root / "formal/PureS", vendor / "PureSFormal"]:
    for path in base.rglob("*.lean"):
        text = path.read_text()
        assert not re.search(r"^\s*(?:axiom|sorry|admit)\b|\bby\s+(?:sorry|admit)\b|\bsorryAx\b", text, re.M),path
subprocess.run([sys.executable, str(root / "implementation/reference/interpreter_assembly.py")], check=True)
print(f"PASS {len(pins)} Git blobs and proof-source scan")

# The two papers print the same instruction and production tables.
interpreter = json.loads((root / "implementation/reference/universal_register_program.json").read_text())
opcodes = {"H": 0, "I": 1, "B": 2, "J": 3}
primitive_rows = [(address, [opcodes[op], *args])
                  for address, (op, *args) in enumerate(interpreter["instructions"])]
table = (root / "paper/Interpreter_Table.tex").read_text()
printed_rows = [(int(address), list(map(int, fields.split(","))))
                for address, fields in re.findall(r"\\\((\d+)\\\)&\\\(\(([0-9,]+)\)\\\)", table)]
assert printed_rows == primitive_rows and len(printed_rows) == 446, "Printed register instructions"

words = json.loads((root / "examples/cook_productions.json").read_text())
table = (root / "paper/Cook_Table.tex").read_text()
entries = re.findall(r"\\\((\d+)\\mapsto (.*?)\\\)", table)
run = re.compile(r"\\langle (\d+)\\rangle\^\{(\d+)\}")
assert [int(address) for address, _ in entries] == list(range(len(words))) and len(words) == 114
for address, expression in entries:
    if expression == r"\varepsilon":
        word = []
    else:
        assert run.sub("", expression) == "", (address, expression)
        word = [int(symbol) for symbol, count in run.findall(expression) for _ in range(int(count))]
    assert word == words[int(address)], address
print(f"PASS {len(printed_rows)} printed instructions and {len(words)} printed cyclic productions")
