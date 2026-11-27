"""Recheck redistributed module, license and font inventories without network access."""
from pathlib import Path
import hashlib
import json
import subprocess

root = Path(__file__).resolve().parents[1]
inventory = json.loads((root / "THIRD_PARTY_INVENTORY.json").read_text())
modules = inventory["vendor_modules"]
vendor = root / "third_party/cinematic-strawberry-compiler"
pins = json.loads((vendor / "SOURCE_BLOBS.json").read_text())
assert set(pins) == {r["module"] for r in modules}
assert {r["path"] for r in modules} == {str(p.relative_to(root)) for p in (vendor / "PureSFormal").rglob("*.lean")}
for row in modules:
    data = (root / row["path"]).read_bytes()
    assert hashlib.sha256(data).hexdigest() == row["sha256"]
    assert hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest() == pins[row["module"]] == row["source_git_blob"]
    assert row["license"] == "MIT" and (root / row["notice"]).is_file()
assert hashlib.sha256((vendor / "LICENSE").read_bytes()).hexdigest() == inventory["upstream"]["license_sha256"]
for face in inventory["font_subsets"]:
    assert face["notice"] and all((root / f).is_file() for f in face["license_files"])
for pdf in (root / "paper").glob("*.pdf"):
    names = {line.split()[0].split("+",1)[-1].removesuffix("-Identity-H")
             for line in subprocess.check_output(["pdffonts",str(pdf)],text=True).splitlines()[2:]}
    assert names == {face["postscript_name"] for face in inventory["font_subsets"]
                     if f"{inventory['edition']}/paper/{pdf.name}" in face["uses"]}
print(f"PASS {len(modules)} pinned modules, both PDF font inventories and included notices")
