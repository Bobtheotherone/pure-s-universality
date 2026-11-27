"""Replay one module at a time to keep the alternative checker within a bounded heap."""
from pathlib import Path
import os
import subprocess
import sys

root = Path(__file__).resolve().parents[1]
binary = str(Path(sys.argv[1]).resolve())
roots = [root / "formal", root / "third_party/cinematic-strawberry-compiler"]
modules = []
for base, package in zip(roots, ["PureS", "PureSFormal"]):
    for source in sorted((base / package).rglob("*.lean")):
        modules.append(".".join(source.relative_to(base).with_suffix("").parts))
total = 0
for module in modules:
    p = subprocess.run(["lake", "env", binary, module], cwd=roots[0],
                       env=dict(os.environ, LEAN_NUM_THREADS="1"),
                       text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    print(f"{module} | exit={p.returncode} | {p.stdout.strip()}", flush=True)
    if p.returncode:
        raise SystemExit(p.returncode)
    total += int(p.stdout.strip().splitlines()[-1].split()[1])
print(f"{len(modules)} source modules; {total} reported declaration replays")
