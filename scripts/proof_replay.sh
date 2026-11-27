#!/usr/bin/env bash
set -euo pipefail
set -x
root_dir="$(cd "$(dirname "$0")/.." && pwd)"
cd "$root_dir/formal"
lean --version
lake --version
lake build
lake env lean --run Example.lean
lake env lean --run NumericalExamples.lean
lake env lean NumericalCLI.lean
python3 "$root_dir/scripts/audit.py"
lake env leanchecker --fresh -v CandidateCertificate
if [[ -n "${LEAN4LEAN_BIN:-}" ]]; then
  python3 "$root_dir/scripts/replay_alternate.py" "$LEAN4LEAN_BIN"
fi
