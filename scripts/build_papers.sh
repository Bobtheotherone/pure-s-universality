#!/usr/bin/env bash
set -euo pipefail
paper_dir="$(cd "$(dirname "$0")/../paper" && pwd)"
cd "$paper_dir"
export SOURCE_DATE_EPOCH=1795651200
font_flags=()
if command -v kpsewhich >/dev/null; then
  tex_tree="$(kpsewhich -var-value=TEXMFDIST || true)"
  if [[ -f "$tex_tree/tex/latex/amscls/amsart.cls" ]]; then
    font_flags+=(-Z "search-path=$tex_tree/tex/latex/amscls")
  fi
  for sample in lmroman9-bold.otf cmtt9.tfm cmtt9.pfb msbm10.tfm eufm10.tfm; do
    asset="$(kpsewhich "$sample" || true)"
    if [[ -n "$asset" ]]; then font_flags+=(-Z "search-path=$(dirname "$asset")"); fi
  done
fi
for doc in Universal_Pure_S Symbolic_Complete_Proof; do
  tectonic "${font_flags[@]}" --keep-logs "$doc.tex"
done
