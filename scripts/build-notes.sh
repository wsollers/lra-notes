#!/usr/bin/env bash
# Build TeX study notes against the compiled Lean.
#
#   scripts/build-notes.sh Zorich/RealAnalysisI/Chapter02/notes.tex [more.tex ...]
#
# Steps: lake build -> lake exe texexport -> notation macros -> latexmk (LuaLaTeX).
# PDFs land in build/notes/. lra-common and lra-governance are resolved from
# LRA_COMMON_ROOT / LRA_GOVERNANCE_ROOT, else from sibling checkouts.
set -euo pipefail

repo="$(cd "$(dirname "$0")/.." && pwd)"
cd "$repo"

resolve() {  # resolve <env value> <sibling name> <marker file>
  for c in "$1" "$repo/../$2" "/lra-repos/$2"; do
    if [ -n "$c" ] && [ -e "$c/$3" ]; then (cd "$c" && pwd); return 0; fi
  done
  echo "build-notes: $2 is not present (set the matching *_ROOT variable)" >&2
  return 1
}
common="$(resolve "${LRA_COMMON_ROOT:-}" lra-common common/volume-preamble.tex)"
governance="$(resolve "${LRA_GOVERNANCE_ROOT:-}" lra-governance notation.yaml)"

[ "$#" -gt 0 ] || { echo "usage: $0 path/to/notes.tex ..." >&2; exit 2; }

lake build
lake exe texexport
python3 scripts/notation_macros.py --governance "$governance"

# Trailing ':' keeps TeX's default search path.
export TEXINPUTS="$repo:$repo/tex:$common:"
mkdir -p build/notes
for tex in "$@"; do
  name="$(echo "${tex%.tex}" | tr '/' '-')"
  latexmk -lualatex -interaction=nonstopmode -halt-on-error \
    -outdir=build/notes -jobname="$name" "$tex"
  echo "build-notes: build/notes/$name.pdf"
done
