#!/usr/bin/env bash
# Build the doc-gen4 documentation site for lra-notes.
#
#   scripts/build-docs.sh
#
# Output: .lake/build/doc/ (open index.html, or serve the folder). doc-gen4 is
# required only under -Kenv=dev, so ordinary `lake build` never fetches it;
# -R makes Lake re-read the lakefile so the option takes effect.
#
# The doc-gen4 pin in lakefile.lean must match lean-toolchain. When Lean or
# mathlib is upgraded, bump it too (see "Upgrading Lean" in the README).
set -euo pipefail

repo="$(cd "$(dirname "$0")/.." && pwd)"
cd "$repo"

lake exe cache get
lake -R -Kenv=dev build LRANotes:docs Munkres:docs
echo "build-docs: .lake/build/doc/index.html"
