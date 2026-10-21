import Lake
open Lake DSL

package LRANotes where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.32.1"

/- doc-gen4 is needed only to build the documentation site, so it is required
only under `-Kenv=dev`; ordinary `lake build` never fetches it.
Build the docs with `scripts/build-docs.sh`. -/
meta if get_config? env = some "dev" then
require «doc-gen4» from git
  "https://github.com/leanprover/doc-gen4" @ "v4.32.1"

@[default_target]
lean_lib Munkres where
  roots := #[`Munkres, `Common]

@[default_target]
lean_lib LRANotes where
  roots := #[`LRANotes, `Searcoid, `Bruckner, `Bartle, `Zorich, `Laczkovich, `Rudin, `Enderton, `Fefferman,
    `Tao, `Abbott, `Lebl, `Tarski, `Su, `Dieudonne, `Kolmogorov, `Halmos, `Givant, `Axler, `Suppes, `Thurston, `Olmsted, `MendelsonE, `MendelsonB, `Spivak, `Apostol, `Bridger, `Common]

/-- Renders theorem and definition statements as TeX snippets under
`generated/lean/`. Run after `lake build`: `lake exe texexport [Root ...]`. -/
lean_exe texexport where
  root := `Tools.TexExport
  supportInterpreter := true
