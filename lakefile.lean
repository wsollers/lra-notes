import Lake
open Lake DSL

package LRANotes where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.32.1"

@[default_target]
lean_lib Munkres where
  roots := #[`Munkres, `Common]

@[default_target]
lean_lib LRANotes where
  roots := #[`LRANotes, `Searcoid, `Bruckner, `Bartle, `Zorich, `Laczkovich, `Rudin, `Enderton, `Fefferman,
    `Tao, `Abbott, `Lebl, `Tarski, `Su, `Dieudonne, `Kolmogorov, `Halmos, `Givant, `Axler, `Suppes, `Thurston, `Olmsted, `MendelsonE, `MendelsonB, `Spivak, `Apostol, `Common]

/-- Renders theorem and definition statements as TeX snippets under
`generated/lean/`. Run after `lake build`: `lake exe texexport [Root ...]`. -/
lean_exe texexport where
  root := `Tools.TexExport
  supportInterpreter := true
