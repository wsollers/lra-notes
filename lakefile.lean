import Lake
open Lake DSL

package LRANotes where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.32.1"

@[default_target]
lean_lib Munkres where
  roots := #[`Munkres]

@[default_target]
lean_lib LRANotes where
  roots := #[`LRANotes, `Searcoid, `Bruckner, `Integration]
