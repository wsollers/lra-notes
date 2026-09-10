import Lake
open Lake DSL

/-!
Minimal Lake project used only while building the reusable dev container image.

Keep dependency declarations here synchronized with the repository manifest. The
ordinary project `lakefile.lean` is available in the opened workspace, so
changes to build targets do not invalidate the expensive environment image.
-/

package LRANotesEnvironment where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.32.1"
