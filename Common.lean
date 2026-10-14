import Lean.Parser.Command

/-!
# Shared Note Commands

This module provides small command aliases for textbook-facing declarations.
Lean still elaborates these declarations as ordinary theorems; the aliases are
only a readability layer for the notes.
-/

open Lean

/-- `proposition` is a textbook-facing synonym for `theorem`. -/
syntax (name := propositionCommand) declModifiers
  group("proposition " declId ppIndent(declSig) declVal) : command

@[macro propositionCommand] def expandProposition : Macro := fun stx =>
  let stx := stx.modifyArg 1 fun stx =>
    let stx := stx.modifyArg 0 (mkAtomFrom · "theorem" (canonical := true))
    stx.setKind ``Parser.Command.theorem
  pure <| stx.setKind ``Parser.Command.declaration

/-- `corollary` is a textbook-facing synonym for `theorem`. -/
syntax (name := corollaryCommand) declModifiers
  group("corollary " declId ppIndent(declSig) declVal) : command

@[macro corollaryCommand] def expandCorollary : Macro := fun stx =>
  let stx := stx.modifyArg 1 fun stx =>
    let stx := stx.modifyArg 0 (mkAtomFrom · "theorem" (canonical := true))
    stx.setKind ``Parser.Command.theorem
  pure <| stx.setKind ``Parser.Command.declaration

/-- `named_exercise` is a textbook-facing synonym for a named `theorem`: an
exercise whose result later declarations cite. -/
syntax (name := namedExerciseCommand) declModifiers
  group("named_exercise " declId ppIndent(declSig) declVal) : command

@[macro namedExerciseCommand] def expandNamedExercise : Macro := fun stx =>
  let stx := stx.modifyArg 1 fun stx =>
    let stx := stx.modifyArg 0 (mkAtomFrom · "theorem" (canonical := true))
    stx.setKind ``Parser.Command.theorem
  pure <| stx.setKind ``Parser.Command.declaration

/-- `exercise` is a textbook-facing synonym for an anonymous `example`: an
exercise checked once and never cited. Use `named_exercise` for one that is. -/
syntax (name := exerciseCommand) declModifiers
  group("exercise " ppIndent(optDeclSig) declVal) : command

@[macro exerciseCommand] def expandExercise : Macro := fun stx =>
  let stx := stx.modifyArg 1 fun stx =>
    let stx := stx.modifyArg 0 (mkAtomFrom · "example" (canonical := true))
    stx.setKind ``Parser.Command.example
  pure <| stx.setKind ``Parser.Command.declaration

/-- `counterexample` is a textbook-facing synonym for an anonymous `example`. -/
syntax (name := counterexampleCommand) "counterexample " ":" term " := " term : command

macro_rules
  | `(counterexample : $ty:term := $val:term) =>
      `(example : $ty :=$val)
