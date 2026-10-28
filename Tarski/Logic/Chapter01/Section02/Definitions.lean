import Tarski.Logic.Chapter01.Section01.Definitions

/-!
# Tarski, Introduction to Logic, Chapter 1, §2 — Definitions

Reserve this module for the definitions and notation of §2 that the theorems,
examples, and exercises build on.
-/

namespace Tarski.Logic.Chapter01

/--
A sentential function is a sentence containing
at least one variable.
-/
def IsSententialFunction (s : Sentence) : Prop :=
  ∃ v : Variable, v.symbol ∈ s.symbols

/--
A sentential function is a sentence equipped with
evidence that it contains at least one variable.
-/
structure SententialFunction where
  sentence : Sentence
  containsVariable : IsSententialFunction sentence
  deriving Repr, DecidableEq

/-- Replace each variable symbol in a sentence according to a list of
simultaneous variable-to-constant substitutions. -/
def SentenceConstantReplacer
    (sentence : Sentence) (replacements : List (Variable × Constant)) : Sentence :=
  { symbols := sentence.symbols.map fun symbol =>
      match replacements.find? (fun replacement => replacement.1.symbol == symbol) with
      | some replacement => replacement.2.symbol
      | none => symbol }

end Tarski.Logic.Chapter01
