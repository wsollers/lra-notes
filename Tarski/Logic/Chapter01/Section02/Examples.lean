import Tarski.Logic.Chapter01.Section02.Definitions

/-!
# Tarski, Introduction to Logic, Chapter 1, §2 — Examples

Reserve this file for the book's worked examples of §2, and for
`counterexample`s showing that a hypothesis cannot be dropped.
-/

namespace Tarski.Logic.Chapter01




namespace Tarski.Logic.Chapter01

namespace Arithmetic

/-! ## Example: Substitution of Constants for Variables -/

/-- The sentential function a + b = 1. -/
def exampleSentence : Sentence :=
  { symbols := [
      ⟨"a"⟩,
      ⟨"+"⟩,
      ⟨"b"⟩,
      ⟨"="⟩,
      ⟨"1"⟩
    ] }

/-- Variables occurring in the sentential function. -/
def variableA : Variable := ⟨⟨"a"⟩⟩
def variableB : Variable := ⟨⟨"b"⟩⟩

/-- Constants used as replacements. -/
def constantZero : Constant := ⟨⟨"0"⟩⟩
def constantOne  : Constant := ⟨⟨"1"⟩⟩

/--
Simultaneous substitution:

  a ↦ 0
  b ↦ 1

  a + b = 1  ↦  0 + 1 = 1
-/
def exampleReplacements : List (Variable × Constant) :=
  [
    (variableA, constantZero),
    (variableB, constantOne)
  ]

def substitutedSentence : Sentence :=
  SentenceConstantReplacer exampleSentence exampleReplacements

#eval substitutedSentence

/-- Verify that substitution produces 0 + 1 = 1. -/
example :
    substitutedSentence.symbols =
      [⟨"0"⟩, ⟨"+"⟩, ⟨"1"⟩, ⟨"="⟩, ⟨"1"⟩] := by
  decide

end Arithmetic

end Tarski.Logic.Chapter01
