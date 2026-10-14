import Tarski.Logic.Chapter03.Section20.Observations

/-!
# Tarski, Introduction to Logic, Chapter 3 (On the Theory of Identity), §20 — Theorems

Reserve this file for the theorems of §20 and their proofs. Prose notes
belong in the chapter's notes.tex.
-/

universe u

namespace Tarski.Logic.Chapter03

variable {D : Type u}

/-- **At least two is not at most one** [Tarski, §20, [p. 59](https://drive.google.com/file/d/1o98AJ7PAh5KMmiSim79q_dmaxvEVYQb9/view#page=84)]: "there
are at least two objects satisfying the given condition" is "equivalent to the
negation of: there is at most one object satisfying the given condition". It
needs no law of identity, only classical logic. -/
theorem atLeastTwo_iff_not_atMostOne (I : D → D → Prop) (P : D → Prop) :
    AtLeastTwo I P ↔ ¬ AtMostOne I P := by
  sorry

end Tarski.Logic.Chapter03
