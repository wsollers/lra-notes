import Mathlib.Data.Real.Basic
import Tarski.Logic.Chapter03.Section20.Theorems
import Tarski.Logic.Chapter03.Section20.Exercises

/-!
# Tarski, Introduction to Logic, Chapter 3 (On the Theory of Identity), §20 — Examples

"A few true sentences of arithmetic … in which numerical quantifiers appear"
([p. 59](https://drive.google.com/file/d/1o98AJ7PAh5KMmiSim79q_dmaxvEVYQb9/view#page=84)). Numbers are real numbers, and identity is Lean's `=`.
"Exactly two" is our answer to Exercise 9 (`Exercises.lean`); Tarski uses the
phrase here before defining it.
-/

namespace Tarski.Logic.Chapter03

/-- [Tarski, §20, [p. 59](https://drive.google.com/file/d/1o98AJ7PAh5KMmiSim79q_dmaxvEVYQb9/view#page=84)]: "there is exactly one number x, such that
x + 2 = 5". -/
example : ExactlyOne (@Eq ℝ) (fun x => x + 2 = 5) := by
  sorry

/-- [Tarski, §20, [p. 59](https://drive.google.com/file/d/1o98AJ7PAh5KMmiSim79q_dmaxvEVYQb9/view#page=84)]: "there are exactly two numbers y, such
that y² = 4". -/
example : ExactlyTwo (@Eq ℝ) (fun y => y ^ 2 = 4) := by
  sorry

/-- [Tarski, §20, [p. 59](https://drive.google.com/file/d/1o98AJ7PAh5KMmiSim79q_dmaxvEVYQb9/view#page=84)]: "there are at least two numbers z, such
that z + 2 < 6". -/
example : AtLeastTwo (@Eq ℝ) (fun z => z + 2 < 6) := by
  sorry

end Tarski.Logic.Chapter03
