import Mathlib.Data.Real.Basic
import Tarski.Logic.Chapter03.Section20.Definitions

/-!
# Tarski, Introduction to Logic, Chapter 3 (On the Theory of Identity), §20 — Exercises

Chapter III exercises on numerical quantifiers (pp. 61–62).

§20 defines only at least one, at most one, exactly one, and at least two;
for the rest it says "in a similar way we explain the meanings of other
expressions of this category" (p. 59). `AtMostTwo` and `ExactlyTwo` are our
answers to Exercise 9, and `AtLeastThree`, used in Exercises 10(d) and 13, is
defined the same way. They are not Tarski's text.

**Numbers are real numbers**, and identity between them is Lean's `=`, which
satisfies Leibniz's law (`eq_leibnizLaw`, §17). Where Tarski asks which
sentences are true, each exercise states the answer: the sentence if it is
true, its negation if it is false.

**OCR readings.** The extract garbles `=` and `−` alike as "--", so in
Exercise 10 "x + 3 -- 7 -- x" is read as `x + 3 = 7 - x`, "y + 5 < 11 -- 2y"
as `y + 5 < 11 - 2y`, and "x • y -- 3" as `x * y = 3`. Exercise 11 is left
out: its equation is missing from the extract.
-/

universe u

namespace Tarski.Logic.Chapter03

variable {D : Type u}

/-- **Exercise 9(a)** [Tarski, Ch. III, [p. 61](https://drive.google.com/file/d/1o98AJ7PAh5KMmiSim79q_dmaxvEVYQb9/view#page=86)]: "there are at most
two objects satisfying the given condition". Our answer: among any three
objects satisfying `P`, two are identical. -/
def AtMostTwo (I : D → D → Prop) (P : D → Prop) : Prop :=
  ∀ x y z : D, P x → P y → P z → I x y ∨ I x z ∨ I y z

/-- **Exercise 9(b)** [Tarski, Ch. III, [p. 61](https://drive.google.com/file/d/1o98AJ7PAh5KMmiSim79q_dmaxvEVYQb9/view#page=86)]: "there are exactly
two objects satisfying the given condition". Our answer: at least two and at
most two. -/
def ExactlyTwo (I : D → D → Prop) (P : D → Prop) : Prop :=
  AtLeastTwo I P ∧ AtMostTwo I P

/-- **At least three**, used in Exercises 10(d) and 13 [Tarski, Ch. III,
[pp. 61–62](https://drive.google.com/file/d/1o98AJ7PAh5KMmiSim79q_dmaxvEVYQb9/view#page=86)]: there are `x`, `y`, `z`, pairwise different, that all
satisfy `P`. Defined after Tarski's "at least two". -/
def AtLeastThree (I : D → D → Prop) (P : D → Prop) : Prop :=
  ∃ x y z : D, P x ∧ P y ∧ P z ∧ Different I x y ∧ Different I x z ∧ Different I y z

/-! ### Exercise 10 [Tarski, Ch. III, [p. 61](https://drive.google.com/file/d/1o98AJ7PAh5KMmiSim79q_dmaxvEVYQb9/view#page=86)]: which sentences are true? -/

/-- **Exercise 10(a)**: "there is exactly one number x such that
x + 3 = 7 − x". True: `x = 2`. -/
exercise : ExactlyOne (@Eq ℝ) (fun x => x + 3 = 7 - x) := by
  sorry

/-- **Exercise 10(b)**: "there are exactly two numbers x such that
x² + 4 = 4x". False: `(x − 2)² = 0` has the single root `2`. -/
exercise : ¬ ExactlyTwo (@Eq ℝ) (fun x => x ^ 2 + 4 = 4 * x) := by
  sorry

/-- **Exercise 10(c)**: "there are at most two numbers y such that
y + 5 < 11 − 2y". False: it holds for every `y < 2`. -/
exercise : ¬ AtMostTwo (@Eq ℝ) (fun y => y + 5 < 11 - 2 * y) := by
  sorry

/-- **Exercise 10(d)**: "there are at least three numbers z such that
z² < 2z". True: it holds for every `z` with `0 < z < 2`. -/
exercise : AtLeastThree (@Eq ℝ) (fun z => z ^ 2 < 2 * z) := by
  sorry

/-- **Exercise 10(e)**: "for any number x there is exactly one number y such
that x + y = 1". True: `y = 1 − x`. -/
exercise : ∀ x : ℝ, ExactlyOne (@Eq ℝ) (fun y => x + y = 1) := by
  sorry

/-- **Exercise 10(f)**: "for any number x there is exactly one number y such
that x · y = 3". False: for `x = 0` there is none. -/
exercise : ¬ ∀ x : ℝ, ExactlyOne (@Eq ℝ) (fun y => x * y = 3) := by
  sorry

/-- **Exercise 12** [Tarski, Ch. III, [p. 61](https://drive.google.com/file/d/1o98AJ7PAh5KMmiSim79q_dmaxvEVYQb9/view#page=86)]: "What numbers x satisfy
the sentential function: there are exactly two numbers y such that x = y²?"
Answer: the positive numbers. (The second part, on free and bound variables,
is not a statement to prove.) -/
exercise (x : ℝ) : ExactlyTwo (@Eq ℝ) (fun y => x = y ^ 2) ↔ 0 < x := by
  sorry

/-- **Exercise 13(a)** [Tarski, Ch. III, [p. 62](https://drive.google.com/file/d/1o98AJ7PAh5KMmiSim79q_dmaxvEVYQb9/view#page=87)]: express "there are
x, y, and z such that x < a, y < a, z < a, x ≠ y, x ≠ z, and y ≠ z" using
numerical quantifiers. Answer: there are at least three numbers less than
`a`. (Part (b)'s formula is missing from the extract.) -/
exercise (a : ℝ) :
    (∃ x y z : ℝ, x < a ∧ y < a ∧ z < a ∧ x ≠ y ∧ x ≠ z ∧ y ≠ z) ↔
      AtLeastThree (@Eq ℝ) (fun x => x < a) := by
  sorry

end Tarski.Logic.Chapter03
