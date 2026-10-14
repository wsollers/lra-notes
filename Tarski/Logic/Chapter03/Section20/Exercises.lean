import Tarski.Logic.Chapter03.Section20.Definitions

/-!
# Tarski, Introduction to Logic, Chapter 3 (On the Theory of Identity), §20 — Exercises

Selected Chapter III exercises on numerical quantifiers (pp. 61–62).

§20 defines only at least one, at most one, exactly one, and at least two;
for the rest it says "in a similar way we explain the meanings of other
expressions of this category" (p. 59). The two below are our answers to
Exercise 9, not Tarski's text.
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

end Tarski.Logic.Chapter03
