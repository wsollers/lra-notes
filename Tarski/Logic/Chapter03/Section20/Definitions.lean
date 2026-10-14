import Tarski.Logic.Chapter03.Section19

/-!
# Tarski, Introduction to Logic, Chapter 3 (On the Theory of Identity), §20 — Definitions

§20, "Numerical quantifiers" ([pp. 58–59](https://drive.google.com/file/d/1o98AJ7PAh5KMmiSim79q_dmaxvEVYQb9/view#page=83)): with the concept of
identity, phrases such as "there is at least one, or at most one, or exactly
one, object x such that…" and "there are at least two, or at most two, or
exactly two, objects x such that…" get a precise, purely logical meaning.
Tarski writes them in words, with no special symbol, and gives no general
`n` case.

The text defines at least one, at most one, exactly one, and at least two.
"At most two" and "exactly two" are left to Exercise 9; see `Exercises.lean`.

**Identity is the primitive `I`.** As in §17, identity is a relation
`I : D → D → Prop`, not Lean's `=`, so each numerical quantifier is stated
through `I`; `x ≠ y` is written `¬ I x y`. None of these definitions assumes
`LeibnizLaw I`; theorems about them take it as a hypothesis.
-/

universe u

namespace Tarski.Logic.Chapter03

variable {D : Type u}

/-- **At least one** [Tarski, §20, [p. 58](https://drive.google.com/file/d/1o98AJ7PAh5KMmiSim79q_dmaxvEVYQb9/view#page=83)]: there is at least one
object satisfying `P`. Tarski: "at least one" may simply be replaced by the
article "an"; it is the existential quantifier and needs no identity.
Lean: `∃ x, P x`. -/
def AtLeastOne (P : D → Prop) : Prop :=
  ∃ x : D, P x

/-- **At most one** [Tarski, §20, [p. 58](https://drive.google.com/file/d/1o98AJ7PAh5KMmiSim79q_dmaxvEVYQb9/view#page=83)]: "for any x and y, if x
satisfies the given condition and if y satisfies the given condition, then
x = y". Lean: `Set.Subsingleton` (mathlib). -/
def AtMostOne (I : D → D → Prop) (P : D → Prop) : Prop :=
  ∀ x y : D, P x → P y → I x y

/-- **Exactly one** [Tarski, §20, [p. 58](https://drive.google.com/file/d/1o98AJ7PAh5KMmiSim79q_dmaxvEVYQb9/view#page=83)]: the conjunction of "at
least one" and "at most one". Lean: `∃! x, P x` (mathlib's `ExistsUnique`). -/
def ExactlyOne (I : D → D → Prop) (P : D → Prop) : Prop :=
  AtLeastOne P ∧ AtMostOne I P

/-- **At least two** [Tarski, §20, [p. 58](https://drive.google.com/file/d/1o98AJ7PAh5KMmiSim79q_dmaxvEVYQb9/view#page=83)]: "there are x and y, such
that both x and y satisfy the given condition and x ≠ y". Tarski notes it is
equivalent to the negation of "at most one" (p. 59). Lean: `Set.Nontrivial`
(mathlib). -/
def AtLeastTwo (I : D → D → Prop) (P : D → Prop) : Prop :=
  ∃ x y : D, P x ∧ P y ∧ ¬ I x y

end Tarski.Logic.Chapter03
