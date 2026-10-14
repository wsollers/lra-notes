import Tarski.Logic.Chapter03.Section19

/-!
# Tarski, Introduction to Logic, Chapter 3 (On the Theory of Identity), §20 — Definitions

§20, "Numerical quantifiers" (from
[p. 58](https://drive.google.com/file/d/1o98AJ7PAh5KMmiSim79q_dmaxvEVYQb9/view#page=83)):
"there is at least one", "at most one", "exactly one" `x` such that `x` has
the property `P`, and the same for two.

**Identity is the primitive `I`.** As in §17, identity is a relation
`I : D → D → Prop`, not Lean's `=`, so each numerical quantifier is stated
through `I`; `x ≠ y` is written `¬ I x y`. None of these definitions assumes
`LeibnizLaw I`; theorems about them take it as a hypothesis.

The page of each definition within §20 is not yet checked.
-/

universe u

namespace Tarski.Logic.Chapter03

variable {D : Type u}

/-- **At least one** [Tarski, §20]: there is at least one `x` such that `x`
has the property `P`. It needs no identity: it is the existential quantifier.
Lean: `∃ x, P x`. -/
def AtLeastOne (P : D → Prop) : Prop :=
  ∃ x : D, P x

/-- **At most one** [Tarski, §20]: for any `x` and `y`, if `x` has `P` and `y`
has `P`, then `x` is identical with `y`. Lean: `Set.Subsingleton` (mathlib). -/
def AtMostOne (I : D → D → Prop) (P : D → Prop) : Prop :=
  ∀ x y : D, P x → P y → I x y

/-- **Exactly one** [Tarski, §20]: there is at least one and at most one `x`
such that `x` has `P`. Lean: `∃! x, P x` (mathlib's `ExistsUnique`). -/
def ExactlyOne (I : D → D → Prop) (P : D → Prop) : Prop :=
  AtLeastOne P ∧ AtMostOne I P

/-- **At least two** [Tarski, §20]: there are `x` and `y`, not identical, that
both have `P`. Lean: `Set.Nontrivial` (mathlib). -/
def AtLeastTwo (I : D → D → Prop) (P : D → Prop) : Prop :=
  ∃ x y : D, ¬ I x y ∧ P x ∧ P y

/-- **At most two** [Tarski, §20]: for any `x`, `y`, `z` that all have `P`,
two of them are identical. -/
def AtMostTwo (I : D → D → Prop) (P : D → Prop) : Prop :=
  ∀ x y z : D, P x → P y → P z → I x y ∨ I x z ∨ I y z

/-- **Exactly two** [Tarski, §20]: there are at least two and at most two `x`
such that `x` has `P`. -/
def ExactlyTwo (I : D → D → Prop) (P : D → Prop) : Prop :=
  AtLeastTwo I P ∧ AtMostTwo I P

end Tarski.Logic.Chapter03
