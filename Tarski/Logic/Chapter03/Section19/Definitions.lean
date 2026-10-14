import Tarski.Logic.Chapter03.Section17

/-!
# Tarski, Introduction to Logic, Chapter 3 (On the Theory of Identity), §19 — Definitions

§19, "Equality in arithmetic and in geometry, and its relationship to logical
identity" (from
[p. 56](https://drive.google.com/file/d/1o98AJ7PAh5KMmiSim79q_dmaxvEVYQb9/view#page=81)).

**Congruence is not identity.** In geometry "equal" often means congruent:
two segments are "equal" when they have the same length, though they are
different segments. That is equality of value, not identity. So congruence is
a primitive relation of its own, `C : D → D → Prop`, separate from the
identity relation `I` of §17, and Leibniz's law is not assumed of it.

The page of each definition within §19 is not yet checked.
-/

universe u

namespace Tarski.Logic.Chapter03

/-- **Congruence** [Tarski, §19]: equality of value rather than identity.
Congruence is reflexive, symmetric, and transitive, like identity, but need
not satisfy Leibniz's law: congruent segments can differ in position.
Defined as core Lean's `Equivalence`; its fields `refl`, `symm`, `trans`
state the three laws. -/
abbrev Congruence {D : Type u} (C : D → D → Prop) : Prop :=
  Equivalence C

end Tarski.Logic.Chapter03
