import Tarski.Logic.Chapter03.Section17

/-!
# Tarski, Introduction to Logic, Chapter 3 (On the Theory of Identity), §19 — Definitions

§19, "Equality in arithmetic and in geometry, and its relationship to logical
identity" ([pp. 56–57](https://drive.google.com/file/d/1o98AJ7PAh5KMmiSim79q_dmaxvEVYQb9/view#page=81)).

**Equality in arithmetic is identity** (p. 56): Tarski treats `=` between
numbers "always as a special case of the general concept of logical identity".

**Equality in geometry is congruence, not identity** ([p. 57](https://drive.google.com/file/d/1o98AJ7PAh5KMmiSim79q_dmaxvEVYQb9/view#page=82)): two
figures are "equal" in the sense of congruent when they have the same size and
shape. Two sides of a triangle can be "geometrically equal" and "yet these
sides are certainly not identical". Tarski recommends saying "congruent" and
writing a different symbol, `≅`, instead of `=`. So congruence here is a
primitive relation of its own, `C : D → D → Prop`, separate from the identity
`I` of §17, and Leibniz's law is not assumed of it.
-/

universe u

namespace Tarski.Logic.Chapter03

/-- **Congruence** [Tarski, §19, [p. 57](https://drive.google.com/file/d/1o98AJ7PAh5KMmiSim79q_dmaxvEVYQb9/view#page=82)]: geometric equality, "the
same size and shape", as opposed to logical identity. Tarski states the laws
it satisfies later, in Ch. V, §30 ([p. 88](https://drive.google.com/file/d/1o98AJ7PAh5KMmiSim79q_dmaxvEVYQb9/view#page=113)): congruence of segments
is reflexive, symmetric, and transitive, like identity (Laws II–IV of §17).
Defined as core Lean's `Equivalence`; its fields `refl`, `symm`, `trans`
state the three laws. -/
abbrev Congruence {D : Type u} (C : D → D → Prop) : Prop :=
  Equivalence C

end Tarski.Logic.Chapter03
