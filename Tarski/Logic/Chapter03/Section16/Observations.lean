import Tarski.Logic.Chapter03.Section16.Definitions

/-!
# Tarski, Introduction to Logic, Chapter 3 (On the Theory of Identity), §16 — Observations

Facts we derive that the book does not state. `Theorems.lean` holds only what
the book states; anything here has no page of its own, only the axioms it
comes from.

**Leibniz's law and Lean's `=`.** Lean's `=` satisfies Leibniz's law, and it is
the only relation that does. So reading the law as a definition of identity
and reading it as an axiom about a primitive identity give the same relation.
-/

universe u

namespace Tarski.Logic.Chapter03

variable {D : Type u}

/-- Not in the book. Lean's `=` satisfies **Leibniz's law**: it is a theorem
about `=`, not an assumption. -/
theorem eq_leibnizLaw : LeibnizLaw (@Eq D) := by
  sorry

/-- Not in the book. Any relation satisfying **Leibniz's law** is Lean's `=`:
the law determines identity uniquely. -/
theorem eq_of_leibnizLaw {I : D → D → Prop} (h_leibniz : LeibnizLaw I) : I = @Eq D := by
  sorry

end Tarski.Logic.Chapter03
