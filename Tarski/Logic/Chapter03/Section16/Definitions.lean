import Common

/-!
# Tarski, Introduction to Logic, Chapter 3 (On the Theory of Identity), §16 — Definitions

Leibniz's law, the law Tarski builds the theory of identity on.

**The primitive.** Tarski treats identity as a primitive term. Here it is a
relation `I : D → D → Prop` on a carrier `D`, not Lean's `=`: Lean's `=` is
already defined, so Leibniz's law about it is a theorem (see
`Observations.lean`), not something we may assume.

**The axiom is a hypothesis, not a bundle.** As in the other notes, the law is
a `Prop` about `I`, and a theorem that uses it takes it as a hypothesis.

**Definition or axiom?** Tarski remarks that Leibniz's law could serve as a
definition of identity, but takes identity as primitive and the law as an
axiom. `Observations.lean` shows the two readings agree in Lean: the only
relation satisfying the law is `=`.
-/

universe u

namespace Tarski.Logic.Chapter03

/-- **Leibniz's law** [Tarski, Ch. 3]: `x` is identical with `y` if and only
if `x` has every property that `y` has, and `y` has every property that `x`
has. Properties are predicates `P : D → Prop`. Lean: `Eq.subst` gives the
forward direction for `=`. -/
def LeibnizLaw {D : Type u} (I : D → D → Prop) : Prop :=
  ∀ x y : D, I x y ↔ ((∀ P : D → Prop, P y → P x) ∧ (∀ P : D → Prop, P x → P y))

end Tarski.Logic.Chapter03
