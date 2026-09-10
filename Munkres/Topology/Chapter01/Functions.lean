import Mathlib

/-!
# Munkres Topology, Chapter 1: Functions

Lean-facing notes for the basic vocabulary of functions in Munkres Chapter 1.
The declarations here are proof stubs for study: the learner should replace
`sorry` with their own proofs during the proof cycle.
-/

namespace Munkres.Topology.Chapter01

variable {A B C : Type*}

/-- A function with a left inverse is injective.

Textbook role: one of the basic tests connecting inverse-like data with
injectivity.
-/
theorem InjectiveOfLeftInverse
    {f : A -> B} {g : B -> A}
    (h : Function.LeftInverse g f) :
    Function.Injective f := by
  sorry

/-- A function with a right inverse is surjective.

Textbook role: one of the basic tests connecting inverse-like data with
surjectivity.
-/
theorem SurjectiveOfRightInverse
    {f : A -> B} {g : B -> A}
    (h : Function.RightInverse g f) :
    Function.Surjective f := by
  sorry

/-- The composite of two injective functions is injective. -/
theorem Injective.comp_munkres
    {f : A -> B} {g : B -> C}
    (hg : Function.Injective g)
    (hf : Function.Injective f) :
    Function.Injective (g ∘ f) := by
  sorry

/-- The composite of two surjective functions is surjective. -/
theorem Surjective.comp_munkres
    {f : A -> B} {g : B -> C}
    (hg : Function.Surjective g)
    (hf : Function.Surjective f) :
    Function.Surjective (g ∘ f) := by
  sorry

end Munkres.Topology.Chapter01

