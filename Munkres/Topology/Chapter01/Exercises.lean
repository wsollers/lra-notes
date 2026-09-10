import Munkres.Topology.Chapter01.Functions
import Munkres.Topology.Chapter01.ImagesPreimages
import Munkres.Topology.Chapter01.EquivalenceRelations

/-!
# Munkres Topology, Chapter 1: Exercise Staging

Put selected exercise statements here after each reading session. Keep this
file curated: formalize exercises that teach a reusable mathematical or Lean
pattern.
-/

namespace Munkres.Topology.Chapter01

open Set

variable {A B C : Type*}

/-- Exercise pattern: if a composite is injective, then the first map is
injective. -/
theorem InjectiveOfInjectiveComp
    {f : A -> B} {g : B -> C}
    (h : Function.Injective (g ∘ f)) :
    Function.Injective f := by
  sorry

/-- Exercise pattern: if a composite is surjective, then the second map is
surjective. -/
theorem SurjectiveOfSurjectiveComp
    {f : A -> B} {g : B -> C}
    (h : Function.Surjective (g ∘ f)) :
    Function.Surjective g := by
  sorry

end Munkres.Topology.Chapter01

