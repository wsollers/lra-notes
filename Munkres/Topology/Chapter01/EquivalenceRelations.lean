import Mathlib

/-!
# Munkres Topology, Chapter 1: Equivalence Relations

Mathlib usually packages equivalence relations as `Setoid A`.
-/

namespace Munkres.Topology.Chapter01

variable {A B : Type*}

/-- The relation induced by a function, where two points are related when they
have the same image. -/
def KernelRelation (f : A -> B) : A -> A -> Prop :=
  fun x y => f x = f y

/-- The kernel relation of a function is an equivalence relation. -/
theorem KernelRelationEquivalence (f : A -> B) :
    Equivalence (KernelRelation f) := by
  sorry

/-- The setoid induced by identifying points with the same image under a
function. -/
def KernelSetoid (f : A -> B) : Setoid A where
  r := KernelRelation f
  iseqv := KernelRelationEquivalence f

end Munkres.Topology.Chapter01

