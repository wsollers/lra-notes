import Mathlib

/-!
# Munkres Topology, Chapter 1: Images and Preimages

The central Lean notation is:

- `f '' s` for the image of a set `s`;
- `f ⁻¹' t` for the preimage of a set `t`.
-/

namespace Munkres.Topology.Chapter01

open Set

variable {A B : Type*} (f : A -> B)
variable (s s₀ s₁ : Set A) (t t₀ t₁ : Set B)

/-- Every set is contained in the preimage of its image. -/
theorem subset_preimage_image_munkres :
    s ⊆ f ⁻¹' (f '' s) := by
  sorry

/-- The image of a preimage is contained in the original target set. -/
theorem image_preimage_subset_munkres :
    f '' (f ⁻¹' t) ⊆ t := by
  sorry

/-- Images preserve unions. -/
theorem image_union_munkres :
    f '' (s₀ ∪ s₁) = f '' s₀ ∪ f '' s₁ := by
  sorry

/-- Preimages preserve unions. -/
theorem preimage_union_munkres :
    f ⁻¹' (t₀ ∪ t₁) = f ⁻¹' t₀ ∪ f ⁻¹' t₁ := by
  sorry

/-- Preimages preserve intersections. -/
theorem preimage_inter_munkres :
    f ⁻¹' (t₀ ∩ t₁) = f ⁻¹' t₀ ∩ f ⁻¹' t₁ := by
  sorry

/-- Images of intersections are contained in intersections of images. -/
theorem image_inter_subset_munkres :
    f '' (s₀ ∩ s₁) ⊆ f '' s₀ ∩ f '' s₁ := by
  sorry

end Munkres.Topology.Chapter01

