import Munkres.Topology.Chapter01.Functions
import Munkres.Topology.Chapter01.ImagesPreimages
import Munkres.Topology.Chapter01.EquivalenceRelations

namespace Munkres.Topology.Chapter01

/-!
# Chapter 1 Exercises

Use `exercise` for anonymous practice goals that are meant to train a proof
pattern without adding a named theorem to the chapter API.
-/

section Functions

section Exercise01

variable {A B : Type*} (f : A → B)
variable (A₀ : Set A) (B₀ : Set B)

/- Image/preimage comparison. These are the first warning that `image` and
   `preimage` are not inverse operations unless `f` has the right function
   property. -/

exercise : A₀ ⊆ f ⁻¹' (f '' A₀) := by
  sorry

exercise : Function.Injective f → f ⁻¹' (f '' A₀) = A₀ := by
  sorry

exercise : f '' (f ⁻¹' B₀) ⊆ B₀ := by
  sorry

exercise : Function.Surjective f → f '' (f ⁻¹' B₀) = B₀ := by
  sorry

end Exercise01

section Exercise02

variable {A B : Type*} (f : A → B)
variable (A₀ A₁ : Set A) (B₀ B₁ : Set B)

/- Preimages preserve inclusions, unions, intersections, and differences. -/

exercise : B₀ ⊆ B₁ → f ⁻¹' B₀ ⊆ f ⁻¹' B₁ := by
  sorry

exercise : f ⁻¹' (B₀ ∪ B₁) = (f ⁻¹' B₀) ∪ (f ⁻¹' B₁) := by
  sorry

exercise : f ⁻¹' (B₀ ∩ B₁) = (f ⁻¹' B₀) ∩ (f ⁻¹' B₁) := by
  sorry

exercise : f ⁻¹' (B₀ \ B₁) = (f ⁻¹' B₀) \ (f ⁻¹' B₁) := by
  sorry

/- Images preserve inclusions and unions. For intersections and differences,
   one direction always holds; equality needs injectivity. -/

exercise : A₀ ⊆ A₁ → f '' A₀ ⊆ f '' A₁ := by
  sorry

exercise : f '' (A₀ ∪ A₁) = (f '' A₀) ∪ (f '' A₁) := by
  sorry

exercise : f '' (A₀ ∩ A₁) ⊆ (f '' A₀) ∩ (f '' A₁) := by
  sorry

exercise : Function.Injective f → f '' (A₀ ∩ A₁) = (f '' A₀) ∩ (f '' A₁) := by
  sorry

exercise : (f '' A₀) \ (f '' A₁) ⊆ f '' (A₀ \ A₁) := by
  sorry

exercise : Function.Injective f → f '' (A₀ \ A₁) = (f '' A₀) \ (f '' A₁) := by
  sorry

end Exercise02

section Exercise03

variable {A B ι : Type*} (f : A → B)
variable (S : ι → Set A) (T : ι → Set B)

/- Arbitrary versions of selected parts of Exercise 2. -/

exercise : f ⁻¹' (⋃ i, T i) = ⋃ i, f ⁻¹' T i := by
  sorry

exercise : f ⁻¹' (⋂ i, T i) = ⋂ i, f ⁻¹' T i := by
  sorry

exercise : f '' (⋃ i, S i) = ⋃ i, f '' S i := by
  sorry

variable [Nonempty ι]

exercise : f '' (⋂ i, S i) ⊆ ⋂ i, f '' S i := by
  sorry

exercise :
    Function.Injective f → f '' (⋂ i, S i) = ⋂ i, f '' S i := by
  sorry

end Exercise03

section Exercise04

variable {A B C : Type*} (f : A → B) (g : B → C)
variable (C₀ : Set C)

/- Composition and function properties. -/

exercise : (g ∘ f) ⁻¹' C₀ = f ⁻¹' (g ⁻¹' C₀) := by
  sorry

exercise :
    Function.Injective f → Function.Injective g → Function.Injective (g ∘ f) := by
  sorry

exercise :
    Function.Injective (g ∘ f) → Function.Injective f := by
  sorry

/- No global injectivity of `g` follows from injectivity of `g ∘ f` without
   extra hypotheses, because `g` may fail to be injective away from the range of
   `f`. -/

exercise :
    Function.Surjective f → Function.Surjective g → Function.Surjective (g ∘ f) := by
  sorry

exercise :
    Function.Surjective (g ∘ f) → Function.Surjective g := by
  sorry

/- No surjectivity of `f` follows from surjectivity of `g ∘ f` without extra
   hypotheses, because `g` may collapse extra points of `B`. -/

end Exercise04

section Exercise05

/- Identity, left inverses, right inverses, and bijections. -/

variable {A B : Type*} (f : A → B)

exercise :
    (∃ g : B → A, Function.LeftInverse g f) → Function.Injective f := by
  sorry

exercise :
    (∃ h : B → A, Function.RightInverse h f) → Function.Surjective f := by
  sorry

/- A concrete left-inverse/no-right-inverse example: the unique map from `PUnit`
   into `Bool` hitting only `true`. -/

exercise :
    (∃ g : Bool → PUnit, Function.LeftInverse g (fun _ : PUnit => true)) ∧
      ¬ ∃ h : Bool → PUnit, Function.RightInverse h (fun _ : PUnit => true) := by
  sorry

/- A concrete right-inverse/no-left-inverse example: the constant map from
   `Bool` to `PUnit`. -/

exercise :
    (∃ h : PUnit → Bool, Function.RightInverse h (fun _ : Bool => PUnit.unit)) ∧
      ¬ ∃ g : PUnit → Bool, Function.LeftInverse g (fun _ : Bool => PUnit.unit) := by
  sorry

variable (g h : B → A)

exercise :
    Function.LeftInverse g f →
      Function.RightInverse h f →
        Function.Bijective f ∧ g = h := by
  sorry

end Exercise05

end Functions

end Munkres.Topology.Chapter01
