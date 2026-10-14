import Munkres.Topology.Chapter01.Section02.Theorems
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.Function

namespace Munkres.Topology.Chapter01

/-!
# Chapter 1, §2 Functions — Exercises

Use `exercise` for named textbook exercises that should become reusable chapter
facts. Use `counterexample` for anonymous scratch checks.
-/

section Functions

section Exercise01

variable {A B : Type*} (f : A → B)
variable (A₀ : Set A) (B₀ : Set B)

/- Image/preimage comparison. These are the first warning that `image` and
   `preimage` are not inverse operations unless `f` has the right function
   property. -/

/-- **Exercise 2.1(a)** [Munkres, §2, p. 20]: A₀ ⊆ f⁻¹(f(A₀)). -/
named_exercise Munkres_Section02_Exercise01_part1 : A₀ ⊆ f ⁻¹' (f '' A₀) := by
  sorry

/-- **Exercise 2.1(a)** [Munkres, §2, p. 20]: equality when f is injective. -/
named_exercise Munkres_Section02_Exercise01_part2 : Function.Injective f → f ⁻¹' (f '' A₀) = A₀ := by
  sorry

/-- **Exercise 2.1(b)** [Munkres, §2, p. 20]: f(f⁻¹(B₀)) ⊆ B₀. -/
named_exercise Munkres_Section02_Exercise01_part3 : f '' (f ⁻¹' B₀) ⊆ B₀ := by
  sorry

/-- **Exercise 2.1(b)** [Munkres, §2, p. 20]: equality when f is surjective. -/
named_exercise Munkres_Section02_Exercise01_part4 : Function.Surjective f → f '' (f ⁻¹' B₀) = B₀ := by
  sorry

end Exercise01

section Exercise02

variable {A B : Type*} (f : A → B)
variable (A₀ A₁ : Set A) (B₀ B₁ : Set B)

/- Preimages preserve inclusions, unions, intersections, and differences. -/

/-- **Exercise 2.2(a)** [Munkres, §2, p. 20]: preimage preserves inclusion. -/
named_exercise Munkres_Section02_Exercise02_part1 : B₀ ⊆ B₁ → f ⁻¹' B₀ ⊆ f ⁻¹' B₁ := by
  sorry

/-- **Exercise 2.2(b)** [Munkres, §2, p. 20]: preimage of a union. -/
named_exercise Munkres_Section02_Exercise02_part2 : f ⁻¹' (B₀ ∪ B₁) = (f ⁻¹' B₀) ∪ (f ⁻¹' B₁) := by
  sorry

/-- **Exercise 2.2(c)** [Munkres, §2, p. 20]: preimage of an intersection. -/
named_exercise Munkres_Section02_Exercise02_part3 : f ⁻¹' (B₀ ∩ B₁) = (f ⁻¹' B₀) ∩ (f ⁻¹' B₁) := by
  sorry

/-- **Exercise 2.2(d)** [Munkres, §2, p. 20]: preimage of a difference. -/
named_exercise Munkres_Section02_Exercise02_part4 : f ⁻¹' (B₀ \ B₁) = (f ⁻¹' B₀) \ (f ⁻¹' B₁) := by
  sorry

/- Images preserve inclusions and unions. For intersections and differences,
   one direction always holds; equality needs injectivity. -/

/-- **Exercise 2.2(e)** [Munkres, §2, p. 20]: image preserves inclusion. -/
named_exercise Munkres_Section02_Exercise02_part5 : A₀ ⊆ A₁ → f '' A₀ ⊆ f '' A₁ := by
  sorry

/-- **Exercise 2.2(f)** [Munkres, §2, p. 21]: image of a union. -/
named_exercise Munkres_Section02_Exercise02_part6 : f '' (A₀ ∪ A₁) = (f '' A₀) ∪ (f '' A₁) := by
  sorry

/-- **Exercise 2.2(g)** [Munkres, §2, p. 21]: image of an intersection, inclusion. -/
named_exercise Munkres_Section02_Exercise02_part7 : f '' (A₀ ∩ A₁) ⊆ (f '' A₀) ∩ (f '' A₁) := by
  sorry

/-- **Exercise 2.2(g)** [Munkres, §2, p. 21]: equality when f is injective. -/
named_exercise Munkres_Section02_Exercise02_part8 :
    Function.Injective f → f '' (A₀ ∩ A₁) = (f '' A₀) ∩ (f '' A₁) := by
  sorry

/-- **Exercise 2.2(h)** [Munkres, §2, p. 21]: image of a difference, inclusion. -/
named_exercise Munkres_Section02_Exercise02_part9 : (f '' A₀) \ (f '' A₁) ⊆ f '' (A₀ \ A₁) := by
  sorry

/-- **Exercise 2.2(h)** [Munkres, §2, p. 21]: equality when f is injective. -/
named_exercise Munkres_Section02_Exercise02_part10 :
    Function.Injective f → f '' (A₀ \ A₁) = (f '' A₀) \ (f '' A₁) := by
  sorry

end Exercise02

section Exercise03

variable {A B ι : Type*} (f : A → B)
variable (S : ι → Set A) (T : ι → Set B)

/- Arbitrary versions of selected parts of Exercise 2. -/

/-- **Exercise 2.3** [Munkres, §2, p. 21]: 2.2(b) for arbitrary unions. -/
named_exercise Munkres_Section02_Exercise03_part1 :
    f ⁻¹' (⋃ i, T i) = ⋃ i, f ⁻¹' T i := by
  sorry

/-- **Exercise 2.3** [Munkres, §2, p. 21]: 2.2(c) for arbitrary intersections. -/
named_exercise Munkres_Section02_Exercise03_part2 :
    f ⁻¹' (⋂ i, T i) = ⋂ i, f ⁻¹' T i := by
  sorry

/-- **Exercise 2.3** [Munkres, §2, p. 21]: 2.2(f) for arbitrary unions. -/
named_exercise Munkres_Section02_Exercise03_part3 :
    f '' (⋃ i, S i) = ⋃ i, f '' S i := by
  sorry

variable [Nonempty ι]

/-- **Exercise 2.3** [Munkres, §2, p. 21]: 2.2(g), inclusion, for arbitrary intersections. -/
named_exercise Munkres_Section02_Exercise03_part4 :
    f '' (⋂ i, S i) ⊆ ⋂ i, f '' S i := by
  sorry

/-- **Exercise 2.3** [Munkres, §2, p. 21]: 2.2(g), equality when f is injective. -/
named_exercise Munkres_Section02_Exercise03_part5 :
    Function.Injective f → f '' (⋂ i, S i) = ⋂ i, f '' S i := by
  sorry

end Exercise03

section Exercise04

variable {A B C : Type*} (f : A → B) (g : B → C)
variable (C₀ : Set C)

/- Composition and function properties. -/

/-- **Exercise 2.4(a)** [Munkres, §2, p. 21]: preimage under a composite. -/
named_exercise Munkres_Section02_Exercise04_part1 :
    (g ∘ f) ⁻¹' C₀ = f ⁻¹' (g ⁻¹' C₀) := by
  sorry

/-- **Exercise 2.4(b)** [Munkres, §2, p. 21]: a composite of injections is injective. -/
named_exercise Munkres_Section02_Exercise04_part2 :
    Function.Injective f → Function.Injective g → Function.Injective (g ∘ f) := by
  sorry

/-- **Exercise 2.4(c)** [Munkres, §2, p. 21]: positive half only, g ∘ f injective gives f injective. -/
named_exercise Munkres_Section02_Exercise04_part3 :
    Function.Injective (g ∘ f) → Function.Injective f := by
  sorry

/- No global injectivity of `g` follows from injectivity of `g ∘ f` without
   extra hypotheses, because `g` may fail to be injective away from the range of
   `f`. -/

/-- **Exercise 2.4(d)** [Munkres, §2, p. 21]: a composite of surjections is surjective. -/
named_exercise Munkres_Section02_Exercise04_part4 :
    Function.Surjective f → Function.Surjective g → Function.Surjective (g ∘ f) := by
  sorry

/-- **Exercise 2.4(e)** [Munkres, §2, p. 21]: positive half only, g ∘ f surjective gives g surjective. -/
named_exercise Munkres_Section02_Exercise04_part5 :
    Function.Surjective (g ∘ f) → Function.Surjective g := by
  sorry

/- No surjectivity of `f` follows from surjectivity of `g ∘ f` without extra
   hypotheses, because `g` may collapse extra points of `B`. -/

end Exercise04

section Exercise05

/- Identity, left inverses, right inverses, and bijections. -/

variable {A B : Type*} (f : A → B)

/-- **Exercise 2.5(a)** [Munkres, §2, p. 21]: a left inverse makes f injective. -/
named_exercise Munkres_Section02_Exercise05_part1 :
    (∃ g : B → A, Function.LeftInverse g f) → Function.Injective f := by
  sorry

/-- **Exercise 2.5(a)** [Munkres, §2, p. 21]: a right inverse makes f surjective. -/
named_exercise Munkres_Section02_Exercise05_part2 :
    (∃ h : B → A, Function.RightInverse h f) → Function.Surjective f := by
  sorry

/- A concrete left-inverse/no-right-inverse example: the unique map from `PUnit`
   into `Bool` hitting only `true`. -/

/-- **Exercise 2.5(b)** [Munkres, §2, p. 21]: a function with a left inverse but no right inverse. -/
exercise :
    (∃ g : Bool → PUnit, Function.LeftInverse g (fun _ : PUnit => true)) ∧
      ¬ ∃ h : Bool → PUnit, Function.RightInverse h (fun _ : PUnit => true) := by
  sorry

/- A concrete right-inverse/no-left-inverse example: the constant map from
   `Bool` to `PUnit`. -/

/-- **Exercise 2.5(c)** [Munkres, §2, p. 21]: a function with a right inverse but no left inverse. -/
exercise :
    (∃ h : PUnit → Bool, Function.RightInverse h (fun _ : Bool => PUnit.unit)) ∧
      ¬ ∃ g : PUnit → Bool, Function.LeftInverse g (fun _ : Bool => PUnit.unit) := by
  sorry

variable (g h : B → A)

/-- **Exercise 2.5(e)** [Munkres, §2, p. 21]: left and right inverses make f bijective and agree. Restates Lemma 2.1; omits that both equal f⁻¹. -/
named_exercise Munkres_Section02_Exercise05_part5 :
    Function.LeftInverse g f →
      Function.RightInverse h f →
        Function.Bijective f ∧ g = h := by
  sorry

end Exercise05

end Functions

end Munkres.Topology.Chapter01
