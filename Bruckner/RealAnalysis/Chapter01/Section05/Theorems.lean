import Bruckner.RealAnalysis.Chapter01.Section05.Definitions

/-!
# Chapter 1, Section 1.5: Bounds — Theorems

Consequences stated in the prose of [Thomson2008, §1.5, p. 11](http://classicalrealanalysis.com).
-/

namespace Bruckner.RealAnalysis.Chapter01

/--
**Empty set upper bound (prose remark)** [[Thomson2008, §1.5, p. 11](http://classicalrealanalysis.com)]

Every real number is an upper bound for the empty set.
-/
theorem empty_isUpperBound (M : ℝ) : IsUpperBound (∅ : Set ℝ) M := by
  intro x hx
  cases hx

/--
**Empty set lower bound (dual remark; not in the book)**

Every real number is also vacuously a lower bound for the empty set.
-/
theorem empty_isLowerBound (m : ℝ) : IsLowerBound (∅ : Set ℝ) m := by
  intro x hx
  cases hx

/--
**Empty set boundedness (not in the book)**

As a consequence of possessing both upper and lower bounds, the empty set is bounded.
-/
theorem empty_isBounded : IsBounded (∅ : Set ℝ) := by
  refine ⟨⟨0, empty_isUpperBound 0⟩, ⟨0, empty_isLowerBound 0⟩⟩

end Bruckner.RealAnalysis.Chapter01
