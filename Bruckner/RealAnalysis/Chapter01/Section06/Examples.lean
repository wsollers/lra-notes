import Bruckner.RealAnalysis.Chapter01.Section06.Theorems

/-!
# Chapter 1, Section 1.6: Sups and Infs — Examples
-/

open Set

namespace Bruckner.RealAnalysis.Chapter01

/--
**Example 1.8** [[Thomson2008, §1.6, p. 12](http://classicalrealanalysis.com)]
The open interval (0, 1) has no maximum, but many upper bounds.
-/
theorem example_1_8_ub_two : IsUpperBound (Ioo (0 : ℝ) 1) 2 := by
  sorry

/-- **Example 1.8** [Thomson2008, §1.6, p. 12]: 1 is an upper bound of (0, 1). -/
theorem example_1_8_ub_one : IsUpperBound (Ioo (0 : ℝ) 1) 1 := by
  sorry

/-- **Example 1.8** [Thomson2008, §1.6, p. 12]: no upper bound of (0, 1) is below 1. -/
theorem example_1_8_least_ub : ∀ M' : ℝ, IsUpperBound (Ioo (0 : ℝ) 1) M' → 1 ≤ M' := by
  sorry

end Bruckner.RealAnalysis.Chapter01
