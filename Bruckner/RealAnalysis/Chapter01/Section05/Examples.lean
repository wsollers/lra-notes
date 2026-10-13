import Bruckner.RealAnalysis.Chapter01.Section05.Theorems

/-!
# Chapter 1, Section 1.5: Bounds — Examples

Examples 1.5–1.7 of [Thomson2008, §1.5, p. 12](http://classicalrealanalysis.com).
-/

namespace Bruckner.RealAnalysis.Chapter01

/--
**Example 1.5** [[Thomson2008, §1.5, p. 12](http://classicalrealanalysis.com)]

The closed interval [0, 1] has maximum 1 and minimum 0; each is also a bound.
-/

abbrev closedUnitInterval : Set ℝ := Set.Icc (0 : ℝ) 1 -- [0,1]

/-- **Example 1.5** [Thomson2008, §1.5, p. 12]: 1 is the maximum of [0, 1]. -/
theorem example_1_5_max : IsMaximum (closedUnitInterval) 1 := by
  have oneMember : 1 ∈ closedUnitInterval := by
    rw [Set.mem_Icc]
    norm_num

  have ub1 : IsUpperBound closedUnitInterval 1 := by
    intro x hxMember
    rw [Set.mem_Icc] at hxMember
    exact hxMember.2

  -- IsMaximum closedUnitInterval 1 unfolds to (1 ∈ closedUnitInterval ∧ IsUpperBound closedUnitInterval 1)
  exact ⟨oneMember, ub1⟩

/-- **Example 1.5** [Thomson2008, §1.5, p. 12]: 0 is the minimum of [0, 1]. -/
theorem example_1_5_min : IsMinimum (closedUnitInterval) 0 := by
  sorry

/--
Example 1.5 continued [Thomson2008, §1.5, p. 12]: any number larger than 1 is
also an upper bound. The book says "larger"; this states `1 ≤ M`, which also holds.
-/
theorem example_1_5_larger_isUpperBound (M : ℝ) (hM : 1 ≤ M) :
    IsUpperBound (Set.Icc (0 : ℝ) 1) M := by
  sorry

/--
**Example 1.6** [[Thomson2008, §1.5, p. 12](http://classicalrealanalysis.com)]

The open interval (0, 1) has no maximum and no minimum, although 1 and 0 are an
upper and a lower bound that lie outside the set.
-/
theorem example_1_6_bounds :
    IsUpperBound (Set.Ioo (0 : ℝ) 1) 1 ∧ IsLowerBound (Set.Ioo (0 : ℝ) 1) 0 := by
  sorry

/-- **Example 1.6** [Thomson2008, §1.5, p. 12]: (0, 1) has no maximum. -/
theorem example_1_6_no_max : ¬ ∃ M : ℝ, IsMaximum (Set.Ioo (0 : ℝ) 1) M := by
  sorry

/-- **Example 1.6** [Thomson2008, §1.5, p. 12]: (0, 1) has no minimum. -/
theorem example_1_6_no_min : ¬ ∃ m : ℝ, IsMinimum (Set.Ioo (0 : ℝ) 1) m := by
  sorry

/--
**Example 1.7** [[Thomson2008, §1.5, p. 12](http://classicalrealanalysis.com)]

The natural numbers have a minimum but no maximum and no upper bound: bounded
below, not bounded above. Following the book, ℕ starts at 1, so it is modelled as
`{n : ℝ | ∃ k : ℕ, k ≥ 1 ∧ n = k}`.
-/
def NatPos : Set ℝ := {x : ℝ | ∃ n : ℕ, n ≥ 1 ∧ x = (n : ℝ)}

/-- **Example 1.7** [Thomson2008, §1.5, p. 12]: 1 is the minimum of ℕ. -/
theorem example_1_7_min : IsMinimum NatPos 1 := by
  sorry

/-- **Example 1.7** [Thomson2008, §1.5, p. 12]: ℕ is bounded below. -/
theorem example_1_7_boundedBelow : BoundedBelow NatPos := by
  sorry

/-- **Example 1.7** [Thomson2008, §1.5, p. 12]: ℕ has no upper bound. -/
theorem example_1_7_unboundedAbove : UnboundedAbove NatPos := by
  sorry

/-- **Example 1.7** [Thomson2008, §1.5, p. 12]: ℕ has no maximum. -/
theorem example_1_7_no_max : ¬ ∃ M : ℝ, IsMaximum NatPos M := by
  sorry

end Bruckner.RealAnalysis.Chapter01
