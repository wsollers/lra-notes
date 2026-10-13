import Mathlib.Data.Real.Basic
import Mathlib.Order.Interval.Set.Basic




namespace Bruckner.RealAnalysis.Chapter01

/-!
# Chapter 1, Section 1.5: Bounds

Formalized from:
* [Thomson2008, §1.5, pp. 11–12](http://classicalrealanalysis.com)
  Thomson, Brian S., Judith B. Bruckner, and Andrew M. Bruckner.
  *Elementary Real Analysis*, 2nd ed. ClassicalRealAnalysis.com, 2008.
-/

/- Context variables for Section 1.5 -/
variable (E : Set ℝ) -- The set of real numbers under consideration [Thomson2008, §1.5, p. 11](http://classicalrealanalysis.com)
variable (M : ℝ)     -- Potential upper bound for E [Thomson2008, §1.5, p. 11](http://classicalrealanalysis.com)
variable (m : ℝ)     -- Potential lower bound for E [Thomson2008, §1.5, p. 11](http://classicalrealanalysis.com)

/--
**Definition 1.1 (Upper Bounds)** [[Thomson2008, §1.5, p. 11](http://classicalrealanalysis.com)]

"Let `E` be a set of real numbers. A number `M` is said to be an upper bound
for `E` if x ≤ M for all x ∈ E."
-/
def IsUpperBound (E : Set ℝ) (M : ℝ) : Prop :=
  ∀ x ∈ E, x ≤ M

/--
**Definition 1.2 (Lower Bounds)** [[Thomson2008, §1.5, p. 11](http://classicalrealanalysis.com)]

"Let `E` be a set of real numbers. A number `m` is said to be a lower bound
for `E` if m ≤ x for all x ∈ E."
-/
def IsLowerBound (E : Set ℝ) (m : ℝ) : Prop :=
  ∀ x ∈ E, m ≤ x

/--
**Bounded Above (Informal Preamble)** [[Thomson2008, §1.5, p. 11](http://classicalrealanalysis.com)]

"There may or may not be a number `M` that is bigger than every number in the set `E`.
If there is, we say that `M` is an upper bound for the set."
-/
def BoundedAbove (E : Set ℝ) : Prop :=
  ∃ M : ℝ, IsUpperBound E M

/--
**Bounded Below (Dual Concept)** [[Thomson2008, §1.5, p. 11](http://classicalrealanalysis.com)]

Dual formulation for the existence of a lower bound.
-/
def BoundedBelow (E : Set ℝ) : Prop :=
  ∃ m : ℝ, IsLowerBound E m

/--
**Unbounded Above (Inline Concept)** [[Thomson2008, §1.5, p. 11](http://classicalrealanalysis.com)]

"If there is no upper bound, then the set is said to be unbounded above or to have
no upper bound... We can use the phrase 'E is unbounded above' if there are no upper bounds."
-/
def UnboundedAbove (E : Set ℝ) : Prop :=
  ¬ BoundedAbove E

/--
**Unbounded Below (Dual Concept)** [[Thomson2008, §1.5, p. 11](http://classicalrealanalysis.com)]

The set `E` has no lower bound.
-/
def UnboundedBelow (E : Set ℝ) : Prop :=
  ¬ BoundedBelow E

/--
**Bounded (Inline Definition)** [[Thomson2008, §1.5, p. 11](http://classicalrealanalysis.com)]

"It is often important to note whether a set has bounds or not. A set that has an
upper bound and a lower bound is called bounded."
-/
def IsBounded (E : Set ℝ) : Prop :=
  BoundedAbove E ∧ BoundedBelow E

/--
**Empty Set Upper Bound Remark (Inline Prose)** [[Thomson2008, §1.5, p. 11](http://classicalrealanalysis.com)]

"A set can have many upper bounds. Indeed every number is an upper bound
for the empty set ∅."
-/
theorem empty_isUpperBound (M : ℝ) : IsUpperBound (∅ : Set ℝ) M := by
  intro x hx
  cases hx

/--
**Empty Set Lower Bound (Dual Inline Remark)** [[Thomson2008, §1.5, p. 11](http://classicalrealanalysis.com)]

Every real number is also vacuously a lower bound for the empty set.
-/
theorem empty_isLowerBound (m : ℝ) : IsLowerBound (∅ : Set ℝ) m := by
  intro x hx
  cases hx

/--
**Empty Set Boundedness** [[Thomson2008, §1.5, p. 11](http://classicalrealanalysis.com)]

As a consequence of possessing both upper and lower bounds, the empty set is bounded.
-/
theorem empty_isBounded : IsBounded (∅ : Set ℝ) := by
  refine ⟨⟨0, empty_isUpperBound 0⟩, ⟨0, empty_isLowerBound 0⟩⟩

/--
**Definition 1.3 (Maximum)** [[Thomson2008, §1.5, p. 11](http://classicalrealanalysis.com)]

"Let `E` be a set of real numbers. If there is a number `M` that belongs to `E`
and is larger than every other member of `E`, then `M` is called the maximum of
the set `E` and we write `M` = max `E`."
-/
def IsMaximum (E : Set ℝ) (M : ℝ) : Prop :=
  M ∈ E ∧ IsUpperBound E M

/--
**Definition 1.4 (Minimum)** [[Thomson2008, §1.5, pp. 11–12](http://classicalrealanalysis.com)]

"Let `E` be a set of real numbers. If there is a number `m` that belongs to `E`
and is smaller than every other member of `E`, then `m` is called the minimum of
the set `E` and we write `m` = min `E`."
-/
def IsMinimum (E : Set ℝ) (m : ℝ) : Prop :=
  m ∈ E ∧ IsLowerBound E m


/--
**Example 1.5** [[Thomson2008, §1.5, p. 12](http://classicalrealanalysis.com)]

"The interval [0, 1] = {x : 0 ≤ x ≤ 1} has a maximum and a minimum.
The maximum is 1 and 1 is also an upper bound for the set... The number 0
is the minimum and also a lower bound."
-/

abbrev closedUnitInterval : Set ℝ := Set.Icc (0 : ℝ) 1 -- [0,1]

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

theorem example_1_5_min : IsMinimum (closedUnitInterval) 0 := by
  sorry

/--
"Any number larger than 1 is also an upper bound." [Thomson2008, §1.5, p. 12]
-/
theorem example_1_5_larger_isUpperBound (M : ℝ) (hM : 1 ≤ M) :
    IsUpperBound (Set.Icc (0 : ℝ) 1) M := by
  sorry

/--
**Example 1.6** [[Thomson2008, §1.5, p. 12](http://classicalrealanalysis.com)]

"The interval (0, 1) = {x : 0 < x < 1} has no maximum and no minimum...
Here 1 and 0 are upper and lower bounds, respectively, but do not belong to the set."
-/
theorem example_1_6_bounds :
    IsUpperBound (Set.Ioo (0 : ℝ) 1) 1 ∧ IsLowerBound (Set.Ioo (0 : ℝ) 1) 0 := by
  sorry

theorem example_1_6_no_max : ¬ ∃ M : ℝ, IsMaximum (Set.Ioo (0 : ℝ) 1) M := by
  sorry

theorem example_1_6_no_min : ¬ ∃ m : ℝ, IsMinimum (Set.Ioo (0 : ℝ) 1) m := by
  sorry

/--
**Example 1.7** [[Thomson2008, §1.5, p. 12](http://classicalrealanalysis.com)]

"The set ℕ of natural numbers has a minimum but no maximum and
no upper bounds at all. We would say that it is bounded below but not bounded above."
Here ℕ is indexed starting at 1 following textbook convention: {n : ℝ | ∃ k : ℕ, k ≥ 1 ∧ n = k}.
-/
def NatPos : Set ℝ := {x : ℝ | ∃ n : ℕ, n ≥ 1 ∧ x = (n : ℝ)}

theorem example_1_7_min : IsMinimum NatPos 1 := by
  sorry

theorem example_1_7_boundedBelow : BoundedBelow NatPos := by
  sorry

theorem example_1_7_unboundedAbove : UnboundedAbove NatPos := by
  sorry

theorem example_1_7_no_max : ¬ ∃ M : ℝ, IsMaximum NatPos M := by
  sorry

end Bruckner.RealAnalysis.Chapter01
