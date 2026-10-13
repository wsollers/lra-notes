import Mathlib.Data.Real.Basic
import Mathlib.Order.Interval.Set.Basic

/-!
# Chapter 1, Section 1.5: Bounds — Definitions

Formalized from:
* [Thomson2008, §1.5, pp. 11–12](http://classicalrealanalysis.com)
  Thomson, Brian S., Judith B. Bruckner, and Andrew M. Bruckner.
  *Elementary Real Analysis*, 2nd ed. ClassicalRealAnalysis.com, 2008.
-/

namespace Bruckner.RealAnalysis.Chapter01

/- Context variables for Section 1.5 -/
variable (E : Set ℝ) -- The set of real numbers under consideration [Thomson2008, §1.5, p. 11](http://classicalrealanalysis.com)
variable (M : ℝ)     -- Potential upper bound for E [Thomson2008, §1.5, p. 11](http://classicalrealanalysis.com)
variable (m : ℝ)     -- Potential lower bound for E [Thomson2008, §1.5, p. 11](http://classicalrealanalysis.com)

/--
**Definition 1.1 (Upper Bounds)** [[Thomson2008, §1.5, p. 11](http://classicalrealanalysis.com)]

`M` is an upper bound for a set `E` of reals when every element of `E` is at most `M`.
-/
def IsUpperBound (E : Set ℝ) (M : ℝ) : Prop :=
  ∀ x ∈ E, x ≤ M

/--
**Definition 1.2 (Lower Bounds)** [[Thomson2008, §1.5, p. 11](http://classicalrealanalysis.com)]

`m` is a lower bound for a set `E` of reals when `m` is at most every element of `E`.
-/
def IsLowerBound (E : Set ℝ) (m : ℝ) : Prop :=
  ∀ x ∈ E, m ≤ x

/--
**Bounded Above (prose before Definition 1.1)** [[Thomson2008, §1.5, p. 11](http://classicalrealanalysis.com)]

`E` is bounded above when some real number is an upper bound for it.
-/
def BoundedAbove (E : Set ℝ) : Prop :=
  ∃ M : ℝ, IsUpperBound E M

/--
**Bounded Below (dual of `BoundedAbove`; not stated separately in the book)**

`E` is bounded below when some real number is a lower bound for it.
-/
def BoundedBelow (E : Set ℝ) : Prop :=
  ∃ m : ℝ, IsLowerBound E m

/--
**Unbounded Above (prose)** [[Thomson2008, §1.5, p. 11](http://classicalrealanalysis.com)]

`E` is unbounded above when it has no upper bound.
-/
def UnboundedAbove (E : Set ℝ) : Prop :=
  ¬ BoundedAbove E

/--
**Unbounded Below (dual of `UnboundedAbove`; not stated separately in the book)**

`E` has no lower bound.
-/
def UnboundedBelow (E : Set ℝ) : Prop :=
  ¬ BoundedBelow E

/--
**Bounded (prose)** [[Thomson2008, §1.5, p. 11](http://classicalrealanalysis.com)]

`E` is bounded when it has both an upper bound and a lower bound.
-/
def IsBounded (E : Set ℝ) : Prop :=
  BoundedAbove E ∧ BoundedBelow E

/--
**Definition 1.3 (Maximum)** [[Thomson2008, §1.5, p. 11](http://classicalrealanalysis.com)]

`M` is the maximum of `E` when `M` belongs to `E` and is at least every element
of `E`; the book writes `M = max E`.
-/
def IsMaximum (E : Set ℝ) (M : ℝ) : Prop :=
  M ∈ E ∧ IsUpperBound E M

/--
**Definition 1.4 (Minimum)** [[Thomson2008, §1.5, p. 11](http://classicalrealanalysis.com)]

`m` is the minimum of `E` when `m` belongs to `E` and is at most every element
of `E`; the book writes `m = min E`.
-/
def IsMinimum (E : Set ℝ) (m : ℝ) : Prop :=
  m ∈ E ∧ IsLowerBound E m

end Bruckner.RealAnalysis.Chapter01
