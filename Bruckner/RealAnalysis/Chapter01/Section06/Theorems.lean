import Mathlib.Data.Real.Basic
import Mathlib.Data.EReal.Basic
import Mathlib.Order.Interval.Set.Basic
import Bruckner.RealAnalysis.Chapter01.Section05

open Set

namespace Bruckner.RealAnalysis.Chapter01

/-!
# Chapter 1, Section 1.6: Sups and Infs

Formalized from:
* [Thomson2008, §1.6, pp. 12–16](http://classicalrealanalysis.com)
  Thomson, Brian S., Judith B. Bruckner, and Andrew M. Bruckner.
  *Elementary Real Analysis*, 2nd ed. ClassicalRealAnalysis.com, 2008.
-/

variable (E : Set ℝ)
variable (M m : ℝ)

/--
**Example 1.8** [[Thomson2008, §1.6, pp. 12–13](http://classicalrealanalysis.com)]
The open interval (0, 1) has no maximum, but many upper bounds.
-/
theorem example_1_8_ub_two : IsUpperBound (Ioo (0 : ℝ) 1) 2 := by
  sorry

theorem example_1_8_ub_one : IsUpperBound (Ioo (0 : ℝ) 1) 1 := by
  sorry

theorem example_1_8_least_ub : ∀ M' : ℝ, IsUpperBound (Ioo (0 : ℝ) 1) M' → 1 ≤ M' := by
  sorry

/--
**Definition 1.9: (Least Upper Bound / Supremum)** [[Thomson2008, §1.6, p. 13](http://classicalrealanalysis.com)]
-/
def IsLUB (E : Set ℝ) (M : ℝ) : Prop :=
  E.Nonempty ∧ BoundedAbove E ∧ IsUpperBound E M ∧ (∀ M' : ℝ, IsUpperBound E M' → M ≤ M')

/--
**Definition 1.10: (Greatest Lower Bound / Infimum)** [[Thomson2008, §1.6, p. 13](http://classicalrealanalysis.com)]
-/
def IsGLB (E : Set ℝ) (m : ℝ) : Prop :=
  E.Nonempty ∧ BoundedBelow E ∧ IsLowerBound E m ∧ (∀ m' : ℝ, IsLowerBound E m' → m' ≤ m)

/--
**Completeness Axiom** [[Thomson2008, §1.6, p. 13](http://classicalrealanalysis.com)]
-/
theorem completeness_axiom (hne : E.Nonempty) (hbdd : BoundedAbove E) :
    ∃ M : ℝ, IsLUB E M := by
  sorry

/--
**Completeness Axiom (Dual Form)** [[Thomson2008, §1.6, p. 13](http://classicalrealanalysis.com)]

The greatest-lower-bound counterpart, needed to define `extInf` below.
-/
theorem completeness_axiom_below (hne : E.Nonempty) (hbdd : BoundedBelow E) :
    ∃ m : ℝ, IsGLB E m := by
  sorry

/-!
### Extended Real Conventions for Sup and Inf

Formalized from:
* [Thomson2008, §1.6, p. 13](http://classicalrealanalysis.com)
  "To complete the definition of inf E and sup E it is most convenient to be able to
  write this expression even for E = ∅ or for unbounded sets. Thus we write
  1. inf ∅ = ∞ and sup ∅ = −∞.
  2. If E is unbounded above, then sup E = ∞.
  3. If E is unbounded below, then inf E = −∞."
-/

/-- Embed a set of real numbers into `EReal`. -/
def toERealSet (E : Set ℝ) : Set EReal :=
  ((↑) : ℝ → EReal) '' E

open Classical in
/--
**Extended Supremum Function (`extSup`)** [Thomson2008, §1.6, p. 13]
- If `E = ∅`, `extSup E = -∞`
- If `E` is unbounded above, `extSup E = ∞`
- If `E` is nonempty and bounded above, `extSup E = ↑M` where `M = sup E`
-/
noncomputable def extSup (E : Set ℝ) : EReal :=
  if hE : E = ∅ then
    (-⊤ : EReal)
  else if hub : UnboundedAbove E then
    (⊤ : EReal)
  else
    -- Under completeness, a nonempty set bounded above has a least upper bound in ℝ
    ↑(Classical.choose (completeness_axiom E (nonempty_iff_ne_empty.mpr hE)
      (not_not.mp hub)))

open Classical in
/--
**Extended Infimum Function (`extInf`)** [Thomson2008, §1.6, p. 13]
- If `E = ∅`, `extInf E = ∞`
- If `E` is unbounded below, `extInf E = -∞`
- If `E` is nonempty and bounded below, `extInf E = ↑m` where `m = inf E`
-/
noncomputable def extInf (E : Set ℝ) : EReal :=
  if hE : E = ∅ then
    (⊤ : EReal)
  else if hlb : UnboundedBelow E then
    (-⊤ : EReal)
  else
    ↑(Classical.choose (completeness_axiom_below E (nonempty_iff_ne_empty.mpr hE)
      (not_not.mp hlb)))

/--
**Convention 1 (Empty Set Infimum)** [Thomson2008, §1.6, p. 13]
`inf ∅ = ∞`
-/
theorem extInf_empty : extInf ∅ = ⊤ := by
  sorry

/--
**Convention 1 (Empty Set Supremum)** [Thomson2008, §1.6, p. 13]
`sup ∅ = -∞`
-/
theorem extSup_empty : extSup ∅ = -⊤ := by
  sorry

/--
**Convention 2 (Unbounded Above Supremum)** [Thomson2008, §1.6, p. 13]
"If E is unbounded above, then sup E = ∞."
-/
theorem extSup_of_unboundedAbove {E : Set ℝ} (h : UnboundedAbove E) :
    extSup E = ⊤ := by
  sorry

/--
**Convention 3 (Unbounded Below Infimum)** [Thomson2008, §1.6, p. 13]
"If E is unbounded below, then inf E = -∞."
-/
theorem extInf_of_unboundedBelow {E : Set ℝ} (h : UnboundedBelow E) :
    extInf E = -⊤ := by
  sorry

end Bruckner.RealAnalysis.Chapter01
