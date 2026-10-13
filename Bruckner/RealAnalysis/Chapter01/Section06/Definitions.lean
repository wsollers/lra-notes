import Mathlib.Data.Real.Basic
import Mathlib.Data.EReal.Basic
import Mathlib.Data.EReal.Operations
import Mathlib.Order.Interval.Set.Basic
import Bruckner.RealAnalysis.Chapter01.Section05.Definitions

/-!
# Chapter 1, Section 1.6: Sups and Infs — Definitions and the Completeness Axiom

Formalized from:
* [Thomson2008, §1.6, pp. 12–16](http://classicalrealanalysis.com)
  Thomson, Brian S., Judith B. Bruckner, and Andrew M. Bruckner.
  *Elementary Real Analysis*, 2nd ed. ClassicalRealAnalysis.com, 2008.

The Completeness Axiom is one of the book's axioms, so it lives with the
definitions; `extSup` and `extInf` are built from it.
-/

open Set

namespace Bruckner.RealAnalysis.Chapter01

variable (E : Set ℝ)
variable (M m : ℝ)

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

An axiom in the book. Stated here as a theorem whose proof is still `sorry`.
-/
theorem completeness_axiom (hne : E.Nonempty) (hbdd : BoundedAbove E) :
    ∃ M : ℝ, IsLUB E M := by
  sorry

/--
**Completeness for infima** — the book's **Exercise 1.6.19**, not an axiom
[Thomson2008, §1.6, p. 16]. Stated here because `extInf` below is built from it;
`exercise_1_6_19` restates it.
-/
theorem completeness_axiom_below (hne : E.Nonempty) (hbdd : BoundedBelow E) :
    ∃ m : ℝ, IsGLB E m := by
  sorry

/-!
### Extended Real Conventions for Sup and Inf

Formalized from [Thomson2008, §1.6, p. 13](http://classicalrealanalysis.com): so
that `inf E` and `sup E` make sense for every set, the book sets inf ∅ = ∞ and
sup ∅ = −∞, sup E = ∞ when E is unbounded above, and inf E = −∞ when E is
unbounded below.
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

end Bruckner.RealAnalysis.Chapter01
