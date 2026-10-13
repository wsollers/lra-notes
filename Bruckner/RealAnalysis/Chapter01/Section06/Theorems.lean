import Bruckner.RealAnalysis.Chapter01.Section06.Definitions

/-!
# Chapter 1, Section 1.6: Sups and Infs — Theorems

The extended-real conventions of [Thomson2008, §1.6, p. 13](http://classicalrealanalysis.com),
as properties of `extSup` and `extInf`.
-/

namespace Bruckner.RealAnalysis.Chapter01

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
If `E` is unbounded above, `sup E = ∞`.
-/
theorem extSup_of_unboundedAbove {E : Set ℝ} (h : UnboundedAbove E) :
    extSup E = ⊤ := by
  sorry

/--
**Convention 3 (Unbounded Below Infimum)** [Thomson2008, §1.6, p. 13]
If `E` is unbounded below, `inf E = -∞`.
-/
theorem extInf_of_unboundedBelow {E : Set ℝ} (h : UnboundedBelow E) :
    extInf E = -⊤ := by
  sorry

end Bruckner.RealAnalysis.Chapter01
