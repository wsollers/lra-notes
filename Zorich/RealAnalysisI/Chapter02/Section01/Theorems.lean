import Mathlib.Data.Real.Basic
import Mathlib.Tactic

import Zorich.RealAnalysisI.Chapter02.Section01.Definitions

/-!
# Zorich, Mathematical Analysis I, §2.1 The Axiom System for the Real Numbers — Theorems

Consequences of the axioms (§2.1.2). Prose notes belong in the chapter's notes.tex.
-/

namespace Zorich.RealAnalysisI.Chapter02

/-- **2.1.2 d.1°** [Zorich, §2.1.2 d, p. 41]: trichotomy. The book says exactly one of the three holds; this states that at least one does. -/
theorem RealTrichotomy (x y : ℝ) : x < y ∨ x = y ∨ y < x :=
  lt_trichotomy x y

/-- **2.1.2 a.1°** [Zorich, §2.1.2 a, p. 39]: zero is unique. Stated over mathlib's ℝ. -/
theorem ZeroUniqueInReals (z : ℝ) (h : ∀ x : ℝ, x + z = x) : z = 0 := by
  simpa using h 0

/-- **2.1.2 a.2°** [Zorich, §2.1.2 a, p. 39]: each element has a unique negative. As stated the hypothesis is false, so the theorem is vacuous; see `study/source-audit.md`. -/
theorem AdditiveInverseUniqueInReals (x y : ℝ) (h : ∀ x y : ℝ, x + y = 0) : y = -x := by
  specialize h x
  specialize h y
  linarith

/-- Intended as **2.1.2 a.3°** [Zorich, §2.1.2 a, p. 40] (a + x = b), but the statement is the multiplicative equation of b.3°; see `study/source-audit.md`. -/
theorem LinearEquationUniqueSolutionInReals
    {a b x : ℝ} (ha : a ≠ 0) (h : a * x = b) :
    x = b / a := by
  field_simp
  simpa [mul_comm] using h

/-- **2.1.2 b.3°** [Zorich, §2.1.2 b, p. 40]: for a ≠ 0, a·x = b has the solution x = b·a⁻¹. Uniqueness half only. -/
theorem MulEquationUniqueSolutionInReals
    {a b x : ℝ} (ha : a ≠ 0) (h : a * x = b) :
    x = b / a := by
  apply (eq_div_iff ha).2
  simpa [mul_comm] using h

end Zorich.RealAnalysisI.Chapter02
