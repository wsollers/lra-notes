import Mathlib.Data.Real.Basic
import Mathlib.Tactic

import Zorich.RealAnalysisI.Chapter02.Section01.Definitions

/-!
# Zorich, Mathematical Analysis I, §2.1 The Axiom System for the Real Numbers — Theorems

Consequences of the axioms (§2.1.2). Prose notes belong in the chapter's notes.tex.
-/

namespace Zorich.RealAnalysisI.Chapter02

theorem RealTrichotomy (x y : ℝ) : x < y ∨ x = y ∨ y < x :=
  lt_trichotomy x y

theorem ZeroUniqueInReals (z : ℝ) (h : ∀ x : ℝ, x + z = x) : z = 0 := by
  simpa using h 0

theorem AdditiveInverseUniqueInReals (x y : ℝ) (h : ∀ x y : ℝ, x + y = 0) : y = -x := by
  specialize h x
  specialize h y
  linarith

theorem LinearEquationUniqueSolutionInReals
    {a b x : ℝ} (ha : a ≠ 0) (h : a * x = b) :
    x = b / a := by
  field_simp
  simpa [mul_comm] using h

theorem MulEquationUniqueSolutionInReals
    {a b x : ℝ} (ha : a ≠ 0) (h : a * x = b) :
    x = b / a := by
  apply (eq_div_iff ha).2
  simpa [mul_comm] using h

end Zorich.RealAnalysisI.Chapter02
