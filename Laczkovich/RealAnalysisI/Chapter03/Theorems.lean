import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Field.Basic
import Laczkovich.RealAnalysisI.Chapter03.Definitions

/-!
# Laczkovich–Sós, Real Analysis: Foundations and Functions of One Variable, Chapter 3 — Theorems

Results stated before the chapter's first section. Prose notes belong in the
chapter's notes.tex.
-/

namespace Laczkovich.RealAnalysisI.Chapter03

variable {R : Type u} (sys : RealAxiomSystem R)

theorem add_zero_right {R : Type u} (sys : RealAxiomSystem R) (x : R) :
    sys.add x sys.zero = x :=
  (sys.add_zero x).1

theorem zero_add_left {R : Type u} (sys : RealAxiomSystem R) (x : R) :
    sys.add sys.zero x = x :=
  (sys.add_zero x).2

theorem AdditiveIdentityUnique (z : R)
    (zLeftIdentity : ∀ x : R, sys.add z x = x) : z = sys.zero := by

  calc
    z = sys.add z sys.zero := by rw [add_zero_right sys z]
    _ = sys.zero := zLeftIdentity sys.zero

theorem AdditiveInverseExists (x : R) :
  ∃ y : R, sys.add x y = sys.zero ∧ sys.add y x = sys.zero :=
  sys.exists_neg x

theorem LeftAdditiveInverse {x : R} :
  ∃ y : R, sys.add x y = sys.zero := by
  have ⟨y,hy⟩ := sys.exists_neg x
  refine ⟨y, ?_⟩
  exact hy.1

theorem RightAdditiveInverse {x : R} :
  ∃ y : R, sys.add y x = sys.zero := by
  have ⟨y,hy⟩ := sys.exists_neg x
  refine ⟨y, ?_⟩
  exact hy.2

/-- **Theorem 3.2** (p. 31): between any two real numbers there is a rational
number. A consequence of the axiom of Archimedes. Stated over mathlib's ℝ, not
over `RealAxiomSystem`. -/
theorem RationalBetweenReals (x y : ℝ) (hOrder : x < y) :
  ∃ q : ℚ, x < (q : ℝ) ∧ (q : ℝ) < y := by

  sorry

end Laczkovich.RealAnalysisI.Chapter03
