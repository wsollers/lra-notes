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

/-- Not in the book: the right-identity half of the structure's two-sided `add_zero`. -/
theorem add_zero_right {R : Type u} (sys : RealAxiomSystem R) (x : R) :
    sys.add x sys.zero = x :=
  (sys.add_zero x).1

/-- Not in the book: the left-identity half of the structure's two-sided `add_zero`. -/
theorem zero_add_left {R : Type u} (sys : RealAxiomSystem R) (x : R) :
    sys.add sys.zero x = x :=
  (sys.add_zero x).2

/-- Not in the book: a left identity for addition equals `zero`. -/
theorem AdditiveIdentityUnique (z : R)
    (zLeftIdentity : ∀ x : R, sys.add z x = x) : z = sys.zero := by

  calc
    z = sys.add z sys.zero := by rw [add_zero_right sys z]
    _ = sys.zero := zLeftIdentity sys.zero

/-- Restates **Axiom 4** [Laczkovich–Sós, Ch. 3, p. 29]. -/
theorem AdditiveInverseExists (x : R) :
  ∃ y : R, sys.add x y = sys.zero ∧ sys.add y x = sys.zero :=
  sys.exists_neg x

/-- Not in the book: one half of **Axiom 4** [Laczkovich–Sós, Ch. 3, p. 29] as stated here. -/
theorem LeftAdditiveInverse {x : R} :
  ∃ y : R, sys.add x y = sys.zero := by
  have ⟨y,hy⟩ := sys.exists_neg x
  refine ⟨y, ?_⟩
  exact hy.1

/-- Not in the book: the other half of the structure's two-sided **Axiom 4** [Laczkovich–Sós, Ch. 3, p. 29]. -/
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
