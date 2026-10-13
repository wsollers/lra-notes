import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Field.Basic
import Laczkovich.RealAnalysisI.Chapter03.Definitions

/-!
# Laczkovich–Sós, Real Analysis: Foundations and Functions of One Variable, Chapter 3 — Theorems

Results stated before the chapter's first section. Prose notes belong in the
chapter's notes.tex.
-/

namespace Laczkovich.RealAnalysisI.Chapter03

/-! Elementary consequences of the field axioms (group I, p. 29). None is a
numbered result in the book; they are the first steps it leaves to the reader.
Proofs are left for you. -/

variable {R : Type u} (F : FieldAxioms R)

/-- Restates **Axiom 3** [Laczkovich–Sós, Ch. 3, p. 29]: a + 0 = a. -/
theorem add_zero_right (x : R) :
    F.add x F.zero = x := by
  sorry

/-- Not in the book as a numbered result: 0 is also a left identity.
Follows from Axioms 1 and 3 [Laczkovich–Sós, Ch. 3, p. 29]. -/
theorem zero_add_left (x : R) :
    F.add F.zero x = x := by
  sorry

/-- Not in the book as a numbered result: an element that is a left identity for
addition equals 0. Follows from Axioms 1 and 3 [Laczkovich–Sós, Ch. 3, p. 29]. -/
theorem AdditiveIdentityUnique (z : R)
    (zLeftIdentity : ∀ x : R, F.add z x = x) : z = F.zero := by
  sorry

/-- Not in the book as a numbered result: every element has a two-sided
additive inverse. Follows from Axioms 1 and 4 [Laczkovich–Sós, Ch. 3, p. 29]. -/
theorem AdditiveInverseExists (x : R) :
    ∃ y : R, F.add x y = F.zero ∧ F.add y x = F.zero := by
  sorry

/-- Restates **Axiom 4** [Laczkovich–Sós, Ch. 3, p. 29]: a right additive inverse exists. -/
theorem LeftAdditiveInverse {x : R} :
    ∃ y : R, F.add x y = F.zero := by
  sorry

/-- Not in the book as a numbered result: a left additive inverse exists.
Follows from Axioms 1 and 4 [Laczkovich–Sós, Ch. 3, p. 29]. -/
theorem RightAdditiveInverse {x : R} :
    ∃ y : R, F.add y x = F.zero := by
  sorry

/-- **Theorem 3.2** (p. 31): between any two real numbers there is a rational
number. A consequence of the axiom of Archimedes. Stated over mathlib's ℝ, not
over the axioms above; it needs the axiom of Archimedes (Axiom 14), not yet stated. -/
theorem RationalBetweenReals (x y : ℝ) (hOrder : x < y) :
  ∃ q : ℚ, x < (q : ℝ) ∧ (q : ℝ) < y := by

  sorry

end Laczkovich.RealAnalysisI.Chapter03
