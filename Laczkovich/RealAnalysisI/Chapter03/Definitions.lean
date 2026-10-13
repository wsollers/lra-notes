import Common

/-!
# Laczkovich–Sós, Real Analysis: Foundations and Functions of One Variable, Chapter 3 — Definitions

The axioms of the real numbers (Chapter 3, pp. 28–33), packaged as a structure.

**Not yet the book's axiom system.** The book takes `<` as primitive and lists
fifteen axioms: field axioms 1–9 (group I), order axioms 10–13 (group II), the
axiom of Archimedes 14 (group III), and Cantor's nested-interval axiom 15
(group IV). The structure below takes `≤` as primitive, uses two-sided field
axioms, omits Archimedes, and states completeness in Zorich's separation form.
The group labels in its comments follow that arrangement, not the book's. See
`study/source-audit.md` for the book-faithful field statements.
-/

namespace Laczkovich.RealAnalysisI.Chapter03

structure RealAxiomSystem (R : Type u) where
  -- Data
  add : R → R → R
  mul : R → R → R
  zero : R
  one : R
  le : R → R → Prop

  -- I. Addition axioms
  add_zero : ∀ x : R, add x zero = x ∧ add zero x = x
  exists_neg : ∀ x : R, ∃ y : R, add x y = zero ∧ add y x = zero
  add_assoc : ∀ x y z : R, add x (add y z) = add (add x y) z
  add_comm : ∀ x y : R, add x y = add y x

  -- II. Multiplication axioms
  mul_one : ∀ x : R, mul x one = x ∧ mul one x = x
  one_ne_zero : one ≠ zero
  exists_inv :
    ∀ x : R, x ≠ zero → ∃ y : R, mul x y = one ∧ mul y x = one
  mul_assoc : ∀ x y z : R, mul x (mul y z) = mul (mul x y) z
  mul_comm : ∀ x y : R, mul x y = mul y x

  -- I/II. Distributivity
  distrib : ∀ x y z : R, mul (add x y) z = add (mul x z) (mul y z)

  -- III. Order axioms
  le_refl : ∀ x : R, le x x
  le_antisymm : ∀ x y : R, le x y → le y x → x = y
  le_trans : ∀ x y z : R, le x y → le y z → le x z
  le_total : ∀ x y : R, le x y ∨ le y x

  -- I/III. Addition and order
  add_le_add_right : ∀ x y z : R, le x y → le (add x z) (add y z)

  -- II/III. Multiplication and order
  mul_nonneg : ∀ x y : R, le zero x → le zero y → le zero (mul x y)

  -- IV. Completeness, Zorich cut/separation form
  completeness :
    ∀ X Y : R → Prop,
      (∃ x, X x) →
      (∃ y, Y y) →
      (∀ x y, X x → Y y → le x y) →
      ∃ c : R, (∀ x, X x → le x c) ∧ (∀ y, Y y → le c y)

variable {R : Type u} (sys : RealAxiomSystem R)

def lt (x y : R) : Prop :=
  sys.le x y ∧ x ≠ y

end Laczkovich.RealAnalysisI.Chapter03
