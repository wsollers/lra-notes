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

/-- The axioms of the real numbers, Chapter 3 [Laczkovich–Sós, Ch. 3, p. 28–33]. Not yet the book's system; see the module docstring. -/
structure RealAxiomSystem (R : Type u) where
  -- Data
  /-- Addition, a primitive operation. -/
  add : R → R → R
  /-- Multiplication, a primitive operation. -/
  mul : R → R → R
  /-- The element 0. -/
  zero : R
  /-- The element 1. -/
  one : R
  /-- The order. The book's primitive is `<` instead [Laczkovich–Sós, Ch. 3, p. 30]. -/
  le : R → R → Prop

  -- I. Addition axioms
  /-- **Axiom 3** [Laczkovich–Sós, Ch. 3, p. 29]: a + 0 = a. Two-sided here; the book states the right identity only. -/
  add_zero : ∀ x : R, add x zero = x ∧ add zero x = x
  /-- **Axiom 4** [Laczkovich–Sós, Ch. 3, p. 29]: every element has a negative. Two-sided here. -/
  exists_neg : ∀ x : R, ∃ y : R, add x y = zero ∧ add y x = zero
  /-- **Axiom 2** [Laczkovich–Sós, Ch. 3, p. 29]: associativity of addition. -/
  add_assoc : ∀ x y z : R, add x (add y z) = add (add x y) z
  /-- **Axiom 1** [Laczkovich–Sós, Ch. 3, p. 29]: commutativity of addition. -/
  add_comm : ∀ x y : R, add x y = add y x

  -- II. Multiplication axioms
  /-- **Axiom 7** [Laczkovich–Sós, Ch. 3, p. 29]: a · 1 = a. Two-sided here. -/
  mul_one : ∀ x : R, mul x one = x ∧ mul one x = x
  /-- 0 ≠ 1, assumed before the axioms are numbered [Laczkovich–Sós, Ch. 3, p. 29]. -/
  one_ne_zero : one ≠ zero
  /-- **Axiom 8** [Laczkovich–Sós, Ch. 3, p. 29]: every nonzero element has an inverse. Two-sided here. -/
  exists_inv :
    ∀ x : R, x ≠ zero → ∃ y : R, mul x y = one ∧ mul y x = one
  /-- **Axiom 6** [Laczkovich–Sós, Ch. 3, p. 29]: associativity of multiplication. -/
  mul_assoc : ∀ x y z : R, mul x (mul y z) = mul (mul x y) z
  /-- **Axiom 5** [Laczkovich–Sós, Ch. 3, p. 29]: commutativity of multiplication. -/
  mul_comm : ∀ x y : R, mul x y = mul y x

  -- I/II. Distributivity
  /-- Distributivity, (x + y)z = xz + yz. The book's **Axiom 9** [Laczkovich–Sós, Ch. 3, p. 29] is the left-hand form a(b + c) = ab + ac. -/
  distrib : ∀ x y z : R, mul (add x y) z = add (mul x z) (mul y z)

  -- III. Order axioms
  /-- Reflexivity of `≤`. Not a book axiom: the book's order axioms 10–13 [Laczkovich–Sós, Ch. 3, p. 29] are stated for `<`. -/
  le_refl : ∀ x : R, le x x
  /-- Antisymmetry of `≤`. Not a book axiom; compare trichotomy, **Axiom 10** [Laczkovich–Sós, Ch. 3, p. 29]. -/
  le_antisymm : ∀ x y : R, le x y → le y x → x = y
  /-- Transitivity of `≤`. Compare **Axiom 11** [Laczkovich–Sós, Ch. 3, p. 29], transitivity of `<`. -/
  le_trans : ∀ x y z : R, le x y → le y z → le x z
  /-- Totality of `≤`. Compare trichotomy, **Axiom 10** [Laczkovich–Sós, Ch. 3, p. 29]. -/
  le_total : ∀ x y : R, le x y ∨ le y x

  -- I/III. Addition and order
  /-- Compare **Axiom 12** [Laczkovich–Sós, Ch. 3, p. 29], stated in the book for `<`. -/
  add_le_add_right : ∀ x y z : R, le x y → le (add x z) (add y z)

  -- II/III. Multiplication and order
  /-- Non-negativity of products. A different statement from **Axiom 13** [Laczkovich–Sós, Ch. 3, p. 29] (a < b and 0 < c give ac < bc). -/
  mul_nonneg : ∀ x y : R, le zero x → le zero y → le zero (mul x y)

  -- IV. Completeness, Zorich cut/separation form
  /-- Completeness in Zorich's separation form. Not this book's axiom: its group IV is Cantor's nested-interval axiom, **Axiom 15** [Laczkovich–Sós, Ch. 3, p. 33], and the book also needs **Axiom 14** (Archimedes, p. 31), which is missing here. -/
  completeness :
    ∀ X Y : R → Prop,
      (∃ x, X x) →
      (∃ y, Y y) →
      (∀ x y, X x → Y y → le x y) →
      ∃ c : R, (∀ x, X x → le x c) ∧ (∀ y, Y y → le c y)

variable {R : Type u} (sys : RealAxiomSystem R)

/-- Strict order defined from `≤`. The book does the reverse: `<` is primitive and `≤` is defined from it [Laczkovich–Sós, Ch. 3, p. 30]. -/
def lt (x y : R) : Prop :=
  sys.le x y ∧ x ≠ y

end Laczkovich.RealAnalysisI.Chapter03
