import Common

/-!
# Laczkovich–Sós, Real Analysis: Foundations and Functions of One Variable, Chapter 3 — Definitions

The axioms of the real numbers, as the book states them at the start of
Chapter 3 [Laczkovich–Sós, Ch. 3, pp. 28–33].

The book numbers fifteen axioms in four groups. This file states groups I and II
(p. 29) and the definitions that follow them (p. 30):

* `FieldAxioms` — group I, the field axioms 1–9, with the two distinct elements
  0 and 1 assumed in the group's preamble. The book calls any set satisfying
  them a field.
* `OrderedFieldAxioms` — group II, the order axioms 10–13, on top of a field.
  Order is the primitive strict relation `<`.
* `le`, `gt`, `ge`, `IsPositive`, … — the derived notions of p. 30.

Group III (the axiom of Archimedes, Axiom 14, p. 31) and group IV (Cantor's
axiom, Axiom 15, p. 33) are not yet stated.

The book writes the axioms for the real numbers ℝ. They are stated here for an
arbitrary carrier `R`, so that mathlib's `ℝ` and other models can be checked
against them; the book itself uses another ordered field in Remark 3.3 (p. 31).
-/

universe u

namespace Laczkovich.RealAnalysisI.Chapter03

/-- Exactly one of three propositions holds. Used by trichotomy, **Axiom 10**
[Laczkovich–Sós, Ch. 3, p. 29]. -/
def ExactlyOneOf (p q r : Prop) : Prop :=
  (p ∧ ¬ q ∧ ¬ r) ∨ (¬ p ∧ q ∧ ¬ r) ∨ (¬ p ∧ ¬ q ∧ r)

/-- **Group I, the field axioms 1–9** [Laczkovich–Sós, Ch. 3, p. 29].

Two operations, addition and multiplication, and two distinct elements 0 and 1.
Every identity and inverse is on the right, as in the book. -/
structure FieldAxioms (R : Type u) where
  /-- Addition, a primitive operation (group I preamble, p. 29). -/
  add : R → R → R
  /-- Multiplication, a primitive operation (group I preamble, p. 29). -/
  mul : R → R → R
  /-- The element 0 (group I preamble, p. 29). -/
  zero : R
  /-- The element 1 (group I preamble, p. 29). -/
  one : R
  /-- 0 and 1 are distinct. Assumed in the group I preamble, not numbered (p. 29). -/
  zero_ne_one : zero ≠ one
  /-- **Axiom 1** (p. 29): addition is commutative. -/
  add_comm : ∀ a b : R, add a b = add b a
  /-- **Axiom 2** (p. 29): addition is associative. -/
  add_assoc : ∀ a b c : R, add (add a b) c = add a (add b c)
  /-- **Axiom 3** (p. 29): 0 is a right identity for addition. -/
  add_zero : ∀ a : R, add a zero = a
  /-- **Axiom 4** (p. 29): every element has a right additive inverse. -/
  exists_neg : ∀ a : R, ∃ b : R, add a b = zero
  /-- **Axiom 5** (p. 29): multiplication is commutative. -/
  mul_comm : ∀ a b : R, mul a b = mul b a
  /-- **Axiom 6** (p. 29): multiplication is associative. -/
  mul_assoc : ∀ a b c : R, mul (mul a b) c = mul a (mul b c)
  /-- **Axiom 7** (p. 29): 1 is a right identity for multiplication. -/
  mul_one : ∀ a : R, mul a one = a
  /-- **Axiom 8** (p. 29): every nonzero element has a right multiplicative inverse. -/
  exists_inv : ∀ a : R, a ≠ zero → ∃ b : R, mul a b = one
  /-- **Axiom 9** (p. 29): multiplication distributes over addition from the left. -/
  mul_add : ∀ a b c : R, mul a (add b c) = add (mul a b) (mul a c)

/-- **Group II, the order axioms 10–13** [Laczkovich–Sós, Ch. 3, p. 29], on a field.

The primitive is the strict order `<`: for any `a`, `b`, the statement `a < b`
is either true or false. Nothing else about `<` is assumed. -/
structure OrderedFieldAxioms (R : Type u) extends FieldAxioms R where
  /-- The strict order `<`, a primitive relation (group II preamble, p. 29). -/
  lt : R → R → Prop
  /-- **Axiom 10** (p. 29): trichotomy — exactly one of `a < b`, `a = b`, `b < a` holds. -/
  trichotomy : ∀ a b : R, ExactlyOneOf (lt a b) (a = b) (lt b a)
  /-- **Axiom 11** (p. 29): `<` is transitive. -/
  lt_trans : ∀ a b c : R, lt a b ∧ lt b c → lt a c
  /-- **Axiom 12** (p. 29): adding the same element on the right preserves `<`. -/
  add_lt_add_right : ∀ a b c : R, lt a b → lt (add a c) (add b c)
  /-- **Axiom 13** (p. 29): multiplying on the right by a positive element preserves `<`. -/
  mul_lt_mul_of_pos_right : ∀ a b c : R, lt a b ∧ lt zero c → lt (mul a c) (mul b c)

namespace OrderedFieldAxioms

variable {R : Type u} (O : OrderedFieldAxioms R)

/-- `a ≤ b` means `a < b` or `a = b` [Laczkovich–Sós, Ch. 3, p. 30]. -/
def le (a b : R) : Prop := O.lt a b ∨ a = b

/-- `a > b` means `b < a` [Laczkovich–Sós, Ch. 3, p. 30]. -/
def gt (a b : R) : Prop := O.lt b a

/-- `a ≥ b` means `b ≤ a` [Laczkovich–Sós, Ch. 3, p. 30]. -/
def ge (a b : R) : Prop := O.le b a

/-- `a` is positive when `a > 0` [Laczkovich–Sós, Ch. 3, p. 30]. -/
def IsPositive (a : R) : Prop := O.gt a O.zero

/-- `a` is negative when `a < 0` [Laczkovich–Sós, Ch. 3, p. 30]. -/
def IsNegative (a : R) : Prop := O.lt a O.zero

/-- `a` is nonnegative when `a ≥ 0` [Laczkovich–Sós, Ch. 3, p. 30]. -/
def IsNonnegative (a : R) : Prop := O.ge a O.zero

/-- `a` is nonpositive when `a ≤ 0` [Laczkovich–Sós, Ch. 3, p. 30]. -/
def IsNonpositive (a : R) : Prop := O.le a O.zero

end OrderedFieldAxioms

end Laczkovich.RealAnalysisI.Chapter03
