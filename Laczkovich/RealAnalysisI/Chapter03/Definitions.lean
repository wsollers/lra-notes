import Common

/-!
# Laczkovich–Sós, Real Analysis: Foundations and Functions of One Variable, Chapter 3 — Definitions

The field axioms and the order axioms [Laczkovich–Sós, Ch. 3, p. 29], and the
definition of `≤` (p. 30).

**The primitives.** The book assumes two operations, addition and multiplication,
two distinct elements 0 and 1, and a relation `<`. Here they are a carrier `R`
with Lean's notation classes `[Add R] [Mul R] [Zero R] [One R] [LT R]`, so the
axioms read as the book writes them: `a + 0 = a`, `a * (b + c) = …`, `a < b`.
No mathlib is used.

**The axioms are hypotheses, not a bundle.** Each axiom is a `Prop` about `R`.
A theorem takes as hypotheses exactly the axioms it uses, so its signature says
what the book says when it proves a result "from Axioms 1–3".

**Names** follow the Lean naming conventions: each axiom is named after the
Lean name of its statement (Axiom 1 is `AddComm`, after `add_comm`). Where Lean
has no declaration with that statement, the name is built the same way.

**Derived notions (p. 30).** `a > b` and `a ≥ b` are core Lean's definitions,
`b < a` and `b ≤ a`, which are the book's. `≤` is a second relation tied to `<`
by `LeIffLtOrEq`, the book's definition. Positive and negative are written
`0 < a` and `a < 0`.

Not yet stated: the axiom of Archimedes (Axiom 14, p. 31) and Cantor's axiom
(Axiom 15, p. 33).
-/

universe u

namespace Laczkovich.RealAnalysisI.Chapter03

/-! ### Group I: the field axioms (p. 29) -/

/-- **0 ≠ 1**, assumed in the preamble to group I, unnumbered
[Laczkovich–Sós, Ch. 3, p. 29]. Lean: `zero_ne_one`. -/
def ZeroNeOne (R : Type u) [Zero R] [One R] : Prop :=
  (0 : R) ≠ 1

/-- **Axiom 1** [Laczkovich–Sós, Ch. 3, p. 29]: addition is commutative.
Lean: `add_comm`. -/
def AddComm (R : Type u) [Add R] : Prop :=
  ∀ a b : R, a + b = b + a

/-- **Axiom 2** [Laczkovich–Sós, Ch. 3, p. 29]: addition is associative.
Lean: `add_assoc`. -/
def AddAssoc (R : Type u) [Add R] : Prop :=
  ∀ a b c : R, (a + b) + c = a + (b + c)

/-- **Axiom 3** [Laczkovich–Sós, Ch. 3, p. 29]: 0 is a right identity for
addition. Lean: `add_zero`. -/
def AddZero (R : Type u) [Add R] [Zero R] : Prop :=
  ∀ a : R, a + 0 = a

/-- **Axiom 4** [Laczkovich–Sós, Ch. 3, p. 29]: every element has a right
additive inverse. No Lean declaration has this statement: mathlib's
`add_neg_cancel` presupposes the operation `-a`, which the book defines only
after uniqueness (Theorem 3.28). -/
def ExistsAddEqZero (R : Type u) [Add R] [Zero R] : Prop :=
  ∀ a : R, ∃ b : R, a + b = 0

/-- **Axiom 5** [Laczkovich–Sós, Ch. 3, p. 29]: multiplication is commutative.
Lean: `mul_comm`. -/
def MulComm (R : Type u) [Mul R] : Prop :=
  ∀ a b : R, a * b = b * a

/-- **Axiom 6** [Laczkovich–Sós, Ch. 3, p. 29]: multiplication is associative.
Lean: `mul_assoc`. -/
def MulAssoc (R : Type u) [Mul R] : Prop :=
  ∀ a b c : R, (a * b) * c = a * (b * c)

/-- **Axiom 7** [Laczkovich–Sós, Ch. 3, p. 29]: 1 is a right identity for
multiplication. Lean: `mul_one`. -/
def MulOne (R : Type u) [Mul R] [One R] : Prop :=
  ∀ a : R, a * 1 = a

/-- **Axiom 8** [Laczkovich–Sós, Ch. 3, p. 29]: every nonzero element has a right
multiplicative inverse. No Lean declaration has this statement; compare Axiom 4. -/
def ExistsMulEqOneOfNeZero (R : Type u) [Mul R] [Zero R] [One R] : Prop :=
  ∀ a : R, a ≠ 0 → ∃ b : R, a * b = 1

/-- **Axiom 9** [Laczkovich–Sós, Ch. 3, p. 29]: multiplication distributes over
addition from the left. Lean: `mul_add`. -/
def MulAdd (R : Type u) [Add R] [Mul R] : Prop :=
  ∀ a b c : R, a * (b + c) = a * b + a * c

/-! ### Group II: the order axioms (p. 29) -/

/-- **Axiom 10** [Laczkovich–Sós, Ch. 3, p. 29]: for any `a`, `b`, exactly one of
`a < b`, `a = b`, `b < a` holds.

No Lean declaration has this statement. Lean splits it in three: `lt_trichotomy`
(at least one holds), `lt_irrefl` and `lt_asymm` (no two hold). Those are
derived from this axiom in `Theorems.lean`. -/
def LtTrichotomyExclusive (R : Type u) [LT R] : Prop :=
  ∀ a b : R,
    (a < b ∧ ¬ a = b ∧ ¬ b < a) ∨
    (¬ a < b ∧ a = b ∧ ¬ b < a) ∨
    (¬ a < b ∧ ¬ a = b ∧ b < a)

/-- **Axiom 11** [Laczkovich–Sós, Ch. 3, p. 29]: `<` is transitive.
Lean: `lt_trans`, which states it in curried form. -/
def LtTrans (R : Type u) [LT R] : Prop :=
  ∀ a b c : R, a < b ∧ b < c → a < c

/-- **Axiom 12** [Laczkovich–Sós, Ch. 3, p. 29]: adding the same element on the
right preserves `<`. Lean: `add_lt_add_left`. Note that mathlib's
`add_lt_add_right` adds on the *left* (`a + b < a + c`). -/
def AddLtAddLeft (R : Type u) [Add R] [LT R] : Prop :=
  ∀ a b c : R, a < b → a + c < b + c

/-- **Axiom 13** [Laczkovich–Sós, Ch. 3, p. 29]: multiplying on the right by a
positive element preserves `<`. Lean: `mul_lt_mul_of_pos_right`. -/
def MulLtMulOfPosRight (R : Type u) [Mul R] [Zero R] [LT R] : Prop :=
  ∀ a b c : R, a < b ∧ 0 < c → a * c < b * c

/-! ### Definitions after the axioms (p. 30) -/

/-- **Definition of `≤`** [Laczkovich–Sós, Ch. 3, p. 30]: `a ≤ b` means `a < b`
or `a = b`. Lean: `le_iff_lt_or_eq`. As in mathlib, `≤` is its own relation,
and this law ties it to `<`. -/
def LeIffLtOrEq (R : Type u) [LT R] [LE R] : Prop :=
  ∀ a b : R, a ≤ b ↔ a < b ∨ a = b

end Laczkovich.RealAnalysisI.Chapter03
