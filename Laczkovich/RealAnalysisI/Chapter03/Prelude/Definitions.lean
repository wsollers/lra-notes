import Common

/-!
# Laczkovich–Sós, Real Analysis: Foundations and Functions of One Variable, Chapter 3 introduction (pp. 27–36, before §3.1) — Definitions

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
`AddZero` and `MulOne` are also mathlib class names (a type with `+` and `0`, or
`*` and `1`); inside this namespace these definitions take precedence.

**Core Lean's names for the laws.** Where core Lean has a class for a law, the
axiom is defined *as* that class, so unfolding it shows Lean's name:
`unfold AddComm at h` gives `h : Std.Commutative (· + ·)`, and
`obtain ⟨comm⟩ := h` then gives `comm : ∀ a b, a + b = b + a`. The field can also
be used directly, as `h.comm a b`. Axioms 1–3 and 5–7 are defined this way; the
others have no core class and are stated directly.

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
Lean: `add_comm`.
Defined as core Lean's `Std.Commutative`; its field `comm` states
`∀ a b : R, a + b = b + a`. -/
abbrev AddComm (R : Type u) [Add R] : Prop :=
  Std.Commutative (α := R) (· + ·)

/-- **Axiom 2** [Laczkovich–Sós, Ch. 3, p. 29]: addition is associative.
Lean: `add_assoc`.
Defined as core Lean's `Std.Associative`; its field `assoc` states
`∀ a b c : R, (a + b) + c = a + (b + c)`. -/
abbrev AddAssoc (R : Type u) [Add R] : Prop :=
  Std.Associative (α := R) (· + ·)

/-- **Axiom 3** [Laczkovich–Sós, Ch. 3, p. 29]: 0 is a right identity for
addition. Lean: `add_zero`.
Defined as core Lean's `Std.LawfulRightIdentity`; its field `right_id` states
`∀ a : R, a + 0 = a`. -/
abbrev AddZero (R : Type u) [Add R] [Zero R] : Prop :=
  Std.LawfulRightIdentity (α := R) (β := R) (· + ·) 0

/-- **Axiom 4** [Laczkovich–Sós, Ch. 3, p. 29]: every element has a right
additive inverse. No Lean declaration has this statement: mathlib's
`add_neg_cancel` presupposes the operation `-a`, which the book defines only
after uniqueness (Theorem 3.28). -/
def ExistsAddEqZero (R : Type u) [Add R] [Zero R] : Prop :=
  ∀ a : R, ∃ b : R, a + b = 0

/-- **Axiom 5** [Laczkovich–Sós, Ch. 3, p. 29]: multiplication is commutative.
Lean: `mul_comm`.
Defined as core Lean's `Std.Commutative`; its field `comm` states
`∀ a b : R, a * b = b * a`. -/
abbrev MulComm (R : Type u) [Mul R] : Prop :=
  Std.Commutative (α := R) (· * ·)

/-- **Axiom 6** [Laczkovich–Sós, Ch. 3, p. 29]: multiplication is associative.
Lean: `mul_assoc`.
Defined as core Lean's `Std.Associative`; its field `assoc` states
`∀ a b c : R, (a * b) * c = a * (b * c)`. -/
abbrev MulAssoc (R : Type u) [Mul R] : Prop :=
  Std.Associative (α := R) (· * ·)

/-- **Axiom 7** [Laczkovich–Sós, Ch. 3, p. 29]: 1 is a right identity for
multiplication. Lean: `mul_one`.
Defined as core Lean's `Std.LawfulRightIdentity`; its field `right_id` states
`∀ a : R, a * 1 = a`. -/
abbrev MulOne (R : Type u) [Mul R] [One R] : Prop :=
  Std.LawfulRightIdentity (α := R) (β := R) (· * ·) 1

/-- **Axiom 8** [Laczkovich–Sós, Ch. 3, p. 29]: every nonzero element has a right
multiplicative inverse. No Lean declaration has this statement; compare Axiom 4. -/
def ExistsMulEqOneOfNeZero (R : Type u) [Mul R] [Zero R] [One R] : Prop :=
  ∀ a : R, a ≠ 0 → ∃ b : R, a * b = 1

/-- **Axiom 9** [Laczkovich–Sós, Ch. 3, p. 29]: multiplication distributes over
addition from the left. Lean: `mul_add`. -/
def MulAdd (R : Type u) [Add R] [Mul R] : Prop :=
  ∀ a b c : R, a * (b + c) = a * b + a * c

/-! ### After the field axioms: −a, 1/a, a/c, and "field" (p. 29)

The book names the inverse that Axiom 4 provides `−a`, and the one Axiom 8
provides `1/a`, as soon as the axioms are stated; their uniqueness is proved
later (Theorems 3.28 and 3.30). As with `≤`, Lean's own symbols `-a` and `/`
(`[Neg R] [Div R]`) are used, tied to the book's definitions by a law. Any
symbol satisfying the law is the book's `−a` or `1/a`, by that uniqueness. -/

/-- **−a** [Laczkovich–Sós, Ch. 3, p. 29]: the element `b` with `a + b = 0`,
unique by Theorem 3.28. Lean: `add_neg_cancel`. -/
def AddNegCancel (R : Type u) [Add R] [Neg R] [Zero R] : Prop :=
  ∀ a : R, a + -a = 0

/-- **1/a** [Laczkovich–Sós, Ch. 3, p. 29], for `a ≠ 0`: the element `b` with
`a · b = 1`, unique by Theorem 3.30. Lean: `mul_one_div_cancel`. -/
def MulOneDivCancel (R : Type u) [Mul R] [Div R] [Zero R] [One R] : Prop :=
  ∀ a : R, a ≠ 0 → a * (1 / a) = 1

/-- **a/c** [Laczkovich–Sós, Ch. 3, p. 29]: `a · (1/c)`, for `c ≠ 0`.
Lean: `div_eq_mul_one_div`, which mathlib states for every `c`. -/
def DivEqMulOneDiv (R : Type u) [Mul R] [Div R] [Zero R] [One R] : Prop :=
  ∀ a c : R, c ≠ 0 → a / c = a * (1 / c)

/-- **Field** [Laczkovich–Sós, Ch. 3, p. 29]: a set with two operations and
distinct elements 0 and 1 satisfying Axioms 1–9, the **field axioms**.
Mathlib also has an `IsField`, for rings in which every nonzero element is
invertible; this one is the book's definition. -/
structure IsField (R : Type u) [Add R] [Mul R] [Zero R] [One R] : Prop where
  zero_ne_one : ZeroNeOne R
  add_comm : AddComm R
  add_assoc : AddAssoc R
  add_zero : AddZero R
  exists_add_eq_zero : ExistsAddEqZero R
  mul_comm : MulComm R
  mul_assoc : MulAssoc R
  mul_one : MulOne R
  exists_mul_eq_one_of_ne_zero : ExistsMulEqOneOfNeZero R
  mul_add : MulAdd R

/-! ### Group II: the order axioms (p. 29) -/

/-- **Axiom 10** [Laczkovich–Sós, Ch. 3, p. 29]: for any `a`, `b`, exactly one of
`a < b`, `a = b`, `b < a` holds.

No Lean declaration has this statement. Lean splits it in three: `lt_trichotomy`
(at least one holds), `lt_irrefl` and `lt_asymm` (no two hold). Those are
derived from this axiom in `Observations.lean`. -/
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

/-! ### Vocabulary (p. 30)

The book bolds these terms as definitions it uses from here on. Lean has no
predicates for them and writes `0 < a`; they are `abbrev`s, so a hypothesis
`IsPositive a` is `0 < a` to Lean with no unfolding needed. -/

section Vocabulary

variable {R : Type u}

/-- **positive** [Laczkovich–Sós, Ch. 3, p. 30]: `a > 0`. -/
abbrev IsPositive [Zero R] [LT R] (a : R) : Prop := 0 < a

/-- **negative** [Laczkovich–Sós, Ch. 3, p. 30]: `a < 0`. -/
abbrev IsNegative [Zero R] [LT R] (a : R) : Prop := a < 0

/-- **nonnegative** [Laczkovich–Sós, Ch. 3, p. 30]: `a ≥ 0`. -/
abbrev IsNonnegative [Zero R] [LE R] (a : R) : Prop := 0 ≤ a

/-- **nonpositive** [Laczkovich–Sós, Ch. 3, p. 30]: `a ≤ 0`. -/
abbrev IsNonpositive [Zero R] [LE R] (a : R) : Prop := a ≤ 0

end Vocabulary

/-! ### The natural numbers, integers and rationals (p. 30)

The book introduces these as subsets of the reals without developing them.
Lean's `ℕ` serves only to count the repeated additions of 1. Core Lean has no
`Set`, so each subset is a predicate. -/

section NumberSets

variable {R : Type u}

/-- Repeatedly adding 1: `0, 1, 1 + 1, 1 + 1 + 1, …` [Laczkovich–Sós, Ch. 3,
p. 30]. Lean: `Nat.unaryCast`. -/
def unaryCast [Zero R] [One R] [Add R] : Nat → R
  | 0 => 0
  | n + 1 => unaryCast n + 1

/-- **natural numbers** ℕ⁺ [Laczkovich–Sós, Ch. 3, p. 30]: `1, 1 + 1, 1 + 1 + 1, …`.
Lean's type of positive naturals is `ℕ+` (`PNat`). -/
def IsPNat [Zero R] [One R] [Add R] (x : R) : Prop :=
  ∃ n : Nat, 1 ≤ n ∧ x = unaryCast n

/-- **integers** ℤ [Laczkovich–Sós, Ch. 3, p. 30]: the natural numbers, their
negatives, and 0. -/
def IsInt [Zero R] [One R] [Add R] [Neg R] (x : R) : Prop :=
  IsPNat x ∨ (∃ n : R, IsPNat n ∧ x = -n) ∨ x = 0

/-- ℕ := ℕ⁺ ∪ {0} [Laczkovich–Sós, Ch. 3, p. 30]. -/
def IsNat [Zero R] [One R] [Add R] (x : R) : Prop :=
  IsPNat x ∨ x = 0

/-- **rational** [Laczkovich–Sós, Ch. 3, p. 30]: `x = p/q` with `p, q ∈ ℤ` and
`q ≠ 0`; ℚ is the set of rational numbers. -/
def IsRat [Zero R] [One R] [Add R] [Neg R] [Div R] (x : R) : Prop :=
  ∃ p q : R, IsInt p ∧ IsInt q ∧ q ≠ 0 ∧ x = p / q

/-- **irrational** [Laczkovich–Sós, Ch. 3, p. 30]: not rational.
Lean: `Irrational`. -/
def Irrational [Zero R] [One R] [Add R] [Neg R] [Div R] (x : R) : Prop :=
  ¬ IsRat x

end NumberSets

/-! ### Absolute value (p. 30) -/

section AbsoluteValue

variable {R : Type u}

open Classical in
/-- **Definition 3.1** [Laczkovich–Sós, Ch. 3, p. 30]: the *absolute value* of
`a` is `a` if `a ≥ 0` and `−a` if `a < 0`. Lean: `abs`, written `|a|`; mathlib
defines it as `max a (-a)`. The `else` branch is "not `a ≥ 0`", which is the
book's `a < 0` given Axiom 10 and the definition of `≤`. Noncomputable because
whether `a ≥ 0` is not decidable for an arbitrary `R`. -/
noncomputable def abs [Zero R] [LE R] [Neg R] (a : R) : R :=
  if 0 ≤ a then a else -a

end AbsoluteValue

end Laczkovich.RealAnalysisI.Chapter03
