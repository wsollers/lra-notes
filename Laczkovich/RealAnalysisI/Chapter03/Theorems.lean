import Laczkovich.RealAnalysisI.Chapter03.Definitions

/-!
# Laczkovich–Sós, Real Analysis: Foundations and Functions of One Variable, Chapter 3 — Theorems

Results before the chapter's first section. Prose notes belong in the chapter's
notes.tex.

**Lean's order facts from the book's axioms.** The book never states
irreflexivity, asymmetry, or any property of `≤`; they are implicit in Axioms
10 and 11 and used freely from p. 30 on. Each is stated here under its Lean
name, with exactly the axioms it needs as hypotheses. None is a book result.
-/

universe u

namespace Laczkovich.RealAnalysisI.Chapter03

variable {R : Type u}

/-! ### `<`, from Axiom 10 -/

/-- Not in the book: at least one of `a < b`, `a = b`, `b < a` holds — the
existence half of **Axiom 10** [Laczkovich–Sós, Ch. 3, p. 29].
Lean: `lt_trichotomy`. -/
theorem lt_trichotomy [LT R] (h10 : LtTrichotomyExclusive R) (a b : R) :
    a < b ∨ a = b ∨ b < a := by
  sorry

/-- Not in the book: no element is less than itself. Implicit in **Axiom 10**
[Laczkovich–Sós, Ch. 3, p. 29]. Lean: `lt_irrefl`. -/
theorem lt_irrefl [LT R] (h10 : LtTrichotomyExclusive R) (a : R) :
    ¬ a < a := by
  sorry

/-- Not in the book: `a < b` and `b < a` never both hold. Implicit in
**Axiom 10** [Laczkovich–Sós, Ch. 3, p. 29]. Lean: `lt_asymm`. -/
theorem lt_asymm [LT R] (h10 : LtTrichotomyExclusive R) {a b : R} :
    a < b → ¬ b < a := by
  sorry

/-! ### `≤`, from its definition (p. 30) and Axioms 10–11 -/

/-- Not in the book: `≤` is reflexive. Follows from the definition of `≤`
[Laczkovich–Sós, Ch. 3, p. 30]. Lean: `le_refl`. -/
theorem le_refl [LT R] [LE R] (hle : LeIffLtOrEq R) (a : R) :
    a ≤ a := by
  sorry

/-- Not in the book: `≤` is antisymmetric. Follows from the definition of `≤`
(p. 30) and **Axiom 10** (p. 29) [Laczkovich–Sós, Ch. 3]. Lean: `le_antisymm`. -/
theorem le_antisymm [LT R] [LE R] (hle : LeIffLtOrEq R) (h10 : LtTrichotomyExclusive R)
    {a b : R} : a ≤ b → b ≤ a → a = b := by
  sorry

/-- Not in the book: `≤` is transitive. Follows from the definition of `≤`
(p. 30) and **Axiom 11** (p. 29) [Laczkovich–Sós, Ch. 3]. Lean: `le_trans`. -/
theorem le_trans [LT R] [LE R] (hle : LeIffLtOrEq R) (h11 : LtTrans R)
    {a b c : R} : a ≤ b → b ≤ c → a ≤ c := by
  sorry

/-- Not in the book: any two elements are comparable under `≤`. Follows from the
definition of `≤` (p. 30) and **Axiom 10** (p. 29) [Laczkovich–Sós, Ch. 3].
Lean: `le_total`. -/
theorem le_total [LT R] [LE R] (hle : LeIffLtOrEq R) (h10 : LtTrichotomyExclusive R)
    (a b : R) : a ≤ b ∨ b ≤ a := by
  sorry

/-! ### Absolute value (p. 30)

The book lists these right after Definition 3.1, unnumbered, as easy to check
from the definition and the order axioms; it gives no proofs. They are stated
for a field (Axioms 1–9) with the order axioms 10–13, the definition of `≤`,
and the book's `−a`, `1/a` and `a/c`. The book stops short of saying which
axioms each one needs. -/

section AbsoluteValue

variable [Add R] [Mul R] [Zero R] [One R] [LT R] [LE R] [Neg R] [Div R]
variable (hF : IsField R) (h10 : LtTrichotomyExclusive R) (h11 : LtTrans R)
  (h12 : AddLtAddLeft R) (h13 : MulLtMulOfPosRight R) (hle : LeIffLtOrEq R)
  (hneg : AddNegCancel R) (hinv : MulOneDivCancel R) (hdiv : DivEqMulOneDiv R)
include hF h10 h11 h12 h13 hle hneg hinv hdiv

/-- [Laczkovich–Sós, Ch. 3, p. 30]: `|a| ≥ 0`. Lean: `abs_nonneg`. -/
theorem abs_nonneg (a : R) : 0 ≤ abs a := by
  sorry

/-- [Laczkovich–Sós, Ch. 3, p. 30]: `|a| = 0` if and only if `a = 0`.
Lean: `abs_eq_zero`. -/
theorem abs_eq_zero (a : R) : abs a = 0 ↔ a = 0 := by
  sorry

/-- [Laczkovich–Sós, Ch. 3, p. 30]: `|a| = |−a|`. Lean: `abs_neg`, which states
it the other way round. -/
theorem abs_neg (a : R) : abs (-a) = abs a := by
  sorry

/-- [Laczkovich–Sós, Ch. 3, p. 30]: `|a · b| = |a| · |b|`. Lean: `abs_mul`. -/
theorem abs_mul (a b : R) : abs (a * b) = abs a * abs b := by
  sorry

/-- [Laczkovich–Sós, Ch. 3, p. 30]: for `b ≠ 0`, `|1/b| = 1/|b|`. Lean:
`abs_one_div`, which mathlib states for every `b` because it sets `1/0 = 0`. -/
theorem abs_one_div (b : R) (hb : b ≠ 0) : abs (1 / b) = 1 / abs b := by
  sorry

/-- [Laczkovich–Sós, Ch. 3, p. 30]: for `b ≠ 0`, `|a/b| = |a|/|b|`. Lean:
`abs_div`, stated in mathlib for every `b`. -/
theorem abs_div (a b : R) (hb : b ≠ 0) : abs (a / b) = abs a / abs b := by
  sorry

/-- **Triangle Inequality** [Laczkovich–Sós, Ch. 3, p. 30]:
`|a + b| ≤ |a| + |b|`. Lean: `abs_add_le`. -/
theorem abs_add_le (a b : R) : abs (a + b) ≤ abs a + abs b := by
  sorry

end AbsoluteValue

end Laczkovich.RealAnalysisI.Chapter03
