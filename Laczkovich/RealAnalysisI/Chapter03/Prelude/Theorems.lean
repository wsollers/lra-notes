import Laczkovich.RealAnalysisI.Chapter03.Prelude.Observations

/-!
# Laczkovich–Sós, Real Analysis: Foundations and Functions of One Variable, Chapter 3 introduction (pp. 27–36, before §3.1) — Theorems

What the book states before §3.1, with its page. Facts we derive ourselves
(the order facts the book uses without stating) are in `Observations.lean`.
-/

universe u

namespace Laczkovich.RealAnalysisI.Chapter03

variable {R : Type u}

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
