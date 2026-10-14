import Laczkovich.RealAnalysisI.Chapter03.Prelude.Definitions

/-!
# Laczkovich–Sós, Real Analysis: Foundations and Functions of One Variable, Chapter 3 introduction (pp. 27–36, before §3.1) — Observations

Facts we derive that the book does not state. `Theorems.lean` holds only what
the book states; anything here has no page of its own, only the axioms it
comes from.

**Lean's order facts from the book's axioms.** The book never states
irreflexivity, asymmetry, or any property of `≤`; they are implicit in Axioms
10 and 11 and used freely from p. 30 on. Each is stated here under its Lean
name, with exactly the axioms it needs as hypotheses.

The first three are corollaries of Axiom 10 alone: together they say exactly
what it says, split the way Lean splits it — `lt_trichotomy` (at least one
holds) and `lt_irrefl`, `lt_asymm` (no two hold).
-/

universe u

namespace Laczkovich.RealAnalysisI.Chapter03

variable {R : Type u}

/-! ### `<`, from Axiom 10 -/

/-- Corollary of **Axiom 10** [Laczkovich–Sós, Ch. 3, p. 29]; not in the book.
At least one of `a < b`, `a = b`, `b < a` holds: the axiom's "exactly one"
weakened to "at least one". Lean: `lt_trichotomy`. -/
corollary lt_trichotomy [LT R] (h_ax10_trichotomy : LtTrichotomyExclusive R) (a b : R) :
    a < b ∨ a = b ∨ b < a := by
  rcases h_ax10_trichotomy a b with h | h | h
  . --
    have hab : a < b := h.1
    left
    exact hab
  . --
    have heq : a = b := h.2.1
    right
    left
    exact heq
  . --
    have hgt : a > b := h.2.2
    right
    right
    exact hgt


/-- Corollary of **Axiom 10** [Laczkovich–Sós, Ch. 3, p. 29]; not in the book.
No element is less than itself. Lean: `lt_irrefl`. -/
corollary lt_irrefl [LT R] (h_ax10_trichotomy : LtTrichotomyExclusive R) (a : R) :
    ¬ a < a := by
  rcases h_ax10_trichotomy a a with h | h | h
  · --
    have hnlt : ¬ a < a := h.2.2
    exact hnlt
  · --
    have hnlt : ¬ a < a := h.2.2
    exact hnlt
  · --
    have hnlt : ¬ a < a := h.1
    exact hnlt

/-- Corollary of **Axiom 10** [Laczkovich–Sós, Ch. 3, p. 29]; not in the book.
`a < b` and `b < a` never both hold. Lean: `lt_asymm`. -/
corollary lt_asymm [LT R] (h_ax10_trichotomy : LtTrichotomyExclusive R) {a b : R} :
    a < b → ¬ b < a := by
  intro haltb
  rcases h_ax10_trichotomy a b with h | h | h
  · -- Case 1: a < b
    exact h.2.2
  · -- Case 2: a = b (contradicts a < b)
    exact h.2.2
  · -- Case 3: b < a (contradicts a < b)
    have h_not := h.1
    contradiction


/-! ### `≤`, from its definition (p. 30) and Axioms 10–11 -/

/-- Not in the book: `≤` is reflexive. Follows from the definition of `≤`
[Laczkovich–Sós, Ch. 3, p. 30]. Lean: `le_refl`. -/
theorem le_refl [LT R] [LE R] (d_le : LeIffLtOrEq R) (a : R) :
    a ≤ a := by
  unfold LeIffLtOrEq at d_le
  rw [d_le]
  exact Or.inr (Eq.refl a)

/-- Not in the book: `≤` is antisymmetric. Follows from the definition of `≤`
(p. 30) and **Axiom 10** (p. 29) [Laczkovich–Sós, Ch. 3]. Lean: `le_antisymm`. -/
theorem le_antisymm [LT R] [LE R] (d_le : LeIffLtOrEq R)
    (h_ax10_trichotomy : LtTrichotomyExclusive R)
    {a b : R} : a ≤ b → b ≤ a → a = b := by
  sorry

/-- Not in the book: `≤` is transitive. Follows from the definition of `≤`
(p. 30) and **Axiom 11** (p. 29) [Laczkovich–Sós, Ch. 3]. Lean: `le_trans`. -/
theorem le_trans [LT R] [LE R] (d_le : LeIffLtOrEq R) (h_ax11_lt_trans : LtTrans R)
    {a b c : R} : a ≤ b → b ≤ c → a ≤ c := by
  sorry

/-- Not in the book: any two elements are comparable under `≤`. Follows from the
definition of `≤` (p. 30) and **Axiom 10** (p. 29) [Laczkovich–Sós, Ch. 3].
Lean: `le_total`. -/
theorem le_total [LT R] [LE R] (d_le : LeIffLtOrEq R)
    (h_ax10_trichotomy : LtTrichotomyExclusive R)
    (a b : R) : a ≤ b ∨ b ≤ a := by
  sorry

end Laczkovich.RealAnalysisI.Chapter03
