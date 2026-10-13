# Source audit — 2026-10-13

Each formalized declaration was checked against the book PDF for numbering,
label, and statement fidelity. Structural fixes (file placement, section
layout, citations, over-long quotations) were applied at the time. **No
mathematical statement was changed.** The items below are mathematics left for
you; corrected statements are given without proofs.

Book references are paraphrased; page numbers are the printed ones.

## Zorich, *Mathematical Analysis I*, §2.1

- [ ] **`AdditiveInverseUniqueInReals` is vacuous.** Its hypothesis
  `∀ x y : ℝ, x + y = 0` is false, and its binders shadow the theorem's `x, y`.
  The book's a.2° (p. 39) says any two negatives of `x` coincide:
  ```lean
  theorem AdditiveInverseUniqueInReals (x y₁ y₂ : ℝ)
      (h₁ : x + y₁ = 0) (h₂ : x + y₂ = 0) : y₁ = y₂ := by sorry
  ```
- [ ] **a.3°, the additive equation, is missing.** `LinearEquationUniqueSolutionInReals`
  and `MulEquationUniqueSolutionInReals` state the same multiplicative result
  (b.3°, p. 40). The additive one (p. 40):
  ```lean
  theorem LinearEquationUniqueSolutionInReals (a b : ℝ) :
      ∃! x : ℝ, a + x = b := by sorry
  ```
  and b.3° in the book's existence-and-uniqueness form:
  ```lean
  theorem MulEquationUniqueSolutionInReals (a b : ℝ) (ha : a ≠ 0) :
      ∃! x : ℝ, a * x = b := by sorry
  ```
- [ ] **`RealTrichotomy` is weaker than d.1° (p. 41).** The book says exactly
  one of `x < y`, `x = y`, `y < x` holds; the Lean states at least one.
- [ ] **`OrderFragmentTrichotomy`** is a `def` that restates totality (3≤) with
  an extra `x = y` disjunct; it is not the book's trichotomy, which uses strict
  order. Strict order is not yet defined over `OrderFragment`.
- [ ] **`MultiplicativeFieldFragment` omits `1 ≠ 0`**, which is part of axiom 1•
  (p. 37). It appears only later, in `FieldFragment`.
- [ ] **`OrderFragment` is not tied to the field operations**: its `add`, `mul`,
  `zero` are independent of `FieldFragment`. Its field
  `multiplication_preserves_order` states non-negativity of products (II, III).
- [ ] **Completeness (IV, p. 38) is not formalized**, and no structure assembles
  Definition 1 as a whole.
- [ ] The consequences are proved on mathlib's ℝ (`simp`, `linarith`), not
  derived from the fragment structures, so they do not yet exercise the book's
  derivations.
- Not yet formalized: b.1°, b.2°, c.1°–5°, d.2°, e.1°–2°.

## Laczkovich–Sós, *Real Analysis: Foundations and Functions of One Variable*, Ch. 3

- [x] **Groups I and II restated from the book** (p. 29) on the `laczkovich-p29`
  branch: 0 ≠ 1, Axioms 1–13 and the definition of `≤` (p. 30) are individual
  `Prop`s over core notation classes, with `<` primitive and one-sided field
  axioms as in the book. The old `RealAxiomSystem` (with `≤` primitive,
  two-sided axioms and Zorich's cut axiom) was removed.
- [x] **p. 29–30 definitions and facts, through the Triangle Inequality**: −a,
  1/a and a/c (as laws on Lean's `-` and `/`), "field" (`IsField`), the p. 30
  vocabulary (positive … nonpositive), ℕ⁺, ℤ, ℕ, rational, irrational,
  Definition 3.1 (`abs`), and the unnumbered absolute-value facts up to the
  Triangle Inequality (`abs_add_le`). Proofs are `sorry`.
- [ ] Next on p. 30: the reverse triangle inequality `||a| − |b|| ≤ |a − b|`.
- [ ] **Axiom 14** (Archimedes, group III, p. 31) and **Axiom 15** (Cantor's
  nested-interval axiom, group IV, p. 33) are not yet stated:
  ```lean
  archimedes : ∀ b : R, ∃ n : ℕ, b < nat n                                 -- 14
  cantor : ∀ a b : ℕ → R, (∀ n, a n < b n) →
             (∀ n, a n ≤ a (n+1) ∧ b (n+1) ≤ b n) →
             ∃ x, ∀ n, a n ≤ x ∧ x ≤ b n                                   -- 15
  ```
  where `nat : ℕ → R` embeds 1, 1 + 1, … (the book's ℕ⁺, p. 30).
- [ ] **Theorem 3.2** (a rational between two reals, p. 31; Lean `exists_rat_btwn`)
  waits for Axiom 14 and the book's ℚ (p. 30).
- Lean's order facts (`lt_trichotomy`, `lt_irrefl`, `lt_asymm`, `le_refl`,
  `le_antisymm`, `le_trans`, `le_total`) are stated as non-book lemmas from
  Axioms 10–11; the book never states them (searched: no occurrences).

## Thomson–Bruckner–Bruckner, *Elementary Real Analysis*, §§1.4–1.6

- [ ] **The Completeness Axiom is a `sorry`'d theorem**, and `extSup` / `extInf`
  are built on it, so everything downstream inherits the `sorry`. Either make it
  an `axiom`, or prove it from mathlib (`Real.exists_isLUB`) and note it is an
  axiom in the book.
- [ ] `completeness_axiom_below` is the book's **Exercise 1.6.19**, not an
  axiom; it duplicates `exercise_1_6_19`.
- [ ] `bounded_sets_have_bounds` duplicates `exercise_1_6_1`.
- [ ] `exercise_1_6_23_nat_complement_dist` has an unused `(δ : ℝ)` parameter
  and covers only part (a).
- [ ] `exercise_1_6_17` adds hypotheses the book does not have (harmless).
- Not yet formalized: Exercises 1.6.2, 1.6.5, 1.6.6, 1.6.12, 1.6.15, 1.6.20–22,
  1.6.23(b–d).

## Munkres, *Topology*, Ch. 1 §2

- [ ] **Lemma 2.1** and **Exercise 2.5(e)** omit the conclusion that both
  inverses equal `f⁻¹`, and state the same result twice.
- [ ] Exercises 2.4(c) and 2.4(e) encode only the positive halves; the negative
  answers belong as `counterexample`s in `Section02/Examples.lean`.
- Part numbers are sequential rather than the book's letters (e.g. Exercise 2's
  parts 7–8 are (g)). Not yet formalized: 2.4(f), 2.5(d), 2.6.

## Enderton, *Elements of Set Theory*

- Faithful. `NoUniversalSet` / `NoUniversalSet2` are Theorem 2A (Ch. 2, p. 22)
  and now live in `Chapter02`. `NoUniversalSet2` follows the book's proof.
