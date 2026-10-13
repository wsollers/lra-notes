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

- [ ] **`RealAxiomSystem` is not this book's axiom system** (pp. 29–33):
  - the book's group IV is **Cantor's nested-interval axiom** (Axiom 15); the
    Lean uses Zorich's separation (cut) form;
  - the **axiom of Archimedes (14, group III) is missing** — with Cantor's
    axiom it is independent and required;
  - the book's primitive is **`<`** (with `≤` defined from it), not `≤`;
  - the field axioms are one-sided in the book (3, 4, 7, 8) and distributivity
    is left-sided (9); the Lean versions are two-sided / right-sided;
  - group labels in the comments do not match the book (I = field, II = order,
    III = Archimedes, IV = Cantor).

  Book-faithful fields, with `lt` primitive, `le a b := lt a b ∨ a = b`, and
  `nat : ℕ → R` the embedding built from `one`:
  ```lean
  add_comm   : ∀ a b, add a b = add b a                                  -- 1
  add_assoc  : ∀ a b c, add (add a b) c = add a (add b c)                -- 2
  add_zero   : ∀ a, add a zero = a                                       -- 3
  exists_neg : ∀ a, ∃ b, add a b = zero                                  -- 4
  mul_comm   : ∀ a b, mul a b = mul b a                                  -- 5
  mul_assoc  : ∀ a b c, mul (mul a b) c = mul a (mul b c)                -- 6
  mul_one    : ∀ a, mul a one = a                                        -- 7
  exists_inv : ∀ a, a ≠ zero → ∃ b, mul a b = one                        -- 8
  distrib    : ∀ a b c, mul a (add b c) = add (mul a b) (mul a c)        -- 9
  trichotomy : ∀ a b, (lt a b ∧ a ≠ b ∧ ¬ lt b a) ∨ (¬ lt a b ∧ a = b ∧ ¬ lt b a)
                      ∨ (¬ lt a b ∧ a ≠ b ∧ lt b a)                      -- 10
  lt_trans   : ∀ a b c, lt a b → lt b c → lt a c                         -- 11
  add_lt_add_right : ∀ a b c, lt a b → lt (add a c) (add b c)            -- 12
  mul_lt_mul_pos   : ∀ a b c, lt a b → lt zero c → lt (mul a c) (mul b c) -- 13
  archimedes : ∀ b : R, ∃ n : ℕ, lt b (nat n)                            -- 14
  cantor : ∀ a b : ℕ → R, (∀ n, lt (a n) (b n)) →
             (∀ n, le (a n) (a (n+1)) ∧ le (b (n+1)) (b n)) →
             ∃ x, ∀ n, le (a n) x ∧ le x (b n)                           -- 15
  ```
  `one_ne_zero` stays: the book assumes it before numbering the axioms. If you
  want the cut form too, keep it in a separate Zorich-attributed structure and
  prove the equivalence.
- [ ] **Theorem 3.2** (renamed from `Archimedes` to `RationalBetweenReals`) is
  stated over mathlib's ℝ, not over `RealAxiomSystem`, and is `sorry`.
- `AdditiveIdentityUnique` and the three `…Inverse…` restatements are not book
  results; `AdditiveInverseUnique` is Theorem 3.28 (§3.4, p. 48).

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
