# Pain Points: Lean + Mathlib

This document diagnoses the recurring issues that appeared while working through the Lean notes in this project. The pattern is not a lack of mathematical understanding so much as a mismatch between three things:

1. the shape of the goal,
2. the shape of the assumptions/hypotheses,
3. the theorem that actually matches the statement.

The key weakness is not “doing math,” but “reading Lean goals correctly and choosing the right theorem.”

## 1. Confusing the goal with the hypothesis

A major repeated issue was failing to distinguish:

- the goal you are trying to prove
- the assumptions already available in context
- the theorem that turns the assumptions into the goal

Examples from this work:

- `show x * (y + z) = (x * y) + (x * z)` was wrong when the target was already a different distributive formulation.
- `show x ≤ y ∧ y ≤ x → x = y` was not the right way to attack the goal before introducing the hypothesis.
- `le_antisymm` was correct for equality, but not for a nonnegativity goal.

Pattern:

- The user often wrote a `show` statement that looked plausible but did not match the current target.
- Lean then rejected the proof because the expression was not definitionally equal to the goal.

Fix:

- Always inspect the exact goal first.
- Use `intro` to expose hypotheses.
- Only then apply the correct theorem.

## 2. Choosing the wrong theorem for the wrong proposition

This was a repeated weakness: knowing a theorem exists but not recognizing which theorem matches the proposition.

Examples:

- For `x = y` from `x ≤ y` and `y ≤ x`, the right theorem is `le_antisymm`.
- For `0 ≤ x * y` from `0 ≤ x` and `0 ≤ y`, the right theorem is `mul_nonneg`.
- For totality on `ℝ`, the right theorem is `le_total`.
- For transitivity, the right theorem is `le_trans`.

Pattern:

- The user often reached for a theorem based on a vague memory of a related fact instead of matching the exact statement.
- This caused proof scripts to fail even when the underlying mathematics was straightforward.

Fix:

- Translate the goal into a theorem statement before proving it.
- Ask: “What proposition am I trying to produce?”
- Then search for a theorem of exactly that shape.

## 3. Weakness with `show`, `intro`, and proof shape management

The user repeatedly struggled with the mechanics of Lean proof scripts:

- when to use `show`
- how to `intro` hypotheses
- when to destructure a conjunction with `rcases` or pattern matching
- how to transform a hypothesis like `h : A ∧ B` into usable assumptions

Examples:

- `intro h; exact le_antisymm h.1 h.2` is the correct pattern.
- `rcases h with ⟨hxy, hyx⟩; exact le_antisymm hxy hyx` is also correct and often clearer.

Pattern:

- The user would often try to rewrite or “massage” the goal rather than simply producing the required proof term.

Fix:

- Learn the standard proof skeleton:
  - `intro ...`
  - `intro h`
  - `rcases h with ...`
  - `exact theorem ...`
- Prefer “proof by direct application of the theorem” over manual rewriting.

## 4. Weakness with polymorphic generic structures and typeclass requirements

There were problems with definitions like:

- `OrderFragment (R : Type u) [Add R]`
- `x + y` being used before an `Add` instance is in scope
- generic structures where the type parameter is not constrained enough

This is a classic Lean issue: `+` is not available for arbitrary `R` unless a typeclass instance exists.

Examples:

- `add := fun x y => x + y` fails outside a context where `R` has `Add R`.
- The field names and structure fields had to match precisely.

Pattern:

- The user sometimes defined a generic structure and then used operations as if the type carried those instances automatically.

Fix:

- Add the correct typeclass restrictions (`[Add R]`, `[Mul R]`, `[LE R]`, etc.) when needed.
- Check the parameter context before writing operations on variables.

## 5. Not recognizing field and theorem names exactly

There were repeated mismatches in names and definitions, for example:

- `order_rfl` vs `order_reflexive`
- `x <= y` vs `x ≤ y`
- `order_is_total` proof needs `le_total`, not a custom ad hoc expression
- `multiplication_preserves_order` is a nonnegativity property, not an equality property

Pattern:

- Lean is strict about exact names and notation.
- Small syntax errors change the meaning of the whole proof.

Fix:

- Use the exact theorem name and exact notation.
- Check the relevant local type signature before writing the proof.

## 6. Missing the habit of reducing the problem to a minimal theorem

The strongest pattern in this project is that proofs became difficult only because the user tried to solve the whole structure at once instead of reducing to the smallest theorem that matches the goal.

Examples:

- Instead of proving a complex order property manually, use `le_trans`, `le_antisymm`, `le_total`, and `mul_nonneg`.
- Instead of reasoning about the full structure, inspect the exact type of the field being proved.

Fix:

- Reduce every proof to the exact type of the field.
- Ask: “What is this field supposed to mean?”
- Then apply the standard theorem matching that meaning.

## 7. Core weakness summary

The central weakness is not abstract algebra; it is structural Lean reasoning:

- reading goals precisely,
- matching hypotheses to theorems,
- using correct notation and field names,
- respecting typeclass constraints,
- and avoiding overcomplicated proof scripts.

This project exposed the need to strengthen the following habits:

- inspect the goal before writing a proof,
- use theorem statements as a guide,
- destructure conjunctions deliberately,
- import and use the right Mathlib theorem,
- keep proofs minimal and direct.

## 8. Suggested practice plan

To improve, each proof should follow this pattern:

1. Read the goal exactly.
2. Read the required type of the field.
3. Find the matching theorem in Mathlib.
4. Introduce hypotheses.
5. Apply the theorem directly.
6. Only if necessary, `rcases` or `simp`.

This will be far more reliable than trying to manually “rewrite” the goal into a different form.

## Bottom line

The weakness is primarily in Lean proof strategy, not in the underlying mathematics. The user understands the mathematical ideas, but the proof workflow is often blocked by a mismatch between goal shape and theorem shape, plus uncertainty around typeclass and notation details.

The fix is to build a disciplined Lean habit:

- the goal is the source of truth,
- the theorem should match the goal exactly,
- and `show`/`intro`/`rcases` are tools for exposing the structure, not for guessing a proof.
