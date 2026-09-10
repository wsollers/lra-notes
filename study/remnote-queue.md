# RemNote Queue

Running list of cards to add to RemNote. Keep cards atomic: one concept, one
answer. Prefer cards that repair a real hesitation or failed proof attempt.

## Functions.lean

### Math Vocabulary

- Q: What does it mean for `f : A -> B` to be injective?
  A: Whenever `f x = f y`, we have `x = y`.

- Q: What does it mean for `f : A -> B` to be surjective?
  A: For every `y : B`, there exists `x : A` such that `f x = y`.

- Q: What is a left inverse of `f : A -> B`?
  A: A function `g : B -> A` such that `g (f x) = x` for every `x : A`.

- Q: What is a right inverse of `f : A -> B`?
  A: A function `g : B -> A` such that `f (g y) = y` for every `y : B`.

### Lean Vocabulary

- Q: What is the mathlib predicate for injectivity?
  A: `Function.Injective f`.

- Q: What is the mathlib predicate for surjectivity?
  A: `Function.Surjective f`.

- Q: What is the mathlib predicate for `g` being a left inverse of `f`?
  A: `Function.LeftInverse g f`.

- Q: What is the mathlib predicate for `g` being a right inverse of `f`?
  A: `Function.RightInverse g f`.

- Q: How do you read `g ∘ f`?
  A: First apply `f`, then apply `g`.

- Q: What does `variable {A B C : Type*}` do?
  A: It declares reusable implicit type variables for later declarations.

### Proof Patterns

- Q: To prove `Function.Injective f`, what should you introduce?
  A: Introduce two inputs and a proof their images are equal.

- Q: To prove `Function.Surjective f`, what should you introduce?
  A: Introduce an arbitrary target value and provide a preimage witness.

- Q: To prove a goal of the form `exists x, P x`, what tactic usually starts the proof?
  A: `use x`, where `x` is the witness.

### Failure Repairs

- Q: What is a common mistake with `g ∘ f`?
  A: Reading it backwards; `g ∘ f` means first `f`, then `g`.

- Q: What should you check before proving a function theorem?
  A: Whether mathlib already has the right predicate, such as `Function.Injective`.

