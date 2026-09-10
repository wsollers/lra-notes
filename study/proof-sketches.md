# Proof Sketches

Short coaching sketches for proofs. Keep these blunt and operational: one or
two lines that tell the learner what to introduce, what witness to choose, or
what theorem shape to unfold.

## Functions.lean

### `InjectiveOfLeftInverse`

Statement shape:

```lean
theorem InjectiveOfLeftInverse
    {A B : Type*} {f : A -> B} {g : B -> A}
    (h : Function.LeftInverse g f) :
    Function.Injective f := by
  ...
```

One-line sketch:

> To show `x = y`, rewrite `x` as `g (f x)` and `y` as `g (f y)`, then use the hypothesis `f x = f y`.

Stuck-state repair:

> If the goal is `x = y` and `hxy : f x = f y`, use the left-inverse facts to rewrite both sides back through the inverse candidate, then rewrite by `hxy`.

Lean move tested:

```lean
rw [← hlI x, ← hlI y, hxy]
```

Expanded learner proof:

```lean
have heq : e (f x) = e (f y) :=
  congrArg e hxy
rw [hlI x, hlI y] at heq
exact heq
```

What each line does:

- `have heq : e (f x) = e (f y) := ...` creates an intermediate fact and
  names it `heq`.
- `congrArg e hxy` applies the same function `e` to both sides of the equality
  `hxy : f x = f y`.
- `rw [hlI x, hlI y] at heq` rewrites inside the hypothesis `heq`, not in the
  main goal.
- `exact heq` closes the goal because, after rewriting, `heq` has type `x = y`.

Proof-state transition:

```text
Goal:
  x = y

Known:
  hxy : f x = f y
  hlI x : e (f x) = x
  hlI y : e (f y) = y

After `have heq : e (f x) = e (f y) := congrArg e hxy`:
  heq : e (f x) = e (f y)

After `rw [hlI x, hlI y] at heq`:
  heq : x = y

Then `exact heq` solves the goal.
```

Operational sketch:

1. Introduce `x y hxy`.
2. Use the left-inverse facts `h x` and `h y`.
3. Apply congruence of `g` to `hxy`, then finish by rewriting.

### `SurjectiveOfRightInverse`

Statement shape:

```lean
theorem SurjectiveOfRightInverse
    {A B : Type*} {f : A -> B} {g : B -> A}
    (h : Function.RightInverse g f) :
    Function.Surjective f := by
  ...
```

One-line sketch:

> To hit `y : B`, use `g y : A` as the preimage; the right-inverse hypothesis proves `f (g y) = y`.

Stuck-state repair:

> If the goal asks for an existential witness, give Lean the witness expression directly with `use g b`; then the right-inverse hypothesis should match the remaining equality.

Failure mode:

```lean
have a : A := g b
use a
exact hrI b
```

This can get sticky because the goal after `use a` is `f a = b`, while
`hrI b` has type `f (g b) = b`. Mathematically `a` was defined to be `g b`,
but the visible goal no longer shows the expression that `hrI b` talks about.
For a first pass, prefer the direct witness.

Beginner-clean version:

```lean
use g b
exact hrI b
```

What `use` does:

- `use t` is for goals of the form `Exists`.
- It gives Lean the witness `t`.
- Lean then replaces the existential goal with the property that must be shown
  for that witness.

Proof-state transition:

```text
Goal:
  exists a : A, f a = b

After `use g b`:
  f (g b) = b

Known:
  hrI b : f (g b) = b

Then `exact hrI b` solves the goal.
```

Operational sketch:

1. Introduce `y`.
2. Use witness `g y`.
3. Close the goal with `h y`.

### Composite Of Injective Functions

Statement shape:

```lean
theorem Injective.comp_munkres
    {A B C : Type*} {f : A -> B} {g : B -> C}
    (hg : Function.Injective g)
    (hf : Function.Injective f) :
    Function.Injective (g ∘ f) := by
  ...
```

One-line sketch:

> To show `x = y`, use injectivity of `g` to reduce equality of `g (f x)` and `g (f y)` to `f x = f y`, then use injectivity of `f`.

Operational sketch:

1. Introduce `x y hxy`.
2. Apply `hf`.
3. Apply `hg`.
4. Use `hxy`.

### Composite Of Surjective Functions

Statement shape:

```lean
theorem Surjective.comp_munkres
    {A B C : Type*} {f : A -> B} {g : B -> C}
    (hg : Function.Surjective g)
    (hf : Function.Surjective f) :
    Function.Surjective (g ∘ f) := by
  ...
```

One-line sketch:

> To hit `c : C`, first use surjectivity of `g` to get `b : B`; then use surjectivity of `f` to get `a : A`.

Operational sketch:

1. Introduce `c`.
2. Obtain `b` with `g b = c` from `hg c`.
3. Obtain `a` with `f a = b` from `hf b`.
4. Use witness `a` and compose the equalities.
