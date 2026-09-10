# Lean Header Clause Experiments

Goal: make Lean theorem headers readable while learning. These are not source
format rules yet. They are study views for parsing a theorem statement.

Use the same theorem in multiple views and decide which view best teaches the
structure.

## Base Lean Header

```lean
theorem Surjective.comp_munkres
    {A B C : Type*} {f : A -> B} {g : B -> C}
    (hg : Function.Surjective g)
    (hf : Function.Surjective f) :
    Function.Surjective (g ∘ f) := by
```

## View 1: Types Emphasized

Purpose: see the universe of objects first.

```text
theorem Surjective.comp_munkres
    **{A B C : Type*}** {f : A -> B} {g : B -> C}
    (hg : Function.Surjective g)
    (hf : Function.Surjective f) :
    Function.Surjective (g ∘ f) := by
```

Reading:

- `A`, `B`, and `C` are arbitrary types.
- The functions move through these types as `A -> B -> C`.

## View 2: Functions Emphasized

Purpose: see the maps before the properties.

```text
theorem Surjective.comp_munkres
    {A B C : Type*} **{f : A -> B} {g : B -> C}**
    (hg : Function.Surjective g)
    (hf : Function.Surjective f) :
    Function.Surjective (g ∘ f) := by
```

Reading:

- `f` is the first map.
- `g` is the second map.
- `g ∘ f` means first `f`, then `g`.

## View 3: Hypotheses Emphasized

Purpose: see what facts we are allowed to use.

```text
theorem Surjective.comp_munkres
    {A B C : Type*} {f : A -> B} {g : B -> C}
    **(hg : Function.Surjective g)**
    **(hf : Function.Surjective f)** :
    Function.Surjective (g ∘ f) := by
```

Reading:

- `hg` is the proof that `g` is surjective.
- `hf` is the proof that `f` is surjective.
- The names `hg` and `hf` are proof variables.

## View 4: Conclusion Emphasized

Purpose: identify the target before proving.

```text
theorem Surjective.comp_munkres
    {A B C : Type*} {f : A -> B} {g : B -> C}
    (hg : Function.Surjective g)
    (hf : Function.Surjective f) :
    **Function.Surjective (g ∘ f)** := by
```

Reading:

- The thing to prove is that the composite is surjective.
- Before writing tactics, unfold the conclusion mentally:
  for every `c : C`, find an `a : A` with `(g ∘ f) a = c`.

## View 5: Clause Table

| Clause | Text | Meaning |
| --- | --- | --- |
| Name | `Surjective.comp_munkres` | Our study theorem name. |
| Types | `{A B C : Type*}` | Three arbitrary spaces/types. |
| Data | `{f : A -> B} {g : B -> C}` | Two composable functions. |
| Hypothesis | `(hg : Function.Surjective g)` | `g` hits every point of `C`. |
| Hypothesis | `(hf : Function.Surjective f)` | `f` hits every point of `B`. |
| Conclusion | `Function.Surjective (g ∘ f)` | The composite hits every point of `C`. |

## Current Preference

Use the clause table in the Google Doc for first exposure. Use the emphasized
views only when a specific clause causes confusion.

