import Tarski.Logic.Chapter03.Section19.Observations

/-!
# Tarski, Introduction to Logic, Chapter 3 (On the Theory of Identity), §19 — Theorems

§19, "Equality in arithmetic and in geometry, and its relationship to logical
identity" ([pp. 56–57](https://drive.google.com/file/d/1o98AJ7PAh5KMmiSim79q_dmaxvEVYQb9/view#page=81)).

Reserve this file for the theorems of §19 and their proofs. Prose notes
belong in the chapter's notes.tex.

Identity is the primitive relation `I` of §17, with `LeibnizLaw I` as a
hypothesis. `<` is Lean's notation class `[LT D]`; no law of `<` is assumed.
-/

universe u

namespace Tarski.Logic.Chapter03

variable {D : Type u}

/-- **Replacing equals in `<`** [Tarski, §19, [p. 56](https://drive.google.com/file/d/1o98AJ7PAh5KMmiSim79q_dmaxvEVYQb9/view#page=81)]: if `x = y`
and `x < z`, then `y < z`. Tarski gives it as an example of the consequences
of Leibniz's law that mathematicians who rejected the law in general still
recognised: whenever `x = y` and `x` satisfies a formula built from
arithmetical symbols only, `y` satisfies it too. It needs only Leibniz's law,
with the property "is less than `z`". Lean: `Eq.subst`. -/
theorem lt_of_eq_of_lt_left [LT D] {I : D → D → Prop} (h_leibniz : LeibnizLaw I) {x y z : D}
    (hxy : I x y) (hxz : x < z) : y < z := by
  sorry

end Tarski.Logic.Chapter03
