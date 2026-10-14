import Tarski.Logic.Chapter03.Section19.Observations

/-!
# Tarski, Introduction to Logic, Chapter 3 (On the Theory of Identity), §19 — Theorems

Reserve this file for the theorems of §19 and their proofs. Prose notes
belong in the chapter's notes.tex.

Identity is the primitive relation `I` of §16, with `LeibnizLaw I` as a
hypothesis. `<` is Lean's notation class `[LT D]`; no law of `<` is assumed.
-/

universe u

namespace Tarski.Logic.Chapter03

variable {D : Type u}

/-- **Replacing equals in `<`** [Tarski, §19]: if `x` is equal to `y` and
`x < z`, then `y < z`. It needs only Leibniz's law, with the property
"is less than `z`". Lean: `Eq.subst`. -/
theorem lt_of_eq_of_lt_left [LT D] {I : D → D → Prop} (h_leibniz : LeibnizLaw I) {x y z : D}
    (hxy : I x y) (hxz : x < z) : y < z := by
  sorry

end Tarski.Logic.Chapter03
