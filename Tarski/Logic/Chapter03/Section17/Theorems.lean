import Tarski.Logic.Chapter03.Section17.Observations

/-!
# Tarski, Introduction to Logic, Chapter 3 (On the Theory of Identity), §17 — Theorems

Reserve this file for the theorems of §17 and their proofs. Prose notes
belong in the chapter's notes.tex.

Each theorem is about a primitive identity relation `I` and takes as a
hypothesis exactly the laws it uses (here, `LeibnizLaw I`).

"Laws II, III, and IV are called the LAWS OF REFLEXIVITY, SYMMETRY, and
TRANSITIVITY, respectively, for the relation of identity"
([p. 53](https://drive.google.com/file/d/1o98AJ7PAh5KMmiSim79q_dmaxvEVYQb9/view#page=78)).
-/

universe u

namespace Tarski.Logic.Chapter03

variable {D : Type u}

/-- **Reflexivity**, Law II [Tarski, §17, [p. 51](https://drive.google.com/file/d/1o98AJ7PAh5KMmiSim79q_dmaxvEVYQb9/view#page=76)]: every object is
equal to itself. Tarski
derives it from Leibniz's law. Lean: `Eq.refl`. -/
theorem refl {I : D → D → Prop} (h_leibniz : LeibnizLaw I) (x : D) : I x x := by
  sorry

/-- **Symmetry**, Law III [Tarski, §17, [p. 52](https://drive.google.com/file/d/1o98AJ7PAh5KMmiSim79q_dmaxvEVYQb9/view#page=77)]: if `x` is equal to `y`, then `y` is equal
to `x`. Tarski derives it from Leibniz's law. Lean: `Eq.symm`. -/
theorem symm {I : D → D → Prop} (h_leibniz : LeibnizLaw I) {x y : D} (hxy : I x y) : I y x := by
  sorry

/-- **Transitivity**, Law IV [Tarski, §17, [p. 52](https://drive.google.com/file/d/1o98AJ7PAh5KMmiSim79q_dmaxvEVYQb9/view#page=77)]: if `x` is equal to `y` and `y` is equal
to `z`, then `x` is equal to `z`. Tarski derives it from Leibniz's law.
Lean: `Eq.trans`. -/
theorem trans {I : D → D → Prop} (h_leibniz : LeibnizLaw I) {x y z : D} (hxy : I x y) (hyz : I y z) :
    I x z := by
  sorry

/-- **Law V** [Tarski, §17, [p. 53](https://drive.google.com/file/d/1o98AJ7PAh5KMmiSim79q_dmaxvEVYQb9/view#page=78)]: if `x = z` and `y = z`, then
`x = y`; "in other words, two objects which are equal to the same object are
equal to each other". Tarski proves it from Leibniz's law, and notes it "can
also be deduced from Laws III and IV, without using LEIBNIZ'S law" (that proof
is Exercise 1, in `Exercises.lean`). It is Euclid's first common notion. No
core Lean declaration has this statement; for `=` it is `hxz.trans hyz.symm`. -/
theorem euclid {I : D → D → Prop} (h_leibniz : LeibnizLaw I) {x y z : D} (hxz : I x z) (hyz : I y z) :
    I x y := by
  sorry

end Tarski.Logic.Chapter03
