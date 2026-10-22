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

/-- **Leibniz's law, more simply** [Tarski, §17, [p. 50](https://drive.google.com/file/d/1o98AJ7PAh5KMmiSim79q_dmaxvEVYQb9/view#page=75)]: "x = y if,
and only if, x and y have every property in common". Tarski gives it as a
simpler wording of Law I. -/
theorem iff_forall_iff {I : D → D → Prop} (h_leibniz : LeibnizLaw I) (x y : D) :
    I x y ↔ ∀ P : D → Prop, (P x ↔ P y) := by
  unfold LeibnizLaw at h_leibniz
  have h_xyyx := h_leibniz x y
  constructor
  . -- mp
    intro h_xy PP
    rw [h_xyyx] at h_xy
    sorry
  . --
    intro PP
    let pp : PP 
    have ii := h_xyyx
    sorry



/-- **Rule of replacement of equals** [Tarski, §17, [p. 51](https://drive.google.com/file/d/1o98AJ7PAh5KMmiSim79q_dmaxvEVYQb9/view#page=76)]: if
\`x = y\` "has been assumed or proved, then one is allowed to replace in any
formula or sentence occurring in this context the left side of the equation by
its right side … and the right side by the left side". Tarski derives it as a
consequence of Leibniz's law. Replacing only some occurrences, which Tarski
allows, is the case where \`P\` keeps the other occurrences fixed: to turn
\`φ x x\` into \`φ x y\`, take \`P := fun z => φ x z\`. Lean: \`Eq.subst\`, \`congrArg\`. -/
theorem replace {I : D → D → Prop} (h_leibniz : LeibnizLaw I) {x y : D} (hxy : I x y)
    (P : D → Prop) : P x ↔ P y := by
  sorry

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
