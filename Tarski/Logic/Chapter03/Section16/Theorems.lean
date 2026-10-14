import Tarski.Logic.Chapter03.Section16.Observations

/-!
# Tarski, Introduction to Logic, Chapter 3 (On the Theory of Identity), §16 — Theorems

Reserve this file for the theorems of §16 and their proofs. Prose notes
belong in the chapter's notes.tex.

Each theorem is about a primitive identity relation `I` and takes as a
hypothesis exactly the laws it uses (here, `LeibnizLaw I`).
-/

universe u

namespace Tarski.Logic.Chapter03

variable {D : Type u}

/-- **Reflexivity** [Tarski, Ch. 3]: everything is equal to itself. Tarski
derives it from Leibniz's law. Lean: `Eq.refl`. -/
theorem refl {I : D → D → Prop} (h_leibniz : LeibnizLaw I) (x : D) : I x x := by
  sorry

/-- **Symmetry** [Tarski, Ch. 3]: if `x` is equal to `y`, then `y` is equal
to `x`. Tarski derives it from Leibniz's law. Lean: `Eq.symm`. -/
theorem symm {I : D → D → Prop} (h_leibniz : LeibnizLaw I) {x y : D} (hxy : I x y) : I y x := by
  sorry

/-- **Transitivity** [Tarski, Ch. 3]: if `x` is equal to `y` and `y` is equal
to `z`, then `x` is equal to `z`. Tarski derives it from Leibniz's law.
Lean: `Eq.trans`. -/
theorem trans {I : D → D → Prop} (h_leibniz : LeibnizLaw I) {x y z : D} (hxy : I x y) (hyz : I y z) :
    I x z := by
  sorry

end Tarski.Logic.Chapter03
