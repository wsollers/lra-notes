import Tarski.Logic.Chapter03.Section17.Definitions

/-!
# Tarski, Introduction to Logic, Chapter 3 (On the Theory of Identity), §17 — Exercises

Chapter III exercises on the laws of §17 (pp. 59–60). Each states, as
hypotheses, exactly the laws the exercise allows.
-/

universe u

namespace Tarski.Logic.Chapter03

variable {D : Type u}

/-- **Exercise 1** [Tarski, Ch. III, [p. 59](https://drive.google.com/file/d/1o98AJ7PAh5KMmiSim79q_dmaxvEVYQb9/view#page=84)]: prove Law V of §17
"by using exclusively Laws III and IV, thus without the use of LEIBNIZ'S law
(or of the rule of replacement of equals)". Tarski's hint: by Law III,
interchange the variables in `y = z`, then apply Law IV. -/
named_exercise euclid_of_symm_of_trans {I : D → D → Prop}
    (h_law3_symm : ∀ x y : D, I x y → I y x)
    (h_law4_trans : ∀ x y z : D, I x y → I y z → I x z)
    {x y z : D} (hxz : I x z) (hyz : I y z) : I x y := by
  sorry

/-- **Exercise 2** [Tarski, Ch. III, [p. 60](https://drive.google.com/file/d/1o98AJ7PAh5KMmiSim79q_dmaxvEVYQb9/view#page=85)]: prove "if x = y,
y = z, and z = t, then x = t, using exclusively Law IV of Section 17". -/
exercise {I : D → D → Prop}
    (h_law4_trans : ∀ x y z : D, I x y → I y z → I x z)
    {x y z t : D} (hxy : I x y) (hyz : I y z) (hzt : I z t) : I x t := by
  sorry

/-- **Exercise 3**, Law III [Tarski, Ch. III, [p. 60](https://drive.google.com/file/d/1o98AJ7PAh5KMmiSim79q_dmaxvEVYQb9/view#page=85)]: replacing
`=` by `≠` throughout Law III gives "if x ≠ y, then y ≠ x", which is true. It
follows from Leibniz's law. (The extract's OCR garbles the replacement symbol;
`≠` is our reading.) -/
named_exercise ne_symm {I : D → D → Prop} (h_leibniz : LeibnizLaw I) {x y : D}
    (hxy : Different I x y) : Different I y x := by
  sorry

/-- **Exercise 3**, Law IV [Tarski, Ch. III, [p. 60](https://drive.google.com/file/d/1o98AJ7PAh5KMmiSim79q_dmaxvEVYQb9/view#page=85)]: replacing
`=` by `≠` throughout Law IV gives "if x ≠ y and y ≠ z, then x ≠ z", which is
false: take `x = z` with `y` different. -/
exercise : ¬ ∀ x y z : Bool, x ≠ y → y ≠ z → x ≠ z := by
  sorry

end Tarski.Logic.Chapter03
