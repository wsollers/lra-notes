import Common
import Mathlib.Logic.Function.Basic
import Munkres.Topology.Chapter01.Section02.Definitions

/-!
# Munkres, Topology, Chapter 1, §2 Functions — Theorems
-/

namespace Munkres.Topology.Chapter01

/-- **Lemma 2.1** [Munkres, §2, p. 19]. A function with a left inverse and a right inverse is
bijective, and the two inverses agree. The book also concludes that both equal
`f⁻¹`; that part is not yet stated here. Exercise 2.5(e) restates this lemma. -/
theorem Munkres_2_1_BijectiveOfLeftRightInverse
  {A B : Type*}
  (f : A → B) (e g : B → A)
  (hlI : Function.LeftInverse e f)
  (hrI : Function.RightInverse g f) :
  Function.Bijective f ∧ e = g := by
  constructor
  case left =>
    constructor
    case left =>
      intro x y hxy
      have heq : e (f x) = e (f y) := congrArg e hxy
      calc
        x = e (f x) := by symm; exact hlI x
        _ = e (f y) := heq
        _ = y := hlI y
    case right =>
      intro b
      refine ⟨g b, hrI b⟩
  case right =>
    funext b
    calc
      e b = e (f (g b)) := by simp [hrI b]
      _ = g b := by simpa using hlI (g b)

end Munkres.Topology.Chapter01
