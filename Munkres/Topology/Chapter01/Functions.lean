import Common
import Mathlib.Logic.Function.Basic

namespace Munkres.Topology.Chapter01

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
      e b = e (f (g b)) := by simpa [hrI b]
      _ = g b := by simpa using hlI (g b)

end Munkres.Topology.Chapter01
