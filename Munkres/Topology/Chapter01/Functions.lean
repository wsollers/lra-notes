import Mathlib

namespace Munkres.Topology.Chapter01

lemma Munkres_2_1_BijectiveOfLeftRightInverse
  { A B : Type*}
  (f : A → B) (e g : B → A)
  (hlI : Function.LeftInverse e f)
  (hrI : Function.RightInverse g f) :
  (Function.Bijective f ∧ e = g) := by

  constructor
  . -- prove Function.Bijective f
    -- To prove that f is bijective, we need to show it is both injective and surjective.
    -- To prove injectivity, assume f a₁ = f a₂ and show a₁ = a₂ using the left inverse e.
    -- To prove surjectivity, for any b : B, show there exists a : A such that f a = b using the right inverse g.
    --unfold Function.LeftInverse at hlI
    --unfold Function.RightInverse at hrI
    unfold Function.Bijective
    constructor
    . -- prove injectivity
      unfold Function.Injective
      intro x y hxy

      sorry
    . -- prove surjectivity
      sorry
  . -- prove e = g

    sorry



end Munkres.Topology.Chapter01
