import Mathlib.Data.Real.Basic
import Mathlib.Tactic

import Zorich.RealAnalysisI.Chapter02.Section01.Theorems

/-!
# Zorich, Mathematical Analysis I, §2.1 The Axiom System for the Real Numbers — Examples

The real numbers of mathlib satisfy each axiom group.
-/

namespace Zorich.RealAnalysisI.Chapter02

example : AdditiveFieldFragment ℝ where
  zero := 0
  add := fun x y => x + y
  additive_inverse_exists := by
    unfold InverseExists
    intro x
    use -x
    constructor
    · show (-x) + x = 0
      simp
    · show x + (-x) = 0
      simp
  addition_is_commutative := by
    unfold OperationIsCommutative
    intro x y
    show x + y = y + x
    exact add_comm x y
  addition_is_associative := by
    unfold OperationIsAssociative
    intro x y z
    show (x + y) + z = x + (y + z)
    exact add_assoc x y z
  zero_is_additive_identity := by
    unfold IsIdentityElement
    intro x
    constructor
    . -- LeftIdentity
      show 0 + x = x
      simp

    . -- RightIdentity
      show x + 0 = x
      simp

example : MultiplicativeFieldFragment ℝ where
  zero := 0
  one := 1
  mul := fun x y => x * y
  nonzero_multiplicative_inverse_exists := by
    unfold NonzeroInverseExists
    intro x hx
    use x⁻¹
    constructor
    · show x⁻¹ * x = 1
      exact inv_mul_cancel₀ hx
    · show x * x⁻¹ = 1
      exact mul_inv_cancel₀ hx
  one_is_multiplicative_identity := by
    unfold IsIdentityElement
    intro x
    constructor
    . -- LeftIdentity
      show 1 * x = x
      simp

    . -- RightIdentity
      show x * 1 = x
      simp
  multiplication_is_commutative := by
    unfold OperationIsCommutative
    intro x y
    show x * y = y * x
    exact mul_comm x y
  multiplication_is_associative := by
    unfold OperationIsAssociative
    intro x y z
    show (x * y) * z = x * (y * z)
    exact mul_assoc x y z

example : FieldFragment ℝ where
  zero := 0
  one := 1
  add := fun x y => x + y
  additive_inverse_exists := by
    unfold InverseExists
    intro x
    use -x
    constructor
    · show (-x) + x = 0
      simp
    · show x + (-x) = 0
      simp
  zero_is_additive_identity := by
    unfold IsIdentityElement
    intro x
    constructor
    . -- LeftIdentity
      show 0 + x = x
      simp

    . -- RightIdentity
      show x + 0 = x
      simp
  addition_is_commutative := by
    unfold OperationIsCommutative
    intro x y
    show x + y = y + x
    exact add_comm x y
  addition_is_associative := by
    unfold OperationIsAssociative
    intro x y z
    show (x + y) + z = x + (y + z)
    exact add_assoc x y z
  mul := fun x y => x * y
  nonzero_multiplicative_inverse_exists := by
    unfold NonzeroInverseExists
    intro x hx
    use x⁻¹
    constructor
    · show x⁻¹ * x = 1
      exact inv_mul_cancel₀ hx
    · show x * x⁻¹ = 1
      exact mul_inv_cancel₀ hx
  one_is_multiplicative_identity := by
    unfold IsIdentityElement
    intro x
    constructor
    . -- LeftIdentity
      show 1 * x = x
      simp

    . -- RightIdentity
      show x * 1 = x
      simp
  multiplication_is_commutative := by
    unfold OperationIsCommutative
    intro x y
    show x * y = y * x
    exact mul_comm x y
  multiplication_is_associative := by
    unfold OperationIsAssociative
    intro x y z
    show (x * y) * z = x * (y * z)
    exact mul_assoc x y z
  multiplication_distributes_over_addition := by
    constructor
    . -- Left
      intro x y z
      show x * (y + z) = (x * y) + (x * z)
      ring
    . -- Right
      intro x y z
      show (x + y) * z = (x * z) + (y * z)
      ring
  zero_ne_one := by
    unfold DistinguishedElementsAreDistinct
    show 0 ≠ 1
    simp

example : OrderFragment ℝ where
  zero := 0

  le := fun x y => x ≤ y
  add := fun x y => x + y
  mul := fun x y => x * y

  order_reflexive := by
    unfold OrderIsReflexive
    intro x
    show x ≤ x
    simp

  order_transitive := by
    unfold OrderIsTransitive
    intro x y z
    show x ≤ y ∧ y ≤ z → x ≤ z
    intro h
    exact le_trans h.1 h.2

  order_anti_symmetric := by
    unfold OrderIsAntiSymmetric
    intro x y
    intro h
    exact le_antisymm h.1 h.2

  order_is_total := by
    intro x y
    exact le_total x y

  addition_preserves_order := by
    unfold AdditionPreservesOrder
    intro x y z
    intro h
    show x + z ≤ y + z
    simp
    exact h

  multiplication_preserves_order := by
    unfold MultiplicationPreservesNonNegativity
    intro x y
    intro h
    exact mul_nonneg h.1 h.2

end Zorich.RealAnalysisI.Chapter02
