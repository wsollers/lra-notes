import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Basic
import Mathlib.Tactic.Bound.Init
import Mathlib.Util.CompileInductive
import Mathlib.Order.ConditionallyCompleteLattice.Basic

import Zorich.RealAnalysis.Chapter02.Basic

/-!
# Zorich, Mathematical Analysis, Chapter 2 Notes

Reserve this file for independently written notes, Lean translation reminders,
and proof-pattern observations for Chapter 2.
-/

namespace Zorich.RealAnalysis.Chapter02

/-- Definition 1 (Zorich, 2.1.1): The Axiom System for the Set of Real Numbers. -/

/- Axiom system for the real numbers -/

def IsLeftInverse {R : Type u} (op : R → R → R)(zero : R)
  (e x : R) : Prop :=
  op e x = zero

def IsRightInverse {R : Type u} (op : R → R → R)(zero : R)
  (x e : R) : Prop :=
  op x e = zero

def IsInverse {R : Type u} (op : R → R → R) (zero : R)
  (x y : R) : Prop :=
  IsLeftInverse op zero y x ∧ IsRightInverse op zero x y

def InverseExists {R : Type u} (zero : R) (op : R → R → R) : Prop :=
  (∀ x : R, ∃ e : R, IsInverse op zero x e)

def NonzeroInverseExists {R : Type u} (zero one : R)
    (op : R → R → R) : Prop :=
  ∀ x : R, x ≠ zero → ∃ e : R, IsInverse op one x e

def IsLeftIdentity {R : Type u} (op : R → R → R)
  (e x : R) : Prop :=
  op e x = x

def IsRightIdentity {R : Type u} (op : R → R → R)
  (x e : R) : Prop :=
  op x e = x

def IsIdentity {R : Type u} (op : R → R → R)
  (x y : R) : Prop :=
  IsLeftIdentity op y x ∧ IsRightIdentity op x y

def IsIdentityElement {R : Type u} (op : R → R → R) (e : R) : Prop :=
  ∀ x : R, IsIdentity op x e

def IdentityExists {R : Type u} (op : R → R → R) : Prop :=
  (∃ e : R, ∀ x : R, IsIdentity op x e)

def OperationIsAssociative {R : Type u} (op : R → R → R) : Prop :=
  ∀ x y z : R, op (op x y) z = op x (op y z)

def OperationIsCommutative {R : Type u} (op : R → R → R) : Prop :=
  ∀ x y : R, op x y = op y x

def DistinguishedElementsAreDistinct {R : Type u}
  (zero : R) (one : R) : Prop :=
  (zero ≠ one)

structure AdditiveFieldFragment (R : Type u) where
  zero : R
  add : R → R → R
  additive_inverse_exists : InverseExists zero add
  zero_is_additive_identity : IsIdentityElement add zero
  addition_is_commutative : OperationIsCommutative add
  addition_is_associative : OperationIsAssociative add

structure MultiplicativeFieldFragment (R : Type u) where
  zero : R
  one : R
  mul : R → R → R
  nonzero_multiplicative_inverse_exists : NonzeroInverseExists zero one mul
  one_is_multiplicative_identity : IsIdentityElement mul one
  multiplication_is_commutative : OperationIsCommutative mul
  multiplication_is_associative : OperationIsAssociative mul

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

def IsLeftDistributive {R : Type u}
  (times : R → R → R) (plus : R → R → R) : Prop :=
  ∀ x y z : R,
  times x (plus y z) = plus (times x y) (times x z)

def IsRightDistributive {R : Type u}
  (times : R → R → R) (plus : R → R → R) : Prop :=
  ∀ x y z : R,
  times (plus x y) z = plus (times x z) (times y z)

def IsDistributive {R : Type u}
  (times : R → R → R) (plus : R → R → R) : Prop :=
  IsLeftDistributive times plus ∧ IsRightDistributive times plus

structure FieldFragment (R : Type u) where
  zero : R
  one : R
  add : R → R → R
  additive_inverse_exists : InverseExists zero add
  zero_is_additive_identity : IsIdentityElement add zero
  addition_is_commutative : OperationIsCommutative add
  addition_is_associative : OperationIsAssociative add
  mul : R → R → R
  nonzero_multiplicative_inverse_exists : NonzeroInverseExists zero one mul
  one_is_multiplicative_identity : IsIdentityElement mul one
  multiplication_is_commutative : OperationIsCommutative mul
  multiplication_is_associative : OperationIsAssociative mul
  multiplication_distributes_over_addition : IsDistributive mul add
  zero_ne_one : DistinguishedElementsAreDistinct zero one

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

def OrderIsReflexive  {R : Type u} (le : R → R → Prop) : Prop :=
  ∀ x : R, le x x

def OrderIsTransitive  {R : Type u} (le : R → R → Prop) : Prop :=
  ∀ x y z: R, le x y ∧ le y z → le x z

def OrderIsAntiSymmetric  {R : Type u} (le : R → R → Prop) : Prop :=
  ∀ x y: R, le x y  ∧ le y x → x = y

def OrderIsTotal  {R : Type u} (le : R → R → Prop) : Prop :=
  ∀ x y: R, le x y  ∨ le y x

def AdditionPreservesOrder  {R : Type u} (le : R → R → Prop) ( add :R → R → R) : Prop :=
  ∀ x y z: R, le x y → le (add x z) (add y z)

def MultiplicationPreservesNonNegativity  {R : Type u} (le : R → R → Prop) ( mul :R → R → R) (zero : R): Prop :=
  ∀ x y : R, le zero x ∧ le zero y → le zero ( mul x y)

structure OrderFragment (R : Type u) [Add R] where
  zero : R

  le : R → R → Prop
  add : R → R → R := fun x y => x + y
  mul : R → R → R := fun x y => x + y

  order_reflexive : OrderIsReflexive le
  order_transitive : OrderIsTransitive le
  order_anti_symmetric : OrderIsAntiSymmetric le
  order_is_total : OrderIsTotal le
  addition_preserves_order : AdditionPerservesOrder le add
  multiplication_preserves_order : MultiplicationPerservesNonNegativity le mul zero

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

    sorry

  order_anti_symmetric := by
    unfold OrderIsAntiSymmetric
    intro x y
    show x ≤ y ∧ y ≤ x → x = y
    sorry

  order_is_total := by
    sorry

  addition_preserves_order := by
    sorry

  multiplication_preserves_order := by
    sorry

end Zorich.RealAnalysis.Chapter02
