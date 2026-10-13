import Common

/-!
# Zorich, Mathematical Analysis I, §2.1 The Axiom System for the Real Numbers — Definitions

Definition 1 (§2.1.1) presents ℝ through four groups of axioms: (I) addition,
(II) multiplication, the distributive law (I, II), (III) order with its links
to addition (I, III) and multiplication (II, III), and (IV) completeness.
The predicates below name each axiom; the structures package one group each.
Completeness (IV) is not yet formalized.
-/

namespace Zorich.RealAnalysisI.Chapter02

/-! ### Groups (I) and (II): addition and multiplication -/

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

/-! ### The distributive law (I, II) -/

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

/-! ### Group (III): order, and its links to addition (I, III) and multiplication (II, III) -/

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

structure OrderFragment (R : Type u) where
  zero : R

  le : R → R → Prop
  add : R → R → R
  mul : R → R → R

  order_reflexive : OrderIsReflexive le
  order_transitive : OrderIsTransitive le
  order_anti_symmetric : OrderIsAntiSymmetric le
  order_is_total : OrderIsTotal le
  addition_preserves_order : AdditionPreservesOrder le add
  multiplication_preserves_order : MultiplicationPreservesNonNegativity le mul zero

def OrderFragmentTrichotomy {R : Type u} (O : OrderFragment R) : Prop :=
  ∀ x y : R, O.le x y ∨ x = y ∨ O.le y x

end Zorich.RealAnalysisI.Chapter02
