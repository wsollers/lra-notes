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

/-- Helper for axioms 2₊ and 2• [Zorich, §2.1.1, p. 36–37]: `e` is a left inverse of `x` for `op`. Not a separate notion in the book. -/
def IsLeftInverse {R : Type u} (op : R → R → R)(zero : R)
  (e x : R) : Prop :=
  op e x = zero

/-- Helper for axioms 2₊ and 2• [Zorich, §2.1.1, p. 36–37]: `e` is a right inverse of `x` for `op`. Not a separate notion in the book. -/
def IsRightInverse {R : Type u} (op : R → R → R)(zero : R)
  (x e : R) : Prop :=
  op x e = zero

/-- Helper for axioms 2₊ and 2• [Zorich, §2.1.1, p. 36–37]: `y` is a two-sided inverse of `x`, as the book requires. -/
def IsInverse {R : Type u} (op : R → R → R) (zero : R)
  (x y : R) : Prop :=
  IsLeftInverse op zero y x ∧ IsRightInverse op zero x y

/-- **Axiom 2₊** [Zorich, §2.1.1, p. 36]: every element has a negative. -/
def InverseExists {R : Type u} (zero : R) (op : R → R → R) : Prop :=
  (∀ x : R, ∃ e : R, IsInverse op zero x e)

/-- **Axiom 2•** [Zorich, §2.1.1, p. 37]: every nonzero element has an inverse. -/
def NonzeroInverseExists {R : Type u} (zero one : R)
    (op : R → R → R) : Prop :=
  ∀ x : R, x ≠ zero → ∃ e : R, IsInverse op one x e

/-- Helper for axioms 1₊ and 1• [Zorich, §2.1.1, p. 36–37]: `e` acts as a left identity on `x`. -/
def IsLeftIdentity {R : Type u} (op : R → R → R)
  (e x : R) : Prop :=
  op e x = x

/-- Helper for axioms 1₊ and 1• [Zorich, §2.1.1, p. 36–37]: `e` acts as a right identity on `x`. -/
def IsRightIdentity {R : Type u} (op : R → R → R)
  (x e : R) : Prop :=
  op x e = x

/-- Helper for axioms 1₊ and 1• [Zorich, §2.1.1, p. 36–37]: `y` is a two-sided identity for `x`. -/
def IsIdentity {R : Type u} (op : R → R → R)
  (x y : R) : Prop :=
  IsLeftIdentity op y x ∧ IsRightIdentity op x y

/-- **Axioms 1₊ / 1•** [Zorich, §2.1.1, p. 36–37]: `e` is a neutral element for `op`. -/
def IsIdentityElement {R : Type u} (op : R → R → R) (e : R) : Prop :=
  ∀ x : R, IsIdentity op x e

/-- Existence of a neutral element, as asserted in axioms 1₊ / 1• [Zorich, §2.1.1, p. 36–37]. Not used by the structures below. -/
def IdentityExists {R : Type u} (op : R → R → R) : Prop :=
  (∃ e : R, ∀ x : R, IsIdentity op x e)

/-- **Axioms 3₊ / 3•** [Zorich, §2.1.1, p. 36–37]: the operation is associative. -/
def OperationIsAssociative {R : Type u} (op : R → R → R) : Prop :=
  ∀ x y z : R, op (op x y) z = op x (op y z)

/-- **Axioms 4₊ / 4•** [Zorich, §2.1.1, p. 36–37]: the operation is commutative. -/
def OperationIsCommutative {R : Type u} (op : R → R → R) : Prop :=
  ∀ x y : R, op x y = op y x

/-- **1 ≠ 0**, part of axiom 1• [Zorich, §2.1.1, p. 37], which places 1 in ℝ∖0. -/
def DistinguishedElementsAreDistinct {R : Type u}
  (zero : R) (one : R) : Prop :=
  (zero ≠ one)

/-- **Group (I), axioms 1₊–4₊** [Zorich, §2.1.1, p. 36]: the axioms of addition. -/
structure AdditiveFieldFragment (R : Type u) where
  zero : R
  add : R → R → R
  additive_inverse_exists : InverseExists zero add
  zero_is_additive_identity : IsIdentityElement add zero
  addition_is_commutative : OperationIsCommutative add
  addition_is_associative : OperationIsAssociative add

/-- **Group (II), axioms 1•–4•** [Zorich, §2.1.1, p. 37]: the axioms of multiplication. Omits 1 ≠ 0, which axiom 1• includes; `FieldFragment` adds it. -/
structure MultiplicativeFieldFragment (R : Type u) where
  zero : R
  one : R
  mul : R → R → R
  nonzero_multiplicative_inverse_exists : NonzeroInverseExists zero one mul
  one_is_multiplicative_identity : IsIdentityElement mul one
  multiplication_is_commutative : OperationIsCommutative mul
  multiplication_is_associative : OperationIsAssociative mul

/-! ### The distributive law (I, II) -/

/-- Left distributivity. Not stated in the book, which gives only the right-hand form [Zorich, §2.1.1, p. 37]; it follows from that and commutativity. -/
def IsLeftDistributive {R : Type u}
  (times : R → R → R) (plus : R → R → R) : Prop :=
  ∀ x y z : R,
  times x (plus y z) = plus (times x y) (times x z)

/-- **Axiom (I, II)** [Zorich, §2.1.1, p. 37]: the book's distributive law (x + y)z = xz + yz. -/
def IsRightDistributive {R : Type u}
  (times : R → R → R) (plus : R → R → R) : Prop :=
  ∀ x y z : R,
  times (plus x y) z = plus (times x z) (times y z)

/-- Both distributive laws. The book's axiom (I, II) [Zorich, §2.1.1, p. 37] is the right-hand one. -/
def IsDistributive {R : Type u}
  (times : R → R → R) (plus : R → R → R) : Prop :=
  IsLeftDistributive times plus ∧ IsRightDistributive times plus

/-- **Field**, groups (I), (II) and axiom (I, II) [Zorich, §2.1.1, p. 37]: the book calls a set satisfying them a field. -/
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

/-- **Axiom 0≤** [Zorich, §2.1.1, p. 37]: reflexivity. -/
def OrderIsReflexive  {R : Type u} (le : R → R → Prop) : Prop :=
  ∀ x : R, le x x

/-- **Axiom 2≤** [Zorich, §2.1.1, p. 37]: transitivity. -/
def OrderIsTransitive  {R : Type u} (le : R → R → Prop) : Prop :=
  ∀ x y z: R, le x y ∧ le y z → le x z

/-- **Axiom 1≤** [Zorich, §2.1.1, p. 37]: antisymmetry. -/
def OrderIsAntiSymmetric  {R : Type u} (le : R → R → Prop) : Prop :=
  ∀ x y: R, le x y  ∧ le y x → x = y

/-- **Axiom 3≤** [Zorich, §2.1.1, p. 37]: any two elements are comparable. -/
def OrderIsTotal  {R : Type u} (le : R → R → Prop) : Prop :=
  ∀ x y: R, le x y  ∨ le y x

/-- **Axiom (I, III)** [Zorich, §2.1.1, p. 38]: adding the same element preserves order. -/
def AdditionPreservesOrder  {R : Type u} (le : R → R → Prop) ( add :R → R → R) : Prop :=
  ∀ x y z: R, le x y → le (add x z) (add y z)

/-- **Axiom (II, III)** [Zorich, §2.1.1, p. 38]: the product of non-negative elements is non-negative. -/
def MultiplicationPreservesNonNegativity  {R : Type u} (le : R → R → Prop) ( mul :R → R → R) (zero : R): Prop :=
  ∀ x y : R, le zero x ∧ le zero y → le zero ( mul x y)

/-- **Group (III) with axioms (I, III) and (II, III)** [Zorich, §2.1.1, p. 37–38]. Its `add`, `mul`, `zero` are not tied to a `FieldFragment`. -/
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

/-- Not in the book in this form. Compare consequence d.1° [Zorich, §2.1.2 d, p. 41], which uses strict order and says exactly one alternative holds. -/
def OrderFragmentTrichotomy {R : Type u} (O : OrderFragment R) : Prop :=
  ∀ x y : R, O.le x y ∨ x = y ∨ O.le y x

end Zorich.RealAnalysisI.Chapter02
