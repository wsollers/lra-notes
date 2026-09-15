import Mathlib
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
structure RealAxiomSystem (R : Type u) where
  -- Operations (Data)
  add : R → R → R
  mul : R → R → R
  le : R → R → Prop
  zero : R
  one : R
  neg : R → R
  inv : R → R
  sSup : (R → Prop) → R

  -- (I) AXIOMS FOR ADDITION
  -- 1+: Identity element 0
  add_zero : ∀ x : R, add x zero = x ∧ add zero x = x
  -- 2+: Additive inverse (-x)
  add_left_neg : ∀ x : R, add x (neg x) = zero ∧ add (neg x) x = zero
  -- 3+: Associativity of addition
  add_assoc : ∀ x y z : R, add x (add y z) = add (add x y) z
  -- 4+: Commutativity of addition
  add_comm : ∀ x y : R, add x y = add y x

  -- (II) AXIOMS FOR MULTIPLICATION
  mul_one : ∀ x : R, mul x one = x ∧ mul one x = x
  mul_inv : ∀ x : R, x ≠ zero → mul x (inv x) = one ∧ mul (inv x) x = one
  mul_assoc : ∀ x y z : R, mul x (mul y z) = mul (mul x y) z
  mul_comm : ∀ x y : R, mul x y = mul y x
  distrib : ∀ x y z : R, mul (add x y) z = add (mul x z) (mul y z)
  zero_ne_one : zero ≠ one

  -- (III) ORDER AXIOMS & COMPATIBILITY
  le_refl : ∀ x : R, le x x
  le_trans : ∀ x y z : R, le x y → le y z → le x z
  le_antisymm : ∀ x y : R, le x y → le y x → x = y
  le_total : ∀ x y : R, le x y ∨ le y x
  add_le_add : ∀ x y z : R, le x y → le (add x z) (add y z)
  mul_pos : ∀ x y : R, le zero x → le zero y → le zero (mul x y)

  -- (IV) COMPLETENESS AXIOM (Least Upper Bound Property)
  cSup_upper : ∀ (S : R → Prop) (M : R),
    (∃ x, S x) → (∀ x, S x → le x M) → ∀ x, S x → le x (sSup S)
  cSup_least : ∀ (S : R → Prop) (M : R),
    (∃ x, S x) → (∀ x, S x → le x M) → le (sSup S) M

attribute [class] RealAxiomSystem

variable {R : Type u} [sys : RealAxiomSystem R]

-- Set up textbook notation for this section
local infixl:65 " + " => sys.add
local infixl:70 " * " => sys.mul
local prefix:100 "-" => sys.neg
local postfix:102 "⁻¹" => sys.inv
local infix:50 " ≤ " => sys.le

-- Enable numeral literals 0 and 1
local instance : OfNat R 0 where
  ofNat := sys.zero

local instance : OfNat R 1 where
  ofNat := sys.one

/-
  Theorem 1: Uniqueness of the Neutral Element (0)
  In any real number system, the additive identity is unique.
  If an element z acts as an additive identity (that is, x + z = x and z + x = x for all x), then z must equal 0.

-/
theorem AdditiveIdentityUnique (z : R)
    (zeroUniqueRight : ∀ x : R, x + z = x)
    (zeroUniqueLeft : ∀ x : R, z + x = x) : z = 0 := by

  -- 1. Specialize zeroUniqueRight to x = 0:
  have h0Z : (0 : R) + z = 0 := zeroUniqueRight 0
  have hZ0 : z + (0 : R) = (0 : R) := zeroUniqueLeft 0
  have z0 := hZ0.trans h0Z.symm


  sorry



end Zorich.RealAnalysis.Chapter02
