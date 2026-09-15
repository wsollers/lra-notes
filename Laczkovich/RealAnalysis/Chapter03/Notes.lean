import Laczkovich.RealAnalysis.Chapter03.Basic

/-!
# Laczkovich, Real Analysis, Chapter 3 Notes

Reserve this file for independently written notes, Lean translation reminders,
and proof-pattern observations for Chapter 3.
-/

namespace Laczkovich.RealAnalysis.Chapter03


structure RealAxiomSystem (R : Type u) where
  -- Data
  add : R → R → R
  mul : R → R → R
  zero : R
  one : R
  le : R → R → Prop

  -- I. Addition axioms
  add_zero : ∀ x : R, add x zero = x ∧ add zero x = x
  exists_neg : ∀ x : R, ∃ y : R, add x y = zero ∧ add y x = zero
  add_assoc : ∀ x y z : R, add x (add y z) = add (add x y) z
  add_comm : ∀ x y : R, add x y = add y x

  -- II. Multiplication axioms
  mul_one : ∀ x : R, mul x one = x ∧ mul one x = x
  one_ne_zero : one ≠ zero
  exists_inv :
    ∀ x : R, x ≠ zero → ∃ y : R, mul x y = one ∧ mul y x = one
  mul_assoc : ∀ x y z : R, mul x (mul y z) = mul (mul x y) z
  mul_comm : ∀ x y : R, mul x y = mul y x

  -- I/II. Distributivity
  distrib : ∀ x y z : R, mul (add x y) z = add (mul x z) (mul y z)

  -- III. Order axioms
  le_refl : ∀ x : R, le x x
  le_antisymm : ∀ x y : R, le x y → le y x → x = y
  le_trans : ∀ x y z : R, le x y → le y z → le x z
  le_total : ∀ x y : R, le x y ∨ le y x

  -- I/III. Addition and order
  add_le_add_right : ∀ x y z : R, le x y → le (add x z) (add y z)

  -- II/III. Multiplication and order
  mul_nonneg : ∀ x y : R, le zero x → le zero y → le zero (mul x y)

  -- IV. Completeness, Zorich cut/separation form
  completeness :
    ∀ X Y : R → Prop,
      (∃ x, X x) →
      (∃ y, Y y) →
      (∀ x y, X x → Y y → le x y) →
      ∃ c : R, (∀ x, X x → le x c) ∧ (∀ y, Y y → le c y)

variable {R : Type u} (sys : RealAxiomSystem R)

def lt (x y : R) : Prop :=
  sys.le x y ∧ x ≠ y


lemma add_zero_right {R : Type u} (sys : RealAxiomSystem R) (x : R) :
    sys.add x sys.zero = x :=
  (sys.add_zero x).1

lemma zero_add_left {R : Type u} (sys : RealAxiomSystem R) (x : R) :
    sys.add sys.zero x = x :=
  (sys.add_zero x).2


theorem ZeroUnique (z : R)
  (zeroUniqueRight : ∀ x : R, sys.add x z = x)
  (zeroUniqueLeft : ∀ x : R, sys.add z x = x) : z = sys.zero := by
  have h0Z : sys.add z sys.zero = z := zeroUniqueLeft sys.zero

/-
  calc
    z = sys.add z sys.zero := by rw [add_zero_right sys z]
    _ = sys.zero := zeroUniqueLeft sys.zero
-/
  sorry

theorem AdditiveIdentityUnique (z : R)
    (zeroUniqueRight : ∀ x : R, sys.add x z = x)
    (zeroUniqueLeft : ∀ x : R, sys.add z x = x) : z = sys.zero := by

  -- 1. Specialize zeroUniqueRight to x = 0:
  have h0Z : sys.add sys.zero z = sys.zero := zeroUniqueRight sys.zero
  have hZ0 : sys.add z sys.zero = sys.zero := zeroUniqueLeft sys.zero
  have z0 : z = sys.zero := by
    rw [hZ0]
    exact h0Z




  sorry

end Laczkovich.RealAnalysis.Chapter03
