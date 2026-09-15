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


theorem AdditiveIdentityUnique (z : R)
    (zLeftIdentity : ∀ x : R, sys.add z x = x) : z = sys.zero := by

  calc
    z = sys.add z sys.zero := by rw [add_zero_right sys z]
    _ = sys.zero := zLeftIdentity sys.zero

lemma AdditiveInverseExists (x : R) :
  ∃ y : R, sys.add x y = sys.zero ∧ sys.add y x = sys.zero :=
  sys.exists_neg x

lemma LeftAdditiveInverse {x : R} :
  ∃ y : R, sys.add x y = sys.zero := by
  have ⟨y,hy⟩ := sys.exists_neg x
  use y
  rw [<-sys.add_comm x y] at hy
  exact hy.2

lemma RightAdditiveInverse {x : R} :
  ∃ y : R, sys.add y x = sys.zero := by
  have ⟨y,hy⟩ := sys.exists_neg x
  use y
  rw [<-sys.add_comm y x] at hy
  exact hy.2

theorem AdditiveInverseUnique (x y z : R)
  (yInverse : sys.add x y = sys.zero ∧ sys.add y x = sys.zero)
  (zInverse : sys.add x z = sys.zero ∧ sys.add z x = sys.zero) : y = z := by

  have hy := yInverse.1
  have hz := zInverse.1.symm
  have hyz := hy.trans hz
  rw [<-sys.add_comm y x] at hyz
  obtain ⟨xi, hxi⟩ := sys.exists_neg x
  have hx_xi : sys.add x xi = sys.zero := hxi.1
  have hxi_x : sys.add xi x = sys.zero := hxi.2

  have yz :
    sys.add (sys.add y x) xi = sys.add (sys.add x z) xi := by
    exact congrArg (fun t => sys.add t xi) hyz
  rw [sys.add_comm x z] at yz
  rw [← sys.add_assoc y x xi] at yz
  rw [← sys.add_assoc z x xi] at yz
  rw [hx_xi] at yz
  rw [add_zero_right sys y] at yz
  rw [add_zero_right sys z] at yz

  exact yz




end Laczkovich.RealAnalysis.Chapter03
