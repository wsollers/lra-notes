import Common
import Mathlib.Tactic.Use
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Tactic.Ring


namespace Bartle.RealAnalysis.Chapter02

-- Note: 'Type*' without a space, and '[Field F]' to provide 0, -, +, *, and lemmas
variable {F : Type*} [Field F]

def addition (x y : F) : F := x + y

def multiplication (x y : F) : F := x * y

/-- (A1) Commutativity of Addition: a + b = b + a -/
theorem A1_add_comm (a b : F) : a + b = b + a :=
  add_comm a b

/-- (A2) Associativity of Addition: (a + b) + c = a + (b + c) -/
theorem A2_add_assoc (a b c : F) : (a + b) + c = a + (b + c) :=
  add_assoc a b c

/-- (A3) Existence of a Zero Element -/
theorem A3_add_zero (a : F) : 0 + a = a ∧ a + 0 = a :=
  ⟨zero_add a, add_zero a⟩

/-- (A4) Existence of Negative Elements -/
theorem A4_add_neg (a : F) : a + (-a) = 0 ∧ (-a) + a = 0 :=
  ⟨add_neg_cancel a, neg_add_cancel a⟩

/-- (M1) Commutativity of Multiplication: a * b = b *+* a -/
theorem M1_mul_comm (a b : F) : a * b = b * a :=
  mul_comm a b

/-- (M2) Associativity of Multiplication: (a * b) * c = a * (b * c) -/
theorem M2_mul_assoc (a b c : F) : (a * b) * c = a * (b * c) :=
  mul_assoc a b c

theorem M3_mul_ident (a : F) : 1 * a = a ∧ a * 1 = a :=
  ⟨one_mul a, mul_one a⟩

theorem M4_mul_recip (a : F) (hanezero : a ≠ 0) :
    ∃ b : F, a * b = 1 ∧ b * a = 1 := by
  use 1 / a
  constructor
  · exact mul_one_div_cancel hanezero
  · exact one_div_mul_cancel hanezero

theorem D_distrib_mul_over_add ( a b c: F) : a * ( b + c) = (a*b) + (a*c) := by
  ring

/-- Bartle & Sherbert 2.1.2 (a): If z + a = a, then z = 0 -/
theorem Theoreom_2_1_2_a (z a : F) (h : z + a = a) : z = 0 := by
  calc
    z = z            := rfl
    _ = z + 0        := (add_zero z).symm
    _ = z + (a + -a) := by rw [← add_neg_cancel a]
    _ = (z + a) + -a := (add_assoc z a (-a)).symm
    _ = a + -a       := by rw [h]
    _ = 0            := add_neg_cancel a

/-- Theorem 2.1.2 (b): Uniqueness of identity -/
theorem Theoreom_2_1_2_b (u b : F) (hb : b ≠ 0) (h : u * b = b) : u = 1 := by
  calc
    u = u                 := rfl
    _ = u * 1             := (mul_one u).symm
    _ = u * (b * (1 / b)) := by rw [mul_one_div_cancel hb]
    _ = (u * b) * (1 / b) := (mul_assoc u b (1 / b)).symm
    _ = b * (1 / b)       := by rw [h]
    _ = 1                 := mul_one_div_cancel hb

/-- Bartle & Sherbert 2.1.3 (a) -/
theorem Theoreom_2_1_3_a (a b : F) (h : a + b = 0) : b = -a := by
  calc
    b = b            := rfl
    _ = b + 0        := (add_zero b).symm
    _ = b + (a + -a) := by rw [add_neg_cancel]
    _ = (b + a) + -a := (add_assoc b a (-a)).symm
    _ = (a + b) + -a := by rw [add_comm b a]
    _ = 0 + -a       := by rw [h]
    _ = -a           := zero_add (-a)

/-- Bartle & Sherbert 2.1.3 (b) -/
theorem Theoreom_2_1_3_b (a b : F) (h : a ≠ 0) (h : a * b = 1) : b = 1/a := by
  sorry

end Bartle.RealAnalysis.Chapter02
