import Common
import Mathlib.Tactic.Use
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Tactic.Ring
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Int.GCD
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.GCD.Basic

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
theorem Theoreom_2_1_3_b (a b : F) (ha : a ≠ 0) (h : a * b = 1) : b = 1/a := by
  calc
    b = b                 := rfl
    _ = b * 1             := (mul_one b).symm
    _ = b * (a * (1 / a)) := by rw [mul_one_div_cancel ha]
    _ = (b * a) * (1 / a) := (mul_assoc b a (1 / a)).symm
    _ = (a * b) * (1 / a) := by rw [mul_comm b a]
    _ = 1 * (1 / a)       := by rw [h]
    _ = 1 / a             := one_mul (1 / a)

/-!
### Bartle Theorem 2.1.4: Irrationality of √2
-/

/-! ### Step 1: Parity on ℕ (Clean and cast-free) -/

/-- If 2 divides n^2 for n : ℕ, then 2 divides n. -/
lemma nat_even_of_sq_even {n : ℕ} (h : 2 ∣ n ^ 2) : 2 ∣ n := by
  have hp : Nat.Prime 2 := Nat.prime_two
  rw [sq] at h
  cases (Nat.Prime.dvd_mul hp).mp h with
  | inl h1 => exact h1
  | inr h2 => exact h2

/-- Theorem: No coprime pair of integers p and q satisfies p^2 = 2 * q^2. -/
theorem no_coprime_sq_eq_two (p q : ℤ) (h_coprime : p.natAbs.Coprime q.natAbs) :
    p ^ 2 ≠ 2 * q ^ 2 := by
  intro h_eq

  -- Translate the equation p^2 = 2 * q^2 entirely to Nat:
  have h_nat_eq : p.natAbs ^ 2 = 2 * q.natAbs ^ 2 := by
    have h_abs := congrArg Int.natAbs h_eq
    simpa [Int.natAbs_pow, Int.natAbs_mul] using h_abs

  -- 1. 2 ∣ p.natAbs^2 ==> 2 ∣ p.natAbs
  have hp_even : 2 ∣ p.natAbs := by
    apply nat_even_of_sq_even
    use q.natAbs ^ 2

  -- Write p.natAbs = 2 * k
  rcases hp_even with ⟨k, hk⟩

  -- 2. Substitute into (2 * k)^2 = 2 * q.natAbs^2
  have h_subst : (2 * k) ^ 2 = 2 * q.natAbs ^ 2 := by
    rwa [hk] at h_nat_eq

  -- Expand (2 * k)^2 to 2 * (2 * k^2)
  have h_expand : (2 * k) ^ 2 = 2 * (2 * k ^ 2) := by
    ring

  have h_mul_eq : 2 * (2 * k ^ 2) = 2 * q.natAbs ^ 2 := by
    rwa [h_expand] at h_subst

  -- Cancel the leading 2 using core Lean's Nat.mul_left_cancel
  have h_two_pos : 0 < 2 := by decide
  have hq2_eq : 2 * k ^ 2 = q.natAbs ^ 2 :=
    Nat.mul_left_cancel h_two_pos h_mul_eq

  -- 3. 2 ∣ q.natAbs^2 ==> 2 ∣ q.natAbs
  have hq_even : 2 ∣ q.natAbs := by
    apply nat_even_of_sq_even
    use k ^ 2
    exact hq2_eq.symm

  -- 4. Contradiction with Coprime (gcd = 1)
  have hp_dvd : 2 ∣ p.natAbs := by
    rw [hk]
    exact dvd_mul_right 2 k

  have h_dvd_gcd : 2 ∣ Nat.gcd p.natAbs q.natAbs :=
    Nat.dvd_gcd hp_dvd hq_even

  rw [Nat.Coprime] at h_coprime
  rw [h_coprime] at h_dvd_gcd
  revert h_dvd_gcd
  decide

end Bartle.RealAnalysis.Chapter02
