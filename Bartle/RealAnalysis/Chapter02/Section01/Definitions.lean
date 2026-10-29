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

variable {F : Type*} [Field F]

def addition (x y : F) : F := x + y

def multiplication (x y : F) : F := x * y

/-!
### Field axioms
-/

/-- The field axioms, grouped under Bartle's labels. -/
structure FieldAxiom (F : Type*) [Field F] : Prop where
  /-- (A1) Commutativity of addition. -/
  A1 : ∀ a b : F, a + b = b + a

  /-- (A2) Associativity of addition. -/
  A2 : ∀ a b c : F, (a + b) + c = a + (b + c)

  /-- (A3) Additive identity. -/
  A3 : ∀ a : F, 0 + a = a ∧ a + 0 = a

  /-- (A4) Additive inverses. -/
  A4 : ∀ a : F, a + (-a) = 0 ∧ (-a) + a = 0

  /-- (M1) Commutativity of multiplication. -/
  M1 : ∀ a b : F, a * b = b * a

  /-- (M2) Associativity of multiplication. -/
  M2 : ∀ a b c : F, (a * b) * c = a * (b * c)

  /-- (M3) Multiplicative identity. -/
  M3 : ∀ a : F, 1 * a = a ∧ a * 1 = a

  /-- (M4) Multiplicative inverses for nonzero elements. -/
  M4 : ∀ a : F, a ≠ 0 → ∃ b : F, a * b = 1 ∧ b * a = 1

  /-- (D) Distributivity of multiplication over addition. -/
  D : ∀ a b c : F, a * (b + c) = a * b + a * c

/-- Every Mathlib field satisfies the bundled field axioms. -/
theorem fieldAxiom (F : Type*) [Field F] : FieldAxiom F :=
  {
    A1 := add_comm
    A2 := add_assoc
    A3 := fun a => ⟨zero_add a, add_zero a⟩
    A4 := fun a => ⟨add_neg_cancel a, neg_add_cancel a⟩
    M1 := mul_comm
    M2 := mul_assoc
    M3 := fun a => ⟨one_mul a, mul_one a⟩
    M4 := by
      intro a ha
      exact ⟨1 / a, mul_one_div_cancel ha, one_div_mul_cancel ha⟩
    D := mul_add
  }

/-!
### Bartle & Sherbert Theorem 2.1.2
-/

/-- Bartle & Sherbert 2.1.2 (a): If z + a = a, then z = 0. -/
theorem Theoreom_2_1_2_a
    (z a : F) (h : z + a = a) : z = 0 := by
  calc
    z = z + 0        := (add_zero z).symm
    _ = z + (a + -a) := by rw [add_neg_cancel]
    _ = (z + a) + -a := (add_assoc z a (-a)).symm
    _ = a + -a       := by rw [h]
    _ = 0            := add_neg_cancel a

/-- Bartle & Sherbert 2.1.2 (b): Uniqueness of multiplicative identity. -/
theorem Theoreom_2_1_2_b
    (u b : F) (hb : b ≠ 0) (h : u * b = b) : u = 1 := by
  calc
    u = u * 1             := (mul_one u).symm
    _ = u * (b * (1 / b)) := by rw [mul_one_div_cancel hb]
    _ = (u * b) * (1 / b) := (mul_assoc u b (1 / b)).symm
    _ = b * (1 / b)       := by rw [h]
    _ = 1                 := mul_one_div_cancel hb

/-!
### Bartle & Sherbert Theorem 2.1.3
-/

/-- Bartle & Sherbert 2.1.3 (a): Uniqueness of additive inverse. -/
theorem Theoreom_2_1_3_a
    (a b : F) (h : a + b = 0) : b = -a := by
  calc
    b = b + 0        := (add_zero b).symm
    _ = b + (a + -a) := by rw [add_neg_cancel]
    _ = (b + a) + -a := (add_assoc b a (-a)).symm
    _ = (a + b) + -a := by rw [add_comm b a]
    _ = 0 + -a       := by rw [h]
    _ = -a           := zero_add (-a)

/-- Bartle & Sherbert 2.1.3 (b): Uniqueness of multiplicative inverse. -/
theorem Theoreom_2_1_3_b
    (a b : F) (ha : a ≠ 0) (h : a * b = 1) : b = 1 / a := by
  calc
    b = b * 1             := (mul_one b).symm
    _ = b * (a * (1 / a)) := by rw [mul_one_div_cancel ha]
    _ = (b * a) * (1 / a) := (mul_assoc b a (1 / a)).symm
    _ = (a * b) * (1 / a) := by rw [mul_comm b a]
    _ = 1 * (1 / a)       := by rw [h]
    _ = 1 / a             := one_mul (1 / a)

/-!
### Bartle & Sherbert Theorem 2.1.4: Irrationality of √2
-/

/-- If 2 divides n² for n : ℕ, then 2 divides n. -/
lemma nat_even_of_sq_even {n : ℕ} (h : 2 ∣ n ^ 2) : 2 ∣ n := by
  have hp : Nat.Prime 2 := Nat.prime_two
  rw [sq] at h
  cases (Nat.Prime.dvd_mul hp).mp h with
  | inl h1 => exact h1
  | inr h2 => exact h2

/-- No coprime pair of integers p and q satisfies p² = 2q². -/
lemma no_coprime_sq_eq_two
    (p q : ℤ)
    (h_coprime : p.natAbs.Coprime q.natAbs) :
    p ^ 2 ≠ 2 * q ^ 2 := by
  intro h_eq

  have h_nat_eq : p.natAbs ^ 2 = 2 * q.natAbs ^ 2 := by
    have h_abs := congrArg Int.natAbs h_eq
    simpa [Int.natAbs_pow, Int.natAbs_mul] using h_abs

  have hp_even : 2 ∣ p.natAbs := by
    apply nat_even_of_sq_even
    exact ⟨q.natAbs ^ 2, h_nat_eq⟩

  rcases hp_even with ⟨k, hk⟩

  have h_subst : (2 * k) ^ 2 = 2 * q.natAbs ^ 2 := by
    rwa [hk] at h_nat_eq

  have h_expand : (2 * k) ^ 2 = 2 * (2 * k ^ 2) := by
    ring

  have h_mul_eq : 2 * (2 * k ^ 2) = 2 * q.natAbs ^ 2 := by
    rwa [h_expand] at h_subst

  have hq2_eq : 2 * k ^ 2 = q.natAbs ^ 2 := by
    exact mul_left_cancel₀ (by decide : (2 : ℕ) ≠ 0) h_mul_eq

  have hq_even : 2 ∣ q.natAbs := by
    apply nat_even_of_sq_even
    exact ⟨k ^ 2, hq2_eq.symm⟩

  have hp_dvd : 2 ∣ p.natAbs := by
    exact ⟨k, hk⟩

  have h_dvd_gcd : 2 ∣ Nat.gcd p.natAbs q.natAbs :=
    Nat.dvd_gcd hp_dvd hq_even

  have h_gcd_eq_one : Nat.gcd p.natAbs q.natAbs = 1 := h_coprime
  rw [h_gcd_eq_one] at h_dvd_gcd
  norm_num at h_dvd_gcd

/-- There does not exist a rational number r such that r² = 2. -/
theorem Theorem_2_1_4 : ¬ ∃ r : ℚ, r ^ 2 = 2 := by
  rintro ⟨r, hr⟩

  have h_cleared : (r.num : ℤ) ^ 2 = 2 * (r.den : ℤ) ^ 2 := by
    have h_eval : (r.num : ℚ) / (r.den : ℚ) = r :=
      Rat.num_div_den r

    have h_sq : ((r.num : ℚ) / (r.den : ℚ)) ^ 2 = 2 := by
      rwa [h_eval]

    have h_den_ne : (r.den : ℚ) ≠ 0 :=
      Nat.cast_ne_zero.mpr r.den_nz

    have h_mul : (r.num : ℚ) ^ 2 = 2 * (r.den : ℚ) ^ 2 := by
      calc
        (r.num : ℚ) ^ 2 =
            ((r.num : ℚ) / (r.den : ℚ)) ^ 2 * (r.den : ℚ) ^ 2 := by
              rw [div_pow, div_mul_cancel₀ _ (pow_ne_zero 2 h_den_ne)]
        _ = 2 * (r.den : ℚ) ^ 2 := by rw [h_sq]

    exact_mod_cast h_mul

  have h_coprime : r.num.natAbs.Coprime (r.den : ℤ).natAbs := by
    simpa using r.reduced

  exact no_coprime_sq_eq_two r.num (r.den : ℤ) h_coprime h_cleared

/-!
### 2.1.5 Order axioms
-/

namespace Order

/-- Order axioms on the same field F, expressed through a positive cone. -/
structure Axioms (F : Type*) [Field F] where
  /-- The postulated positive cone. -/
  P : Set F

  /-- The positive cone is nonempty. -/
  P_nonempty : P.Nonempty

  /-- (i) Closure under addition in positive cone. -/
  add_closed :
    ∀ a b : F, a ∈ P → b ∈ P → a + b ∈ P

  /-- (ii) Closure under multiplication in positive cone. -/
  mul_closed :
    ∀ a b : F, a ∈ P → b ∈ P → a * b ∈ P

  /-- (iii) Exactly one of positivity, zero, or negativity holds. -/
  trichotomy :
    ∀ a : F,
      (a ∈ P ∧ a ≠ 0 ∧ -a ∉ P) ∨
      (a ∉ P ∧ a = 0 ∧ -a ∉ P) ∨
      (a ∉ P ∧ a ≠ 0 ∧ -a ∈ P)

/-!
### Sign predicates
-/
namespace Predicates

/-- An element is positive if it belongs to the positive cone. -/
def Positive (o : Order.Axioms F) (a : F) : Prop :=
  a ∈ o.P

/-- An element is nonnegative if it is positive or zero. -/
def Nonnegative (o : Order.Axioms F) (a : F) : Prop :=
  a ∈ o.P ∨ a = 0

/-- An element is negative if its additive inverse is positive. -/
def Negative (o : Order.Axioms F) (a : F) : Prop :=
  -a ∈ o.P

/-- An element is nonpositive if it is negative or zero. -/
def Nonpositive (o : Order.Axioms F) (a : F) : Prop :=
  -a ∈ o.P ∨ a = 0

end Predicates

/-!
### 2.1.6 Order relations
-/
namespace Relations

/-- a < b means b - a is positive. -/
def LessThan (o : Order.Axioms F) (a b : F) : Prop :=
  b - a ∈ o.P

/-- a > b means a - b is positive. -/
def GreaterThan (o : Order.Axioms F) (a b : F) : Prop :=
  a - b ∈ o.P

/-- a ≤ b means b - a is positive or zero. -/
def LessEqual (o : Order.Axioms F) (a b : F) : Prop :=
  b - a ∈ o.P ∨ b - a = 0

/-- a ≥ b means a - b is positive or zero. -/
def GreaterEqual (o : Order.Axioms F) (a b : F) : Prop :=
  a - b ∈ o.P ∨ a - b = 0

end Relations

end Order
/-!
### Bartle & Sherbert Theorem 2.1.7
-/
open Order.Relations Order.Predicates

/-- Bartle & Sherbert 2.1.7 (a): Transitivity. -/
theorem Theorem_2_1_7_a
    (o : Order.Axioms F) (a b c : F)
    (hab : GreaterThan o a b)
    (hbc : GreaterThan o b c) :
    GreaterThan o a c := by
  change a - b ∈ o.P at hab
  change b - c ∈ o.P at hbc
  have hagtc := o.add_closed (a-b) (b-c) hab hbc
  have hcancel : (a - b) + (b - c) = a - c := by
    ring
  rw [hcancel] at hagtc
  exact hagtc

/-- Bartle & Sherbert 2.1.7 (b): Addition preserves strict inequality. -/
theorem Theorem_2_1_7_b
    (o : Order.Axioms F) (a b c : F)
    (hab : GreaterThan o a b) :
    GreaterThan o (a + c) (b + c) := by
  unfold GreaterThan at hab
  unfold GreaterThan
  have hcancel : (a + c) - (b + c) = a - b := by
    ring
  rw [hcancel]
  exact hab

/-- Bartle & Sherbert 2.1.7 (c): Multiplication by a positive element
preserves strict inequality. -/
theorem Theorem_2_1_7_c_positive
    (o : Order.Axioms F) (a b c : F)
    (hab : GreaterThan o a b)
    (hc : GreaterThan o c 0) :
    GreaterThan o (c * a) (c * b) := by
  unfold GreaterThan at hab
  unfold GreaterThan
  have hcP : c ∈ o.P := by
    simpa [GreaterThan] using hc
  have hac := o.mul_closed c a
  have hbc := o.mul_closed c b
  have hcancel : (c * a) - (c * b) = c * a - c * b := by
    ring
  have hfactor : c * a - c * b = c * (a - b) := by
    ring
  rw [hfactor]
  exact o.mul_closed c (a - b) hcP hab

/-- Bartle & Sherbert 2.1.7 (c): Multiplication by a negative element
reverses strict inequality. -/
theorem Theorem_2_1_7_c_negative
    (o : Order.Axioms F) (a b c : F)
    (hab : GreaterThan o a b)
    (hc : LessThan o c 0) :
    LessThan o (c * a) (c * b) := by
  unfold GreaterThan at hab
  unfold LessThan at hc
  unfold LessThan
  have hncp : (-c) ∈ o.P := by
    simpa [sub_eq_add_neg] using hc
  have hfactor : (c * b) - (c * a) = (-c) * (a - b) := by
    ring
  rw [hfactor]
  exact o.mul_closed (-c) (a - b) hncp hab

/-- Bartle & Sherbert 2.1.8 (a): Every nonzero square is positive. -/
theorem Theorem_2_1_8_a
    (o : Order.Axioms F) (a : F) (ha : a ≠ 0) :
    GreaterThan o (a ^ 2) 0 := by
  rcases o.trichotomy a with
    ⟨hpos, hne, hnotneg⟩ |
    ⟨hnotpos, hzero, hnotneg⟩ |
    ⟨hnotpos, hne, hneg⟩
  · -- Positive case: you have hpos : a ∈ o.P.
    have h2pos := o.mul_closed a a
    have haa : a * a ∈ o.P := h2pos hpos hpos
    simpa [GreaterThan, pow_two] using haa
  · -- Zero case: you have hzero : a = 0.
    exact False.elim (ha hzero)
  · -- Negative case: you have hneg : -a ∈ o.P.
    have h2pos := o.mul_closed (-a) (-a)
    have haa : (-a) * (-a) ∈ o.P := h2pos hneg hneg
    simpa [GreaterThan, pow_two] using haa

/-- Bartle & Sherbert 2.1.8 (b): One is positive. -/
theorem Theorem_2_1_8_b
    (o : Order.Axioms F) :
    GreaterThan o (1 : F) 0 := by
  have h := Theorem_2_1_8_a o (1 : F)
  have hnn := h one_ne_zero
  simpa using hnn

/-- Bartle & Sherbert 2.1.8 (c): Every positive natural number
is positive when embedded in F. -/
theorem Theorem_2_1_8_c
    (o : Order.Axioms F) (n : ℕ) (h_nonzero : n ≠ 0) :
    GreaterThan o (n : F) 0 := by
  have h_one_mem : (1 : F) ∈ o.P := by
    simpa [GreaterThan] using Theorem_2_1_8_b o
  induction n with
  | zero =>
      exact False.elim (h_nonzero rfl)
  | succ n induction_hypothesis =>
      by_cases h_n_zero : n = 0
      · -- If n = 0, its successor is 1.
        have h_one_positive := Theorem_2_1_8_b o
        simpa [h_n_zero] using h_one_positive
      · -- If n ≠ 0, both n and 1 belong to the positive cone.
        have h_n_positive := induction_hypothesis h_n_zero
        have h_n_mem : (n : F) ∈ o.P := by
          simpa [GreaterThan] using h_n_positive
        have h_successor_mem : (n : F) + 1 ∈ o.P :=
          o.add_closed (n : F) 1 h_n_mem h_one_mem
        simpa [GreaterThan, Nat.cast_succ] using h_successor_mem

/-- Bartle & Sherbert 2.1.9: A nonnegative element smaller than
every positive element is zero. -/
theorem Theorem_2_1_9
    (o : Order.Axioms F) (a : F)
    (ha : LessEqual o 0 a)
    (hε : ∀ ε : F, GreaterThan o ε 0 → LessThan o a ε) :
    a = 0 := by
  by_cases h_a_zero : a = 0
  · --
    exact h_a_zero
  · -- Here h_a_zero : a ≠ 0.
    have h_a_positive : GreaterThan o a 0 := by
      rcases ha with h_positive | h_zero
      · --
        exact h_positive
      · --
        exact False.elim (h_a_zero (by simpa using h_zero))

    -- Continue with the a > 0 case.
    have hae := hε a h_a_positive
    have h_zero_mem : (0 : F) ∈ o.P := by
      simpa [LessThan] using hae
    have h_zero_not_mem : (0 : F) ∉ o.P := by
      rcases o.trichotomy (0 : F) with h_positive | h_zero | h_negative
      · exact False.elim (h_positive.2.1 rfl)
      · exact h_zero.1
      · exact h_negative.1
    exact False.elim (h_zero_not_mem h_zero_mem)

/-- Bartle & Sherbert 2.1.10: A positive product has factors
of the same sign. -/
theorem Theorem_2_1_10
    (o : Order.Axioms F) (a b : F)
    (hab : GreaterThan o (a * b) 0) :
    (GreaterThan o a 0 ∧ GreaterThan o b 0) ∨
    (LessThan o a 0 ∧ LessThan o b 0) := by
  constructor
  . --
    constructor
    . --
      have haP := a ∈ o.P
      have hbP := b ∈ o.P
     --have habP := o.mul_closed a b haP hbP

      sorry
    . --

      sorry


/-- Bartle & Sherbert 2.1.11: A negative product has factors
of opposite signs. -/
theorem Corollary_2_1_11
    (o : Order.Axioms F) (a b : F)
    (hab : LessThan o (a * b) 0) :
    (LessThan o a 0 ∧ GreaterThan o b 0) ∨
    (GreaterThan o a 0 ∧ LessThan o b 0) := by
  sorry

end Bartle.RealAnalysis.Chapter02
