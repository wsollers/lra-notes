import Common

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Real.Sqrt

/-!
# Chapter 1, Section 1.4 Exercises

Exercises at the end of [Thomson2008, §1.4, p. 10](http://classicalrealanalysis.com).
-/

namespace Bruckner.RealAnalysis.Chapter01

open Real

/-- **Exercise 1.4.1** [Thomson2008, §1.4, p. 10]. From the axioms alone:
if `a < b` and `c < d` then `ad + bc < ac + bd`. -/
exercise (a b c d : ℝ) (ha_lt_b : a < b) (hc_lt_d : c < d) :
    a * d + b * c < a * c + b * d := by

  have h1 : 0 < b - a := sub_pos.mpr ha_lt_b
  have h2 : 0 < d - c := sub_pos.mpr hc_lt_d
  have h_prod : 0 < (b - a) * (d - c) := mul_pos h1 h2
  linarith

/-- **Exercise 1.4.2** [Thomson2008, §1.4, p. 10]. Every natural number is at
most its square. The book's ℕ starts at 1; Lean's includes 0, where it also holds. -/
exercise : ∀ n : ℕ, n ≤ n ^ 2 := by
  intro n
  cases n with
  | zero =>
    -- If n = 0: 0 ≤ 0^2
    rfl
  | succ k =>
    -- Otherwise: n is of the form (k + 1), so n ≥ 1
    have h1 : 1 ≤ k + 1 := Nat.succ_le_succ (Nat.zero_le k)
    calc
      k + 1 = (k + 1) * 1       := by ring
      _     ≤ (k + 1) * (k + 1) := Nat.mul_le_mul_left (k + 1) h1
      _     = (k + 1) ^ 2       := by ring

/-- **Exercise 1.4.3** [Thomson2008, §1.4, p. 10]. The geometric mean of two
positive reals is at most their arithmetic mean. The book asks for a proof from
the axioms; this one uses mathlib's `Real.sqrt`. -/
named_exercise exercise_1_4_3 (a b : ℝ) (ha : a > 0) (hb : b > 0) :
    sqrt (a * b) ≤ (a + b) / 2 := by

  have h_sq : 0 ≤ (a - b) ^ 2 := sq_nonneg (a - b)
  have h_eq : (a + b) ^ 2 = 4 * a * b + (a - b) ^ 2 := by
    calc
      (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2         := by ring
      _           = 4 * a * b + (a ^ 2 - 2 * a * b + b ^ 2) := by ring
      _           = 4 * a * b + (a - b) ^ 2           := by ring

  -- Step 1: Deduce 4 * a * b ≤ (a + b) ^ 2 from h_eq and h_sq
  have h_4ab : 4 * a * b ≤ (a + b) ^ 2 := by
    linarith

  -- Step 2: Divide both sides by 4 to get a * b ≤ ((a + b) / 2) ^ 2
  have h_div : a * b ≤ ((a + b) / 2) ^ 2 := by
    linarith

  -- Step 3: Verify non-negativity of the arithmetic mean
  have h_am_nonneg : 0 ≤ (a + b) / 2 := by
    linarith

  -- Step 4: Take the square root of both sides
  have h_sqrt := Real.sqrt_le_sqrt h_div

  -- Step 5: Simplify sqrt (((a + b) / 2) ^ 2) to (a + b) / 2
  rw [Real.sqrt_sq h_am_nonneg] at h_sqrt
  exact h_sqrt

end Bruckner.RealAnalysis.Chapter01
