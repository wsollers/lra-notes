import Common
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Bruckner.RealAnalysis.Chapter01.Basic

namespace Bruckner.RealAnalysis.Chapter01

/-!
# Chapter 1 Exercises

Reserve this file for selected real-analysis exercises that support the
metric, topology, and integration tracks.
-/



open Real

exercise gm_le_am (a b : ℝ) (ha : a > 0) (hb : b > 0) :
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

exercise n_le_nsq : ∀ n : ℕ, n ≤ n ^ 2 := by
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

--Using just the axioms, prove that ad + bc < ac + bd if a < b and c < d.
exercise ggg (a b c d : ℝ) (ha_lt_b : a < b) (hc_lt_d : c < d) :
    a * d + b * c < a * c + b * d := by

  have h1 : 0 < b - a := sub_pos.mpr ha_lt_b
  have h2 : 0 < d - c := sub_pos.mpr hc_lt_d
  have h_prod : 0 < (b - a) * (d - c) := mul_pos h1 h2
  linarith

end Bruckner.RealAnalysis.Chapter01
