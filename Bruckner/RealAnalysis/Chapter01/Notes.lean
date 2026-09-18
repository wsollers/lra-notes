import Mathlib.Data.Real.Basic

import Bruckner.RealAnalysis.Chapter01.Basic

/-!
# Thomson/Bruckner, Elementary Real Analysis, Chapter 1 Notes

Reserve this file for independently written notes, Lean translation reminders,
and proof-pattern observations for Chapter 1.
-/

namespace Bruckner.RealAnalysis.Chapter01

def UpperBound (u : ℝ) (X : Set ℝ) : Prop :=
  ∀ x ∈ X, x ≤ u

def LowerBound (l : ℝ) (X : Set ℝ) : Prop :=
  ∀ x ∈ X, l ≤ x

def HasUpperBound (X : Set ℝ) : Prop :=
  ∃ u : ℝ, UpperBound u X

def HasLowerBound (X : Set ℝ) : Prop :=
  ∃ l : ℝ, LowerBound l X

def Maximum (u : ℝ) (X : Set ℝ) : Prop :=
  u ∈ X ∧ UpperBound u X

def Minimum (l : ℝ) (X : Set ℝ) : Prop :=
  l ∈ X ∧ LowerBound l X

def HasMaximum (X : Set ℝ) : Prop :=
  ∃ u ∈ X, UpperBound u X

def HasMinimum (X : Set ℝ) : Prop :=
  ∃ l ∈ X, LowerBound l X

end Bruckner.RealAnalysis.Chapter01
