import Mathlib.Topology.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Data.Set.Basic

/-!
# Bartle, Real Analysis, Chapter 11 (A Glimpse into Topology), §11.3 — Exercises

Statements about continuous functions `f : ℝ → ℝ` and subsets `A ⊆ ℝ`, together
with a topological classification of two subsets of `ℝ`.
-/

namespace Bartle.RealAnalysis.Chapter11

open Set

/-!
## Problem (b)

For each statement, we state either the universal property (if true)
or its negation / counterexample existence (if false).
-/

-- i) False: If A is open then f '' A is open.
-- Counterexample exists (e.g. constant function f x = 0 on ℝ)
theorem part_b_i : ¬ (∀ (f : ℝ → ℝ) (A : Set ℝ), Continuous f → IsOpen A → IsOpen (f '' A)) := by
  sorry

-- ii) True: If A is open then f ⁻¹' A is open.
theorem part_b_ii (f : ℝ → ℝ) (A : Set ℝ) (hf : Continuous f) (hA : IsOpen A) :
    IsOpen (f ⁻¹' A) := by
  sorry

-- iii) True: If A is compact then f '' A is compact.
theorem part_b_iii (f : ℝ → ℝ) (A : Set ℝ) (hf : Continuous f) (hA : IsCompact A) :
    IsCompact (f '' A) := by
  sorry

-- iv) True: If A is compact then f '' A is closed (compact in ℝ is closed).
theorem part_b_iv (f : ℝ → ℝ) (A : Set ℝ) (hf : Continuous f) (hA : IsCompact A) :
    IsClosed (f '' A) := by
  sorry

-- v) True: If A is compact then f '' A is bounded (compact in ℝ is bounded).
theorem part_b_v (f : ℝ → ℝ) (A : Set ℝ) (hf : Continuous f) (hA : IsCompact A) :
    Bornology.IsBounded (f '' A) := by
  sorry

-- vi) False: If A is closed then f '' A is bounded.
-- Counterexample exists (e.g. f(x) = x on closed set ℝ)
theorem part_b_vi :
    ¬ (∀ (f : ℝ → ℝ) (A : Set ℝ),
        Continuous f → IsClosed A → Bornology.IsBounded (f '' A)) := by
  sorry

-- vii) False: If A is compact then f ⁻¹' A is compact.
-- Counterexample exists (e.g. f(x) = 0, A = {0}, f⁻¹(A) = ℝ)
theorem part_b_vii :
    ¬ (∀ (f : ℝ → ℝ) (A : Set ℝ), Continuous f → IsCompact A → IsCompact (f ⁻¹' A)) := by
  sorry

-- viii) True: If A is connected then f '' A is connected.
theorem part_b_viii (f : ℝ → ℝ) (A : Set ℝ) (hf : Continuous f) (hA : IsConnected A) :
    IsConnected (f '' A) := by
  sorry

-- ix) False: If A is connected then f ⁻¹' A is connected.
-- Counterexample exists (e.g. f(x) = x², A = (1, 4), f⁻¹(A) = (-2, -1) ∪ (1, 2))
theorem part_b_ix :
    ¬ (∀ (f : ℝ → ℝ) (A : Set ℝ), Continuous f → IsConnected A → IsConnected (f ⁻¹' A)) := by
  sorry

-- x) False: f ⁻¹' (f '' A) = A for all f and A.
theorem part_b_x : ¬ (∀ (f : ℝ → ℝ) (A : Set ℝ), f ⁻¹' (f '' A) = A) := by
  sorry

-- xi) False: f ⁻¹' (f '' A) ⊆ A for all f and A.
theorem part_b_xi : ¬ (∀ (f : ℝ → ℝ) (A : Set ℝ), f ⁻¹' (f '' A) ⊆ A) := by
  sorry

-- xii) True: f ⁻¹' (f '' A) ⊇ A (i.e. A ⊆ f ⁻¹' (f '' A)).
theorem part_b_xii (f : ℝ → ℝ) (A : Set ℝ) :
    A ⊆ f ⁻¹' (f '' A) := by
  sorry

-- xiii) False: f '' (f ⁻¹' A) = A for all f and A.
theorem part_b_xiii : ¬ (∀ (f : ℝ → ℝ) (A : Set ℝ), f '' (f ⁻¹' A) = A) := by
  sorry

-- xiv) True: f '' (f ⁻¹' A) ⊆ A.
theorem part_b_xiv (f : ℝ → ℝ) (A : Set ℝ) :
    f '' (f ⁻¹' A) ⊆ A := by
  sorry

-- xv) False: f '' (f ⁻¹' A) ⊇ A (i.e. A ⊆ f '' (f ⁻¹' A)).
theorem part_b_xv : ¬ (∀ (f : ℝ → ℝ) (A : Set ℝ), A ⊆ f '' (f ⁻¹' A)) := by
  sorry

/-!
## Problem (c)

Topological and metric classification of subsets of `ℝ` under the properties
`IsOpen`, `IsClosed`, `Bornology.IsBounded`, `IsCompact`, `IsConnected`.
-/

-- i) S₁ = ℝ \ {0}: open, not closed, not bounded, not compact, not connected.
def S₁ : Set ℝ := univ \ {0}

theorem part_c_i_isOpen : IsOpen S₁ := by sorry
theorem part_c_i_not_isClosed : ¬ IsClosed S₁ := by sorry
theorem part_c_i_not_isBounded : ¬ Bornology.IsBounded S₁ := by sorry
theorem part_c_i_not_isCompact : ¬ IsCompact S₁ := by sorry
theorem part_c_i_not_isConnected : ¬ IsConnected S₁ := by sorry

-- ii) S₂ = ℝ \ [-1, 1]: open, not closed, not bounded, not compact, not connected.
def S₂ : Set ℝ := univ \ Icc (-1 : ℝ) 1

theorem part_c_ii_isOpen : IsOpen S₂ := by sorry
theorem part_c_ii_not_isClosed : ¬ IsClosed S₂ := by sorry
theorem part_c_ii_not_isBounded : ¬ Bornology.IsBounded S₂ := by sorry
theorem part_c_ii_not_isCompact : ¬ IsCompact S₂ := by sorry
theorem part_c_ii_not_isConnected : ¬ IsConnected S₂ := by sorry

end Bartle.RealAnalysis.Chapter11
