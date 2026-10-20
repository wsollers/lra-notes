import Su.Topology.Chapter01.Definitions

/-!
# Starbird–Su, Topology Through Inquiry, Chapter 1 Theorems

Reserve this file for the theorems of Chapter 1 and their proofs. Prose notes
belong in the chapter's notes.tex.
-/

namespace Su.Topology.Chapter01


-- Page 11 Indexed DeMorgan's Law
-- Theorem 1.2
theorem IndexedDeMorgans (X : Set α) {K : ℕ} [NeZero K]
    (A : Fin K → Set α) :
    X \ IndexedUnion A =
      IndexedIntersection (fun k => X \ A k) ∧
    X \ IndexedIntersection A =
      IndexedUnion (fun k => X \ A k) := by
  sorry





end Su.Topology.Chapter01
