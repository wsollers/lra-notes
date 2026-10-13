import Mathlib.SetTheory.ZFC.Basic

import Enderton.SetTheory.Chapter02.Definitions

/-!
# Herbert B. Enderton, Elements of Set Theory, Chapter 2: Axioms and Operations — Theorems

Prose notes belong in the chapter's notes.tex.
-/

namespace Enderton.SetTheory.Chapter02

/-- **Theorem 2A** (Chapter 2, "Axioms", p. 22): there is no set to which
every set belongs. Russell's argument, via Separation on a would-be universal
set; this version derives a contradiction from the assumed universal set. -/
theorem NoUniversalSet : ¬ ∃ A : ZFSet, ∀ x : ZFSet, x ∈ A := by
  rintro ⟨A, hA⟩
  set B := ZFSet.sep (fun x => x ∉ x) A with hB
  have hBA : B ∈ A := hA B
  by_cases h : B ∈ B
  · exact (ZFSet.mem_sep.mp h).2 h
  · exact h (ZFSet.mem_sep.mpr ⟨hBA, h⟩)


/-- **Theorem 2A**, following the book's proof: for any set `A`, the set
`{x ∈ A | x ∉ x}` is not a member of `A`. -/
theorem NoUniversalSet2 : ¬ ∃ A : ZFSet, ∀ x : ZFSet, x ∈ A := by
  push Not
  intro A
  set B := ZFSet.sep (fun x => x ∉ x) A with hB
  refine ⟨B, ?_⟩
  intro hBA
  by_cases h : B ∈ B
  · exact (ZFSet.mem_sep.mp h).2 h
  · exact h (ZFSet.mem_sep.mpr ⟨hBA, h⟩)

end Enderton.SetTheory.Chapter02
