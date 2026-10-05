import Mathlib.SetTheory.ZFC.Basic

import Enderton.SetTheory.Chapter01.Basic

/-!
# Enderton, Elements of Set Theory, Chapter 1 Notes

Reserve this file for independently written notes, Lean translation reminders,
and proof-pattern observations for Chapter 1.
-/

namespace Enderton.SetTheory.Chapter01

/-- There is no set to which every set belongs (Russell's paradox, via
Separation on the would-be universal set). -/
theorem NoUniversalSet : ¬ ∃ A : ZFSet, ∀ x : ZFSet, x ∈ A := by
  rintro ⟨A, hA⟩
  set B := ZFSet.sep (fun x => x ∉ x) A with hB
  have hBA : B ∈ A := hA B
  by_cases h : B ∈ B
  · exact (ZFSet.mem_sep.mp h).2 h
  · exact h (ZFSet.mem_sep.mpr ⟨hBA, h⟩)


theorem NoUniversalSet2 : ¬ ∃ A : ZFSet, ∀ x : ZFSet, x ∈ A := by
  push Not
  intro A
  set B := ZFSet.sep (fun x => x ∉ x) A with hB
  refine ⟨B, ?_⟩
  intro hBA
  by_cases h : B ∈ B
  · exact (ZFSet.mem_sep.mp h).2 h
  · exact h (ZFSet.mem_sep.mpr ⟨hBA, h⟩)

end Enderton.SetTheory.Chapter01
