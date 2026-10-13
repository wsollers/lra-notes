import Laczkovich.RealAnalysisI.Chapter03.Section04.Definitions

/-!
# Laczkovich–Sós, Real Analysis: Foundations and Functions of One Variable, §3.4 First Appendix — Theorems

Consequences of the field axioms (§3.4, p. 48).
-/

namespace Laczkovich.RealAnalysisI.Chapter03

variable {R : Type u} (F : FieldAxioms R)

/-- **Theorem 3.28** [Laczkovich–Sós, §3.4, p. 48]: the additive inverse is
unique — if a + b = 0 and a + c = 0 then b = c. The book proves it from
Axioms 1–3. -/
theorem AdditiveInverseUnique (a b c : R)
    (hb : F.add a b = F.zero) (hc : F.add a c = F.zero) : b = c := by
  sorry

end Laczkovich.RealAnalysisI.Chapter03
