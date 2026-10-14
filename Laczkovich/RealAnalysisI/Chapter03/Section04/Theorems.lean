import Laczkovich.RealAnalysisI.Chapter03.Section04.Definitions

/-!
# Laczkovich–Sós, Real Analysis: Foundations and Functions of One Variable, §3.4 First Appendix — Theorems

Consequences of the field axioms (§3.4, from p. 48).
-/

universe u

namespace Laczkovich.RealAnalysisI.Chapter03

variable {R : Type u}

/-- **Theorem 3.28** [Laczkovich–Sós, §3.4, p. 48]: the additive inverse is
unique — if `a + b = 0` and `a + c = 0` then `b = c`. The book proves it from
Axioms 1–3. Lean: `neg_unique`. -/
theorem neg_unique [Add R] [Zero R]
    (h_ax1_add_comm : AddComm R) (h_ax2_add_assoc : AddAssoc R) (h_ax3_add_zero : AddZero R)
    {a b c : R} (hb : a + b = 0) (hc : a + c = 0) : b = c := by
  sorry

end Laczkovich.RealAnalysisI.Chapter03
