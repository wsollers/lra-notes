import Laczkovich.RealAnalysisI.Chapter03.Section04.Definitions

/-!
# Laczkovich–Sós, Real Analysis: Foundations and Functions of One Variable, §3.4 First Appendix — Theorems
-/

namespace Laczkovich.RealAnalysisI.Chapter03

variable {R : Type u} (sys : RealAxiomSystem R)

/-- **Theorem 3.28** (§3.4, p. 48): the additive inverse is unique. The book
derives it from axioms 1–3 with one-sided inverses; here the structure's
two-sided axioms are used. -/
theorem AdditiveInverseUnique (x y z : R)
  (yInverse : sys.add x y = sys.zero ∧ sys.add y x = sys.zero)
  (zInverse : sys.add x z = sys.zero ∧ sys.add z x = sys.zero) : y = z := by

  have hy := yInverse.1
  have hz := zInverse.1.symm
  have hyz := hy.trans hz
  rw [← sys.add_comm y x] at hyz
  obtain ⟨xi, hxi⟩ := sys.exists_neg x
  have hx_xi : sys.add x xi = sys.zero := hxi.1
  have hxi_x : sys.add xi x = sys.zero := hxi.2

  have yz :
    sys.add (sys.add y x) xi = sys.add (sys.add x z) xi := by
    exact congrArg (fun t => sys.add t xi) hyz
  rw [sys.add_comm x z] at yz
  rw [← sys.add_assoc y x xi] at yz
  rw [← sys.add_assoc z x xi] at yz
  rw [hx_xi] at yz
  rw [add_zero_right sys y] at yz
  rw [add_zero_right sys z] at yz

  exact yz

end Laczkovich.RealAnalysisI.Chapter03
