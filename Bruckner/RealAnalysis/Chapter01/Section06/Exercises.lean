import Common

import Mathlib.Data.Real.Basic

import Bruckner.RealAnalysis.Chapter01.Definitions
import Bruckner.RealAnalysis.Chapter01.Section05
import Bruckner.RealAnalysis.Chapter01.Section06.Theorems

open Set

namespace Bruckner.RealAnalysis.Chapter01

variable (E A B : Set ℝ)
variable (M M' M₁ M₂ m m' m₁ m₂ : ℝ)



/--
**Exercise 1.6.1** [[Thomson2008, §1.6, p. 14](http://classicalrealanalysis.com)]
A set of real numbers $E$ is bounded if and only if there is a positive number $r$
so that $|x| < r$ for all $x \in E$.
-/
theorem exercise_1_6_1 :
    IsBounded E ↔ ∃ r : ℝ, r > 0 ∧ ∀ x ∈ E, |x| < r := by
  sorry

/--
**Exercise 1.6.3** [[Thomson2008, §1.6, p. 14](http://classicalrealanalysis.com)]
Under what conditions does $\sup E = \max E$?
-/
theorem exercise_1_6_3 (hM : IsLUB E M) :
    IsMaximum E M ↔ M ∈ E := by
  sorry

/--
**Exercise 1.6.4** [[Thomson2008, §1.6, p. 14](http://classicalrealanalysis.com)]
Every nonempty, finite set $E$ has $\sup E = \max E$.
-/
theorem exercise_1_6_4 (hne : E.Nonempty) (hfin : E.Finite) :
    ∃ M : ℝ, IsLUB E M ∧ IsMaximum E M := by
  sorry

/--
**Exercise 1.6.6 & 1.6.7 (Reflection $-A$)** [[Thomson2008, §1.6, p. 14](http://classicalrealanalysis.com)]
Let $B = \{-x : x \in A\}$. Then $\sup A = M \iff \inf B = -M$.
-/
def NegSet (A : Set ℝ) : Set ℝ := {y : ℝ | ∃ x ∈ A, y = -x}

theorem exercise_1_6_7_sup_to_inf (hA : IsLUB A M) :
    IsGLB (NegSet A) (-M) := by
  sorry

theorem exercise_1_6_7_inf_to_sup (hA : IsGLB A m) :
    IsLUB (NegSet A) (-m) := by
  sorry

/--
**Exercise 1.6.8 (Translation $A + r$)** [[Thomson2008, §1.6, p. 14](http://classicalrealanalysis.com)]
Let $B = \{x + r : x \in A\}$. Then $\sup B = \sup A + r$.
-/
def ShiftSet (A : Set ℝ) (r : ℝ) : Set ℝ := {y : ℝ | ∃ x ∈ A, y = x + r}

theorem exercise_1_6_8 (hA : IsLUB A M) (r : ℝ) :
    IsLUB (ShiftSet A r) (M + r) := by
  sorry

/--
**Exercise 1.6.9 (Positive Scaling $r \cdot A$)** [[Thomson2008, §1.6, p. 15](http://classicalrealanalysis.com)]
Let $B = \{xr : x \in A\}$ for $r > 0$. Then $\sup B = r \cdot \sup A$.
-/
def ScaleSet (A : Set ℝ) (r : ℝ) : Set ℝ := {y : ℝ | ∃ x ∈ A, y = x * r}

theorem exercise_1_6_9_pos (hA : IsLUB A M) {r : ℝ} (hr : r > 0) :
    IsLUB (ScaleSet A r) (M * r) := by
  sorry

theorem exercise_1_6_9_neg (hA : IsLUB A M) {r : ℝ} (hr : r < 0) :
    IsGLB (ScaleSet A r) (M * r) := by
  sorry

/--
**Exercise 1.6.10 (Monotonicity of Bounds)** [[Thomson2008, §1.6, p. 15](http://classicalrealanalysis.com)]
If $A \subseteq B$, then $\sup A \le \sup B$ and $\inf B \le \inf A$.
-/
theorem exercise_1_6_10_sup (hsub : A ⊆ B) (hA : IsLUB A M) (hB : IsLUB B M') :
    M ≤ M' := by
  sorry

theorem exercise_1_6_10_inf (hsub : A ⊆ B) (hA : IsGLB A m) (hB : IsGLB B m') :
    m' ≤ m := by
  sorry

/--
**Exercise 1.6.11 (Supremum of Union)** [[Thomson2008, §1.6, p. 15](http://classicalrealanalysis.com)]
$\sup(A \cup B) = \max(\sup A, \sup B)$.
-/
theorem exercise_1_6_11 (hA : IsLUB A M₁) (hB : IsLUB B M₂) :
    IsLUB (A ∪ B) (max M₁ M₂) := by
  sorry

/--
**Exercise 1.6.13 (Minkowski Sum: Sup)** [[Thomson2008, §1.6, p. 15](http://classicalrealanalysis.com)]
Let $C = \{x + y : x \in A, y \in B\}$. Then $\sup C = \sup A + \sup B$.
-/
def AddSet (A B : Set ℝ) : Set ℝ := {z : ℝ | ∃ x ∈ A, ∃ y ∈ B, z = x + y}

theorem exercise_1_6_13 (hA : IsLUB A M₁) (hB : IsLUB B M₂) :
    IsLUB (AddSet A B) (M₁ + M₂) := by
  sorry

/--
**Exercise 1.6.14 (Minkowski Sum: Inf)** [[Thomson2008, §1.6, p. 15](http://classicalrealanalysis.com)]
$\inf C = \inf A + \inf B$.
-/
theorem exercise_1_6_14 (hA : IsGLB A m₁) (hB : IsGLB B m₂) :
    IsGLB (AddSet A B) (m₁ + m₂) := by
  sorry

/--
**Exercise 1.6.16 (Non-Upper Bound Characterization)** [[Thomson2008, §1.6, p. 15](http://classicalrealanalysis.com)]
-/
theorem exercise_1_6_16 (x : ℝ) :
    ¬ IsUpperBound E x ↔ ∃ e ∈ E, e > x := by
  sorry

/--
**Exercise 1.6.17 (Supremum $\varepsilon$-Criterion)** [[Thomson2008, §1.6, p. 15](http://classicalrealanalysis.com)]
-/
theorem exercise_1_6_17 (x : ℝ) (hne : A.Nonempty) (hbdd : BoundedAbove A) :
    IsLUB A x ↔ IsUpperBound A x ∧ (∀ ε > 0, ∃ a' ∈ A, x - ε < a') := by
  sorry

/--
**Exercise 1.6.18 (Infimum $\varepsilon$-Criterion)** [[Thomson2008, §1.6, p. 15](http://classicalrealanalysis.com)]
-/
theorem exercise_1_6_18 (x : ℝ) (hne : A.Nonempty) (hbdd : BoundedBelow A) :
    IsGLB A x ↔ IsLowerBound A x ∧ (∀ ε > 0, ∃ a' ∈ A, a' < x + ε) := by
  sorry

/--
**Exercise 1.6.19 (Existence of GLB from Completeness)** [[Thomson2008, §1.6, p. 15](http://classicalrealanalysis.com)]
-/
theorem exercise_1_6_19 (hne : E.Nonempty) (hbdd : BoundedBelow E) :
    ∃ m : ℝ, IsGLB E m := by
  sorry

/--
**Exercise 1.6.23 (Set Distance)** [[Thomson2008, §1.6, p. 16](http://classicalrealanalysis.com)]
$\delta(A, B) = \inf \{|a - b| : a \in A, b \in B\}$.
-/
def SetDist (A B : Set ℝ) : Set ℝ := {d : ℝ | ∃ a ∈ A, ∃ b ∈ B, d = |a - b|}

theorem exercise_1_6_23_nat_complement_dist (δ : ℝ) :
    IsGLB (SetDist {x : ℝ | ∃ n : ℕ, n ≥ 1 ∧ x = (n : ℝ)} (univ \ {x : ℝ | ∃ n : ℕ, n ≥ 1 ∧ x = (n : ℝ)})) 0 := by
  sorry

end Bruckner.RealAnalysis.Chapter01
