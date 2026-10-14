import Common

/-!
# Tarski, Introduction to Logic, Chapter 3 (On the Theory of Identity), §16 — Definitions

§16, "Logical concepts not belonging to sentential calculus; the concept of
identity" ([pp. 49–50](https://drive.google.com/file/d/1o98AJ7PAh5KMmiSim79q_dmaxvEVYQb9/view#page=74)).

**Identity.** "x is identical with y", "x is the same as y", and "x equals y"
all mean the same, written `x = y`. Identity is taken as primitive: here it is
a relation `I : D → D → Prop`, and `I x y` is Tarski's `x = y`. Lean's own `=`
is already defined, so laws about it would be theorems, not assumptions.

**Difference.** "x is not identical with y" and "x is different from y" are
written `x ≠ y`: `Different I x y`.

The general laws governing these expressions make up the **theory of
identity**, the subject of §17.
-/

universe u

namespace Tarski.Logic.Chapter03

/-- **Difference** [Tarski, §16, [pp. 49–50](https://drive.google.com/file/d/1o98AJ7PAh5KMmiSim79q_dmaxvEVYQb9/view#page=74)]: `x ≠ y`, "x is not
identical with y" or "x is different from y". Lean: `Ne`. -/
def Different {D : Type u} (I : D → D → Prop) (x y : D) : Prop :=
  ¬ I x y

end Tarski.Logic.Chapter03
