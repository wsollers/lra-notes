import Common

import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Lattice

/-!
# Michael Starbird and Francis Su, Topology Through Inquiry, Chapter 1

Reserve this module for the definitions and notation of Chapter 1 that the
theorems, examples, and exercises build on.
-/

namespace Su.Topology.Chapter01


variable {α : Type*}

-- Built-in membership syntax:
-- #check fun (a : α) (A : Set α) => a ∈ A

-- Page 9
def isElementOf (a : α) (A : Set α) : Prop :=
  a ∈ A

def isSubsetOf (A B : Set α) : Prop :=
  ∀ a ∈ A, a ∈ B

def isEqual (A B : Set α) : Prop :=
  isSubsetOf A B ∧ isSubsetOf B A

--Page 10

def Union (A B : Set α) : Set α := {x : α | x ∈ A ∨ x ∈ B}

def Intersection (A B : Set α) : Set α := {x : α | x ∈ A ∧ x ∈ B}

def Complement (A : Set α) : Set α := {x : α | x ∉ A}

--The author writes "Complement of A in B" for this, but I think "RelativeComplement" is better
def RelativeComplement (A B : Set α) : Set α := {x : α | x ∈ B ∧ x ∉ A}


-- Page 10 (Indexed operations)
variable {α : Type*}

/-- Indexed union over an entire type I -/
def IndexedUnion {I : Type*} (A : I → Set α) : Set α :=
  {x : α | ∃ i : I, x ∈ A i}

/-- Indexed intersection over an entire type I -/
def IndexedIntersection {I : Type*} (A : I → Set α) : Set α :=
  {x : α | ∀ i : I, x ∈ A i}

end Su.Topology.Chapter01
