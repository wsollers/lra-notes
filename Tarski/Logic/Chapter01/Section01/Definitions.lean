
import Common

/-!
# Alfred Tarski
## Introduction to Logic and to the Methodology of the Deductive Sciences

### Chapter I — On the Use of Variables
### §1 — Constants and Variables

This module records the elementary concepts introduced
in §1, without presupposing later logical machinery.
-/

namespace Tarski.Logic.Chapter01

/-! ## 1. Symbols -/

/--
A symbol is a written sign or term occurring in a
mathematical statement or proof.
-/
structure Symbol where
  name : String
  deriving Repr, DecidableEq, BEq

/-! ## 2. Constants and Variables -/

/--
A constant is a term or symbol having a well-determined
meaning which remains unchanged throughout the
considerations.
-/
structure Constant where
  symbol : Symbol
  deriving Repr, DecidableEq

/--
A variable is a symbol used as a variable in mathematical
statements and proofs.

Variables are generally represented by selected letters.
-/
structure Variable where
  symbol : Symbol
  deriving Repr, DecidableEq

/-! ## 4. Sentences and Statements -/

/--
A sentence is a linguistic expression occurring in
a scientific theory.

Tarski introduces sentences without yet specifying
their grammatical structure.
-/
structure Sentence where
  symbols : List Symbol
  deriving Repr, DecidableEq

/--
A statement is a sentence considered in the context
of mathematical assertions.

At this stage, we use the same underlying representation.

Tarski also uses "asserted statement" for a sentence
accepted as true within a scientific theory.
-/
abbrev Statement := Sentence


/-! ## 5. Proofs -/

/--
A proof is an argument whose purpose is to demonstrate
the truth of a statement.

At this introductory stage, its internal logical
structure is left unspecified.
-/
structure Proof where
  steps : List Statement
  deriving Repr, DecidableEq

/-! ## 6. Theorems -/

/--
A theorem is a statement established by a proof.

The structure records the statement and its accompanying
argument, without yet formalizing proof correctness.
-/
structure Theorem where
  statement : Statement
  proof     : Proof
  deriving Repr, DecidableEq

/-! ## 7. Laws -/

/--
A law is a statement accepted as true within a
scientific theory.

A law may be introduced as an asserted statement or
presented as a theorem established by proof.
-/
inductive Law where
  | asserted : Statement → Law
  | theorem  : Theorem → Law
  deriving Repr, DecidableEq

/-! ## 8. Scientific Theories -/

/--
A scientific theory is a system of sentences accepted
as true.

In mathematics, these statements occur in a definite
order and are generally accompanied by proofs.
-/
structure ScientificTheory where
  name : String
  laws : List Law
  deriving Repr, DecidableEq

end Tarski.Logic.Chapter01
