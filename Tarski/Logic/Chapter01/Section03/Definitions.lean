import Tarski.Logic.Chapter01.Section01.Definitions
import Tarski.Logic.Chapter01.Section02.Definitions

/-!
# Alfred Tarski
## Introduction to Logic and to the Methodology of the Deductive Sciences

### Chapter I — On the Use of Variables
### §3 — Universal and Existential Quantifiers

This module formalizes quantifiers and the sentence-formation rules that
produce universal sentences and existential sentences from sentential functions.
-/

namespace Tarski.Logic.Chapter01

/-! ## 1. Quantifier Symbols -/

/--
The universal quantifier symbol is commonly expressed in English by
the phrases "for every" or "for all", and symbolized by "∀".
-/
def universalQuantifierSymbol : Symbol := ⟨"∀"⟩

/--
The existential quantifier symbol is commonly expressed in English by
the phrases "there exists" or "for some", and symbolized by "∃".
-/
def existentialQuantifierSymbol : Symbol := ⟨"∃"⟩


/-! ## 2. Quantifiers -/

/--
A universal quantifier consists of the universal quantifier symbol
together with a bound variable (e.g., "for every x").
-/
structure UniversalQuantifier where
  boundVariable : Variable
  deriving Repr, DecidableEq

/--
An existential quantifier consists of the existential quantifier symbol
together with a bound variable (e.g., "there exists an x").
-/
structure ExistentialQuantifier where
  boundVariable : Variable
  deriving Repr, DecidableEq


/-! ## 3. Universal Sentences -/

/--
A universal sentence (or general sentence) is a sentence obtained
from a sentential function by prefixing it with a universal quantifier
governing a variable that occurs in that function.

Tarski: "If in a sentential function containing only one variable,
say x, we precede this function by the phrase: 'for every x'
(or 'for all x'), we obtain a sentence. ... Sentences of this kind
are called universal sentences (or general sentences)."
-/
structure UniversalSentence where
  /-- The variable bound by the universal quantifier. -/
  boundVariable : Variable
  /-- The underlying sentential function (the matrix or scope of the quantifier). -/
  matrix : SententialFunction
  deriving Repr, DecidableEq

/--
Render a `UniversalSentence` into a concrete `Sentence` by prefixing
the universal quantifier symbol and the variable symbol to the matrix symbols.
-/
def UniversalSentence.toSentence (u : UniversalSentence) : Sentence :=
  ⟨universalQuantifierSymbol :: u.boundVariable.symbol :: u.matrix.sentence.symbols⟩

/--
A sentence is universal if it is the concrete expansion of some
`UniversalSentence`.
-/
def IsUniversalSentence (s : Sentence) : Prop :=
  ∃ u : UniversalSentence, u.toSentence = s


/-! ## 4. Existential Sentences -/

/--
An existential sentence is a sentence obtained from a sentential
function by prefixing it with an existential quantifier.

Tarski: "Phrases of the form: 'there exists an x such that...'
are called existential quantifiers... sentences obtained by prefixing
such phrases are called existential sentences."
-/
structure ExistentialSentence where
  /-- The variable bound by the existential quantifier. -/
  boundVariable : Variable
  /-- The underlying sentential function. -/
  matrix : SententialFunction
  deriving Repr, DecidableEq

/--
Render an `ExistentialSentence` into a concrete `Sentence` by prefixing
the existential quantifier symbol and the variable symbol to the matrix symbols.
-/
def ExistentialSentence.toSentence (e : ExistentialSentence) : Sentence :=
  ⟨existentialQuantifierSymbol :: e.boundVariable.symbol :: e.matrix.sentence.symbols⟩

/--
A sentence is existential if it is the concrete expansion of some
`ExistentialSentence`.
-/
def IsExistentialSentence (s : Sentence) : Prop :=
  ∃ e : ExistentialSentence, e.toSentence = s


/-! ## 5. Quantified Sentences -/

/--
A quantified sentence is either a universal sentence or an
existential sentence formed by binding a variable in a sentential function.
-/
inductive QuantifiedSentence where
  | universal   : UniversalSentence → QuantifiedSentence
  | existential : ExistentialSentence → QuantifiedSentence
  deriving Repr, DecidableEq

/-- Convert any quantified sentence to its concrete underlying `Sentence`. -/
def QuantifiedSentence.toSentence : QuantifiedSentence → Sentence
  | .universal u   => u.toSentence
  | .existential e => e.toSentence

end Tarski.Logic.Chapter01
