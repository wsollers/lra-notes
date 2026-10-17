
import Tarski.Logic.Chapter01.Section01.Theorems

namespace Tarski.Logic.Chapter01

/-! ## Arithmetic Examples -/

namespace Arithmetic

def number : Constant :=
  { symbol := { name := "number" } }

def zero : Constant :=
  { symbol := { name := "0" } }

def one : Constant :=
  { symbol := { name := "1" } }

def sum : Constant :=
  { symbol := { name := "+" } }

def a : Variable :=
  { symbol := { name := "a" } }

def b : Variable :=
  { symbol := { name := "b" } }

def c : Variable :=
  { symbol := { name := "c" } }

end Arithmetic

end Tarski.Logic.Chapter01
