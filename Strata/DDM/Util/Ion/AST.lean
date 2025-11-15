/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
import Strata.DDM.Util.ByteArray
import Strata.DDM.Util.Decimal

namespace Ion

export Strata (Decimal)

inductive CoreType
| null
| bool
| int
| float
| decimal
| timestamp
| string
| symbol
| blob
| clob
| struct
| list
| sexp
deriving BEq, Repr, Inhabited

namespace CoreType

def codes : Array CoreType := #[
  .null, .bool, .int, .int,
  .float, .decimal, .timestamp, .symbol,
  .string, .clob, .blob, .list,
  .sexp, .struct
]

end CoreType

/--
Ion values.

Note. This represents most of the Ion 1.0 values, but is currently
missing support for timestamps, blobs, and clob values.  Those will
be added at a later date.
-/
inductive IonF (Sym : Type) (Ind : Type)
| null (tp : CoreType := .null)
| bool (b : Bool)
| int (i : Int)
| float (f : Float)
| decimal (d : Decimal)
-- TODO: Add timestamp
| string (s : String)
| symbol (s : Sym)
| blob (a : ByteArray)
-- TODO: Add clob
| struct (a : Array (Sym × Ind))
| list (a : Array Ind)
| sexp (a : Array Ind)
| annotation (annot : Array Sym) (v : Ind)
deriving BEq, Inhabited, Repr

structure Ion (α : Type) where
  app : IonF α (Ion α)
  deriving Repr, Inhabited, BEq

namespace Ion

def null (tp : CoreType := .null) : Ion Sym := .mk (.null tp)

def bool (b : Bool) : Ion Sym := .mk (.bool b)

def int (i : Int) : Ion Sym := .mk (.int i)

def float (f : Float) : Ion Sym := .mk (.float f)

def decimal (d : Decimal) : Ion Sym := .mk (.decimal d)

def string (s : String) : Ion Sym := .mk (.string s)

def symbol {Sym} (s : Sym) : Ion Sym := .mk (.symbol s)

def blob {Sym} (s : ByteArray) : Ion Sym := .mk (.blob s)

def struct (s : Array (Sym × Ion Sym)) : Ion Sym := .mk (.struct s)

def list (a : Array (Ion Sym)) : Ion Sym := .mk (.list a)

def sexp (a : Array (Ion Sym)) : Ion Sym := .mk (.sexp a)

def annotation (annot : Array Sym) (v : Ion Sym) : Ion Sym := .mk (.annotation annot v)

end Ion

/--
A symbolId denotes an index into an Ion symbol table.
-/
structure SymbolId where
  value : Nat
deriving DecidableEq, Inhabited, Repr

namespace SymbolId

protected def zero : SymbolId := ⟨0⟩

end SymbolId

instance : Coe SymbolId (Ion SymbolId) where
  coe := .symbol

end Ion
