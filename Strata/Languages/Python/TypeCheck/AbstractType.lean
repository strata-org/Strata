/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

/-!
# Abstract Types for Python Type Checking

The abstract type lattice used by forward type analysis over SSA IR.
Separate from `SSA.PyType` (which annotates the IR); `AbstractType` is
the analysis-level representation with blame tracking and refinements.

Lattice structure:
- `bottom` — unreachable / no information
- `any(blame)` — top / unknown, with blame for error reporting
- Concrete types: int, str, bool, float, none, bytes, object
- `literal` — known literal value (more precise than its base type)
- `union` — set of alternative types
- `instance` — instance of a named class
- `callable` — a callable with a known signature name
-/

public section
namespace Strata.Python.TypeCheck

inductive Blame where
  | unknown (description : String)
  | uninit (varName : String)
  | unsupported (what : String)
deriving Inhabited, Repr, BEq

instance : ToString Blame where
  toString
    | .unknown d => d
    | .uninit v => s!"possibly uninitialized: {v}"
    | .unsupported w => s!"unsupported: {w}"

inductive LitValue where
  | int (v : Int)
  | str (v : String)
  | bool (v : Bool)
  | float (v : String)
  | none
deriving Inhabited, Repr, BEq

def LitValue.baseTypeName : LitValue → String
  | .int _ => "int"
  | .str _ => "str"
  | .bool _ => "bool"
  | .float _ => "float"
  | .none => "None"

inductive AbstractType where
  | bottom
  | any (blame : Blame)
  | int
  | str
  | bool
  | float
  | none
  | bytes
  | object
  | literal (val : LitValue)
  | union (alts : Array AbstractType)
  | instance_ (className : String)
  | callable (name : String)
deriving Inhabited, Repr

namespace AbstractType

def isBottom : AbstractType → Bool
  | .bottom => true
  | _ => false

def isAny : AbstractType → Bool
  | .any _ => true
  | _ => false

partial def toString : AbstractType → String
  | .bottom => "bottom"
  | .any blame => s!"Any({blame})"
  | .int => "int"
  | .str => "str"
  | .bool => "bool"
  | .float => "float"
  | .none => "None"
  | .bytes => "bytes"
  | .object => "object"
  | .literal (.int v) => s!"Literal({v})"
  | .literal (.str v) => s!"Literal(\"{v}\")"
  | .literal (.bool v) => s!"Literal({v})"
  | .literal (.float v) => s!"Literal({v})"
  | .literal .none => "Literal(None)"
  | .union alts => alts.toList.map toString |> " | ".intercalate
  | .instance_ name => name
  | .callable name => s!"Callable({name})"

instance : ToString AbstractType where
  toString := AbstractType.toString

/-- Widen a literal to its base type. -/
def widenLiteral : AbstractType → AbstractType
  | .literal (.int _) => .int
  | .literal (.str _) => .str
  | .literal (.bool _) => .bool
  | .literal (.float _) => .float
  | .literal .none => .none
  | t => t

protected partial def beq : AbstractType → AbstractType → Bool
  | .bottom, .bottom => true
  | .any _, .any _ => true
  | .int, .int => true
  | .str, .str => true
  | .bool, .bool => true
  | .float, .float => true
  | .none, .none => true
  | .bytes, .bytes => true
  | .object, .object => true
  | .literal a, .literal b => a == b
  | .instance_ a, .instance_ b => a == b
  | .callable a, .callable b => a == b
  | .union as_, .union bs =>
    as_.size == bs.size && as_.toList.all (fun a => bs.toList.any (AbstractType.beq a ·))
  | _, _ => false

instance : BEq AbstractType where
  beq := AbstractType.beq

/-- Flatten nested unions into a single-level array. -/
private partial def flattenUnion (acc : Array AbstractType) : AbstractType → Array AbstractType
  | .union alts => alts.foldl flattenUnion acc
  | .bottom => acc
  | t => if acc.any (· == t) then acc else acc.push t

/-- Least upper bound (join) of two types.
    Any ⊔ T = Any.  bottom ⊔ T = T.  Otherwise union. -/
partial def join (a b : AbstractType) : AbstractType :=
  if a == b then a
  else match a, b with
  | .bottom, t | t, .bottom => t
  | .any blame, _ | _, .any blame => .any blame
  | _, _ =>
    let flat := flattenUnion #[] a |> (flattenUnion · b)
    if flat.size == 1 then flat[0]!
    else .union flat

/-- Join an array of types. -/
def joinAll (types : Array AbstractType) : AbstractType :=
  types.foldl join .bottom

end AbstractType
end Strata.Python.TypeCheck
end -- public section
