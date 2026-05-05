/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import Std.Data.HashMap.Basic

public section

namespace Strata.Python

/--
A fully-qualified Python identifier consisting of a module path and a name.
For example, `typing.List` has module "typing" and name "List".
-/
structure PythonIdent where
  pythonModule : String
  name : String
  deriving DecidableEq, Hashable, Inhabited, Ord, Repr

namespace PythonIdent

protected def ofString (s : String) : Option PythonIdent :=
  match s.revFind? '.' with
  | none => none
  | some idx =>
    some {
      pythonModule := s.extract s.startPos idx
      name := s.extract idx.next! s.endPos
    }

instance : ToString PythonIdent where
  toString i := s!"{i.pythonModule}.{i.name}"

end PythonIdent

/--
All overloads for a single function name: maps a string literal
argument value to the return type (`PythonIdent`), together with
the expected dispatch parameter name (e.g., `"service_name"`).

N.B. Current limitations: dispatch is always on the first positional argument
or the matching keyword argument, and only string literal values are extracted. -/
structure FunctionOverloads where
  /-- Expected keyword argument name for dispatch (from the PySpec). -/
  paramName : Option String := none
  /-- Literal value → return type. -/
  entries : Std.HashMap String PythonIdent := {}
deriving Inhabited

/-- Find the dispatch argument value from positional or keyword arguments.
    Prefers the first positional arg; falls back to the keyword arg whose
    name matches `paramName`. Returns `none` when no match is found. -/
def FunctionOverloads.findDispatchArg (fo : FunctionOverloads)
    (positionalArgs : Array α)
    (kwargPairs : List (Option String × α))
    : Option α :=
  if h : positionalArgs.size > 0 then some positionalArgs[0]
  else fo.paramName.bind fun expected =>
    kwargPairs.findSome? fun (name?, value) =>
      if name? == some expected then some value else none

/-- Dispatch table: function name → its overloads. -/
@[expose] abbrev OverloadTable := Std.HashMap String FunctionOverloads

end Strata.Python

end -- public section
